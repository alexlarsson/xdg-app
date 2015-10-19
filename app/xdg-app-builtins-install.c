/*
 * Copyright © 2014 Red Hat, Inc
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	 See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Authors:
 *       Alexander Larsson <alexl@redhat.com>
 */

#include "config.h"

#include <locale.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

#include <gio/gunixinputstream.h>

#include "libgsystem.h"
#include "libglnx/libglnx.h"

#include "xdg-app-builtins.h"
#include "xdg-app-utils.h"
#include "xdg-app-chain-input-stream.h"

static char *opt_arch;
static char **opt_gpg_file;

static GOptionEntry options[] = {
  { "arch", 0, 0, G_OPTION_ARG_STRING, &opt_arch, "Arch to install for", "ARCH" },
  { NULL }
};

static GOptionEntry options_bundle[] = {
  { "gpg-file", 0, 0, G_OPTION_ARG_FILENAME_ARRAY, &opt_gpg_file, "Check signatures with GPG key from FILE (- for stdin)", "FILE" },
  { NULL }
};

static GBytes *
read_gpg_data (GCancellable *cancellable,
               GError **error)
{
  g_autoptr(GInputStream) source_stream = NULL;
  g_autoptr(GOutputStream) mem_stream = NULL;
  guint n_keyrings = 0;
  g_autoptr(GPtrArray) streams = NULL;

  if (opt_gpg_file != NULL)
    n_keyrings = g_strv_length (opt_gpg_file);

  guint ii;

  streams = g_ptr_array_new_with_free_func (g_object_unref);

  for (ii = 0; ii < n_keyrings; ii++)
    {
      GInputStream *input_stream = NULL;

      if (strcmp (opt_gpg_file[ii], "-") == 0)
        {
          input_stream = g_unix_input_stream_new (STDIN_FILENO, FALSE);
        }
      else
        {
          g_autoptr(GFile) file = g_file_new_for_path (opt_gpg_file[ii]);
          input_stream = G_INPUT_STREAM(g_file_read (file, cancellable, error));

          if (input_stream == NULL)
            return NULL;
        }

      /* Takes ownership. */
      g_ptr_array_add (streams, input_stream);
    }

  /* Chain together all the --keyring options as one long stream. */
  source_stream = (GInputStream *) xdg_app_chain_input_stream_new (streams);

  mem_stream = g_memory_output_stream_new_resizable ();
  if (g_output_stream_splice (mem_stream, source_stream, G_OUTPUT_STREAM_SPLICE_CLOSE_TARGET, cancellable, error) < 0)
    return NULL;

  return g_memory_output_stream_steal_as_bytes (G_MEMORY_OUTPUT_STREAM (mem_stream));
}

gboolean
xdg_app_builtin_install_runtime (int argc, char **argv, GCancellable *cancellable, GError **error)
{
  gboolean ret = FALSE;
  g_autoptr(GOptionContext) context = NULL;
  g_autoptr(XdgAppDir) dir = NULL;
  g_autoptr(GFile) deploy_base = NULL;
  g_autoptr(GFile) origin = NULL;
  const char *repository;
  const char *runtime;
  const char *branch = "master";
  g_autofree char *ref = NULL;
  gboolean created_deploy_base = FALSE;

  context = g_option_context_new ("REPOSITORY RUNTIME [BRANCH] - Install a runtime");

  if (!xdg_app_option_context_parse (context, options, &argc, &argv, 0, &dir, cancellable, error))
    goto out;

  if (argc < 3)
    {
      usage_error (context, "REPOSITORY and RUNTIME must be specified", error);
      goto out;
    }

  repository = argv[1];
  runtime  = argv[2];
  if (argc >= 4)
    branch = argv[3];

  if (!xdg_app_is_valid_name (runtime))
    {
      xdg_app_fail (error, "'%s' is not a valid runtime name", runtime);
      goto out;
    }

  if (!xdg_app_is_valid_branch (branch))
    {
      xdg_app_fail (error, "'%s' is not a valid branch name", branch);
      goto out;
    }

  ref = xdg_app_build_runtime_ref (runtime, branch, opt_arch);

  deploy_base = xdg_app_dir_get_deploy_dir (dir, ref);
  if (g_file_query_exists (deploy_base, cancellable))
    {
      xdg_app_fail (error, "Runtime %s branch %s already installed", runtime, branch);
      goto out;
    }

  if (!xdg_app_dir_pull (dir, repository, ref,
                         cancellable, error))
    goto out;

  if (!g_file_make_directory_with_parents (deploy_base, cancellable, error))
    goto out;
  created_deploy_base = TRUE;

  origin = g_file_get_child (deploy_base, "origin");
  if (!g_file_replace_contents (origin, repository, strlen (repository), NULL, FALSE,
                                G_FILE_CREATE_NONE, NULL, cancellable, error))
    goto out;

  if (!xdg_app_dir_deploy (dir, ref, NULL, cancellable, error))
    goto out;

  xdg_app_dir_cleanup_removed (dir, cancellable, NULL);

  ret = TRUE;

 out:
  if (created_deploy_base && !ret)
    gs_shutil_rm_rf (deploy_base, cancellable, NULL);

  return ret;
}

gboolean
xdg_app_builtin_install_app (int argc, char **argv, GCancellable *cancellable, GError **error)
{
  gboolean ret = FALSE;
  g_autoptr(GOptionContext) context = NULL;
  g_autoptr(XdgAppDir) dir = NULL;
  g_autoptr(GFile) deploy_base = NULL;
  g_autoptr(GFile) origin = NULL;
  const char *repository;
  const char *app;
  const char *branch = "master";
  g_autofree char *ref = NULL;
  gboolean created_deploy_base = FALSE;

  context = g_option_context_new ("REPOSITORY APP [BRANCH] - Install an application");

  if (!xdg_app_option_context_parse (context, options, &argc, &argv, 0, &dir, cancellable, error))
    goto out;

  if (argc < 3)
    {
      usage_error (context, "REPOSITORY and APP must be specified", error);
      goto out;
    }

  repository = argv[1];
  app  = argv[2];
  if (argc >= 4)
    branch = argv[3];

  if (!xdg_app_is_valid_name (app))
    {
      xdg_app_fail (error, "'%s' is not a valid application name", app);
      goto out;
    }

  if (!xdg_app_is_valid_branch (branch))
    {
      xdg_app_fail (error, "'%s' is not a valid branch name", branch);
      goto out;
    }

  ref = xdg_app_build_app_ref (app, branch, opt_arch);

  deploy_base = xdg_app_dir_get_deploy_dir (dir, ref);
  if (g_file_query_exists (deploy_base, cancellable))
    {
      xdg_app_fail (error, "App %s branch %s already installed", app, branch);
      goto out;
    }

  if (!xdg_app_dir_pull (dir, repository, ref,
                         cancellable, error))
    goto out;

  if (!g_file_make_directory_with_parents (deploy_base, cancellable, error))
    goto out;
  created_deploy_base = TRUE;

  origin = g_file_get_child (deploy_base, "origin");
  if (!g_file_replace_contents (origin, repository, strlen (repository), NULL, FALSE,
                                G_FILE_CREATE_NONE, NULL, cancellable, error))
    goto out;

  if (!xdg_app_dir_deploy (dir, ref, NULL, cancellable, error))
    goto out;

  if (!xdg_app_dir_make_current_ref (dir, ref, cancellable, error))
    goto out;

  if (!xdg_app_dir_update_exports (dir, app, cancellable, error))
    goto out;

  xdg_app_dir_cleanup_removed (dir, cancellable, NULL);

  ret = TRUE;

 out:
  if (created_deploy_base && !ret)
    gs_shutil_rm_rf (deploy_base, cancellable, NULL);

  return ret;
}

#define OSTREE_STATIC_DELTA_META_ENTRY_FORMAT "(uayttay)"
#define OSTREE_STATIC_DELTA_FALLBACK_FORMAT "(yaytt)"
#define OSTREE_STATIC_DELTA_SUPERBLOCK_FORMAT "(a{sv}tayay" OSTREE_COMMIT_GVARIANT_STRING "aya" OSTREE_STATIC_DELTA_META_ENTRY_FORMAT "a" OSTREE_STATIC_DELTA_FALLBACK_FORMAT ")"

gboolean
xdg_app_builtin_install_bundle (int argc, char **argv, GCancellable *cancellable, GError **error)
{
  gboolean ret = FALSE;
  g_autoptr(GOptionContext) context = NULL;
  g_autoptr(XdgAppDir) dir = NULL;
  g_autoptr(GFile) deploy_base = NULL;
  g_autoptr(GFile) file = NULL;
  g_autoptr(GFile) gpg_tmp_file = NULL;
  g_autoptr(GBytes) bytes = NULL;
  const char *filename;
  g_autofree char *ref = NULL;
  g_autofree char *origin = NULL;
  g_autofree char *checksum = NULL;
  gboolean created_deploy_base = FALSE;
  gboolean added_remote = FALSE;
  g_autofree char *to_checksum = NULL;
  g_auto(GStrv) parts = NULL;
  OstreeGpgVerifyResult *gpg_result;
  g_autoptr(GBytes) gpg_data = NULL;
  g_autofree char *remote = NULL;
  OstreeRepo *repo;

  context = g_option_context_new ("BUNDLE - Install a application or runtime from a bundle");

  if (!xdg_app_option_context_parse (context, options_bundle, &argc, &argv, 0, &dir, cancellable, error))
    return FALSE;

  if (argc < 2)
    return usage_error (context, "BUNDLE must be specified", error);

  filename = argv[1];

  file = g_file_new_for_commandline_arg (filename);

  {
    g_autoptr(GVariant) delta = NULL;
    g_autoptr(GVariant) metadata = NULL;
    g_autoptr(GBytes) bytes = NULL;
    g_autoptr(GVariant) to_csum_v = NULL;
    g_autoptr(GVariant) gpg_value = NULL;

    GMappedFile *mfile = g_mapped_file_new (gs_file_get_path_cached (file), FALSE, error);
    bytes = g_mapped_file_get_bytes (mfile);
    g_mapped_file_unref (mfile);

    delta = g_variant_new_from_bytes (G_VARIANT_TYPE (OSTREE_STATIC_DELTA_SUPERBLOCK_FORMAT), bytes, FALSE);
    g_variant_ref_sink (delta);

    to_csum_v = g_variant_get_child_value (delta, 3);
    if (!ostree_validate_structureof_csum_v (to_csum_v, error))
      goto out;

    to_checksum = ostree_checksum_from_bytes_v (to_csum_v);

    metadata = g_variant_get_child_value (delta, 0);

    if (!g_variant_lookup (metadata, "ref", "s", &ref))
      return xdg_app_fail (error, "Invalid bundle, no ref in metadata");

    if (!g_variant_lookup (metadata, "origin", "s", &origin))
      origin = NULL;

    gpg_value = g_variant_lookup_value (metadata, "gpg-keys", G_VARIANT_TYPE("ay"));
    g_print ("gpg_value = %p\n", gpg_value);
    if (gpg_value)
      {
        gsize n_elements;
        const char *data = g_variant_get_fixed_array (gpg_value, &n_elements, 1);

        gpg_data = g_bytes_new (data, n_elements);
      }
  }

  parts = xdg_app_decompose_ref (ref, error);
  if (parts == NULL)
    return FALSE;

  deploy_base = xdg_app_dir_get_deploy_dir (dir, ref);
  if (g_file_query_exists (deploy_base, cancellable))
    return xdg_app_fail (error, "%s branch %s already installed", parts[1], parts[3]);

  repo = xdg_app_dir_get_repo (dir);

  if (opt_gpg_file != NULL)
    {
      /* Override gpg_data from file */
      gpg_data = read_gpg_data (cancellable, error);
      if (gpg_data == NULL)
        return FALSE;
    }

  /* Add a remote for later updates */
  if (origin != NULL)
    {
      g_auto(GStrv) remotes = ostree_repo_remote_list (repo, NULL);
      int version = 0;

      do
        {
          g_autofree char *name = NULL;
          if (version == 0)
            name = g_strdup_printf ("%s-origin", parts[1]);
          else
            name = g_strdup_printf ("%s-origin%d", parts[1], version);
          version++;

          if (!g_strv_contains ((const char * const *) remotes, name))
            remote = g_steal_pointer (&name);
        }
      while (remote == NULL);
    }

  if (!ostree_repo_prepare_transaction (repo, NULL, cancellable, error))
    return FALSE;

  ostree_repo_transaction_set_ref (repo, remote, ref, to_checksum);

  if (!ostree_repo_static_delta_execute_offline (repo,
                                                 file,
                                                 FALSE,
                                                 cancellable,
                                                 error))
    return FALSE;

  if (gpg_data)
    {
      g_autoptr(GFileIOStream) stream;
      GOutputStream *o;

      gpg_tmp_file = g_file_new_tmp (".xdg-app-XXXXXX", &stream, error);
      if (gpg_tmp_file == NULL)
        return FALSE;
      g_print ("writing gpg keys to %s\n", g_file_get_path (gpg_tmp_file));
      o = g_io_stream_get_output_stream (G_IO_STREAM (stream));
      if (!g_output_stream_write_all (o, g_bytes_get_data (gpg_data, NULL), g_bytes_get_size (gpg_data), NULL, cancellable, error))
        return FALSE;
    }

  gpg_result = ostree_repo_verify_commit_ext (repo,
                                              to_checksum,
                                              NULL, gpg_tmp_file, cancellable, error);

  if (gpg_tmp_file)
    g_file_delete (gpg_tmp_file, cancellable, NULL);

  if (gpg_result == NULL)
    return FALSE;

  /* TODO: Check verify */

  g_object_unref (gpg_result);

  if (!ostree_repo_commit_transaction (repo, NULL, cancellable, error))
    return FALSE;

  if (!g_file_make_directory_with_parents (deploy_base, cancellable, error))
    return FALSE;

  /* From here we need to goto out on error, to clean up */
  created_deploy_base = TRUE;

  if (remote)
    {
     if (!ostree_repo_remote_add (repo,
                                  remote, origin, /* options */ NULL, cancellable, error))
       goto out;
     }

  added_remote = TRUE;

  if (remote)
    {
      g_autoptr(GFile) origin_file = g_file_get_child (deploy_base, "origin");
      if (!g_file_replace_contents (origin_file, remote, strlen (remote), NULL, FALSE,
                                    G_FILE_CREATE_NONE, NULL, cancellable, error))
        goto out;
    }

  if (!xdg_app_dir_deploy (dir, ref, to_checksum, cancellable, error))
    goto out;

  if (!xdg_app_dir_make_current_ref (dir, ref, cancellable, error))
    goto out;

  if (strcmp (parts[0], "app") == 0)
    {
      if (!xdg_app_dir_update_exports (dir, parts[1], cancellable, error))
        goto out;
    }

  xdg_app_dir_cleanup_removed (dir, cancellable, NULL);

  ret = TRUE;

 out:
  if (created_deploy_base && !ret)
    gs_shutil_rm_rf (deploy_base, cancellable, NULL);

  if (added_remote && remote && !ret)
    ostree_repo_remote_delete (repo, remote, NULL, NULL);

  return ret;
}
