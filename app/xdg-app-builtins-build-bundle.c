/*
 * Copyright © 2015 Red Hat, Inc
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

#ifdef HAVE_LIBARCHIVE
#include <archive.h>
#include <archive_entry.h>
#endif

static char *opt_arch;
static char *opt_repo_url;
static gboolean opt_runtime = FALSE;
static char **opt_gpg_file;
static gboolean opt_oci = FALSE;

static GOptionEntry options[] = {
  { "runtime", 0, 0, G_OPTION_ARG_NONE, &opt_runtime, "Export runtime instead of app"},
  { "arch", 0, 0, G_OPTION_ARG_STRING, &opt_arch, "Arch to bundle for", "ARCH" },
  { "repo-url", 0, 0, G_OPTION_ARG_STRING, &opt_repo_url, "Url for repo", "URL" },
  { "gpg-keys", 0, 0, G_OPTION_ARG_FILENAME_ARRAY, &opt_gpg_file, "Add GPG key from FILE (- for stdin)", "FILE" },
  { "oci", 0, 0, G_OPTION_ARG_NONE, &opt_oci, "Export oci image instead of xdg-app bundle"},

  { NULL }
};

static GBytes *
read_gpg_data (GCancellable *cancellable,
               GError **error)
{
  g_autoptr(GInputStream) source_stream = NULL;
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

  return xdg_app_read_stream (source_stream, FALSE, error);
}

static gboolean
build_bundle (OstreeRepo *repo, GFile *file,
              const char *name, const char *full_branch,
              GCancellable *cancellable, GError **error)
{
  GVariantBuilder metadata_builder;
  GVariantBuilder param_builder;
  g_autoptr(GKeyFile) keyfile = NULL;
  g_autoptr(GFile) xmls_dir = NULL;
  g_autoptr(GFile) metadata_file = NULL;
  g_autoptr(GFile) appstream_file = NULL;
  g_autofree char *appstream_basename = NULL;
  g_autoptr(GInputStream) in = NULL;
  g_autoptr(GInputStream) xml_in = NULL;
  g_autoptr(GFile) root = NULL;
  g_autofree char *commit_checksum = NULL;
  g_autoptr(GBytes) gpg_data = NULL;

  if (!ostree_repo_resolve_rev (repo, full_branch, FALSE, &commit_checksum, error))
    return FALSE;

  if (!ostree_repo_read_commit (repo, commit_checksum, &root, NULL, NULL, error))
    return FALSE;

  g_variant_builder_init (&metadata_builder, G_VARIANT_TYPE ("a{sv}"));

  /* We add this first in the metadata, so this will become the file
   * format header.  The first part is readable to make it easy to
   * figure out the type. The uint32 is basically a random value, but
   * it ensures we have both zero and high bits sets, so we don't get
   * sniffed as text. Also, the last 01 can be used as a version
   * later.  Furthermore, the use of an uint32 lets use detect
   * byteorder issues.
   */
  g_variant_builder_add (&metadata_builder, "{sv}", "xdg-app",
                         g_variant_new_uint32 (0xe5890001));

  g_variant_builder_add (&metadata_builder, "{sv}", "ref", g_variant_new_string (full_branch));

  metadata_file = g_file_resolve_relative_path (root, "metadata");

  keyfile = g_key_file_new ();

  in = (GInputStream*)g_file_read (metadata_file, cancellable, NULL);
  if (in != NULL)
    {
      g_autoptr(GBytes) bytes = xdg_app_read_stream (in, TRUE, error);

      if (bytes == NULL)
        return FALSE;

      if (!g_key_file_load_from_data (keyfile,
                                      g_bytes_get_data (bytes, NULL),
                                      g_bytes_get_size (bytes),
                                      G_KEY_FILE_NONE, error))
        return FALSE;

      g_variant_builder_add (&metadata_builder, "{sv}", "metadata",
                             g_variant_new_string (g_bytes_get_data (bytes, NULL)));
    }

  xmls_dir = g_file_resolve_relative_path (root, "files/share/app-info/xmls");
  appstream_basename = g_strconcat (name, ".xml.gz", NULL);
  appstream_file = g_file_get_child (xmls_dir, appstream_basename);

  xml_in = (GInputStream*)g_file_read (appstream_file, cancellable, NULL);
  if (xml_in)
    {
      g_autoptr(XdgAppXml) appstream_root = NULL;
      g_autoptr(XdgAppXml) xml_root = xdg_app_xml_parse (xml_in, TRUE,
                                                         cancellable, error);
      if (xml_root == NULL)
        return FALSE;

      appstream_root = xdg_app_appstream_xml_new ();
      if (xdg_app_appstream_xml_migrate (xml_root, appstream_root,
                                         full_branch, name, keyfile))
        {
          g_autoptr(GBytes) xml_data = xdg_app_appstream_xml_root_to_data (appstream_root, error);
          int i;
          g_autoptr(GFile) icons_dir =
            g_file_resolve_relative_path (root,
                                          "files/share/app-info/icons/xdg-app");
          const char *icon_sizes[] = { "64x64", "128x128" };
          const char *icon_sizes_key[] = { "icon-64", "icon-128" };
          g_autofree char *icon_name = g_strconcat (name, ".png", NULL);

          if (xml_data == NULL)
            return FALSE;

          g_variant_builder_add (&metadata_builder, "{sv}", "appdata",
                                 g_variant_new_from_bytes (G_VARIANT_TYPE_BYTESTRING,
                                                           xml_data, TRUE));

          for (i = 0; i < G_N_ELEMENTS (icon_sizes); i++)
            {
              g_autoptr(GFile) size_dir =g_file_get_child (icons_dir, icon_sizes[i]);
              g_autoptr(GFile) icon_file = g_file_get_child (size_dir, icon_name);
              g_autoptr(GInputStream) png_in = NULL;

              png_in = (GInputStream*)g_file_read (icon_file, cancellable, NULL);
              if (png_in != NULL)
                {
                  g_autoptr(GBytes) png_data = xdg_app_read_stream (png_in, FALSE, error);
                  if (png_data == NULL)
                    return FALSE;

                  g_variant_builder_add (&metadata_builder, "{sv}", icon_sizes_key[i],
                                         g_variant_new_from_bytes (G_VARIANT_TYPE_BYTESTRING,
                                                                   png_data, TRUE));
                }
            }
        }

    }

  if (opt_repo_url)
    g_variant_builder_add (&metadata_builder, "{sv}", "origin", g_variant_new_string (opt_repo_url));

  if (opt_gpg_file != NULL)
    {
      gpg_data = read_gpg_data (cancellable, error);
      if (gpg_data == NULL)
        return FALSE;
    }

  if (gpg_data)
    g_variant_builder_add (&metadata_builder, "{sv}", "gpg-keys",
                           g_variant_new_fixed_array (G_VARIANT_TYPE_BYTE,
                                                      g_bytes_get_data (gpg_data, NULL),
                                                      g_bytes_get_size (gpg_data),
                                                      1));

  g_variant_builder_init (&param_builder, G_VARIANT_TYPE ("a{sv}"));
  g_variant_builder_add (&param_builder, "{sv}", "min-fallback-size", g_variant_new_uint32 (0));
  g_variant_builder_add (&param_builder, "{sv}", "compression", g_variant_new_byte ('x'));
  g_variant_builder_add (&param_builder, "{sv}", "bsdiff-enabled", g_variant_new_boolean (FALSE));
  g_variant_builder_add (&param_builder, "{sv}", "inline-parts", g_variant_new_boolean (TRUE));
  g_variant_builder_add (&param_builder, "{sv}", "include-detached", g_variant_new_boolean (TRUE));
  g_variant_builder_add (&param_builder, "{sv}", "filename", g_variant_new_bytestring (gs_file_get_path_cached (file)));

  if (!ostree_repo_static_delta_generate (repo,
                                          OSTREE_STATIC_DELTA_GENERATE_OPT_LOWLATENCY,
                                          /* from */ NULL,
                                          commit_checksum,
                                          g_variant_builder_end (&metadata_builder),
                                          g_variant_builder_end (&param_builder),
                                          cancellable,
                                          error))
    return FALSE;

  return TRUE;
}

#if defined(HAVE_LIBARCHIVE) && defined(HAVE_OSTREE_EXPORT_PATH_PREFIX)

GLNX_DEFINE_CLEANUP_FUNCTION(void*, xdg_app_local_free_read_archive, archive_read_free)
#define free_read_archive __attribute__ ((cleanup(xdg_app_local_free_read_archive)))

GLNX_DEFINE_CLEANUP_FUNCTION(void*, xdg_app_local_free_write_archive, archive_write_free)
#define free_write_archive __attribute__ ((cleanup(xdg_app_local_free_write_archive)))

GLNX_DEFINE_CLEANUP_FUNCTION(void*, xdg_app_local_free_archive_entry, archive_entry_free)
#define free_archive_entry __attribute__ ((cleanup(xdg_app_local_free_archive_entry)))

static gboolean
propagate_libarchive_error (GError      **error,
                            struct archive *a)
{
  g_set_error (error, G_IO_ERROR, G_IO_ERROR_FAILED,
               "%s", archive_error_string (a));
  return FALSE;
}

struct archive_entry *
new_entry (struct archive *a,
           const char *name,
           OstreeRepoExportArchiveOptions *opts)
{
  struct archive_entry *entry = archive_entry_new2 (a);
  time_t ts = (time_t) opts->timestamp_secs;

  archive_entry_update_pathname_utf8 (entry, name);
  archive_entry_set_ctime (entry, ts, 0);
  archive_entry_set_mtime (entry, ts, 0);
  archive_entry_set_atime (entry, ts, 0);
  archive_entry_set_uid (entry, 0);
  archive_entry_set_gid (entry, 0);

  return entry;
}


static gboolean
add_dir (struct archive *a,
         const char *name,
         OstreeRepoExportArchiveOptions *opts,
         GError **error)
{
  free_archive_entry struct archive_entry *entry = new_entry (a, name, opts);

  archive_entry_set_mode (entry, AE_IFDIR | 0755);

  if (archive_write_header (a, entry) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  return TRUE;
}

static gboolean
add_symlink (struct archive *a,
             const char *name,
             const char *target,
             OstreeRepoExportArchiveOptions *opts,
             GError **error)
{
  free_archive_entry struct archive_entry *entry = new_entry (a, name, opts);

  archive_entry_set_mode (entry, AE_IFLNK | 0755);
  archive_entry_set_symlink (entry, target);

  if (archive_write_header (a, entry) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  return TRUE;
}

static gboolean
add_file (struct archive *a,
          const char *name,
          OstreeRepo *repo,
          GFile *file,
          OstreeRepoExportArchiveOptions *opts,
          GCancellable *cancellable,
          GError **error)
{
  free_archive_entry struct archive_entry *entry = new_entry (a, name, opts);
  guint8 buf[8192];
  g_autoptr(GInputStream) file_in = NULL;
  g_autoptr(GFileInfo) file_info = NULL;
  const char *checksum;

  checksum = ostree_repo_file_get_checksum ((OstreeRepoFile*)file);

  if (!ostree_repo_load_file (repo, checksum, &file_in, &file_info, NULL,
                              cancellable, error))
    return FALSE;

  archive_entry_set_uid (entry, g_file_info_get_attribute_uint32 (file_info, "unix::uid"));
  archive_entry_set_gid (entry, g_file_info_get_attribute_uint32 (file_info, "unix::gid"));
  archive_entry_set_mode (entry, g_file_info_get_attribute_uint32 (file_info, "unix::mode"));
  archive_entry_set_size (entry, g_file_info_get_size (file_info));

  if (archive_write_header (a, entry) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  while (TRUE)
    {
      ssize_t r;
      gssize bytes_read = g_input_stream_read (file_in, buf, sizeof (buf),
                                               cancellable, error);
      if (bytes_read < 0)
        return FALSE;;
      if (bytes_read == 0)
        break;

      r = archive_write_data (a, buf, bytes_read);
      if (r != bytes_read)
        return propagate_libarchive_error (error, a);
    }

  if (archive_write_finish_entry (a) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  return TRUE;
}

static gboolean
add_file_from_data (struct archive *a,
                    const char *name,
                    OstreeRepo *repo,
                    const char *data,
                    gsize size,
                    OstreeRepoExportArchiveOptions *opts,
                    GCancellable *cancellable,
                    GError **error)
{
  free_archive_entry struct archive_entry *entry = new_entry (a, name, opts);
  ssize_t r;

  archive_entry_set_mode (entry, AE_IFREG | 0755);
  archive_entry_set_size (entry, size);

  if (archive_write_header (a, entry) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  r = archive_write_data (a, data, size);
  if (r != size)
    return propagate_libarchive_error (error, a);

  if (archive_write_finish_entry (a) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  return TRUE;
}

#endif

static gboolean
build_oci (OstreeRepo *repo, GFile *file,
           const char *name, const char *full_branch,
           GCancellable *cancellable, GError **error)
{
#if !defined(HAVE_OSTREE_EXPORT_PATH_PREFIX)
  g_set_error (error, G_IO_ERROR, G_IO_ERROR_NOT_SUPPORTED,
               "This version of ostree is to old to support OCI exports");
  return FALSE;
#elif !defined(HAVE_LIBARCHIVE)
  g_set_error (error, G_IO_ERROR, G_IO_ERROR_NOT_SUPPORTED,
               "This version of xdg-app is not compiled with libarchive support");
  return FALSE;
#else
  struct free_write_archive archive *a = NULL;
  OstreeRepoExportArchiveOptions opts = { 0, };
  g_autoptr(GFile) root = NULL;
  g_autoptr(GFile) files = NULL;
  g_autoptr(GFile) export = NULL;
  g_autoptr(GFile) metadata = NULL;
  g_autoptr(GVariant) commit_data = NULL;
  g_autoptr(GVariant) commit_metadata = NULL;
  g_autofree char *commit_checksum = NULL;

  if (!ostree_repo_resolve_rev (repo, full_branch, FALSE, &commit_checksum, error))
    return FALSE;

  if (!ostree_repo_read_commit (repo, commit_checksum, &root, NULL, NULL, error))
    return FALSE;

  if (!ostree_repo_load_variant (repo, OSTREE_OBJECT_TYPE_COMMIT, commit_checksum, &commit_data, error))
    return FALSE;

  if (!ostree_repo_read_commit_detached_metadata (repo, commit_checksum, &commit_metadata, cancellable, error))
    return FALSE;

  a = archive_write_new ();

  if (archive_write_set_format_gnutar (a) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  if (archive_write_add_filter_none (a) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  if (archive_write_open_filename (a, gs_file_get_path_cached (file)) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  opts.timestamp_secs = ostree_commit_get_timestamp (commit_data);

  files = g_file_get_child (root, "files");
  export = g_file_get_child (root, "export");
  metadata = g_file_get_child (root, "metadata");

  if (opt_runtime)
    opts.path_prefix = "usr/";
  else
    opts.path_prefix = "app/";

  {
    const char *root_dirs[] = { "dev", "home", "proc", "run", "sys", "tmp", "var", "opt", "srv", "media", "mnt" };
    const char *root_symlinks[] = {
      "etc", "usr/etc",
      "lib", "usr/lib",
      "lib64", "usr/lib64",
      "lib32", "usr/lib32",
      "bin", "usr/bin",
      "sbin", "usr/sbin",
      "var/tmp", "/tmp",
      "var/run", "/run",
    };
    int i;

    /* Add the "other" of /app & /usr */
    if (!add_dir (a, opt_runtime ? "app" : "usr", &opts, error))
      return FALSE;

    for (i = 0; i < G_N_ELEMENTS (root_dirs); i++)
      if (!add_dir (a, root_dirs[i], &opts, error))
        return FALSE;

    for (i = 0; i < G_N_ELEMENTS (root_symlinks); i += 2)
      if (!add_symlink (a, root_symlinks[i], root_symlinks[i+1], &opts, error))
        return FALSE;
  }

  if (!ostree_repo_export_tree_to_archive (repo, &opts, (OstreeRepoFile*)files, a,
                                           cancellable, error))
    return FALSE;

  if (!opt_runtime && g_file_query_exists (export, NULL))
    {
      opts.path_prefix = "export";
      if (!ostree_repo_export_tree_to_archive (repo, &opts, (OstreeRepoFile*)export, a,
                                               cancellable, error))
        return FALSE;
    }

  opts.path_prefix = NULL;
  if (!add_file (a, ".metadata", repo, metadata, &opts, cancellable, error))
    return FALSE;

  if (!add_file_from_data (a, ".ref",
                           repo,
                           full_branch,
                           strlen (full_branch),
                           &opts, cancellable, error))
    return FALSE;

  if (!add_file_from_data (a, ".commit",
                           repo,
                           g_variant_get_data (commit_data),
                           g_variant_get_size (commit_data),
                           &opts, cancellable, error))
    return FALSE;

  if (commit_metadata != NULL)
    {
      if (!add_file_from_data (a, ".commitmeta",
                               repo,
                               g_variant_get_data (commit_metadata),
                               g_variant_get_size (commit_metadata),
                               &opts, cancellable, error))
        return FALSE;
    }

  if (archive_write_close (a) != ARCHIVE_OK)
    return propagate_libarchive_error (error, a);

  return TRUE;
#endif
}

gboolean
xdg_app_builtin_build_bundle (int argc, char **argv, GCancellable *cancellable, GError **error)
{
  g_autoptr(GOptionContext) context = NULL;
  g_autoptr(GFile) file = NULL;
  g_autoptr(GFile) repofile = NULL;
  g_autoptr(OstreeRepo) repo = NULL;
  const char *location;
  const char *filename;
  const char *name;
  const char *branch;
  g_autofree char *full_branch = NULL;

  context = g_option_context_new ("LOCATION FILENAME NAME [BRANCH] - Create a single file bundle from a local repository");

  if (!xdg_app_option_context_parse (context, options, &argc, &argv, XDG_APP_BUILTIN_FLAG_NO_DIR, NULL, cancellable, error))
    return FALSE;

  if (argc < 4)
    return usage_error (context, "LOCATION, FILENAME and NAME must be specified", error);

  location = argv[1];
  filename = argv[2];
  name = argv[3];

  if (argc >= 5)
    branch = argv[4];
  else
    branch = "master";

  repofile = g_file_new_for_commandline_arg (location);
  repo = ostree_repo_new (repofile);

  if (!g_file_query_exists (repofile, cancellable))
    return xdg_app_fail (error, "'%s' is not a valid repository", location);

  file = g_file_new_for_commandline_arg (filename);

  if (!xdg_app_is_valid_name (name))
    return xdg_app_fail (error, "'%s' is not a valid name", name);

  if (!xdg_app_is_valid_branch (branch))
    return xdg_app_fail (error, "'%s' is not a valid branch name", branch);

  if (opt_runtime)
    full_branch = xdg_app_build_runtime_ref (name, branch, opt_arch);
  else
    full_branch = xdg_app_build_app_ref (name, branch, opt_arch);

  if (!ostree_repo_open (repo, cancellable, error))
    return FALSE;

  if (opt_oci)
    {
      if (!build_oci (repo, file, name, full_branch, cancellable, error))
        return FALSE;
    }
  else
    {
      if (!build_bundle (repo, file, name, full_branch, cancellable, error))
        return FALSE;
    }

  return TRUE;
}
