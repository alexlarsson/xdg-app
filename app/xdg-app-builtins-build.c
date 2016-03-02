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
#include <string.h>
#include <unistd.h>
#include <errno.h>

#include "libgsystem.h"
#include "libglnx/libglnx.h"

#include "xdg-app-builtins.h"
#include "xdg-app-utils.h"
#include "xdg-app-run.h"

static gboolean opt_runtime;
static char *opt_build_dir;
static char **opt_bind_mounts;

static GOptionEntry options[] = {
  { "runtime", 'r', 0, G_OPTION_ARG_NONE, &opt_runtime, "Use non-devel runtime", NULL },
  { "bind-mount", 0, 0, G_OPTION_ARG_STRING_ARRAY, &opt_bind_mounts, "Add bind mount", "DEST=SRC" },
  { "build-dir", 0, 0, G_OPTION_ARG_STRING, &opt_build_dir, "Start build in this directory", "DIR" },
  { NULL }
};

gboolean
xdg_app_builtin_build (int argc, char **argv, GCancellable *cancellable, GError **error)
{
  g_autoptr(GOptionContext) context = NULL;
  g_autoptr(XdgAppDeploy) runtime_deploy = NULL;
  g_autoptr(GFile) var = NULL;
  g_autoptr(GFile) usr = NULL;
  g_autoptr(GFile) app_deploy = NULL;
  g_autoptr(GFile) app_files = NULL;
  g_autoptr(GFile) runtime_files = NULL;
  g_autoptr(GFile) metadata = NULL;
  g_autofree char *metadata_contents = NULL;
  g_autofree char *runtime = NULL;
  g_autofree char *runtime_ref = NULL;
  g_autoptr(GKeyFile) metakey = NULL;
  g_autoptr(GKeyFile) runtime_metakey = NULL;
  g_autoptr(GPtrArray) argv_array = NULL;
  g_auto(GStrv) envp = NULL;
  gsize metadata_size;
  const char *directory = NULL;
  const char *command = "/bin/sh";
  g_autofree char *app_id = NULL;
  int i;
  int rest_argv_start, rest_argc;
  g_autoptr(XdgAppContext) arg_context = NULL;
  g_autoptr(XdgAppContext) app_context = NULL;
  gboolean custom_usr;

  context = g_option_context_new ("DIRECTORY [COMMAND [args...]] - Build in directory");

  rest_argc = 0;
  for (i = 1; i < argc; i++)
    {
      /* The non-option is the directory, take it out of the arguments */
      if (argv[i][0] != '-')
        {
          rest_argv_start = i;
          rest_argc = argc - i;
          argc = i;
          break;
        }
    }

  arg_context = xdg_app_context_new ();
  g_option_context_add_group (context, xdg_app_context_get_options (arg_context));

  if (!xdg_app_option_context_parse (context, options, &argc, &argv, XDG_APP_BUILTIN_FLAG_NO_DIR, NULL, cancellable, error))
    return FALSE;

  if (rest_argc == 0)
    return usage_error (context, "DIRECTORY must be specified", error);

  directory = argv[rest_argv_start];
  if (rest_argc >= 2)
    command = argv[rest_argv_start+1];

  app_deploy = g_file_new_for_commandline_arg (directory);

  metadata = g_file_get_child (app_deploy, "metadata");
  if (!g_file_load_contents (metadata, cancellable, &metadata_contents, &metadata_size, NULL, error))
    return FALSE;

  metakey = g_key_file_new ();
  if (!g_key_file_load_from_data (metakey, metadata_contents, metadata_size, 0, error))
    return FALSE;

  app_id = g_key_file_get_string (metakey, "Application", "name", error);
  if (app_id == NULL)
    return FALSE;

  runtime = g_key_file_get_string (metakey, "Application", opt_runtime ? "runtime" : "sdk", error);
  if (runtime == NULL)
    return FALSE;

  runtime_ref = g_build_filename ("runtime", runtime, NULL);

  runtime_deploy = xdg_app_find_deploy_for_ref (runtime_ref, cancellable, error);
  if (runtime_deploy == NULL)
    return FALSE;

  runtime_metakey = xdg_app_deploy_get_metadata (runtime_deploy);

  var = g_file_get_child (app_deploy, "var");
  if (!gs_file_ensure_directory (var, TRUE, cancellable, error))
    return FALSE;

  app_files = g_file_get_child (app_deploy, "files");

  argv_array = g_ptr_array_new_with_free_func (g_free);
  g_ptr_array_add (argv_array, g_strdup (HELPER));

  custom_usr = FALSE;
  usr = g_file_get_child (app_deploy, "usr");
  if (g_file_query_exists (usr, cancellable))
    {
      custom_usr = TRUE;
      runtime_files = g_object_ref (usr);
      g_ptr_array_add (argv_array, g_strdup ("-W"));
    }
  else
    runtime_files = xdg_app_deploy_get_files (runtime_deploy);

  g_ptr_array_add (argv_array, g_strdup ("-wrc"));

  app_context = xdg_app_context_new ();
  if (!xdg_app_context_load_metadata (app_context, runtime_metakey, error))
    return FALSE;
  if (!xdg_app_context_load_metadata (app_context, metakey, error))
    return FALSE;
  xdg_app_context_allow_host_fs (app_context);
  xdg_app_context_merge (app_context, arg_context);

  envp = xdg_app_run_get_minimal_env (TRUE);
  envp = xdg_app_run_apply_env_vars (envp, app_context);
  xdg_app_run_add_environment_args (argv_array, &envp, NULL, NULL, app_id,
                                    app_context, NULL);

  if (!custom_usr &&
      !xdg_app_run_add_extension_args (argv_array, runtime_metakey, runtime_ref, cancellable, error))
    return FALSE;

  for (i = 0; opt_bind_mounts != NULL && opt_bind_mounts[i] != NULL; i++)
    {
      if (strchr (opt_bind_mounts[i], '=') == NULL)
        {
          g_set_error (error, G_IO_ERROR, G_IO_ERROR_INVALID_ARGUMENT, "Missing '=' in bind mount option '%s'", opt_bind_mounts[i]);
          return FALSE;
        }

      g_ptr_array_add (argv_array, g_strdup ("-B"));
      g_ptr_array_add (argv_array, g_strdup (opt_bind_mounts[i]));
    }

  if (opt_build_dir != NULL)
    {
      g_ptr_array_add (argv_array, g_strdup ("-P"));
      g_ptr_array_add (argv_array, g_strdup (opt_build_dir));
    }

  g_ptr_array_add (argv_array, g_strdup ("-a"));
  g_ptr_array_add (argv_array, g_file_get_path (app_files));
  g_ptr_array_add (argv_array, g_strdup ("-v"));
  g_ptr_array_add (argv_array, g_file_get_path (var));
  g_ptr_array_add (argv_array, g_file_get_path (runtime_files));

  g_ptr_array_add (argv_array, g_strdup (command));
  for (i = 2; i < rest_argc; i++)
    g_ptr_array_add (argv_array, g_strdup (argv[rest_argv_start + i]));

  g_ptr_array_add (argv_array, NULL);

  if (!execve (HELPER, (char **)argv_array->pdata, envp))
    {
      g_set_error (error, G_IO_ERROR, g_io_error_from_errno (errno), "Unable to start app");
      return FALSE;
    }

  /* Not actually reached... */
  return TRUE;
}
