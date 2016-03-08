#include "config.h"

#define FUSE_USE_VERSION 26

#include <glib-unix.h>

#include <fuse_lowlevel.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <assert.h>
#include <glib/gprintf.h>
#include <gio/gio.h>
#include <pthread.h>

#include "xdg-app-portal-error.h"
#include "xdp-fuse.h"
#include "xdp-util.h"
#include "xdg-app-utils.h"

#define NON_DOC_DIR_PERMS 0500
#define DOC_DIR_PERMS 0700

/* The (fake) directories don't really change */
#define DIRS_ATTR_CACHE_TIME 60.0

/* We pretend that the file is hardlinked. This causes most apps to do
   a truncating overwrite, which suits us better, as we do the atomic
   rename ourselves anyway. This way we don't weirdly change the inode
   after the rename. */
#define DOC_FILE_NLINK 2

typedef enum {
  XDP_INODE_ROOT,
  XDP_INODE_BY_APP,
  XDP_INODE_APP_DIR, /* app id */
  XDP_INODE_DOC_DIR, /* doc id */
  XDP_INODE_DOC_FILE, /* doc id (NULL if tmp), name (== basename) */
} XdpInodeType;

typedef struct _XdpInode XdpInode;

struct _XdpInode {
  fuse_ino_t ino;
  XdpInodeType type;
  char *filename;
  XdpInode *parent;
  GList *children; /* lazily filled, protected by inodes lock */

  guint ref_count;
};

#define ROOT_INODE  0
#define BY_APP_INODE  1
#define BY_APP_NAME "by-app"

static GHashTable *app_name_to_inode_nr;
static GHashTable *doc_id_to_inode_nr;

static GHashTable *inodes; /* The in memory XdpInode:s */
static XdpInode *root_inode;
static XdpInode *by_app_inode;
static fuse_ino_t next_inode_nr = 2;

G_LOCK_DEFINE(inodes);

static GThread *fuse_thread = NULL;
static struct fuse_session *session = NULL;
static struct fuse_chan *main_ch = NULL;
static char *mount_path = NULL;
static pthread_t fuse_pthread = 0;

#ifdef TODO
static int
steal_fd (int *fdp)
{
  int fd = *fdp;
  *fdp = -1;
  return fd;
}

static int
get_user_perms (const struct stat *stbuf)
{
  /* Strip out exec and setuid bits */
  return stbuf->st_mode & 0666;
}

static double
get_attr_cache_time (int st_mode)
{
  if (S_ISDIR (st_mode))
    return DIRS_ATTR_CACHE_TIME;
  return 0.0;
}

static double
get_entry_cache_time (fuse_ino_t inode)
{
  /* We have to disable entry caches because otherwise we have a race
     on rename. The kernel set the target inode as NOEXIST after a
     rename, which breaks in the tmp over real case due to us reusing
     the old non-temp inode. */
  return 0.0;
}
#endif

/* Call with inodes lock held */
static fuse_ino_t
allocate_inode_unlocked (void)
{
  return next_inode_nr++;
}

static fuse_ino_t
allocate_inode_nr (void)
{
  AUTOLOCK(inodes);
  return allocate_inode_unlocked ();
}

static void xdp_inode_unref (XdpInode *inode);

static void
xdp_inode_destroy (XdpInode *inode)
{
  xdp_inode_unref (inode->parent);
  g_free (inode->filename);
  g_free (inode);
}

static XdpInode *
xdp_inode_ref (XdpInode *inode)
{
  if (inode)
    g_atomic_int_inc (&inode->ref_count);
  return inode;
}

static void
xdp_inode_unref (XdpInode *inode)
{
  gint old_ref;

  if (inode == NULL)
    return;

  /* here we want to atomically do: if (ref_count>1) { ref_count--; return; } */
 retry_atomic_decrement1:
  old_ref = g_atomic_int_get (&inode->ref_count);
  if (old_ref > 1)
    {
      if (!g_atomic_int_compare_and_exchange ((int *)&inode->ref_count, old_ref, old_ref - 1))
        goto retry_atomic_decrement1;
    }
  else
    {
      /* Protect against revival from xdp_inode_lookup() */
      G_LOCK(inodes);
      if (!g_atomic_int_compare_and_exchange ((int *)&inode->ref_count, old_ref, old_ref - 1))
        {
          G_UNLOCK(inodes);
          goto retry_atomic_decrement1;
        }

      g_hash_table_remove (inodes, (gpointer)inode->ino);
      if (inode->parent)
        inode->parent->children = g_list_remove (inode->parent->children, inode);

      G_UNLOCK(inodes);

      xdp_inode_destroy (inode);
    }
}

static XdpInode *
xdp_inode_new (fuse_ino_t ino,
               XdpInodeType type,
               XdpInode *parent,
               const char *filename)
{
  XdpInode *inode;

  inode = g_new0 (XdpInode, 1);
  inode->ino = ino;
  inode->type = type;
  inode->parent = xdp_inode_ref (parent);
  inode->filename = g_strdup (filename);
  inode->ref_count = 1;

  AUTOLOCK(inodes);
  if (parent)
    parent->children = g_list_prepend (parent->children, inode);
  g_hash_table_insert (inodes, (gpointer)ino, inode);
  return inode;
}

static XdpInode *
xdp_inode_lookup_unlocked (fuse_ino_t inode_nr)
{
  XdpInode *inode;

  inode = g_hash_table_lookup (inodes, (gpointer)inode_nr);
  if (inode != NULL)
    return xdp_inode_ref (inode);
  return NULL;
}

static XdpInode *
xdp_inode_lookup (fuse_ino_t inode_nr)
{
  AUTOLOCK(inodes);
  return xdp_inode_lookup_unlocked (inode_nr);
}

static fuse_ino_t
get_app_inode_nr_unlocked (const char *app_id)
{
  gpointer res;
  fuse_ino_t allocated;

  res = g_hash_table_lookup (app_name_to_inode_nr, app_id);
  if (res != NULL)
    return (fuse_ino_t)(gsize)res;

  allocated = allocate_inode_unlocked ();
  g_hash_table_insert (app_name_to_inode_nr, g_strdup (app_id), (gpointer)allocated);
  return allocated;
}

static XdpInode *
xdp_inode_get_app_dir (const char *app_id)
{
  fuse_ino_t ino;
  XdpInode *inode;

  AUTOLOCK(inodes);
  ino = get_app_inode_nr_unlocked (app_id);

  inode = xdp_inode_lookup_unlocked (ino);
  if (inode)
    return xdp_inode_ref (inode);

  return xdp_inode_new (ino, XDP_INODE_APP_DIR, by_app_inode, app_id);
}

static fuse_ino_t
get_doc_inode_nr_unlocked (const char *doc_id)
{
  gpointer res;
  fuse_ino_t allocated;

  res = g_hash_table_lookup (doc_id_to_inode_nr, doc_id);
  if (res != NULL)
    return (fuse_ino_t)(gsize)res;

  allocated = allocate_inode_unlocked ();
  g_hash_table_insert (doc_id_to_inode_nr, g_strdup (doc_id), (gpointer)allocated);
  return allocated;
}

static XdpInode *
xdp_inode_get_doc_dir (const char *doc_id)
{
  fuse_ino_t ino;
  XdpInode *inode;

  AUTOLOCK(inodes);
  ino = get_doc_inode_nr_unlocked (doc_id);

  inode = xdp_inode_lookup_unlocked (ino);
  if (inode)
    return xdp_inode_ref (inode);

  return xdp_inode_new (ino, XDP_INODE_DOC_DIR, root_inode, doc_id);
}

static void
xdp_fuse_lookup (fuse_req_t req,
                 fuse_ino_t parent,
                 const char *name)
{
#ifdef TODO
  struct fuse_entry_param e = {0};
  int res;

  g_debug ("xdp_fuse_lookup %lx/%s -> ", parent, name);

  memset (&e, 0, sizeof(e));

  res = xdp_lookup (parent, name, &e.ino, &e.attr, NULL, NULL);

  if (res == 0)
    {
      g_debug ("xdp_fuse_lookup <- inode %lx", (long)e.ino);
      e.attr_timeout = get_attr_cache_time (e.attr.st_mode);
      e.entry_timeout = get_entry_cache_time (e.ino);
      fuse_reply_entry (req, &e);
    }
  else
    {
      g_debug ("xdp_fuse_lookup <- error %s", strerror (res));
      fuse_reply_err (req, res);
    }
#endif
}

void
xdp_fuse_forget (fuse_req_t req, fuse_ino_t ino, unsigned long nlookup)
{
  fuse_reply_none (req);
}


static struct fuse_lowlevel_ops xdp_fuse_oper = {
  .lookup       = xdp_fuse_lookup,
  .forget       = xdp_fuse_forget,
  /*
  .getattr      = xdp_fuse_getattr,
  .opendir      = xdp_fuse_opendir,
  .readdir      = xdp_fuse_readdir,
  .releasedir   = xdp_fuse_releasedir,
  .fsyncdir     = xdp_fuse_fsyncdir,
  .open         = xdp_fuse_open,
  .create       = xdp_fuse_create,
  .read         = xdp_fuse_read,
  .write        = xdp_fuse_write,
  .write_buf    = xdp_fuse_write_buf,
  .release      = xdp_fuse_release,
  .rename       = xdp_fuse_rename,
  .setattr      = xdp_fuse_setattr,
  .fsync        = xdp_fuse_fsync,
  .unlink       = xdp_fuse_unlink,
  */
};

/* Called when a apps permissions to see a document is changed */
void
xdp_fuse_invalidate_doc_app (const char  *doc_id_s,
                             const char  *app_id_s,
                             XdgAppDbEntry *entry)
{
#ifdef TODO
  guint32 app_id = get_app_id_from_name (app_id_s);
  guint32 doc_id = xdp_id_from_name (doc_id_s);
  g_autofree char *basename = xdp_entry_dup_basename (entry);

  g_debug ("invalidate %s/%s\n", doc_id_s, app_id_s);

  /* This can happen if fuse is not initialized yet for the very
     first dbus message that activated the service */
  if (main_ch == NULL)
    return;

  fuse_lowlevel_notify_inval_inode (main_ch, make_app_doc_file_inode (app_id, doc_id), 0, 0);
  fuse_lowlevel_notify_inval_entry (main_ch, make_app_doc_dir_inode (app_id, doc_id),
                                    basename, strlen (basename));
  fuse_lowlevel_notify_inval_inode (main_ch, make_app_doc_dir_inode (app_id, doc_id), 0, 0);
  fuse_lowlevel_notify_inval_entry (main_ch, make_inode (APP_DIR_INO_CLASS, app_id),
                                    doc_id_s, strlen (doc_id_s));
#endif
}

/* Called when a document id is created/removed */
void
xdp_fuse_invalidate_doc (const char  *doc_id_s,
                         XdgAppDbEntry *entry)
{
#ifdef TODO
  guint32 doc_id = xdp_id_from_name (doc_id_s);
  g_autofree char *basename = xdp_entry_dup_basename (entry);

  g_debug ("invalidate %s\n", doc_id_s);

  /* This can happen if fuse is not initialized yet for the very
     first dbus message that activated the service */
  if (main_ch == NULL)
    return;

  fuse_lowlevel_notify_inval_inode (main_ch, make_app_doc_file_inode (0, doc_id), 0, 0);
  fuse_lowlevel_notify_inval_entry (main_ch, make_app_doc_dir_inode (0, doc_id),
                                    basename, strlen (basename));
  fuse_lowlevel_notify_inval_inode (main_ch, make_app_doc_dir_inode (0, doc_id), 0, 0);
  fuse_lowlevel_notify_inval_entry (main_ch, FUSE_ROOT_ID, doc_id_s, strlen (doc_id_s));
#endif
}

guint32
xdp_fuse_lookup_id_for_inode (ino_t inode)
{
#ifdef TODO
  XdpInodeClass class = get_class (inode);
  guint64 class_ino = get_class_ino (inode);

  if (class != APP_DOC_FILE_INO_CLASS)
    return 0;

  return get_doc_id_from_app_doc_ino (class_ino);
#else
  return 0;
#endif
}


const char *
xdp_fuse_get_mountpoint (void)
{
  if (mount_path == NULL)
    mount_path = g_build_filename (g_get_user_runtime_dir(), "doc", NULL);
  return mount_path;
}

void
xdp_fuse_exit (void)
{
  if (session)
    fuse_session_exit (session);

  if (fuse_pthread)
    pthread_kill (fuse_pthread, SIGHUP);

  if (fuse_thread)
    g_thread_join (fuse_thread);
}

static gpointer
xdp_fuse_mainloop (gpointer data)
{
  fuse_pthread = pthread_self ();

  fuse_session_loop_mt (session);

  fuse_session_remove_chan(main_ch);
  fuse_session_destroy (session);
  fuse_unmount (mount_path, main_ch);
  return NULL;
}

gboolean
xdp_fuse_init (GError **error)
{
  char *argv[] = { "xdp-fuse", "-osplice_write,splice_move,splice_read" };
  struct fuse_args args = FUSE_ARGS_INIT(G_N_ELEMENTS(argv), argv);
  struct stat st;
  const char *mount_path;

  inodes =
    g_hash_table_new_full (g_direct_hash, g_direct_equal, NULL, NULL);
  root_inode = xdp_inode_new (ROOT_INODE, XDP_INODE_ROOT, NULL, "/");
  by_app_inode = xdp_inode_new (BY_APP_INODE, XDP_INODE_BY_APP, root_inode, BY_APP_NAME);
  app_name_to_inode_nr =
    g_hash_table_new_full (g_str_hash, g_str_equal, g_free, NULL);
  doc_id_to_inode_nr =
    g_hash_table_new_full (g_str_hash, g_str_equal, g_free, NULL);


  mount_path = xdp_fuse_get_mountpoint ();

  if (stat (mount_path, &st) == -1 && errno == ENOTCONN)
    {
      char *argv[] = { "fusermount", "-u", (char *)mount_path, NULL };

      g_spawn_sync (NULL, argv, NULL, G_SPAWN_SEARCH_PATH,
                    NULL, NULL, NULL, NULL, NULL, NULL);
    }

  if (g_mkdir_with_parents  (mount_path, 0700))
    {
      g_set_error (error, XDG_APP_PORTAL_ERROR, XDG_APP_PORTAL_ERROR_FAILED,
                   "Unable to create dir %s\n", mount_path);
      return FALSE;
    }

  main_ch = fuse_mount (mount_path, &args);
  if (main_ch == NULL)
    {
      g_set_error (error, XDG_APP_PORTAL_ERROR, XDG_APP_PORTAL_ERROR_FAILED, "Can't mount fuse fs");
      return FALSE;
    }

  session = fuse_lowlevel_new (&args, &xdp_fuse_oper,
                               sizeof (xdp_fuse_oper), NULL);
  if (session == NULL)
    {
      g_set_error (error, XDG_APP_PORTAL_ERROR, XDG_APP_PORTAL_ERROR_FAILED,
                   "Can't create fuse session");
      return FALSE;
    }
  fuse_session_add_chan (session, main_ch);

  fuse_thread = g_thread_new ("fuse mainloop", xdp_fuse_mainloop, session);

  return TRUE;
}
