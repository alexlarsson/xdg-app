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

/* TODO: What do we put here */
#define ATTR_CACHE_TIME 1.0
#define ENTRY_CACHE_TIME 1.0

/* We pretend that the file is hardlinked. This causes most apps to do
   a truncating overwrite, which suits us better, as we do the atomic
   rename ourselves anyway. This way we don't weirdly change the inode
   after the rename. */
#define DOC_FILE_NLINK 2

typedef enum {
  XDP_INODE_ROOT,
  XDP_INODE_BY_APP,
  XDP_INODE_APP_DIR, /* app id */
  XDP_INODE_APP_DOC_DIR, /* app_id + doc id */
  XDP_INODE_DOC_DIR, /* doc id */
  XDP_INODE_DOC_FILE, /* doc id (NULL if tmp), name (== basename) */
} XdpInodeType;

typedef struct _XdpInode XdpInode;

struct _XdpInode {
  /* These are all constant */
  fuse_ino_t ino;
  XdpInodeType type;
  XdpInode *parent;
  char *app_id;
  char *doc_id;

  GList *children; /* lazily filled, protected by inodes lock */
  char *filename; /* variable (for non-dirs), protected by inodes lock */

  gint ref_count; /* atomic */
};

#define ROOT_INODE  1
#define BY_APP_INODE  2
#define BY_APP_NAME "by-app"

static GHashTable *dir_to_inode_nr;

static GHashTable *inodes; /* The in memory XdpInode:s, protected by inodes lock */
static XdpInode *root_inode;
static XdpInode *by_app_inode;
static fuse_ino_t next_inode_nr = 3;

G_LOCK_DEFINE(inodes);

static GThread *fuse_thread = NULL;
static struct fuse_session *session = NULL;
static struct fuse_chan *main_ch = NULL;
static char *mount_path = NULL;
static pthread_t fuse_pthread = 0;

/* Call with inodes lock held */
static fuse_ino_t
allocate_inode_unlocked (void)
{
  fuse_ino_t next = next_inode_nr++;

  /* Bail out on overflow, to avoid reuse */
  if (next <= 0)
    g_assert_not_reached ();

  return next;
}

static fuse_ino_t
allocate_inode_nr (void)
{
  AUTOLOCK(inodes);
  return allocate_inode_unlocked ();
}

static fuse_ino_t
get_dir_inode_nr_unlocked (const char *app_id, const char *doc_id)
{
  gpointer res;
  fuse_ino_t allocated;
  g_autofree char *dir = NULL;

  if (app_id == NULL)
    dir = g_strdup (doc_id);
  else
    {
      if (doc_id == NULL)
        dir = g_strconcat (app_id, "/", NULL);
      else
        dir = g_build_filename (app_id, doc_id, NULL);
    }

  res = g_hash_table_lookup (dir_to_inode_nr, dir);
  if (res != NULL)
    return (fuse_ino_t)(gsize)res;

  allocated = allocate_inode_unlocked ();
  g_hash_table_insert (dir_to_inode_nr, g_strdup (dir), (gpointer)allocated);
  return allocated;
}

static fuse_ino_t
get_dir_inode_nr (const char *app_id, const char *doc_id)
{
  AUTOLOCK(inodes);
  return get_dir_inode_nr_unlocked (app_id, doc_id);
}

static void
allocate_app_dir_inode_nr (char **app_ids)
{
  int i;
  AUTOLOCK(inodes);
  for (i = 0; app_ids[i] != NULL; i++)
    get_dir_inode_nr_unlocked (app_ids[i], NULL);
}

static char **
get_allocated_app_dirs (void)
{
  GHashTableIter iter;
  gpointer key, value;
  GPtrArray *array = g_ptr_array_new ();

  AUTOLOCK(inodes);
  g_hash_table_iter_init (&iter, dir_to_inode_nr);
  while (g_hash_table_iter_next (&iter, &key, &value))
    {
      const char *name = key;

      if (g_str_has_suffix (name, "/"))
        {
          char *app = strndup (name, strlen (name) - 1);
          g_ptr_array_add (array, app);
        }
    }
  g_ptr_array_add (array, NULL);
  return (char **)g_ptr_array_free (array, FALSE);
}

static void xdp_inode_unref_internal (XdpInode *inode, gboolean locked);
static void xdp_inode_unref (XdpInode *inode);

G_DEFINE_AUTOPTR_CLEANUP_FUNC(XdpInode, xdp_inode_unref)

static void
xdp_inode_destroy (XdpInode *inode, gboolean locked)
{
  g_assert (inode->children == NULL);
  xdp_inode_unref_internal (inode->parent, locked);
  g_free (inode->filename);
  g_free (inode->app_id);
  g_free (inode->doc_id);
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
xdp_inode_unref_internal (XdpInode *inode, gboolean locked)
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
      if (old_ref <= 0)
        {
          g_warning ("Can't unref dead inode");
          return;
        }
      /* Protect against revival from xdp_inode_lookup() */
      if (!locked)
        G_LOCK(inodes);
      if (!g_atomic_int_compare_and_exchange ((int *)&inode->ref_count, old_ref, old_ref - 1))
        {
          if (!locked)
            G_UNLOCK(inodes);
          goto retry_atomic_decrement1;
        }

      g_hash_table_remove (inodes, (gpointer)inode->ino);
      if (inode->parent)
        inode->parent->children = g_list_remove (inode->parent->children, inode);

      if (!locked)
        G_UNLOCK(inodes);

      xdp_inode_destroy (inode, locked);
    }
}

static void
xdp_inode_unref (XdpInode *inode)
{
  return xdp_inode_unref_internal (inode, FALSE);
}

static XdpInode *
xdp_inode_new_unlocked (fuse_ino_t ino,
                        XdpInodeType type,
                        XdpInode *parent,
                        const char *filename,
                        const char *app_id,
                        const char *doc_id)
{
  XdpInode *inode;

  inode = g_new0 (XdpInode, 1);
  inode->ino = ino;
  inode->type = type;
  inode->parent = xdp_inode_ref (parent);
  inode->filename = g_strdup (filename);
  inode->app_id = g_strdup (app_id);
  inode->doc_id = g_strdup (doc_id);
  inode->ref_count = 1;

  if (parent)
    parent->children = g_list_prepend (parent->children, inode);
  g_hash_table_insert (inodes, (gpointer)ino, inode);

  return inode;
}

static XdpInode *
xdp_inode_new (fuse_ino_t ino,
               XdpInodeType type,
               XdpInode *parent,
               const char *filename,
               const char *app_id,
               const char *doc_id)
{
  AUTOLOCK(inodes);
  return xdp_inode_new_unlocked (ino, type, parent, filename, app_id, doc_id);
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

static GList *
xdp_inode_list_children (XdpInode *inode)
{
  GList *list = NULL, *l;

  AUTOLOCK(inodes);
  for (l = inode->children; l != NULL; l = l->next)
    {
      XdpInode *child = l->data;

      list = g_list_prepend (list, child);
    }

  return g_list_reverse (list);
}

static XdpInode *
xdp_inode_lookup_child_unlocked (XdpInode *inode, const char *filename)
{
  GList *l;

  for (l = inode->children; l != NULL; l = l->next)
    {
      XdpInode *child = l->data;
      if (strcmp (child->filename, filename) == 0)
        return xdp_inode_ref (child);
    }

  return NULL;
}

static XdpInode *
xdp_inode_lookup_child (XdpInode *inode, const char *filename)
{
  AUTOLOCK(inodes);
  return xdp_inode_lookup_child_unlocked (inode, filename);
}

static gboolean
xdp_inode_has_filename (XdpInode *inode, const char *filename)
{
  AUTOLOCK(inodes);
  return strcmp (inode->filename, filename) == 0;
}

char *
xdp_inode_get_filename (XdpInode *inode)
{
  AUTOLOCK(inodes);
  return g_strdup (inode->filename);
}

static XdpInode *
xdp_inode_ensure_document_file (XdpInode *dir,
                                XdgAppDbEntry *entry)
{
  g_autofree char *basename = xdp_entry_dup_basename (entry);
  XdpInode *inode;

  g_assert (dir->type == XDP_INODE_APP_DOC_DIR || dir->type == XDP_INODE_DOC_DIR);

  AUTOLOCK(inodes);

  inode = xdp_inode_lookup_child_unlocked (dir, basename);
  if (inode)
    return inode;

  return xdp_inode_new_unlocked (allocate_inode_unlocked (),
                                 XDP_INODE_DOC_FILE,
                                 dir,
                                 basename,
                                 dir->app_id,
                                 dir->doc_id);
}

static XdpInode *
xdp_inode_lookup (fuse_ino_t inode_nr)
{
  AUTOLOCK(inodes);
  return xdp_inode_lookup_unlocked (inode_nr);
}

static XdpInode *
xdp_inode_get_dir_unlocked (const char *app_id, const char *doc_id)
{
  fuse_ino_t ino;
  XdpInode *inode;
  XdpInode *parent = NULL;
  XdpInodeType type;
  const char *filename;

  ino = get_dir_inode_nr_unlocked (app_id, doc_id);

  inode = xdp_inode_lookup_unlocked (ino);
  if (inode)
    return inode;

  if (app_id == NULL)
    {
      g_assert (doc_id != NULL);
      parent = xdp_inode_ref (root_inode);
      type = XDP_INODE_DOC_DIR;
      filename = doc_id;
    }
  else
    {
      if  (doc_id == NULL)
        {
          parent = xdp_inode_ref (by_app_inode);
          filename = app_id;
          type = XDP_INODE_APP_DIR;
        }
      else
        {
          parent = xdp_inode_get_dir_unlocked (app_id, NULL);
          filename = doc_id;
          type = XDP_INODE_APP_DOC_DIR;
        }
    }

  inode = xdp_inode_new_unlocked (ino, type, parent, filename, app_id, doc_id);
  xdp_inode_unref_internal (parent, TRUE);
  return inode;
}

static XdpInode *
xdp_inode_get_dir (const char *app_id, const char *doc_id)
{
  AUTOLOCK(inodes);
  return xdp_inode_get_dir_unlocked (app_id, doc_id);
}

/********************************************************************** \
 * FUSE Implementation
\***********************************************************************/

static int
get_user_perms (const struct stat *stbuf)
{
  /* Strip out exec and setuid bits */
  return stbuf->st_mode & 0666;
}

static gboolean
app_can_write_doc (XdgAppDbEntry *entry, const char *app_id)
{
  if (app_id == NULL)
    return TRUE;

  if (xdp_entry_has_permissions (entry, app_id, XDP_PERMISSION_FLAGS_WRITE))
    return TRUE;

  return FALSE;
}

static gboolean
app_can_see_doc (XdgAppDbEntry *entry, const char *app_id)
{
  if (app_id == NULL)
    return TRUE;

  if (xdp_entry_has_permissions (entry, app_id, XDP_PERMISSION_FLAGS_READ))
    return TRUE;

  return FALSE;
}

static int
xdp_inode_stat (XdpInode *inode,
                struct stat *stbuf)
{
  stbuf->st_ino = inode->ino;

  switch (inode->type)
    {
    case XDP_INODE_ROOT:
    case XDP_INODE_BY_APP:
    case XDP_INODE_APP_DIR:
      stbuf->st_mode = S_IFDIR | NON_DOC_DIR_PERMS;
      stbuf->st_nlink = 2;
      break;

    case XDP_INODE_DOC_DIR:
    case XDP_INODE_APP_DOC_DIR:
      stbuf->st_mode = S_IFDIR | DOC_DIR_PERMS;
      stbuf->st_nlink = 2;
      break;

    case XDP_INODE_DOC_FILE:
      {
        g_autoptr (XdgAppDbEntry) entry = NULL;
        g_autofree char *basename = NULL;
        struct stat tmp_stbuf;
        gboolean can_write = FALSE;

        entry = xdp_lookup_doc (inode->doc_id);
        if (entry == NULL)
          {
            errno = ENOENT;
            return -1;
          }

        basename = xdp_entry_dup_basename (entry);
        if (xdp_inode_has_filename (inode, basename))
          {
            if (xdp_entry_stat (entry, &tmp_stbuf, AT_SYMLINK_NOFOLLOW) != 0)
              return -1;

            can_write = app_can_write_doc (entry, inode->app_id);
          }
        else
          {
            /* TODO: Handle tmp files */
            errno = ENOENT;
            return -1;
          }

        stbuf->st_mode = S_IFREG | get_user_perms (&tmp_stbuf);
        if (!can_write)
          stbuf->st_mode &= ~(0222);
        stbuf->st_size = tmp_stbuf.st_size;
        stbuf->st_uid = tmp_stbuf.st_uid;
        stbuf->st_gid = tmp_stbuf.st_gid;
        stbuf->st_blksize = tmp_stbuf.st_blksize;
        stbuf->st_blocks = tmp_stbuf.st_blocks;
        stbuf->st_atim = tmp_stbuf.st_atim;
        stbuf->st_mtim = tmp_stbuf.st_mtim;
        stbuf->st_ctim = tmp_stbuf.st_ctim;
      }
      break;

    default:
      g_assert_not_reached ();
    }

  return 0;
}

static void
xdp_fuse_lookup (fuse_req_t req,
                 fuse_ino_t parent,
                 const char *name)
{
  g_autoptr(XdpInode) parent_inode = NULL;
  struct fuse_entry_param e = {0};
  g_autoptr(XdpInode) child_inode = NULL;
  g_autoptr (XdgAppDbEntry) entry = NULL;

  g_debug ("xdp_fuse_lookup %lx/%s -> ", parent, name);

  parent_inode = xdp_inode_lookup (parent);
  if (parent_inode == NULL)
    {
      g_debug ("xdp_fuse_lookup <- error parent ENOENT");
      fuse_reply_err (req, ENOENT);
      return;
    }

  /* Default */
  e.attr_timeout = ATTR_CACHE_TIME;
  e.entry_timeout = ENTRY_CACHE_TIME;

  switch (parent_inode->type)
    {
    case XDP_INODE_ROOT:
      if (strcmp (name, BY_APP_NAME) == 0)
        child_inode = xdp_inode_ref (by_app_inode);
      else
        {
          entry = xdp_lookup_doc (name);
          if (entry != NULL)
            child_inode = xdp_inode_get_dir (NULL, name);
        }
      break;

    case XDP_INODE_BY_APP:
      /* This lazily creates the app dir */
      if (xdg_app_is_valid_name (name))
        child_inode = xdp_inode_get_dir (name, NULL);
      break;

    case XDP_INODE_APP_DIR:
      entry = xdp_lookup_doc (name);
      if (entry != NULL &&
          app_can_see_doc (entry, parent_inode->app_id))
        child_inode = xdp_inode_get_dir (parent_inode->app_id, name);
      break;

    case XDP_INODE_APP_DOC_DIR:
    case XDP_INODE_DOC_DIR:
      {
        g_autoptr(XdpInode) doc_inode = NULL;
        entry = xdp_lookup_doc (parent_inode->doc_id);
        if (entry == NULL)
          {
            g_debug ("xdp_fuse_lookup <- error no parent entry ENOENT");
            fuse_reply_err (req, ENOENT);
            return;
          }

        /* Ensure it is alive at least during lookup_child () */
        doc_inode = xdp_inode_ensure_document_file (parent_inode, entry);

        child_inode = xdp_inode_lookup_child (parent_inode, name);

        /* We verify in the stat below if the backing file exists */

        /* Files can be changed from outside the fuse fs, so don't cache any data */
        e.attr_timeout = 0;
        e.entry_timeout = 0;
      }
      break;

    case XDP_INODE_DOC_FILE:
      fuse_reply_err (req, ENOTDIR);
      return;

    default:
      break;
    }

  if (child_inode == NULL)
    {
      g_debug ("xdp_fuse_lookup <- error child ENOENT");
      fuse_reply_err (req, ENOENT);
      return;
    }

  if (xdp_inode_stat (child_inode, &e.attr) != 0)
    {
      fuse_reply_err (req, errno);
      return;
    }

  e.ino = child_inode->ino;

  g_debug ("xdp_fuse_lookup <- inode %lx", (long)e.ino);
  xdp_inode_ref (child_inode); /* Ref given to the kernel, returned in xdp_fuse_forget() */
  fuse_reply_entry (req, &e);
}

void
xdp_fuse_forget (fuse_req_t req, fuse_ino_t ino, unsigned long nlookup)
{
  g_autoptr(XdpInode) inode = NULL;
  g_debug ("xdp_fuse_forget %lx %ld -> ", ino, nlookup);

  inode = xdp_inode_lookup (ino);
  if (inode == NULL)
    g_warning ("xdp_fuse_forget, unknown inode");
  else
    {
      while (nlookup > 0)
        {
          xdp_inode_unref (inode);
          nlookup--;
        }
    }

  fuse_reply_none (req);
}

struct dirbuf {
  char *p;
  size_t size;
};

static void
dirbuf_add (fuse_req_t req,
            struct dirbuf *b,
            const char *name,
            fuse_ino_t ino,
            mode_t mode)
{
  struct stat stbuf;

  size_t oldsize = b->size;
  b->size += fuse_add_direntry (req, NULL, 0, name, NULL, 0);
  b->p = (char *) g_realloc (b->p, b->size);
  memset (&stbuf, 0, sizeof (stbuf));
  stbuf.st_ino = ino;
  stbuf.st_mode = mode;
  fuse_add_direntry (req, b->p + oldsize,
                     b->size - oldsize,
                     name, &stbuf,
                     b->size);
}

static void
dirbuf_add_docs (fuse_req_t req,
                 struct dirbuf *b,
                 const char *app_id)
{
  g_auto(GStrv) docs = NULL;
  fuse_ino_t ino;
  int i;

  docs = xdp_list_docs ();
  for (i = 0; docs[i] != NULL; i++)
    {
      if (app_id)
        {
          g_autoptr(XdgAppDbEntry) entry = xdp_lookup_doc (docs[i]);
          if (entry == NULL ||
              !app_can_see_doc (entry, app_id))
            continue;
        }
      ino = get_dir_inode_nr (app_id, docs[i]);
      dirbuf_add (req, b, docs[i], ino, S_IFDIR);
    }
}

static int
reply_buf_limited (fuse_req_t req,
                   const char *buf,
                   size_t bufsize,
                   off_t off,
                   size_t maxsize)
{
  if (off < bufsize)
    return fuse_reply_buf (req, buf + off,
                           MIN (bufsize - off, maxsize));
  else
    return fuse_reply_buf (req, NULL, 0);
}

static void
xdp_fuse_readdir (fuse_req_t req, fuse_ino_t ino, size_t size,
                  off_t off, struct fuse_file_info *fi)
{
  struct dirbuf *b = (struct dirbuf *)(fi->fh);

  reply_buf_limited (req, b->p, b->size, off, size);
}

static void
xdp_fuse_opendir (fuse_req_t req,
                  fuse_ino_t ino,
                  struct fuse_file_info *fi)
{
  g_autoptr(XdpInode) inode = NULL;
  struct dirbuf b = {0};
  g_autoptr (XdgAppDbEntry) entry = NULL;

  g_debug ("xdp_fuse_opendir %lx", ino);

  inode = xdp_inode_lookup (ino);
  if (inode == NULL)
    {
      g_debug ("xdp_fuse_opendir <- error ENOENT");
      fuse_reply_err (req, ENOENT);
      return;
    }

  switch (inode->type)
    {
    case XDP_INODE_ROOT:
      dirbuf_add (req, &b, ".", ROOT_INODE, S_IFDIR);
      dirbuf_add (req, &b, "..", ROOT_INODE, S_IFDIR);
      dirbuf_add (req, &b, BY_APP_NAME, BY_APP_INODE, S_IFDIR);
      dirbuf_add_docs (req, &b, NULL);
      break;

    case XDP_INODE_BY_APP:
      {
        g_auto(GStrv) db_app_ids = NULL;
        g_auto(GStrv) app_ids = NULL;
        int i;

        dirbuf_add (req, &b, ".", BY_APP_INODE, S_IFDIR);
        dirbuf_add (req, &b, "..", ROOT_INODE, S_IFDIR);

        /* Ensure that all apps from db are allocated */
        db_app_ids = xdp_list_apps ();
        allocate_app_dir_inode_nr (db_app_ids);

        /* But return all allocated dirs. We might have app dirs
           that have no permissions, and are thus not in the db */
        app_ids = get_allocated_app_dirs ();
        for (i = 0; app_ids[i] != NULL; i++)
          dirbuf_add (req, &b, app_ids[i],
                      get_dir_inode_nr (app_ids[i], NULL), S_IFDIR);
      }
      break;

    case XDP_INODE_APP_DIR:
      dirbuf_add (req, &b, ".", inode->ino, S_IFDIR);
      dirbuf_add (req, &b, "..", BY_APP_INODE, S_IFDIR);
      dirbuf_add_docs (req, &b, inode->app_id);
      break;

    case XDP_INODE_DOC_FILE:
      fuse_reply_err (req, ENOTDIR);
      break;

    case XDP_INODE_APP_DOC_DIR:
    case XDP_INODE_DOC_DIR:
      {
        GList *children, *l;
        g_autoptr(XdpInode) doc_inode = NULL;
        g_autoptr (XdgAppDbEntry) entry = NULL;

        entry = xdp_lookup_doc (inode->doc_id);
        if (entry == NULL)
          {
            fuse_reply_err (req, ENOENT);
            break;
          }

        dirbuf_add (req, &b, ".", inode->ino, S_IFDIR);
        dirbuf_add (req, &b, "..", inode->parent->ino, S_IFDIR);

        /* Ensure it is alive at least during list_children () */
        doc_inode = xdp_inode_ensure_document_file (inode, entry);

        children = xdp_inode_list_children (inode);

        for (l = children; l != NULL; l = l->next)
          {
            struct stat stbuf;
            XdpInode *child = l->data;
            if (xdp_inode_stat (child, &stbuf) == 0)
              {
                g_autofree char *filename = xdp_inode_get_filename (child);
                dirbuf_add (req, &b, filename, child->ino, stbuf.st_mode);
              }
            xdp_inode_unref (child);
          }
        g_list_free (children);
      }
      break;

    default:
      g_assert_not_reached ();
    }

  if (b.p == NULL)
    fuse_reply_err (req, ENOTDIR);
  else
    {
      fi->fh = (gsize)g_memdup (&b, sizeof (b));
      if (fuse_reply_open (req, fi) == -ENOENT)
        {
          g_free (b.p);
          g_free ((gpointer)(fi->fh));
        }
    }
}

static void
xdp_fuse_releasedir (fuse_req_t req,
                     fuse_ino_t ino,
                     struct fuse_file_info *fi)
{
  struct dirbuf *b = (struct dirbuf *)(fi->fh);
  g_free (b->p);
  g_free (b);
  fuse_reply_err (req, 0);
}


static void
xdp_fuse_getattr (fuse_req_t req,
                  fuse_ino_t ino,
                  struct fuse_file_info *fi)
{
  g_autoptr(XdpInode) inode = NULL;
  struct stat stbuf = { 0 };

  g_debug ("xdp_fuse_getattr %lx (fi=%p)", ino, fi);

  inode = xdp_inode_lookup (ino);
  if (inode == NULL)
    {
      g_debug ("xdp_fuse_getattr <- error ENOENT");
      fuse_reply_err (req, ENOENT);
      return;
    }

#ifdef TODO
  g_autoptr(XdpFh) fh = NULL;
  int res;


  /* Fuse passes fi in to verify EOF during read/write/seek, but not during fstat */
  if (fi != NULL)
    {
      XdpFh *fh = (gpointer)fi->fh;

      res = xdp_fh_fstat_locked (fh, &stbuf);
      if (res == 0)
        {
          fuse_reply_attr (req, &stbuf, get_attr_cache_time (stbuf.st_mode));
          return;
        }
    }


  fh = find_open_fh (ino);
  if (fh)
    {
      res = xdp_fh_fstat_locked (fh, &stbuf);
      if (res == 0)
        {
          fuse_reply_attr (req, &stbuf, get_attr_cache_time (stbuf.st_mode));
          return;
        }
    }

#endif

  if (xdp_inode_stat (inode,  &stbuf) != 0)
    {
      fuse_reply_err (req, errno);
      return;
    }

  fuse_reply_attr (req, &stbuf, ATTR_CACHE_TIME);
}


static struct fuse_lowlevel_ops xdp_fuse_oper = {
  .lookup       = xdp_fuse_lookup,
  .forget       = xdp_fuse_forget,
  .getattr      = xdp_fuse_getattr,
  .opendir      = xdp_fuse_opendir,
  .readdir      = xdp_fuse_readdir,
  .releasedir   = xdp_fuse_releasedir,
  /*
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
  root_inode = xdp_inode_new (ROOT_INODE, XDP_INODE_ROOT, NULL, "/", NULL, NULL);
  by_app_inode = xdp_inode_new (BY_APP_INODE, XDP_INODE_BY_APP, root_inode, BY_APP_NAME, NULL, NULL);
  dir_to_inode_nr =
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
