lib_LTLIBRARIES += libxdg-app.la

public_headers = \
	lib/xdg-app.h \
	lib/xdg-app-version-macros.h \
	$(NULL)


xdgappincludedir = $(includedir)/xdg-app
xdgappinclude_HEADERS = $(public_headers)

libxdg_app_la_SOURCES = \
	$(public_headers) \
	lib/xdg-app.c \
	$(NULL)

libxdg_app_la_CFLAGS = \
	-DXDG_APP_COMPILATION \
	-I$(srcdir)/lib \
	$(AM_CFLAGS) \
	$(BASE_CFLAGS) \
	$(OSTREE_CFLAGS) \
	$(SOUP_CFLAGS) \
	$(NULL)

libxdg_app_la_LDFLAGS = \
	$(HIDDEN_VISIBILITY_CFLAGS)		\
	-version-info $(LT_VERSION_INFO)	\
	-export-dynamic				\
	-rpath $(libdir)			\
	$(NULL)

libxdg_app_la_LIBADD = \
	libglnx.la	\
	$(BASE_LIBS)	\
	$(OSTREE_LIBS)	\
	$(SOUP_LIBS)	\
	$(NULL)
