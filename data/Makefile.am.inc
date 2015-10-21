%Backend.xml: %.xml data/to_backend.xsl
	xsltproc --novalid --nonet data/to_backend.xsl $< > $@

introspectiondir = $(datadir)/dbus-1/interfaces
introspection_DATA = \
	data/org.freedesktop.portal.FileChooser.xml \
	data/org.freedesktop.portal.FileChooserBackend.xml \
	data/org.freedesktop.portal.Documents.xml \
	data/org.freedesktop.XdgApp.xml \
	$(NULL)

EXTRA_DIST += \
	data/org.freedesktop.portal.Documents.xml \
	data/org.freedesktop.systemd1.xml \
	data/org.freedesktop.XdgApp.xml \
	$(NULL)
