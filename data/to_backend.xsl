<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">
  <xsl:template match="@*|node()" name="identity">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()" />
    </xsl:copy>
  </xsl:template>
  <xsl:template match="node/interface/method/*[1]">
    <arg type='s' name="sender" direction="in"/>
    <arg type='s' name="app_id" direction="in"/>
    <xsl:call-template name="identity" />
  </xsl:template>
  <xsl:template match="node/interface/signal/*[1]">
    <arg type='s' name="destination"/>
    <xsl:call-template name="identity" />
  </xsl:template>
  <xsl:template match="node/interface">
    <interface name="{@name}Backend">
      <xsl:apply-templates/>
    </interface>
  </xsl:template>
</xsl:stylesheet>
