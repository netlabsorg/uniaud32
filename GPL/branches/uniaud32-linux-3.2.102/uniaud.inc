# Set build constants to be read by mkversion.cmd

# Product name
PRODUCTNAME = Universal Audio Driver for OS/2

# Full UNIAUD build version
# BUILDVERSION must be 3 parts, and only numbers like 5.44.108
# The second and third numbers must be 2 digits
BUILDVERSION = 2.02.06

# Fixpack version
# Use this if you want to add extra chars (comments) to bldlevel
# ex RC3  GA  FIXPACK2 beta_47
# Comment out to avoid a fixpack line in bldlevel
FIXPACK = SVN

# ALSA BUILD VERSION
# Use this to to include the ALSA revision
# ex 0.9.2  1.0.14RC3
# Leave empty or use MIXED
# STRING must be max X chars
ALSAVERSION = 3.2.102
