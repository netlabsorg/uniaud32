/*
 * version.h   Header for version string
 *
 *    Generated by mkversion.cmd, do NOT edit !
 *
 */
 
 
#ifndef __UNIAUDVERSION_H__
#define __UNIAUDVERSION_H__
 
 
#define PRODUCT_NAME            "Universal Audio Driver for OS/2 and eComStation"
#define VENDOR_NAME             "Netlabs"
#define PRODUCT_TIMESTAMP       20080323L       // YYYYMMDD
#define UNIAUD_VERSION          "9.9.9-PS"
#define ALSA_VERSION            "1.0.16"
 
 
#define RM_VERSION              999
#define RM_DRIVER_NAME          "UNIAUD32.SYS"
#define RM_DRIVER_DESCRIPTION   "OS/2 Universal Audio 32 Driver"
#define RM_ADAPTER_NAME         "OS/2 Universal Audio"
#define RM_DRIVER_VENDORNAME    "Netlabs <www.netlabs.org>"
#define RM_DRIVER_BUILDYEAR     (PRODUCT_TIMESTAMP / 10000)
#define RM_DRIVER_BUILDMONTH    ((PRODUCT_TIMESTAMP / 100) % 100)
#define RM_DRIVER_BUILDDAY      (PRODUCT_TIMESTAMP % 100)
 
 
#endif //__UNIAUDVERSION_H__
 