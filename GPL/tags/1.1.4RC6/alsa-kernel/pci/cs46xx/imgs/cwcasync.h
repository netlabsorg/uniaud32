/* generated from cwcasync.osp DO NOT MODIFY */

#ifndef __HEADER_cwcasync_H__
#define __HEADER_cwcasync_H__

static struct dsp_symbol_entry cwcasync_symbols[] = {
  { 0x8000, "EXECCHILD",0x03 },
  { 0x8001, "EXECCHILD_98",0x03 },
  { 0x8003, "EXECCHILD_PUSH1IND",0x03 },
  { 0x8008, "EXECSIBLING",0x03 },
  { 0x800a, "EXECSIBLING_298",0x03 },
  { 0x800b, "EXECSIBLING_2IND1",0x03 },
  { 0x8010, "TIMINGMASTER",0x03 },
  { 0x804f, "S16_CODECINPUTTASK",0x03 },
  { 0x805e, "PCMSERIALINPUTTASK",0x03 },
  { 0x806d, "S16_MIX_TO_OSTREAM",0x03 },
  { 0x809a, "S16_MIX",0x03 },
  { 0x80bb, "S16_UPSRC",0x03 },
  { 0x813b, "MIX3_EXP",0x03 },
  { 0x8164, "DECIMATEBYPOW2",0x03 },
  { 0x8197, "VARIDECIMATE",0x03 },
  { 0x81f2, "_3DINPUTTASK",0x03 },
  { 0x820a, "_3DPRLGCINPTASK",0x03 },
  { 0x8227, "_3DSTEREOINPUTTASK",0x03 },
  { 0x8242, "_3DOUTPUTTASK",0x03 },
  { 0x82c4, "HRTF_MORPH_TASK",0x03 },
  { 0x82c6, "WAIT4DATA",0x03 },
  { 0x82fa, "PROLOGIC",0x03 },
  { 0x8496, "DECORRELATOR",0x03 },
  { 0x84a4, "STEREO2MONO",0x03 },
  { 0x0000, "OVERLAYBEGINADDRESS",0x00 },
  { 0x0000, "SPIOWRITE",0x03 },
  { 0x000d, "S16_ASYNCCODECINPUTTASK",0x03 },
  { 0x0043, "SPDIFITASK",0x03 },
  { 0x007b, "SPDIFOTASK",0x03 },
  { 0x0097, "ASYNCHFGTXCODE",0x03 },
  { 0x00be, "ASYNCHFGRXCODE",0x03 },
  { 0x00db, "#CODE_END",0x00 },
}; /* cwcasync symbols */

static u32 cwcasync_code[] = {
/* OVERLAYBEGINADDRESS */
/* 0000 */ 0x00002731,0x00001400,0x00003725,0x000a8440,
/* 0002 */ 0x000000ae,0x00000000,0x00060630,0x00001000,
/* 0004 */ 0x00000000,0x000c7560,0x00075282,0x0002d640,
/* 0006 */ 0x00021705,0x00000000,0x00072ab8,0x0002d6c0,
/* 0008 */ 0x00020630,0x00001000,0x000c74c2,0x000d4b82,
/* 000A */ 0x000475c2,0x00000000,0x0003430a,0x000c0000,
/* 000C */ 0x00042730,0x00001400,
/* S16_ASYNCCODECINPUTTASK */
/* 000D */ 0x0006a108,0x000cf2c4,0x0004f4c0,0x00000000,
/* 000F */ 0x000fa418,0x0000101f,0x0005d402,0x0001c500,
/* 0011 */ 0x000f0630,0x00001000,0x00004418,0x00001380,
/* 0013 */ 0x000e243d,0x000d394a,0x00049705,0x00000000,
/* 0015 */ 0x0007d530,0x000b4240,0x000e00f2,0x00001000,
/* 0017 */ 0x00009134,0x000ca20a,0x00004c90,0x00001000,
/* 0019 */ 0x0005d705,0x00000000,0x00004f25,0x00098240,
/* 001B */ 0x00004725,0x00000000,0x0000e48a,0x00000000,
/* 001D */ 0x00027295,0x0009c2c0,0x0003df25,0x00000000,
/* 001F */ 0x000e8030,0x00001001,0x0005f718,0x000ac600,
/* 0021 */ 0x0007cf30,0x000c2a01,0x00082630,0x00001001,
/* 0023 */ 0x000504a0,0x00001001,0x00029314,0x000bcb80,
/* 0025 */ 0x0003cf25,0x000b0e00,0x0004f5c0,0x00000000,
/* 0027 */ 0x00049118,0x000d888a,0x0007dd02,0x000c6efa,
/* 0029 */ 0x00000000,0x00000000,0x0004f5c0,0x00069c80,
/* 002B */ 0x0000d402,0x00000000,0x000e8630,0x00001001,
/* 002D */ 0x00079130,0x00000000,0x00049118,0x00090e00,
/* 002F */ 0x0006c10a,0x00000000,0x00000000,0x000c0000,
/* 0031 */ 0x0007cf30,0x00030580,0x00005725,0x00000000,
/* 0033 */ 0x000d84a0,0x00001001,0x00029314,0x000b4780,
/* 0035 */ 0x0003cf25,0x000b8600,0x00000000,0x00000000,
/* 0037 */ 0x00000000,0x000c0000,0x00000000,0x00042c80,
/* 0039 */ 0x0001dec1,0x000e488c,0x00031114,0x00000000,
/* 003B */ 0x0004f5c2,0x00000000,0x0003640a,0x00000000,
/* 003D */ 0x00000000,0x000e5084,0x00000000,0x000eb844,
/* 003F */ 0x00007001,0x00000000,0x00000734,0x00001000,
/* 0041 */ 0x00010705,0x000a6880,0x00006a88,0x000c75c4,
/* SPDIFITASK */
/* 0043 */ 0x0006a108,0x000cf2c4,0x0004f4c0,0x000d5384,
/* 0045 */ 0x0007e48a,0x00000000,0x00067718,0x00001000,
/* 0047 */ 0x0007a418,0x00001000,0x0007221a,0x00000000,
/* 0049 */ 0x0005d402,0x00014500,0x000b8630,0x00001002,
/* 004B */ 0x00004418,0x00001780,0x000e243d,0x000d394a,
/* 004D */ 0x00049705,0x00000000,0x0007d530,0x000b4240,
/* 004F */ 0x000ac0f2,0x00001002,0x00014414,0x00000000,
/* 0051 */ 0x00004c90,0x00001000,0x0005d705,0x00000000,
/* 0053 */ 0x00004f25,0x00098240,0x00004725,0x00000000,
/* 0055 */ 0x0000e48a,0x00000000,0x00027295,0x0009c2c0,
/* 0057 */ 0x0007df25,0x00000000,0x000ac030,0x00001003,
/* 0059 */ 0x0005f718,0x000fe798,0x00029314,0x000bcb80,
/* 005B */ 0x00000930,0x000b0e00,0x0004f5c0,0x000de204,
/* 005D */ 0x000884a0,0x00001003,0x0007cf25,0x000e3560,
/* 005F */ 0x00049118,0x00000000,0x00049118,0x000d888a,
/* 0061 */ 0x0007dd02,0x000c6efa,0x0000c434,0x00030040,
/* 0063 */ 0x000fda82,0x000c2312,0x000fdc0e,0x00001001,
/* 0065 */ 0x00083402,0x000c2b92,0x000706b0,0x00001003,
/* 0067 */ 0x00075a82,0x00000000,0x0000d625,0x000b0940,
/* 0069 */ 0x0000840e,0x00001002,0x0000aabc,0x000c511e,
/* 006B */ 0x00078730,0x00001003,0x0000aaf4,0x000e910a,
/* 006D */ 0x0004628a,0x00000000,0x00006aca,0x00000000,
/* 006F */ 0x00000930,0x00000000,0x0004f5c0,0x00069c80,
/* 0071 */ 0x00046ac0,0x00000000,0x0003c40a,0x000fc898,
/* 0073 */ 0x00049118,0x00090e00,0x0006c10a,0x00000000,
/* 0075 */ 0x00000000,0x000e5084,0x00000000,0x000eb844,
/* 0077 */ 0x00007001,0x00000000,0x00000734,0x00001000,
/* 0079 */ 0x00010705,0x000a6880,0x00006a88,0x000c75c4,
/* SPDIFOTASK */
/* 007B */ 0x0006a108,0x000c0000,0x0004f4c0,0x000c3245,
/* 007D */ 0x0000a418,0x00001000,0x0003a20a,0x00000000,
/* 007F */ 0x00004418,0x00001380,0x000e243d,0x000d394a,
/* 0081 */ 0x000c9705,0x000def92,0x0008c030,0x00001004,
/* 0083 */ 0x0005f718,0x000fe798,0x00000000,0x000c0000,
/* 0085 */ 0x00005725,0x00000000,0x000704a0,0x00001004,
/* 0087 */ 0x00029314,0x000b4780,0x0003cf25,0x000b8600,
/* 0089 */ 0x00000000,0x00000000,0x00000000,0x000c0000,
/* 008B */ 0x00000000,0x00042c80,0x0001dec1,0x000e488c,
/* 008D */ 0x00031114,0x00000000,0x0004f5c2,0x00000000,
/* 008F */ 0x0004a918,0x00098600,0x0006c28a,0x00000000,
/* 0091 */ 0x00000000,0x000e5084,0x00000000,0x000eb844,
/* 0093 */ 0x00007001,0x00000000,0x00000734,0x00001000,
/* 0095 */ 0x00010705,0x000a6880,0x00006a88,0x000c75c4,
/* ASYNCHFGTXCODE */
/* 0097 */ 0x0002a880,0x000b4e40,0x00042214,0x000e5548,
/* 0099 */ 0x000542bf,0x00000000,0x00000000,0x000481c0,
/* 009B */ 0x00000000,0x00000000,0x00000000,0x00000030,
/* 009D */ 0x0000072d,0x000fbf8a,0x00077f94,0x000ea7df,
/* 009F */ 0x0002ac95,0x000d3145,0x00002731,0x00001400,
/* 00A1 */ 0x00006288,0x000c71c4,0x00014108,0x000e6044,
/* 00A3 */ 0x00035408,0x00000000,0x00025418,0x000a0ec0,
/* 00A5 */ 0x0001443d,0x000ca21e,0x00046595,0x000d730c,
/* 00A7 */ 0x0006538e,0x00000000,0x00064630,0x00001005,
/* 00A9 */ 0x000e7b0e,0x000df782,0x000746b0,0x00001005,
/* 00AB */ 0x00036f05,0x000c0000,0x00043695,0x000d598c,
/* 00AD */ 0x0005331a,0x000f2185,0x00000000,0x00000000,
/* 00AF */ 0x000007ae,0x000bdb00,0x00040630,0x00001400,
/* 00B1 */ 0x0005e708,0x000c0000,0x0007ef30,0x000b1c00,
/* 00B3 */ 0x000d86a0,0x00001005,0x00066408,0x000c0000,
/* 00B5 */ 0x00000000,0x00000000,0x00021843,0x00000000,
/* 00B7 */ 0x00000cac,0x00062c00,0x00001dac,0x00063400,
/* 00B9 */ 0x00002cac,0x0006cc80,0x000db943,0x000e5ca1,
/* 00BB */ 0x00000000,0x00000000,0x0006680a,0x000f3205,
/* 00BD */ 0x00042730,0x00001400,
/* ASYNCHFGRXCODE */
/* 00BE */ 0x00014108,0x000f2204,0x00025418,0x000a2ec0,
/* 00C0 */ 0x00015dbd,0x00038100,0x00015dbc,0x00000000,
/* 00C2 */ 0x0005e415,0x00034880,0x0001258a,0x000d730c,
/* 00C4 */ 0x0006538e,0x000baa40,0x00060630,0x00001006,
/* 00C6 */ 0x00067b0e,0x000ac380,0x0003ef05,0x00000000,
/* 00C8 */ 0x0000f734,0x0001c300,0x000586b0,0x00001400,
/* 00CA */ 0x000b6f05,0x000c3a00,0x00048f05,0x00000000,
/* 00CC */ 0x0005b695,0x0008c380,0x0002058e,0x00000000,
/* 00CE */ 0x000500b0,0x00001400,0x0002b318,0x000e998d,
/* 00D0 */ 0x0006430a,0x00000000,0x00000000,0x000ef384,
/* 00D2 */ 0x00004725,0x000c0000,0x00000000,0x000f3204,
/* 00D4 */ 0x00004f25,0x000c0000,0x00080000,0x000e5ca1,
/* 00D6 */ 0x000cb943,0x000e5ca1,0x0004b943,0x00000000,
/* 00D8 */ 0x00040730,0x00001400,0x000cb943,0x000e5ca1,
/* 00DA */ 0x0004b943,0x00000000
};
/* #CODE_END */

static struct dsp_segment_desc cwcasync_segments[] = {
  { SEGTYPE_SP_PROGRAM, 0x00000000, 0x000001b6, cwcasync_code },
};

static struct dsp_module_desc cwcasync_module = {
  "cwcasync",
  {
    32,
    cwcasync_symbols
  },
  1,
  cwcasync_segments,
};

#endif /* __HEADER_cwcasync_H__ */
