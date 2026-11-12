/*
 * mixer.c - software mixer for UNIAUD32 wave PLAYBACK  (experimental, see UNIAUD-probe\MIXER-DESIGN.md)
 *
 * Problem: the sound hardware (e.g. AC97 ICH) has ONE playback substream, ALSA allows one open of it, and
 * MMPM/2 therefore plays one sound at a time.  Here every MMPM stream opens a "virtual stream" with its own
 * ring buffer; the virtual streams are summed into ONE shared hardware stream (fixed format S16_LE, 2 ch,
 * 48000 Hz, which uniaud16 produces for every stream because QueryDevCaps reports only that format).
 *
 * Interface: this file implements the IDC32_WAVE_* commands for virtual streams (OSS32_MixHandleIDC, called
 * first from OSS32IDC in drv32/idc.c) and the mixing pass OSS32_MixService, called from the sound card IRQ
 * path (OSS32_ProcessIRQ) before uniaud16 is notified.  Capture streams are not affected.
 *
 * (C) 2026 - GPL v2 or later, same as uniaud32.
 */

#include <sound/core.h>
#include <sound/control.h>
#include <sound/info.h>
#include <sound/pcm.h>
#include <sound/pcm_params.h>
#include <sound/minors.h>
#include <linux/file.h>
#include <linux/soundcard.h>

#define LINUX
#include <ossidc32.h>
#include <osspci.h>
#include <stacktoflat.h>
#include <stdlib.h>
#include <proto.h>
#include <u32ioctl.h>
#include "soundoss.h"

#ifdef MIXER_ENABLE

extern int pcm_device;

/* ---- fixed mixer format and sizing ------------------------------------------------------------ */
#define MIX_RATE          48000UL
#define MIX_CHANNELS      2UL
#define MIX_BITS          16UL
#define MIX_FRAME         4UL                     /* bytes per frame (S16 stereo)                    */
#define MIX_MAX_STREAMS   8   /* slots (MMPM admits 4 active; idle streams may still hold a slot) */
#define MIX_RING_SIZE     0x10000UL               /* per-stream ring, power of two (64 KB = 340 ms)  */
#define MIX_RING_MASK     (MIX_RING_SIZE - 1)
#define MIX_HW_PERIOD     2048UL                  /* hardware period in bytes (512 frames = 10.7 ms) */
#define MIX_TARGET_FILL   (6 * MIX_HW_PERIOD)     /* keep about 6 periods (64 ms) queued in the hw buffer */
#define MIX_CHUNK         4096UL                  /* bytes mixed per pass through the loop           */

#define MIX_MAGIC         0x4D495831UL            /* 'MIX1'                                          */

/* stream states */
#define MS_OPEN      0
#define MS_PREPARED  1
#define MS_RUNNING   2
#define MS_PAUSED    3

typedef struct mixstream {
    ULONG           magic;
    volatile int    state;
    ULONG           fileid;
    UCHAR          *ring;
    volatile ULONG  wr;          /* free running byte counters; index = counter & MIX_RING_MASK */
    volatile ULONG  rd;
    volatile ULONG  consumed;    /* bytes mixed out: reported as stream position                  */
    volatile ULONG  accepted;    /* bytes accepted from uniaud16                                  */
    volatile LONG   volL, volR;  /* per-stream gain 0..100 (percent), set by IDC32_WAVE_SETVOLUME  */
} MIXSTREAM;

static MIXSTREAM *g_streams[MIX_MAX_STREAMS];
static int        g_nstreams = 0;
static OSSSTREAMID g_hw = 0;           /* the shared hardware stream (a normal OSS32 wave handle)  */
static ULONG      g_hwBufBytes = 0;    /* hardware ring size in bytes                              */
static ULONG      g_deviceid = 0;
static volatile int g_inService = 0;
/* statistics, printed when a virtual stream closes */
static ULONG g_statPasses = 0, g_statClip = 0, g_statHwShort = 0, g_statIdle = 0;
static ULONG g_statUnder[MIX_MAX_STREAMS];

/* interrupt flag save / restore (Watcom inline assembler) */
static ULONG mix_irq_save(void);
#pragma aux mix_irq_save = "pushfd" "cli" "pop eax" value [eax] modify exact [eax];
static void mix_irq_restore(ULONG flags);
#pragma aux mix_irq_restore = "push eax" "popfd" parm [eax] modify exact [];

static SHORT g_mixbuf[MIX_CHUNK / 2];

/* ---- helpers ------------------------------------------------------------------------------------ */
static MIXSTREAM *mix_find(OSSSTREAMID id)
{
    int i;
    for (i = 0; i < MIX_MAX_STREAMS; i++)
        if (g_streams[i] && (OSSSTREAMID)g_streams[i] == id && g_streams[i]->magic == MIX_MAGIC)
            return g_streams[i];
    return NULL;
}

BOOL OSS32_MixIsStream(OSSSTREAMID id)
{
    return mix_find(id) != NULL;
}

static void mix_stream_reset(MIXSTREAM *s)
{
    ULONG f = mix_irq_save();
    s->wr = s->rd = s->consumed = s->accepted = 0;
    mix_irq_restore(f);
}

/* ---- hardware stream management --------------------------------------------------------------- */
static OSSRET mix_hw_open(ULONG deviceid)
{
    OSS32_HWPARAMS hp;
    OSSRET rc;
    ULONG avail = 0;

    if (g_hw) return OSSERR_SUCCESS;

    rc = OSS32_WaveOpen(deviceid, OSS32_STREAM_WAVEOUT, &g_hw, pcm_device, 0);
    if (rc != OSSERR_SUCCESS) { g_hw = 0; rprintf(("MIX: hw open failed rc=%d", rc)); return rc; }

    hp.ulSampleRate    = MIX_RATE;
    hp.ulBitsPerSample = MIX_BITS;
    hp.ulNumChannels   = MIX_CHANNELS;
    hp.ulDataType      = OSS32_PCM_FORMAT_S16_LE;
    hp.ulPeriodSize    = MIX_HW_PERIOD;
    rc = OSS32_WaveSetHwParams(g_hw, &hp);
    if (rc != OSSERR_SUCCESS) {
        rprintf(("MIX: hw SetHwParams failed rc=%d", rc));
        OSS32_WaveClose(g_hw); g_hw = 0; return rc;
    }
    OSS32_WavePrepare(g_hw);
    OSS32_WaveGetSpace(g_hw, &avail);
    g_hwBufBytes = avail;
    g_deviceid = deviceid;
    rprintf(("MIX: hardware stream open, buffer %lu bytes", g_hwBufBytes));
    return OSSERR_SUCCESS;
}

static void mix_hw_close(void)
{
    if (!g_hw) return;
    OSS32_WaveStop(g_hw);
    OSS32_WaveClose(g_hw);
    g_hw = 0;
    g_hwBufBytes = 0;
}

/* ---- the mixing pass ------------------------------------------------------------------------------ */
void OSS32_MixService(void)
{
    ULONG avail, want, done, pass, nfr, i, take, got, rdidx;
    int   k;
    LONG  acc;
    SHORT *src;
    int   contributed;

    if (g_inService) return;
    if (!g_hw || !g_nstreams) return;
    g_inService = 1;

    for (pass = 0; pass < 8; pass++)
    {
        if (OSS32_WaveGetSpace(g_hw, &avail) != OSSERR_SUCCESS) break;
        if (avail + MIX_TARGET_FILL <= g_hwBufBytes) break;       /* already filled up to the target */
        want = avail - (g_hwBufBytes - MIX_TARGET_FILL);
        want &= ~(MIX_FRAME - 1);
        if (want > MIX_CHUNK) want = MIX_CHUNK;
        if (want == 0) break;

        nfr = want / 2;                          /* samples (both channels) in this chunk */
        for (i = 0; i < nfr; i++) g_mixbuf[i] = 0;   /* placeholder; summed below via acc per sample */
        contributed = 0;

        /* per-stream data: first find how many whole frames each running stream can give */
        {
            ULONG takeb[MIX_MAX_STREAMS];
            for (k = 0; k < MIX_MAX_STREAMS; k++) {
                MIXSTREAM *s = g_streams[k];
                takeb[k] = 0;
                if (s && s->state == MS_RUNNING) {
                    got = s->wr - s->rd;
                    take = (got < want) ? got : want;
                    take &= ~(MIX_FRAME - 1);
                    takeb[k] = take;
                    if (take < want) g_statUnder[k]++;     /* this stream could not fill the whole chunk */
                    if (take) contributed = 1;
                }
            }
            if (!contributed) { g_statIdle++; break; }   /* nothing to play: let the hardware drain/idle */
            g_statPasses++;

            for (i = 0; i < nfr; i++) {
                acc = 0;
                for (k = 0; k < MIX_MAX_STREAMS; k++) {
                    MIXSTREAM *s = g_streams[k];
                    if (s && takeb[k] > i * 2) {
                        rdidx = (s->rd + i * 2) & MIX_RING_MASK;
                        src = (SHORT *)(s->ring + rdidx);
                        acc += ((LONG)*src * ((i & 1) ? s->volR : s->volL)) / 100;
                    }
                }
                if (acc > 32767) { acc = 32767; g_statClip++; }
                else if (acc < -32768) { acc = -32768; g_statClip++; }
                g_mixbuf[i] = (SHORT)acc;
            }
            /* advance the consumed streams (interrupts off: AddBuffer/Prepare may race) */
            {
                ULONG f = mix_irq_save();
                for (k = 0; k < MIX_MAX_STREAMS; k++) {
                    MIXSTREAM *s = g_streams[k];
                    if (s && takeb[k] && s->state == MS_RUNNING) {
                        s->rd += takeb[k];
                        s->consumed += takeb[k];
                    }
                }
                mix_irq_restore(f);
            }
        }

        done = 0;
        if (OSS32_WaveAddBuffer(g_hw, (ULONG)g_mixbuf, want, &done, pcm_device) != OSSERR_SUCCESS) break;
        if (done < want) { g_statHwShort++; break; }
    }

    g_inService = 0;
}

/* ---- IDC command handlers --------------------------------------------------------------------------- */
static OSSRET mix_open(PIDC32_PACKET pPacket)
{
    MIXSTREAM *s;
    int i, slot = -1;
    OSSRET rc;
    ULONG f;

    for (i = 0; i < MIX_MAX_STREAMS; i++) if (!g_streams[i]) { slot = i; break; }
    if (slot < 0) { rprintf(("MIX: no free virtual stream")); return OSSERR_NO_DEVICE_AVAILABLE; }

    s = (MIXSTREAM *)kmalloc(sizeof(MIXSTREAM), GFP_KERNEL);
    if (!s) return OSSERR_OUT_OF_MEMORY;
    memset(s, 0, sizeof(MIXSTREAM));
    s->ring = (UCHAR *)kmalloc(MIX_RING_SIZE, GFP_KERNEL);
    if (!s->ring) { kfree(s); return OSSERR_OUT_OF_MEMORY; }
    memset(s->ring, 0, MIX_RING_SIZE);
    s->magic  = MIX_MAGIC;
    s->volL = s->volR = 100;
    s->state  = MS_OPEN;
    s->fileid = pPacket->fileid;

    rc = mix_hw_open(pPacket->open.devicenr);
    if (rc != OSSERR_SUCCESS) { kfree(s->ring); kfree(s); return rc; }

    f = mix_irq_save();
    g_streams[slot] = s;
    g_nstreams++;
    mix_irq_restore(f);

    pPacket->streamid = (OSSSTREAMID)s;
    dprintf(("MIX: open stream %lx slot %d file %lx (now %d)", (ULONG)s, slot, s->fileid, g_nstreams));
    return OSSERR_SUCCESS;
}

static OSSRET mix_close(MIXSTREAM *s)
{
    int i;
    ULONG f;

    f = mix_irq_save();
    for (i = 0; i < MIX_MAX_STREAMS; i++) if (g_streams[i] == s) { g_streams[i] = NULL; g_nstreams--; }
    s->magic = 0;
    mix_irq_restore(f);

    kfree(s->ring);
    kfree(s);
    dprintf(("MIX: close stream %lx (left %d)", (ULONG)s, g_nstreams));
    rprintf(("MIX: stats passes=%lu idle=%lu clip=%lu hwshort=%lu under=%lu/%lu/%lu/%lu", g_statPasses, g_statIdle,
             g_statClip, g_statHwShort, g_statUnder[0], g_statUnder[1], g_statUnder[2], g_statUnder[3]));
    if (g_nstreams == 0) mix_hw_close();
    return OSSERR_SUCCESS;
}

static OSSRET mix_sethwparams(MIXSTREAM *s, OSS32_HWPARAMS *p)
{
    (void)s;
    if (!p) return OSSERR_INVALID_PARAMETER;
    if (p->ulSampleRate != MIX_RATE || p->ulBitsPerSample != MIX_BITS || p->ulNumChannels != MIX_CHANNELS ||
        p->ulDataType != OSS32_PCM_FORMAT_S16_LE)
    {
        rprintf(("MIX: unsupported format rate=%lu bits=%lu ch=%lu type=%lu", p->ulSampleRate,
                 p->ulBitsPerSample, p->ulNumChannels, p->ulDataType));
        return OSSERR_INVALID_PARAMETER;
    }
    return OSSERR_SUCCESS;
}

static OSSRET mix_addbuffer(MIXSTREAM *s, ULONG buffer, ULONG size, ULONG *pTransferred)
{
    ULONG space, n, idx, first;

    if (!buffer || !size) return OSSERR_INVALID_PARAMETER;
    *pTransferred = 0;
    if (s->state == MS_PAUSED) return OSSERR_BUFFER_FULL;

    space = MIX_RING_SIZE - (s->wr - s->rd);
    n = (size < space) ? size : space;
    n &= ~(MIX_FRAME - 1);
    if (n == 0) return OSSERR_BUFFER_FULL;

    idx = s->wr & MIX_RING_MASK;
    first = MIX_RING_SIZE - idx;
    if (first > n) first = n;
    memcpy(s->ring + idx, (void *)buffer, first);
    if (n > first) memcpy(s->ring, (UCHAR *)buffer + first, n - first);

    {
        ULONG f = mix_irq_save();
        s->wr += n;
        s->accepted += n;
        if (s->state == MS_PREPARED || s->state == MS_OPEN) s->state = MS_RUNNING;   /* first data starts playback */
        mix_irq_restore(f);
    }
    *pTransferred = n;
    OSS32_MixService();          /* start/refill the hardware right away */
    return OSSERR_SUCCESS;
}

/* Returns TRUE if the command was handled here (result in *prc). */
BOOL OSS32_MixHandleIDC(ULONG cmd, PIDC32_PACKET pPacket, OSSRET *prc)
{
    MIXSTREAM *s;

    if (cmd == IDC32_WAVE_OPEN)
    {
        if (pPacket->open.streamtype != OSS32_STREAM_WAVEOUT) return FALSE;     /* capture: old path */
        *prc = mix_open(pPacket);
        return TRUE;
    }

    switch (cmd)
    {
    case IDC32_WAVE_CLOSE:
    case IDC32_WAVE_ADDBUFFER:
    case IDC32_WAVE_GETSPACE:
    case IDC32_WAVE_PREPARE:
    case IDC32_WAVE_RESUME:
    case IDC32_WAVE_PAUSE:
    case IDC32_WAVE_START:
    case IDC32_WAVE_STOP:
    case IDC32_WAVE_SETHWPARAMS:
    case IDC32_WAVE_GETPOS:
    case IDC32_WAVE_GETHWPTR:
    case IDC32_WAVE_GETSTATUS:
    case IDC32_WAVE_SETVOLUME:
        break;
    default:
        return FALSE;
    }

    s = mix_find(pPacket->streamid);
    if (!s) return FALSE;                        /* a normal (capture) stream */

    switch (cmd)
    {
    case IDC32_WAVE_CLOSE:
        *prc = mix_close(s);
        break;

    case IDC32_WAVE_ADDBUFFER:
    {
        ULONG transferred = 0;
        *prc = mix_addbuffer(s, pPacket->buffer.buffer, pPacket->buffer.size, &transferred);
        pPacket->buffer.transferred = transferred;
        break;
    }

    case IDC32_WAVE_GETSPACE:
        pPacket->getspace.bytesavail = MIX_RING_SIZE - (s->wr - s->rd);
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_PREPARE:
        mix_stream_reset(s);
        s->state = MS_PREPARED;
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_START:
    case IDC32_WAVE_RESUME:
        if (s->state == MS_PAUSED || s->state == MS_PREPARED) s->state = MS_RUNNING;
        *prc = OSSERR_SUCCESS;
        OSS32_MixService();
        break;

    case IDC32_WAVE_PAUSE:
        if (s->state == MS_RUNNING) s->state = MS_PAUSED;
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_STOP:                        /* DROP: discard queued data */
        mix_stream_reset(s);
        s->state = MS_PREPARED;
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_SETHWPARAMS:
        *prc = mix_sethwparams(s, (OSS32_HWPARAMS *)__Stack16ToFlat(pPacket->sethwparams.hwparams));
        break;

    case IDC32_WAVE_GETPOS:
        pPacket->getpos.position = s->consumed;
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_GETHWPTR:
        pPacket->getpos.position = s->accepted;
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_GETSTATUS:
        /* ALSA state numbers: PREPARED=2 RUNNING=3 PAUSED=6 */
        pPacket->status.state = (s->state == MS_RUNNING) ? 3 : (s->state == MS_PAUSED) ? 6 : 2;
        *prc = OSSERR_SUCCESS;
        break;

    case IDC32_WAVE_SETVOLUME:
    {
        LONG l = (LONG)GET_VOLUME_L(pPacket->setwavevol.volume);
        LONG r = (LONG)GET_VOLUME_R(pPacket->setwavevol.volume);
        if (l > 100) l = 100;
        if (r > 100) r = 100;
        s->volL = l;
        s->volR = r;
        dprintf(("MIX: stream %lx volume %ld/%ld", (ULONG)s, l, r));
        *prc = OSSERR_SUCCESS;
        break;
    }
    }
    return TRUE;
}

#endif /* MIXER_ENABLE */
