/*
 *  Driver for C-Media's CMI8330 soundcards.
 *  Copyright (c) by George Talusan <gstalusan@uwaterloo.ca>
 *    http://www.undergrad.math.uwaterloo.ca/~gstalusa
 *
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
 *
 */

/*
 * NOTES
 *
 *  The extended registers contain mixer settings which are largely
 *  untapped for the time being.
 *
 *  MPU401 and SPDIF are not supported yet.  I don't have the hardware
 *  to aid in coding and testing, so I won't bother.
 *
 *  To quickly load the module,
 *
 *  modprobe -a snd-card-cmi8330 sbport=0x220 sbirq=5 sbdma8=1
 *    sbdma16=5 wssport=0x530 wssirq=11 wssdma=0
 *
 *  This card has two mixers and two PCM devices.  I've cheesed it such
 *  that recording and playback can be done through the same device.
 *  The driver "magically" routes the capturing to the AD1848 codec,
 *  and playback to the SB16 codec.  This allows for full-duplex mode
 *  to some extent.
 *  The utilities in alsa-utils are aware of both devices, so passing
 *  the appropriate parameters to amixer and alsactl will give you
 *  full control over both mixers.
 */

#include <sound/driver.h>
#include <linux/init.h>
#include <linux/slab.h>
#ifndef LINUX_ISAPNP_H
#include <linux/isapnp.h>
#define isapnp_card pci_bus
#define isapnp_dev pci_dev
#endif
#include <sound/core.h>
#include <sound/ad1848.h>
#include <sound/sb.h>
#define SNDRV_GET_ID
#include <sound/initval.h>

MODULE_AUTHOR("George Talusan <gstalusan@uwaterloo.ca>");
MODULE_DESCRIPTION("C-Media CMI8330");
MODULE_LICENSE("GPL");
MODULE_CLASSES("{sound}");
MODULE_DEVICES("{{C-Media,CMI8330,isapnp:{CMI0001,@@@0001,@X@0001}}}");

static int index[SNDRV_CARDS] = SNDRV_DEFAULT_IDX;
static char *id[SNDRV_CARDS] = SNDRV_DEFAULT_STR;
static int enable[SNDRV_CARDS] = SNDRV_DEFAULT_ENABLE_ISAPNP;
#ifdef __ISAPNP__
#ifdef TARGET_OS2
static int isapnp[SNDRV_CARDS] = {REPEAT_SNDRV(1)};
#else
static int isapnp[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 1};
#endif
#endif
static long sbport[SNDRV_CARDS] = SNDRV_DEFAULT_PORT;
static int sbirq[SNDRV_CARDS] = SNDRV_DEFAULT_IRQ;
static int sbdma8[SNDRV_CARDS] = SNDRV_DEFAULT_DMA;
static int sbdma16[SNDRV_CARDS] = SNDRV_DEFAULT_DMA;
static long wssport[SNDRV_CARDS] = SNDRV_DEFAULT_PORT;
static int wssirq[SNDRV_CARDS] = SNDRV_DEFAULT_IRQ;
static int wssdma[SNDRV_CARDS] = SNDRV_DEFAULT_DMA;

MODULE_PARM(index, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(index, "Index value for CMI8330 soundcard.");
MODULE_PARM_SYNTAX(index, SNDRV_INDEX_DESC);
MODULE_PARM(id, "1-" __MODULE_STRING(SNDRV_CARDS) "s");
MODULE_PARM_DESC(id, "ID string  for CMI8330 soundcard.");
MODULE_PARM_SYNTAX(id, SNDRV_ID_DESC);
MODULE_PARM(enable, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(enable, "Enable CMI8330 soundcard.");
MODULE_PARM_SYNTAX(enable, SNDRV_ENABLE_DESC);
#ifdef __ISAPNP__
MODULE_PARM(isapnp, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(isapnp, "ISA PnP detection for specified soundcard.");
MODULE_PARM_SYNTAX(isapnp, SNDRV_ISAPNP_DESC);
#endif

MODULE_PARM(sbport, "1-" __MODULE_STRING(SNDRV_CARDS) "l");
MODULE_PARM_DESC(sbport, "Port # for CMI8330 SB driver.");
MODULE_PARM_SYNTAX(sbport, SNDRV_ENABLED ",allows:{{0x220,0x280,0x20}},prefers:{0x220},base:16,dialog:list");
MODULE_PARM(sbirq, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(sbirq, "IRQ # for CMI8330 SB driver.");
MODULE_PARM_SYNTAX(sbirq, SNDRV_ENABLED ",allows:{{5},{7},{9},{10},{11},{12}},prefers:{5},dialog:list");
MODULE_PARM(sbdma8, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(sbdma8, "DMA8 for CMI8330 SB driver.");
MODULE_PARM_SYNTAX(sbdma8, SNDRV_DMA8_DESC ",prefers:{1}");
MODULE_PARM(sbdma16, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(sbdma16, "DMA16 for CMI8330 SB driver.");
MODULE_PARM_SYNTAX(sbdma16, SNDRV_ENABLED ",allows:{{5},{7}},prefers:{5},dialog:list");

MODULE_PARM(wssport, "1-" __MODULE_STRING(SNDRV_CARDS) "l");
MODULE_PARM_DESC(wssport, "Port # for CMI8330 WSS driver.");
MODULE_PARM_SYNTAX(wssport, SNDRV_ENABLED ",allows:{{0x530},{0xe80,0xf40,0xc0}},prefers:{0x530},base:16,dialog:list");
MODULE_PARM(wssirq, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(wssirq, "IRQ # for CMI8330 WSS driver.");
MODULE_PARM_SYNTAX(wssirq, SNDRV_ENABLED ",allows:{{5},{7},{9},{10},{11},{12}},prefers:{11},dialog:list");
MODULE_PARM(wssdma, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(wssdma, "DMA for CMI8330 WSS driver.");
MODULE_PARM_SYNTAX(wssdma, SNDRV_DMA8_DESC ",prefers:{0}");

#define CMI8330_RMUX3D    16
#define CMI8330_MUTEMUX   17
#define CMI8330_OUTPUTVOL 18
#define CMI8330_MASTVOL   19
#define CMI8330_LINVOL    20
#define CMI8330_CDINVOL   21
#define CMI8330_WAVVOL    22
#define CMI8330_RECMUX    23
#define CMI8330_WAVGAIN   24
#define CMI8330_LINGAIN   25
#define CMI8330_CDINGAIN  26

static unsigned char snd_cmi8330_image[((CMI8330_CDINGAIN)-16) + 1] =
{
	0x0,			/* 16 - recording mux */
	0x40,			/* 17 - mute mux */
	0x0,			/* 18 - vol */
	0x0,			/* 19 - master volume */
	0x0,			/* 20 - line-in volume */
	0x0,			/* 21 - cd-in volume */
	0x0,			/* 22 - wave volume */
	0x0,			/* 23 - mute/rec mux */
	0x0,			/* 24 - wave rec gain */
	0x0,			/* 25 - line-in rec gain */
	0x0			/* 26 - cd-in rec gain */
};

struct snd_cmi8330 {
#ifdef __ISAPNP__
	struct isapnp_dev *cap;
	struct isapnp_dev *play;
#endif
};

static snd_card_t *snd_cmi8330_cards[SNDRV_CARDS] = SNDRV_DEFAULT_PTR;

#ifdef __ISAPNP__

static struct isapnp_card *snd_cmi8330_isapnp_cards[SNDRV_CARDS] __devinitdata = SNDRV_DEFAULT_PTR;
static const struct isapnp_card_id *snd_cmi8330_isapnp_id[SNDRV_CARDS] __devinitdata = SNDRV_DEFAULT_PTR;

#ifdef TARGET_OS2
#define ISAPNP_CMI8330(_va, _vb, _vc, _device, _audio1, _audio2) \
	{ \
		0, ISAPNP_CARD_ID(_va, _vb, _vc, _device), \
		 { ISAPNP_DEVICE_ID('@', '@', '@', _audio1), \
		   ISAPNP_DEVICE_ID('@', 'X', '@', _audio2), } \
	}
#else
#define ISAPNP_CMI8330(_va, _vb, _vc, _device, _audio1, _audio2) \
	{ \
		ISAPNP_CARD_ID(_va, _vb, _vc, _device), \
		devs : { ISAPNP_DEVICE_ID('@', '@', '@', _audio1), \
			 ISAPNP_DEVICE_ID('@', 'X', '@', _audio2), } \
	}
#endif

static struct isapnp_card_id snd_cmi8330_pnpids[] __devinitdata =
{
	ISAPNP_CMI8330('C','M','I',0x0001,0x0001,0x0001),
	{ ISAPNP_CARD_END, }
};

ISAPNP_CARD_TABLE(snd_cmi8330_pnpids);

#endif

#define CMI8330_CONTROLS (sizeof(snd_cmi8330_controls)/sizeof(snd_kcontrol_new_t))

static snd_kcontrol_new_t snd_cmi8330_controls[] __devinitdata = {
AD1848_DOUBLE("Master Playback Volume", 0, CMI8330_MASTVOL, CMI8330_MASTVOL, 4, 0, 15, 0),
AD1848_SINGLE("Loud Playback Switch", 0, CMI8330_MUTEMUX, 6, 1, 1),
AD1848_DOUBLE("PCM Playback Switch", 0, AD1848_LEFT_OUTPUT, AD1848_RIGHT_OUTPUT, 7, 7, 1, 1),
AD1848_DOUBLE("PCM Playback Volume", 0, AD1848_LEFT_OUTPUT, AD1848_RIGHT_OUTPUT, 0, 0, 63, 1),
AD1848_DOUBLE("Line Playback Switch", 0, CMI8330_MUTEMUX, CMI8330_MUTEMUX, 4, 3, 1, 0),
AD1848_DOUBLE("Line Playback Volume", 0, CMI8330_LINVOL, CMI8330_LINVOL, 4, 0, 15, 0),
AD1848_DOUBLE("Line Capture Switch", 0, CMI8330_RMUX3D, CMI8330_RMUX3D, 2, 1, 1, 0),
AD1848_DOUBLE("Line Capture Volume", 0, CMI8330_LINGAIN, CMI8330_LINGAIN, 4, 0, 15, 0),
AD1848_DOUBLE("CD Playback Switch", 0, CMI8330_MUTEMUX, CMI8330_MUTEMUX, 2, 1, 1, 0),
AD1848_DOUBLE("CD Capture Switch", 0, CMI8330_RMUX3D, CMI8330_RMUX3D, 4, 3, 1, 0),
AD1848_DOUBLE("CD Playback Volume", 0, CMI8330_CDINVOL, CMI8330_CDINVOL, 4, 0, 15, 0),
AD1848_DOUBLE("CD Capture Switch", 0, CMI8330_CDINGAIN, CMI8330_CDINGAIN, 4, 0, 15, 0),
AD1848_SINGLE("Mic Playback Switch", 0, CMI8330_MUTEMUX, 0, 1, 0),
AD1848_SINGLE("Mic Playback Volume", 0, CMI8330_OUTPUTVOL, 0, 7, 0),
AD1848_SINGLE("Mic Capture Switch", 0, CMI8330_RMUX3D, 0, 1, 0),
AD1848_SINGLE("Mic Capture Volume", 0, CMI8330_OUTPUTVOL, 5, 7, 0),
AD1848_DOUBLE("Wavetable Playback Switch", 0, CMI8330_RECMUX, CMI8330_RECMUX, 1, 0, 1, 0),
AD1848_DOUBLE("Wavetable Playback Volume", 0, CMI8330_WAVVOL, CMI8330_WAVVOL, 4, 0, 15, 0),
AD1848_DOUBLE("Wavetable Capture Switch", 0, CMI8330_RECMUX, CMI8330_RECMUX, 5, 4, 1, 0),
AD1848_DOUBLE("Wavetable Capture Volume", 0, CMI8330_WAVGAIN, CMI8330_WAVGAIN, 4, 0, 15, 0),
AD1848_SINGLE("3D Control - Switch", 0, CMI8330_RMUX3D, 5, 1, 1),
AD1848_SINGLE("PC Speaker Playback Volume", 0, CMI8330_OUTPUTVOL, 3, 3, 0),
AD1848_SINGLE("FM Playback Switch", 0, CMI8330_RECMUX, 3, 1, 1),
AD1848_SINGLE("IEC958 Input Capture Switch", 0, CMI8330_RMUX3D, 7, 1, 1),
AD1848_SINGLE("IEC958 Input Playback Switch", 0, CMI8330_MUTEMUX, 7, 1, 1),
};

static int __init snd_cmi8330_mixer(snd_card_t *card, ad1848_t *chip)
{
	int idx, err;

	strcpy(card->mixername, "CMI8330/C3D");

	for (idx = 0; idx < CMI8330_CONTROLS; idx++)
		if ((err = snd_ctl_add(card, snd_ctl_new1(&snd_cmi8330_controls[idx], chip))) < 0)
			return err;

	return 0;
}

#ifdef __ISAPNP__
static int __init snd_cmi8330_isapnp(int dev, struct snd_cmi8330 *acard)
{
	const struct isapnp_card_id *id = snd_cmi8330_isapnp_id[dev];
	struct isapnp_card *card = snd_cmi8330_isapnp_cards[dev];
	struct isapnp_dev *pdev;

	acard->cap = isapnp_find_dev(card, id->devs[0].vendor, id->devs[0].function, NULL);
	if (acard->cap->active) {
		acard->cap = NULL;
		return -EBUSY;
	}
	acard->play = isapnp_find_dev(card, id->devs[1].vendor, id->devs[1].function, NULL);
	if (acard->play->active) {
		acard->cap = acard->play = NULL;
		return -EBUSY;
	}

	pdev = acard->cap;
	if (pdev->prepare(pdev)<0)
		return -EAGAIN;
	/* allocate AD1848 resources */
	if (wssport[dev] != SNDRV_AUTO_PORT)
		isapnp_resource_change(&pdev->resource[0], wssport[dev], 8);
	if (wssdma[dev] != SNDRV_AUTO_DMA)
		isapnp_resource_change(&pdev->dma_resource[0], wssdma[dev], 1);
	if (wssirq[dev] != SNDRV_AUTO_IRQ)
		isapnp_resource_change(&pdev->irq_resource[0], wssirq[dev], 1);

	if (pdev->activate(pdev)<0) {
		snd_printk("(AD1848) PnP configure failure\n");
		return -EBUSY;
	}
	wssport[dev] = pdev->resource[0].start;
	wssdma[dev] = pdev->dma_resource[0].start;
	wssirq[dev] = pdev->irq_resource[0].start;

	/* allocate SB16 resources */
	pdev = acard->play;
	if (pdev->prepare(pdev)<0) {
		acard->cap->deactivate(acard->cap);
		return -EAGAIN;
	}
	if (sbport[dev] != SNDRV_AUTO_PORT)
		isapnp_resource_change(&pdev->resource[0], sbport[dev], 16);
	if (sbdma8[dev] != SNDRV_AUTO_DMA)
		isapnp_resource_change(&pdev->dma_resource[0], sbdma8[dev], 1);
	if (sbdma16[dev] != SNDRV_AUTO_DMA)
		isapnp_resource_change(&pdev->dma_resource[1], sbdma16[dev], 1);
	if (sbirq[dev] != SNDRV_AUTO_IRQ)
		isapnp_resource_change(&pdev->irq_resource[0], sbirq[dev], 1);

	if (pdev->activate(pdev)<0) {
		snd_printk("CMI8330/C3D (SB16) PnP configure failure\n");
		acard->cap->deactivate(acard->cap);
		return -EBUSY;
	}
	sbport[dev] = pdev->resource[0].start;
	sbdma8[dev] = pdev->dma_resource[0].start;
	sbdma16[dev] = pdev->dma_resource[1].start;
	sbirq[dev] = pdev->irq_resource[0].start;

	return 0;
}

static void snd_cmi8330_deactivate(struct snd_cmi8330 *acard)
{
	if (acard->cap) {
		acard->cap->deactivate(acard->cap);
		acard->cap = NULL;
	}
	if (acard->play) {
		acard->play->deactivate(acard->play);
		acard->play = NULL;
	}
}
#endif

static void snd_cmi8330_free(snd_card_t *card)
{
	struct snd_cmi8330 *acard = (struct snd_cmi8330 *)card->private_data;

	if (acard) {
#ifdef __ISAPNP__
		snd_cmi8330_deactivate(acard);
#endif
	}
}

static int __init snd_cmi8330_probe(int dev)
{
	snd_card_t *card;
	struct snd_cmi8330 *acard;
	ad1848_t *chip_wss;
	sb_t *chip_sb;
	unsigned long flags;
	int i, err;
	snd_pcm_t *pcm, *wss_pcm, *sb_pcm;
	snd_pcm_str_t *pstr;

#ifdef __ISAPNP__
	if (!isapnp[dev]) {
#endif
		if (wssport[dev] == SNDRV_AUTO_PORT) {
			snd_printk("specify wssport\n");
			return -EINVAL;
		}
		if (sbport[dev] == SNDRV_AUTO_PORT) {
			snd_printk("specify sbport\n");
			return -EINVAL;
		}
#ifdef __ISAPNP__
	}
#endif
	card = snd_card_new(index[dev], id[dev], THIS_MODULE,
			    sizeof(struct snd_cmi8330));
	if (card == NULL) {
		snd_printk("could not get a new card\n");
		return -ENOMEM;
	}
	acard = (struct snd_cmi8330 *)card->private_data;
	card->private_free = snd_cmi8330_free;

#ifdef __ISAPNP__
	if (isapnp[dev] && (err = snd_cmi8330_isapnp(dev, acard)) < 0) {
		snd_printk("PnP detection failed\n");
		snd_card_free(card);
		return err;
	}
#endif

	if ((err = snd_ad1848_create(card,
				     wssport[dev] + 4,
				     wssirq[dev],
				     wssdma[dev],
				     AD1848_HW_DETECT,
				     &chip_wss)) < 0) {
		snd_printk("(AD1848) device busy??\n");
		snd_card_free(card);
		return err;
	}
	if (chip_wss->hardware != AD1848_HW_CMI8330) {
		snd_printk("(AD1848) not found during probe\n");
		snd_card_free(card);
		return -ENODEV;
	}
	if ((err = snd_ad1848_pcm(chip_wss, 0, &wss_pcm)) < 0) {
		snd_printk("(AD1848) no enough memory??\n");
		snd_card_free(card);
		return err;
	}

	if ((err = snd_sbdsp_create(card, sbport[dev],
				    sbirq[dev],
				    snd_sb16dsp_interrupt,
				    sbdma8[dev],
				    sbdma16[dev],
				    SB_HW_AUTO, &chip_sb)) < 0) {
		snd_printk("(SB16) device busy??\n");
		snd_card_free(card);
		return err;
	}
	if ((err = snd_sb16dsp_pcm(chip_sb, 1, &sb_pcm)) < 0) {
		snd_printk("(SB16) no enough memory??\n");
		snd_card_free(card);
		return err;
	}

	if (chip_sb->hardware != SB_HW_16) {
		snd_printk("(SB16) not found during probe\n");
		snd_card_free(card);
		return -ENODEV;
	}

	memcpy(&chip_wss->image[16], &snd_cmi8330_image, sizeof(snd_cmi8330_image));

	spin_lock_irqsave(&chip_wss->reg_lock, flags);
	snd_ad1848_out(chip_wss, AD1848_MISC_INFO,	/* switch on MODE2 */
		       chip_wss->image[AD1848_MISC_INFO] |= 0x40);
	spin_unlock_irqrestore(&chip_wss->reg_lock, flags);

	if ((err = snd_cmi8330_mixer(card, chip_wss)) < 0) {
		snd_printk("failed to create mixers\n");
		snd_card_free(card);
		return err;
	}
	spin_lock_irqsave(&chip_wss->reg_lock, flags);
	for (i = CMI8330_RMUX3D; i <= CMI8330_CDINGAIN; i++)
		snd_ad1848_out(chip_wss, i, chip_wss->image[i]);
	spin_unlock_irqrestore(&chip_wss->reg_lock, flags);

	/*
	 * KLUDGE ALERT
	 *  disable AD1848 playback
	 *  disable SB16 capture
	 */
	pcm = wss_pcm;
	pstr = &pcm->streams[SNDRV_PCM_STREAM_PLAYBACK];
	snd_magic_kfree(pstr->substream);
	pstr->substream = 0;
	pstr->substream_count = 0;

	pcm = sb_pcm;
	pstr = &pcm->streams[SNDRV_PCM_STREAM_CAPTURE];
	snd_magic_kfree(pstr->substream);
	pstr->substream = 0;
	pstr->substream_count = 0;

	strcpy(card->driver, "CMI8330/C3D");
	strcpy(card->shortname, "C-Media CMI8330/C3D");
	sprintf(card->longname, "%s at 0x%lx, irq %d, dma %d",
		wss_pcm->name,
		chip_wss->port,
		wssirq[dev],
		wssdma[dev]);

	if ((err = snd_card_register(card)) < 0) {
		snd_card_free(card);
		return err;
	}

	snd_cmi8330_cards[dev] = card;
	return 0;
}

static void __exit alsa_card_cmi8330_exit(void)
{
	int i;

	for (i = 0; i < SNDRV_CARDS; i++)
		snd_card_free(snd_cmi8330_cards[i]);
}

#ifdef __ISAPNP__
static int __init snd_cmi8330_isapnp_detect(struct isapnp_card *card,
                                            const struct isapnp_card_id *id)
{
	static int dev;
	int res;

	for ( ; dev < SNDRV_CARDS; dev++) {
		if (!enable[dev] || !isapnp[dev])
			continue;
		snd_cmi8330_isapnp_cards[dev] = card;
		snd_cmi8330_isapnp_id[dev] = id;
		res = snd_cmi8330_probe(dev);
		if (res < 0)
			return res;
		dev++;
		return 0;
	}
	return -ENODEV;
}
#endif /* __ISAPNP__ */

static int __init alsa_card_cmi8330_init(void)
{
	int dev, cards = 0;

	for (dev = 0; dev < SNDRV_CARDS; dev++) {
		if (!enable[dev])
			continue;
#ifdef __ISAPNP__
		if (isapnp[dev])
			continue;
#endif
		if (snd_cmi8330_probe(dev) >= 0)
			cards++;
	}
#ifdef __ISAPNP__
	cards += isapnp_probe_cards(snd_cmi8330_pnpids, snd_cmi8330_isapnp_detect);
#endif

	if (!cards) {
#ifdef MODULE
		printk(KERN_ERR "CMI8330 not found or device busy\n");
#endif
		return -ENODEV;
	}
	return 0;
}

module_init(alsa_card_cmi8330_init)
module_exit(alsa_card_cmi8330_exit)

#ifndef MODULE

/* format is: snd-cmi8330=enable,index,id,isapnp,
			  sbport,sbirq,
			  sbdma8,sbdma16,
			  wssport,wssirq,
			  wssdma */

static int __init alsa_card_cmi8330_setup(char *str)
{
	static unsigned __initdata nr_dev = 0;
	int __attribute__ ((__unused__)) pnp = INT_MAX;

	if (nr_dev >= SNDRV_CARDS)
		return 0;
	(void)(get_option(&str,&enable[nr_dev]) == 2 &&
	       get_option(&str,&index[nr_dev]) == 2 &&
	       get_id(&str,&id[nr_dev]) == 2 &&
	       get_option(&str,&pnp) == 2 &&
	       get_option(&str,(int *)&sbport[nr_dev]) == 2 &&
	       get_option(&str,&sbirq[nr_dev]) == 2 &&
	       get_option(&str,&sbdma8[nr_dev]) == 2 &&
	       get_option(&str,&sbdma16[nr_dev]) == 2 &&
	       get_option(&str,(int *)&wssport[nr_dev]) == 2 &&
	       get_option(&str,&wssirq[nr_dev]) == 2 &&
	       get_option(&str,&wssdma[nr_dev]) == 2);
#ifdef __ISAPNP__
	if (pnp != INT_MAX)
		isapnp[nr_dev] = pnp;
#endif
	nr_dev++;
	return 1;
}

__setup("snd-cmi8330=", alsa_card_cmi8330_setup);

#endif /* ifndef MODULE */