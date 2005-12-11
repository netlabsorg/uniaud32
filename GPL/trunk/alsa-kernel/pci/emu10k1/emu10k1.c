/*
 *  The driver for the EMU10K1 (SB Live!) based soundcards
 *  Copyright (c) by Jaroslav Kysela <perex@suse.cz>
 *
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

#include <sound/driver.h>
#include <linux/init.h>
#include <linux/time.h>
#include <sound/core.h>
#include <sound/emu10k1.h>
#define SNDRV_GET_ID
#include <sound/initval.h>

MODULE_AUTHOR("Jaroslav Kysela <perex@suse.cz>");
MODULE_DESCRIPTION("EMU10K1");
MODULE_LICENSE("GPL");
MODULE_CLASSES("{sound}");
MODULE_DEVICES("{{Creative Labs,SB Live!/PCI512/E-mu APS},"
	       "{Creative Labs,SB Audigy}}");

#if defined(CONFIG_SND_SEQUENCER) || (defined(MODULE) && defined(CONFIG_SND_SEQUENCER_MODULE))
#define ENABLE_SYNTH
#include <sound/emu10k1_synth.h>
#endif

static int index[SNDRV_CARDS] = SNDRV_DEFAULT_IDX;	/* Index 0-MAX */
static char *id[SNDRV_CARDS] = SNDRV_DEFAULT_STR;	/* ID for this card */
static int enable[SNDRV_CARDS] = SNDRV_DEFAULT_ENABLE_PNP;	/* Enable this card */

#ifdef TARGET_OS2
static int extin[SNDRV_CARDS] = {0,0,0,0,0,0,0,0};
static int extout[SNDRV_CARDS] = {0,0,0,0,0,0,0,0};
static int seq_ports[SNDRV_CARDS] = {4,4,4,4,4,4,4,4};
static int max_synth_voices[SNDRV_CARDS] = {64,64,64,64,64,64,64,64};
static int max_buffer_size[SNDRV_CARDS] = {128,128,128,128,128,128,128,128};
static int enable_ir[SNDRV_CARDS] = {0,0,0,0,0,0,0,0};
static uint subsystem[SNDRV_CARDS] = {0,0,0,0,0,0,0,0}; /* Force card subsystem model */
#else
static int extin[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 0};
static int extout[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 0};
static int seq_ports[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 4};
static int max_synth_voices[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 64};
static int max_buffer_size[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 128};
static int enable_ir[SNDRV_CARDS] = {[0 ... (SNDRV_CARDS - 1)] = 0};
#endif

MODULE_PARM(index, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(index, "Index value for the EMU10K1 soundcard.");
MODULE_PARM_SYNTAX(index, SNDRV_INDEX_DESC);
MODULE_PARM(id, "1-" __MODULE_STRING(SNDRV_CARDS) "s");
MODULE_PARM_DESC(id, "ID string for the EMU10K1 soundcard.");
MODULE_PARM_SYNTAX(id, SNDRV_ID_DESC);
MODULE_PARM(enable, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(enable, "Enable the EMU10K1 soundcard.");
MODULE_PARM_SYNTAX(enable, SNDRV_ENABLE_DESC);
MODULE_PARM(extin, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(extin, "Available external inputs for FX8010. Zero=default.");
MODULE_PARM_SYNTAX(extin, SNDRV_ENABLED "allows:{{0,0x0ffff}},base:16");
MODULE_PARM(extout, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(extout, "Available external outputs for FX8010. Zero=default.");
MODULE_PARM_SYNTAX(extout, SNDRV_ENABLED "allows:{{0,0x0ffff}},base:16");
MODULE_PARM(seq_ports, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(seq_ports, "Allocated sequencer ports for internal synthesizer.");
MODULE_PARM_SYNTAX(seq_ports, SNDRV_ENABLED "allows:{{0,32}}");
MODULE_PARM(max_synth_voices, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(max_synth_voices, "Maximum number of voices for WaveTable.");
MODULE_PARM_SYNTAX(max_synth_voices, SNDRV_ENABLED);
MODULE_PARM(max_buffer_size, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(max_buffer_size, "Maximum sample buffer size in MB.");
MODULE_PARM_SYNTAX(max_buffer_size, SNDRV_ENABLED);
MODULE_PARM(enable_ir, "1-" __MODULE_STRING(SNDRV_CARDS) "i");
MODULE_PARM_DESC(enable_ir, "Enable IR.");
MODULE_PARM_SYNTAX(enable_ir, SNDRV_ENABLE_DESC);
//module_param_array(subsystem, uint, NULL, 0444);
MODULE_PARM_DESC(subsystem, "Force card subsystem model.");
/*
 * Class 0401: 1102:0008 (rev 00) Subsystem: 1102:1001 -> Audigy2 Value  Model:SB0400
 */

static struct pci_device_id snd_emu10k1_ids[] = {
    { 0x1102, 0x0002, PCI_ANY_ID, PCI_ANY_ID, 0, 0, 0 },	/* EMU10K1 */
    { 0x1102, 0x0004, PCI_ANY_ID, PCI_ANY_ID, 0, 0, 1 },	/* Audigy */
    { 0x1102, 0x0008, PCI_ANY_ID, PCI_ANY_ID, 0, 0, 1 },    /* Audigy 2 Value SB0400 */
    { 0, }
};
/*
 * Audigy 2 Value notes:
 * A_IOCFG Input (GPIO)
 * 0x400  = Front analog jack plugged in. (Green socket)
 * 0x1000 = Read analog jack plugged in. (Black socket)
 * 0x2000 = Center/LFE analog jack plugged in. (Orange socket)
 * A_IOCFG Output (GPIO)
 * 0x60 = Sound out of front Left.
 * Win sets it to 0xXX61
 */

MODULE_DEVICE_TABLE(pci, snd_emu10k1_ids);

static int __devinit snd_card_emu10k1_probe(struct pci_dev *pci,
					    const struct pci_device_id *pci_id)
{
#ifdef TARGET_OS2
	static int dev = 0;
#else
	static int dev;
#endif
	snd_card_t *card;
	struct snd_emu10k1 *emu;
#ifdef ENABLE_SYNTH
	snd_seq_device_t *wave = NULL;
#endif
	int err;

	if (dev >= SNDRV_CARDS)
        	return -ENODEV;
	if (!enable[dev]) {
		dev++;
		return -ENOENT;
	}

	card = snd_card_new(index[dev], id[dev], THIS_MODULE, 0);
	if (card == NULL)
		return -ENOMEM;
	if (max_buffer_size[dev] < 32)
		max_buffer_size[dev] = 32;
	else if (max_buffer_size[dev] > 1024)
		max_buffer_size[dev] = 1024;
	if ((err = snd_emu10k1_create(card, pci, extin[dev], extout[dev],
                                      (long)max_buffer_size[dev] * 1024 * 1024,
                                      enable_ir[dev], subsystem[dev],
				      &emu)) < 0) {
		snd_card_free(card);
		return err;
	}
	if ((err = snd_emu10k1_pcm(emu, 0, NULL)) < 0) {
		snd_card_free(card);
		return err;
	}
	if ((err = snd_emu10k1_pcm_mic(emu, 1, NULL)) < 0) {
		snd_card_free(card);
		return err;
	}
	if ((err = snd_emu10k1_pcm_efx(emu, 2, NULL)) < 0) {
		snd_card_free(card);
		return err;
        }
        /* This stores the periods table. */
        if (emu->card_capabilities->ca0151_chip) { /* P16V */
            if(snd_dma_alloc_pages(SNDRV_DMA_TYPE_DEV, snd_dma_pci_data(pci), 1024, &emu->p16v_buffer) < 0) {
                snd_p16v_free(emu);
                return -ENOMEM;
            }
        }
        if ((err = snd_emu10k1_mixer(emu, 0, 3)) < 0) {
            snd_card_free(card);
            return err;
        }

        if ((err = snd_emu10k1_timer(emu, 0)) < 0) {
            snd_card_free(card);
            return err;
        }

        if ((err = snd_emu10k1_pcm_multi(emu, 3, NULL)) < 0) {
            snd_card_free(card);
            return err;
        }

        if (emu->card_capabilities->ca0151_chip) { /* P16V */
            if ((err = snd_p16v_pcm(emu, 4, NULL)) < 0) {
                snd_card_free(card);
                return err;
            }
        }
#ifdef TARGET_OS2
	if (emu->audigy) {
		if ((err = snd_emu10k1_audigy_midi(emu)) < 0) {
			snd_card_free(card);
			return err;
		}
	} else {
		if ((err = snd_emu10k1_midi(emu)) < 0) {
			snd_card_free(card);
			return err;
		}
	}
#endif
	if ((err = snd_emu10k1_fx8010_new(emu, 0, NULL)) < 0) {
		snd_card_free(card);
		return err;
	}
#ifdef ENABLE_SYNTH
	if (snd_seq_device_new(card, 1, SNDRV_SEQ_DEV_ID_EMU10K1_SYNTH,
			       sizeof(struct snd_emu10k1_synth_arg), &wave) < 0 ||
	    wave == NULL) {
		snd_printk("can't initialize Emu10k1 wavetable synth\n");
	} else {
		struct snd_emu10k1_synth_arg *arg;
		arg = SNDRV_SEQ_DEVICE_ARGPTR(wave);
		strcpy(wave->name, "Emu-10k1 Synth");
		arg->hwptr = emu;
		arg->index = 1;
		arg->seq_ports = seq_ports[dev];
		arg->max_voices = max_synth_voices[dev];
	}
#endif

        strcpy(card->driver, emu->card_capabilities->driver);
        strcpy(card->shortname, emu->card_capabilities->name);
        sprintf(card->longname, "%s (rev.%d) at 0x%lx, irq %i", card->shortname, emu->revision, emu->port, emu->irq);

//        DebugInt3();

	if ((err = snd_card_register(card)) < 0) {
		snd_card_free(card);
		return err;
	}
	pci_set_drvdata(pci, card);
	dev++;
	return 0;
}

static void __devexit snd_card_emu10k1_remove(struct pci_dev *pci)
{
	snd_card_free(pci_get_drvdata(pci));
	pci_set_drvdata(pci, NULL);
}

#ifdef TARGET_OS2
static struct pci_driver driver = {
        0, 0, 0,
/*	name:    */ "EMU10K1/Audigy",
/*	id_table:*/ snd_emu10k1_ids,
/*	probe:   */ snd_card_emu10k1_probe,
/*	remove:  */ snd_card_emu10k1_remove,
        0, 0
};
#else
static struct pci_driver driver = {
	name: "EMU10K1/Audigy",
	id_table: snd_emu10k1_ids,
	probe: snd_card_emu10k1_probe,
	remove: __devexit_p(snd_card_emu10k1_remove),
};
#endif

static int __init alsa_card_emu10k1_init(void)
{
	int err;

	if ((err = pci_module_init(&driver)) < 0) {
#ifdef MODULE
//		printk(KERN_ERR "EMU10K1/Audigy soundcard not found or device busy\n");
#endif
		return err;
	}
	return 0;
}

static void __exit alsa_card_emu10k1_exit(void)
{
	pci_unregister_driver(&driver);
}

module_init(alsa_card_emu10k1_init)
module_exit(alsa_card_emu10k1_exit)

#ifndef MODULE

/* format is: snd-emu10k1=enable,index,id,
			  seq_ports,max_synth_voices */

static int __init alsa_card_emu10k1_setup(char *str)
{
	static unsigned __initdata nr_dev = 0;

	if (nr_dev >= SNDRV_CARDS)
		return 0;
	(void)(get_option(&str,&enable[nr_dev]) == 2 &&
	       get_option(&str,&index[nr_dev]) == 2 &&
	       get_id(&str,&id[nr_dev]) == 2 &&
	       get_option(&str,&seq_ports[nr_dev]) == 2 &&
	       get_option(&str,&max_synth_voices[nr_dev]) == 2);
	nr_dev++;
	return 1;
}

__setup("snd-emu10k1=", alsa_card_emu10k1_setup);

#endif /* ifndef MODULE */
