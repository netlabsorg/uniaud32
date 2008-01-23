/***************************************************************************
 *            au88x0_eq.c
 *  Aureal Vortex Hardware EQ control/access.
 *
 *  Sun Jun  8 18:19:19 2003
 *  2003  Manuel Jander (mjander@users.sourceforge.net)
 *  
 *  02 July 2003: First time something works :)
 *  
 *  TODO:
 *     - Debug (testing)
 *     - Implement peak visualization support.
 *
 ****************************************************************************/
#include "au88x0.h"
#include "au88x0_eq.h"
#include "au88x0_eqdata.c"

/* CEqHw.s */
void vortex_EqHw_SetTimeConsts(vortex_t *vortex, u16 a, u16 b) {
	hwwrite(vortex->mmio, 0x2b3c4, a);
	hwwrite(vortex->mmio, 0x2b3c8, b);
}

void vortex_EqHw_GetTimeConsts(vortex_t *vortex, u16 *a, u16 *b) {
	*a = hwread(vortex->mmio, 0x2b3c4);
	*b = hwread(vortex->mmio, 0x2b3c8);
}

void vortex_EqHw_SetLeftCoefs(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int eax, i = 0, n /*esp2c*/ = 0;
	
	if (eqhw->this04 <= n)
		return;
		
	do {
		hwwrite(vortex->mmio, 0x2b000 + n*0x30, a[i+0]);
		hwwrite(vortex->mmio, 0x2b004 + n*0x30, a[i+1]);
		
		if (eqhw->this08 == 0) {
			hwwrite(vortex->mmio, 0x2b008 + n*0x30, a[i+2]);
			hwwrite(vortex->mmio, 0x2b00c + n*0x30, a[i+3]);
			eax = a[i+4]; //esp24;
		} else {
			if (a[2+i] == 0x8000)
				eax = 0x7fff;
			else
				eax = ~a[2+i];
			hwwrite(vortex->mmio, 0x2b008 + n*0x30, eax & 0xffff);
			if (a[3+i] == 0x8000)
				eax = 0x7fff;
			else
				eax = ~a[3+i];
			hwwrite(vortex->mmio, 0x2b00c + n*0x30, eax & 0xffff);
			if (a[4+i] == 0x8000)
				eax = 0x7fff;
			else
				eax = ~a[4+i];
		}
		hwwrite(vortex->mmio, 0x2b010 + n*0x30, eax);
		
		n++;
		i += 5;
	} while(n < eqhw->this04);	
}

void vortex_EqHw_GetLeftCoefs(vortex_t *vortex, u16 a[]) {
	
	
}

void vortex_EqHw_SetRightCoefs(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int i = 0, n /*esp2c*/ = 0, eax;
	
	if (eqhw->this04 <= n)
		return;
	
	do {
		hwwrite(vortex->mmio, 0x2b1e0 + n*0x30, a[0+i]);
		hwwrite(vortex->mmio, 0x2b1e4 + n*0x30, a[1+i]);
		
		if (eqhw->this08 == 0) {
			hwwrite(vortex->mmio, 0x2b1e8 + n*0x30, a[2+i]);
			hwwrite(vortex->mmio, 0x2b1ec + n*0x30, a[3+i]);
			eax = a[4+i]; //*esp24;
		} else {
			if (a[2+i] == 0x8000)
				eax = 0x7fff;
			else
				eax = ~(a[2+i]);
			hwwrite(vortex->mmio, 0x2b1e8 + n*0x30, eax & 0xffff);
			if (a[3+i] == 0x8000)
				eax = 0x7fff;
			else
				eax = ~a[3+i];
			hwwrite(vortex->mmio, 0x2b1ec + n*0x30, eax & 0xffff);
			if (a[4+i] == 0x8000)
				eax = 0x7fff;
			else
				eax = ~a[4+i];
		}
		hwwrite(vortex->mmio, 0x2b1f0 + n*0x30, eax);
		i += 5;
		n++;	
	} while (n < eqhw->this04);
	
}

void vortex_EqHw_GetRightCoefs(vortex_t *vortex, u16 a[]) {
	
	
}

void vortex_EqHw_SetLeftStates(vortex_t *vortex, u16 a[], u16 b[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int i = 0, ebx = 0;
	
	hwwrite(vortex->mmio, 0x2b3fc, a[0]);
	hwwrite(vortex->mmio, 0x2b400, a[1]);
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		hwwrite(vortex->mmio, 0x2b014 + (i*0xc), b[i]);
		hwwrite(vortex->mmio, 0x2b018 + (i*0xc), b[1+i]);
		hwwrite(vortex->mmio, 0x2b01c + (i*0xc), b[2+i]);
		hwwrite(vortex->mmio, 0x2b020 + (i*0xc), b[3+i]);
		i += 4;
		ebx++;
	} while (eqhw->this04 > ebx);
}

void vortex_EqHw_GetLeftStates(vortex_t *vortex, u16 *a, u16 b[]) {

	
}

void vortex_EqHw_SetRightStates(vortex_t *vortex, u16 a[], u16 b[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int i = 0, ebx = 0;
	
	hwwrite(vortex->mmio, 0x2b404, a[0]);
	hwwrite(vortex->mmio, 0x2b408, a[1]);
	
	if (eqhw->this04 < 0)
		return;
		
	do {
		hwwrite(vortex->mmio, 0x2b1f4 + (i*0xc), b[i]);
		hwwrite(vortex->mmio, 0x2b1f8 + (i*0xc), b[1+i]);
		hwwrite(vortex->mmio, 0x2b1fc + (i*0xc), b[2+i]);
		hwwrite(vortex->mmio, 0x2b200 + (i*0xc), b[3+i]);		
		i += 4;
		ebx++;
	} while (ebx < eqhw->this04);
}

void vortex_EqHw_GetRightStates(vortex_t *vortex, u16 *a, u16 b[]) {
	
}

void vortex_EqHw_SetBypassGain(vortex_t *vortex, u16 a, u16 b) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int eax;
	
	if (eqhw->this08 == 0) {
		hwwrite(vortex->mmio, 0x2b3d4, a);
		hwwrite(vortex->mmio, 0x2b3ec, b);
	} else {
		if (a == 0x8000)
			eax = 0x7fff;
		else
			eax = ~a;
		hwwrite(vortex->mmio, 0x2b3d4, eax & 0xffff);
		if (b == 0x8000)
			eax = 0x7fff;
		else
			eax = ~b;
		hwwrite(vortex->mmio, 0x2b3ec, eax & 0xffff);
	}
}

void vortex_EqHw_SetA3DBypassGain(vortex_t *vortex, u16 a, u16 b) {
	
	hwwrite(vortex->mmio, 0x2b3e0, a);
	hwwrite(vortex->mmio, 0x2b3f8, b);
}

void vortex_EqHw_SetCurrBypassGain(vortex_t *vortex, u16 a, u16 b) {
	
	hwwrite(vortex->mmio, 0x2b3d0, a);
	hwwrite(vortex->mmio, 0x2b3e8, b);
}

void vortex_EqHw_SetCurrA3DBypassGain(vortex_t *vortex, u16 a, u16 b) {
	
	hwwrite(vortex->mmio, 0x2b3dc, a);
	hwwrite(vortex->mmio, 0x2b3f4, b);
}

void vortex_EqHw_SetLeftGainsSingleTarget(vortex_t *vortex, u16 index, u16 b) {
	hwwrite(vortex->mmio, 0x2b02c + (index*0x30), b);
}

void vortex_EqHw_SetRightGainsSingleTarget(vortex_t *vortex, u16 index, u16 b) {
	hwwrite(vortex->mmio, 0x2b20c + (index*0x30), b);
}

void vortex_EqHw_SetLeftGainsTarget(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	do {
		hwwrite(vortex->mmio, 0x2b02c + ebx*0x30, a[ebx]);
		ebx++;
	} while (ebx < eqhw->this04);
}

void vortex_EqHw_SetRightGainsTarget(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		hwwrite(vortex->mmio, 0x2b20c + ebx*0x30, a[ebx]);
		ebx++;
	} while (ebx < eqhw->this04);	
}

void vortex_EqHw_GetLeftGainsTarget(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		a[ebx] = hwread(vortex->mmio, 0x2b02c + ebx*0x30);
		ebx++;
	} while (ebx < eqhw->this04);
}

void vortex_EqHw_GetRightGainsTarget(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		a[ebx] = hwread(vortex->mmio, 0x2b20c + ebx*0x30);
		ebx++;
	} while (ebx < eqhw->this04);	
}

void vortex_EqHw_SetLeftGainsCurrent(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		hwwrite(vortex->mmio, 0x2b028 + ebx*0x30, a[ebx]);
		ebx++;
	} while (ebx < eqhw->this04);
}

void vortex_EqHw_SetRightGainsCurrent(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		hwwrite(vortex->mmio, 0x2b208 + ebx*0x30, a[ebx]);
		ebx++;
	} while (ebx < eqhw->this04);	
}

void vortex_EqHw_GetLeftGainsCurrent(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		a[ebx] = hwread(vortex->mmio, 0x2b028 + ebx*0x30);
		ebx++;
	} while (ebx < eqhw->this04);
}

void vortex_EqHw_GetRightGainsCurrent(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx=0;
	
	if (eqhw->this04 < 0)
		return;
	
	do {
		a[ebx] = hwread(vortex->mmio, 0x2b208 + ebx*0x30);
		ebx++;
	} while (ebx < eqhw->this04);	
}

void vortex_EqHw_SetLevels(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx;
	
	if (eqhw->this04 < 0)
		return;
	
	ebx = 0;
	do {
		hwwrite(vortex->mmio, 0x2b024 + ebx*0x30, a[ebx]);
		ebx++;
	} while (ebx < eqhw->this04);
	
	hwwrite(vortex->mmio, 0x2b3cc, a[eqhw->this04]);
	hwwrite(vortex->mmio, 0x2b3d8, a[eqhw->this04+1]);
	
	ebx = 0;
	do {
		hwwrite(vortex->mmio, 0x2b204 + ebx*0x30, a[ebx + (eqhw->this04+2)]);
		ebx++;
	} while (ebx < eqhw->this04);
	
	hwwrite(vortex->mmio, 0x2b3e4, a[2+(eqhw->this04*2)]);
	hwwrite(vortex->mmio, 0x2b3f0, a[3+(eqhw->this04*2)]);
}

void vortex_EqHw_GetLevels(vortex_t *vortex, u16 a[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int ebx;
	
	if (eqhw->this04 < 0)
		return;
	
	ebx = 0;
	do {
		a[ebx] = hwread(vortex->mmio, 0x2b024 + ebx*0x30);
		ebx++;
	} while (ebx < eqhw->this04);
	
	a[eqhw->this04] = hwread(vortex->mmio, 0x2b3cc);
	a[eqhw->this04+1] = hwread(vortex->mmio, 0x2b3d8);
	
	ebx = 0;
	do {
		a[ebx+(eqhw->this04+2)] = hwread(vortex->mmio, 0x2b204 + ebx*0x30);
		ebx++;
	} while (ebx < eqhw->this04);
	
	a[2+(eqhw->this04*2)] = hwread(vortex->mmio, 0x2b3e4);
	a[3+(eqhw->this04*2)] = hwread(vortex->mmio, 0x2b3f0);
}

void vortex_EqHw_SetControlReg(vortex_t *vortex, unsigned long reg) {
	hwwrite(vortex->mmio, 0x2b440, reg);
}

void vortex_EqHw_GetControlReg(vortex_t *vortex, unsigned long *reg) {
	*reg = hwread(vortex->mmio, 0x2b440);
}

void vortex_EqHw_SetSampleRate(vortex_t *vortex, int sr) {
	hwwrite(vortex->mmio, 0x2b440, ((sr & 0x1f) << 3) | 0xb800);
}

void vortex_EqHw_GetSampleRate(vortex_t *vortex, int *sr) {
	*sr = (hwread(vortex->mmio, 0x2b440) >> 3) & 0x1f;
}

void vortex_EqHw_Enable(vortex_t *vortex) {
	hwwrite(vortex->mmio, 0x2b440, 0xf001);
}

void vortex_EqHw_Disable(vortex_t *vortex) {
	hwwrite(vortex->mmio, 0x2b440, 0xf000);
}

/* Reset (zero) buffers */
void vortex_EqHw_ZeroIO(vortex_t *vortex) {
	int i;
	for (i=0; i<0x8; i++)
		hwwrite(vortex->mmio, 0x2b410 + (i<<2), 0x0);
	for (i=0; i<0x4; i++)
		hwwrite(vortex->mmio, 0x2b430 + (i<<2), 0x0);
}

void vortex_EqHw_ZeroA3DIO(vortex_t *vortex) {
	int i;
	for (i=0; i<0x4; i++)
		hwwrite(vortex->mmio, 0x2b410 + (i<<2), 0x0);	
}

void vortex_EqHw_ZeroState(vortex_t *vortex) {
	
	vortex_EqHw_SetControlReg(vortex, 0);
	vortex_EqHw_ZeroIO(vortex);
	hwwrite(vortex->mmio, 0x2b3c0, 0);
	
	vortex_EqHw_SetTimeConsts(vortex, 0, 0);
	
	vortex_EqHw_SetLeftCoefs(vortex, asEqCoefsZeros);
	vortex_EqHw_SetRightCoefs(vortex, asEqCoefsZeros);
	
	vortex_EqHw_SetLeftGainsCurrent(vortex, eq_gains_zero);
	vortex_EqHw_SetRightGainsCurrent(vortex, eq_gains_zero);
	vortex_EqHw_SetLeftGainsTarget(vortex, eq_gains_zero);
	vortex_EqHw_SetRightGainsTarget(vortex, eq_gains_zero);
	
	vortex_EqHw_SetBypassGain(vortex, 0, 0);
	vortex_EqHw_SetA3DBypassGain(vortex, 0, 0);
	vortex_EqHw_SetLeftStates(vortex, eq_states_zero, asEqOutStateZeros);
	vortex_EqHw_SetRightStates(vortex, eq_states_zero, asEqOutStateZeros);
	vortex_EqHw_SetLevels(vortex, (u16*)eq_levels);
}

/* Program coeficients as pass through */
void vortex_EqHw_ProgramPipe(vortex_t *vortex) {
	vortex_EqHw_SetTimeConsts(vortex, 0, 0);
	
	vortex_EqHw_SetLeftCoefs(vortex, asEqCoefsPipes);
	vortex_EqHw_SetRightCoefs(vortex, asEqCoefsPipes);
	
	vortex_EqHw_SetLeftGainsCurrent(vortex, eq_gains_current);
	vortex_EqHw_SetRightGainsCurrent(vortex, eq_gains_current);
	vortex_EqHw_SetLeftGainsTarget(vortex, eq_gains_current);
	vortex_EqHw_SetRightGainsTarget(vortex, eq_gains_current);
}
/* Program EQ block as 10 band Equalizer */
void vortex_EqHw_Program10Band(vortex_t *vortex, auxxEqCoeffSet_t *coefset) {
	
	vortex_EqHw_SetTimeConsts(vortex, 0xc, 0x7fe0);
	
	vortex_EqHw_SetLeftCoefs(vortex, coefset->LeftCoefs);
	vortex_EqHw_SetRightCoefs(vortex, coefset->RightCoefs);
	
	vortex_EqHw_SetLeftGainsCurrent(vortex, coefset->LeftGains);
	
	vortex_EqHw_SetRightGainsTarget(vortex, coefset->RightGains);
	vortex_EqHw_SetLeftGainsTarget(vortex, coefset->LeftGains);
	
	vortex_EqHw_SetRightGainsCurrent(vortex, coefset->RightGains);
}


void vortex_EqHw_GetTenBandLevels(vortex_t *vortex, u16 peaks[]) {
	eqhw_t *eqhw = &(vortex->eq.this04);
	int i; 
	
	if (eqhw->this04 > 0)
		return;
	
	for (i=0; i<eqhw->this04; i++)
		peaks[i] = hwread(vortex->mmio, 0x2B024 + i*0x30);
	for (i=0; i<eqhw->this04; i++)
		peaks[i+eqhw->this04] = hwread(vortex->mmio, 0x2B204 + i*0x30);
}
/* CEqlzr.s */

int  vortex_Eqlzr_GetLeftGain(vortex_t *vortex, u16 index, u16 *gain) {
	eqlzr_t *eq = &(vortex->eq);
	
	if (eq->this28) {
		*gain = eq->this130[index];
		return 0;
	}
	return 1;
}

void vortex_Eqlzr_SetLeftGain(vortex_t *vortex, u16 index, u16 gain) {
	eqlzr_t *eq = &(vortex->eq);

	if (eq->this28 == 0)
		return;
	
	eq->this130[index] = gain;
	if (eq->this54)
		return;
	
	vortex_EqHw_SetLeftGainsSingleTarget(vortex, index, gain);
}

int  vortex_Eqlzr_GetRightGain(vortex_t *vortex, u16 index, u16 *gain) {
	eqlzr_t *eq = &(vortex->eq);
	
	if (eq->this28) {
		*gain = eq->this130[index + eq->this10];
		return 0;
	}
	return 1;
}

void vortex_Eqlzr_SetRightGain(vortex_t *vortex, u16 index, u16 gain) {
	eqlzr_t *eq = &(vortex->eq);
	
	if (eq->this28 == 0)
		return;
	
	eq->this130[index + eq->this10] = gain;
	if (eq->this54)
		return;
	
	vortex_EqHw_SetRightGainsSingleTarget(vortex, index, gain);
}

int  vortex_Eqlzr_GetAllBands(vortex_t *vortex, u16 *gains, unsigned long *cnt) {
	eqlzr_t *eq = &(vortex->eq);
	int si=0;
	
	if (eq->this10 == 0)
		return 1;
	
	{
		if (vortex_Eqlzr_GetLeftGain(vortex, si, &gains[si]))
			return 1;			
		if (vortex_Eqlzr_GetRightGain(vortex, si, &gains[si + eq->this10]))
			return 1;
		si++;
	} while (eq->this10 > si);
	*cnt = si*2;
	return 0;
}

int  vortex_Eqlzr_SetAllBandsFromActiveCoeffSet(vortex_t *vortex) {
	eqlzr_t *eq = &(vortex->eq);
	
	vortex_EqHw_SetLeftGainsTarget(vortex, eq->this130);
	vortex_EqHw_SetRightGainsTarget(vortex, &(eq->this130[eq->this10]));
	
	return 0;
}

int  vortex_Eqlzr_SetAllBands(vortex_t *vortex, u16 gains[], unsigned long count) {
	eqlzr_t *eq = &(vortex->eq);
	int i;
	
	if (((eq->this10)*2 != count) || (eq->this28 == 0))
		return 1;
	
	if (0 < count) {
		for (i=0; i<count; i++) {
			eq->this130[i] = gains[i];
		}
	}
	if (eq->this54)
		return 0;
	return vortex_Eqlzr_SetAllBandsFromActiveCoeffSet(vortex);
}

void vortex_Eqlzr_ProgramA3dBypassGain(vortex_t *vortex) {
	eqlzr_t *eq = &(vortex->eq);
	int eax, ebx;
	
	if (eq->this54)
		eax = eq->this0e;
	else
		eax = eq->this0a;
	ebx = (eax * eq->this58) >> 0x10;
	eax = (eax * eq->this5c) >> 0x10;
	vortex_EqHw_SetA3DBypassGain(vortex, ebx, eax);
}

void vortex_Eqlzr_SetBypass(vortex_t *vortex, long bp) {
	eqlzr_t *eq = &(vortex->eq);
	
	if ((eq->this28) && (bp == 0)) {
		vortex_Eqlzr_SetAllBandsFromActiveCoeffSet(vortex);
		vortex_EqHw_SetBypassGain(vortex, eq->this08, eq->this08);
	} else {
		vortex_EqHw_SetLeftGainsTarget(vortex, (u16*)(eq->this14));
		vortex_EqHw_SetRightGainsTarget(vortex, (u16*)(eq->this14));
		vortex_EqHw_SetBypassGain(vortex, eq->this0c, eq->this0c);
	}
	// FIXME: no yet implemented.
	vortex_Eqlzr_ProgramA3dBypassGain(vortex);
}

void vortex_Eqlzr_ReadAndSetActiveCoefSet(vortex_t *vortex) {
	eqlzr_t *eq = &(vortex->eq);
	
	/* Set EQ BiQuad filter coeficients */
	memcpy(&(eq->coefset), &asEqCoefsNormal, sizeof(auxxEqCoeffSet_t));
	/* Set EQ Band gain levels and dump into hardware registers. */
	vortex_Eqlzr_SetAllBands(vortex, eq_gains_normal, eq->this10*2);	
}

#if 0
void vortex_Eqlzr_vortex_SetA3dBypassVolume()
void vortex_Eqlzr_ShutDownA3d()
#endif

int  vortex_Eqlzr_GetAllPeaks(vortex_t *vortex, u16 *peaks, int *count) {
	eqlzr_t *eq = &(vortex->eq);
	
	if (eq->this10 == 0)
		return 1;
	*count = eq->this10 * 2;
	vortex_EqHw_GetTenBandLevels(vortex, peaks);
	return 0;
}

auxxEqCoeffSet_t *vortex_Eqlzr_GetActiveCoefSet(vortex_t *vortex) {
	eqlzr_t *eq = &(vortex->eq);
	
	return (&(eq->coefset));
}

void vortex_Eqlzr_init(vortex_t *vortex) {
	eqlzr_t *eq = &(vortex->eq);
	
	/* Object constructor */
	//eq->this04 = 0;
	eq->this08 = 0; /* Bypass gain with EQ in use. */
	eq->this0a = 0x5999; 
	eq->this0c = 0x5999; /* Bypass gain with EQ disabled. */
	eq->this0e = 0x5999;
	
	eq->this10 = 0xa; /* 10 eq frequency bands. */
	eq->this04.this04 = eq->this10;
	eq->this28 = 0x1; /* if 1 => Allow read access to this130 (gains) */
	eq->this54 = 0x0; /* if 1 => Dont Allow access to hardware (gains) */
	eq->this58 = 0xffff;
	eq->this5c = 0xffff;
	
	/* Set gains. */
	memset(eq->this14, 0, 2*10);
	
	/* Actual init. */
	vortex_EqHw_ZeroState(vortex);
	vortex_EqHw_SetSampleRate(vortex, 0x11);
	vortex_Eqlzr_ReadAndSetActiveCoefSet(vortex);
	
	vortex_EqHw_Program10Band(vortex, &(eq->coefset));
	vortex_Eqlzr_SetBypass(vortex, eq->this54);
	vortex_EqHw_Enable(vortex);
}

/* ALSA interface */

/* Control interface */
static int snd_vortex_eqtoggle_info(snd_kcontrol_t *kcontrol, snd_ctl_elem_info_t *uinfo) {
	uinfo->type = SNDRV_CTL_ELEM_TYPE_BOOLEAN;
	uinfo->count = 1;
	uinfo->value.integer.min = 0;
	uinfo->value.integer.max = 1;
	return 0;
}

static int snd_vortex_eqtoggle_get(snd_kcontrol_t *kcontrol, snd_ctl_elem_value_t *ucontrol) {
	vortex_t *vortex = snd_kcontrol_chip(kcontrol);
	eqlzr_t *eq = &(vortex->eq);
	//int i = kcontrol->private_value;
	
	ucontrol->value.integer.value[0] = eq->this54 ? 0 : 1;
	
	return 0;
}

static int snd_vortex_eqtoggle_put(snd_kcontrol_t *kcontrol, snd_ctl_elem_value_t *ucontrol) {
	vortex_t *vortex = snd_kcontrol_chip(kcontrol);
	eqlzr_t *eq = &(vortex->eq);
	//int i = kcontrol->private_value;
	
	eq->this54 = ucontrol->value.integer.value[0] ? 0 : 1;
	vortex_Eqlzr_SetBypass(vortex, eq->this54);
	
	return 1; /* Allways changes */
}

static snd_kcontrol_new_t vortex_eqtoggle_kcontrol __devinitdata = {
    /*	.iface = */ SNDRV_CTL_ELEM_IFACE_MIXER,
    0,0,
/*	.name =  */ "EQ Enable",
/*	.index = */ 0,
/*	.access = */ SNDRV_CTL_ELEM_ACCESS_READWRITE,
0,
/*	.info = */ snd_vortex_eqtoggle_info,
/*	.get = */ snd_vortex_eqtoggle_get,
/*	.put = */ snd_vortex_eqtoggle_put,
/*	.private_value = */ 0
};

static int snd_vortex_eq_info(snd_kcontrol_t *kcontrol, snd_ctl_elem_info_t *uinfo) {
	uinfo->type = SNDRV_CTL_ELEM_TYPE_INTEGER;
	uinfo->count = 2;
	uinfo->value.integer.min = 0x0000;
	uinfo->value.integer.max = 0x7fff;
	return 0;
}

static int snd_vortex_eq_get(snd_kcontrol_t *kcontrol, snd_ctl_elem_value_t *ucontrol) {
	vortex_t *vortex = snd_kcontrol_chip(kcontrol);
	int i = kcontrol->private_value;
	u16 gainL, gainR;
	
	vortex_Eqlzr_GetLeftGain(vortex, i, &gainL);
	vortex_Eqlzr_GetRightGain(vortex, i, &gainR);
	ucontrol->value.integer.value[0] = gainL;
	ucontrol->value.integer.value[1] = gainR;
	return 0;
}

static int snd_vortex_eq_put(snd_kcontrol_t *kcontrol, snd_ctl_elem_value_t *ucontrol) {
	vortex_t *vortex = snd_kcontrol_chip(kcontrol);
	int changed = 0, i = kcontrol->private_value;
	u16 gainL, gainR;
	
	vortex_Eqlzr_GetLeftGain(vortex, i, &gainL);
	vortex_Eqlzr_GetRightGain(vortex, i, &gainR);
	
	if (gainL != ucontrol->value.integer.value[0]) {
		vortex_Eqlzr_SetLeftGain(vortex, i, ucontrol->value.integer.value[0]);
		changed = 1;
	}
	if (gainR != ucontrol->value.integer.value[1]) {
		vortex_Eqlzr_SetRightGain(vortex, i, ucontrol->value.integer.value[1]);
		changed = 1;
	}
	return changed;
}

static snd_kcontrol_new_t vortex_eq_kcontrol __devinitdata = {
    /*	.iface = */SNDRV_CTL_ELEM_IFACE_MIXER,
    0,0,
/*	.name = */"                        .",
/*	.index = */0,
/*	.access = */SNDRV_CTL_ELEM_ACCESS_READWRITE,
0,
/*	.info = */snd_vortex_eq_info,
/*	.get = */snd_vortex_eq_get,
/*	.put = */snd_vortex_eq_put,
/*	.private_value = */0
};

static int snd_vortex_peaks_info(snd_kcontrol_t *kcontrol, snd_ctl_elem_info_t *uinfo) {
	uinfo->type = SNDRV_CTL_ELEM_TYPE_INTEGER;
	uinfo->count = 20;
	uinfo->value.integer.min = 0x0000;
	uinfo->value.integer.max = 0xffff;
	return 0;
}

static int snd_vortex_peaks_get(snd_kcontrol_t *kcontrol, snd_ctl_elem_value_t *ucontrol) {
	vortex_t *vortex = snd_kcontrol_chip(kcontrol);
	int i, count;
	u16 peaks[20];
	
	vortex_Eqlzr_GetAllPeaks(vortex, peaks, &count);
	if (count != 20) {
		printk("vortex: peak count error 20 != %d \n", count);
		return -1;
	}
	for (i=0; i<20; i++)
		ucontrol->value.integer.value[i] = peaks[i];
	
	return 0;
}

static snd_kcontrol_new_t vortex_levels_kcontrol __devinitdata = {
/*	.iface = */SNDRV_CTL_ELEM_IFACE_MIXER,0,0,
/*	.name = */"EQ Peaks",0,
/*	.access = */SNDRV_CTL_ELEM_ACCESS_READ | SNDRV_CTL_ELEM_ACCESS_VOLATILE,
0,
/*	.info = */snd_vortex_peaks_info,
/*	.get = */snd_vortex_peaks_get,
NULL,0
};

/* EQ band gain labels. */
static char *EqBandLabels[10] __devinitdata = {
	"EQ0 31Hz\0",
	"EQ1 63Hz\0",
	"EQ2 125Hz\0",
	"EQ3 250Hz\0",
	"EQ4 500Hz\0",
	"EQ5 1KHz\0",
	"EQ6 2KHz\0",
	"EQ7 4KHz\0",
	"EQ8 8KHz\0",
	"EQ9 16KHz\0",
};

/* ALSA driver entry points. Init and exit. */
int vortex_eq_init(vortex_t *vortex) {
	snd_kcontrol_t *kcontrol;
	int err, i;
	
	vortex_Eqlzr_init(vortex);

	if ((kcontrol = snd_ctl_new1(&vortex_eqtoggle_kcontrol, vortex)) == NULL)
		return -ENOMEM;
	kcontrol->private_value = 0;
	if ((err = snd_ctl_add(vortex->card, kcontrol)) < 0)
       	return err;

	/* EQ gain controls */
	for (i=0; i<10; i++) {
		if ((kcontrol = snd_ctl_new1(&vortex_eq_kcontrol, vortex)) == NULL)
			return -ENOMEM;
		strcpy(kcontrol->id.name, EqBandLabels[i]);
		kcontrol->private_value = i;
		if ((err = snd_ctl_add(vortex->card, kcontrol)) < 0)
        	return err;
		//vortex->eqctrl[i] = kcontrol;
	}
	/* EQ band levels */
	if ((kcontrol = snd_ctl_new1(&vortex_levels_kcontrol, vortex)) == NULL)
		return -ENOMEM;
	if ((err = snd_ctl_add(vortex->card, kcontrol)) < 0)
       	return err;
	
	return 0;
}

int vortex_eq_free(vortex_t *vortex) {
	/*
	//FIXME: segfault because vortex->eqctrl[i] == 4
	int i;
	for (i=0; i<10; i++) {
		if (vortex->eqctrl[i])
			snd_ctl_remove(vortex->card, vortex->eqctrl[i]);
	}
	*/
	return 0;
}

/* End */
