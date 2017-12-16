/*
 *	MP3 huffman table selecting and bit counting
 *
 *	Copyright (c) 1999-2005 Takehiro TOMINAGA
 *	Copyright (c) 2002-2005 Gabriel Bouvigne
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	 See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

/* $Id: takehiro.c,v 1.80 2017/09/06 15:07:30 robert Exp $ */

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#if __ALTIVEC__
#undef TAKEHIRO_IEEE754_HACK
#include <altivec.h>
#endif

#include "lame.h"
#include "machine.h"
#include "encoder.h"
#include "util.h"
#include "quantize_pvt.h"
#include "tables.h"


static const struct {
    const int region0_count;
    const int region1_count;
} subdv_table[23] = {
    {
    0, 0},              /* 0 bands */
    {
    0, 0},              /* 1 bands */
    {
    0, 0},              /* 2 bands */
    {
    0, 0},              /* 3 bands */
    {
    0, 0},              /* 4 bands */
    {
    0, 1},              /* 5 bands */
    {
    1, 1},              /* 6 bands */
    {
    1, 1},              /* 7 bands */
    {
    1, 2},              /* 8 bands */
    {
    2, 2},              /* 9 bands */
    {
    2, 3},              /* 10 bands */
    {
    2, 3},              /* 11 bands */
    {
    3, 4},              /* 12 bands */
    {
    3, 4},              /* 13 bands */
    {
    3, 4},              /* 14 bands */
    {
    4, 5},              /* 15 bands */
    {
    4, 5},              /* 16 bands */
    {
    4, 6},              /* 17 bands */
    {
    5, 6},              /* 18 bands */
    {
    5, 6},              /* 19 bands */
    {
    5, 7},              /* 20 bands */
    {
    6, 7},              /* 21 bands */
    {
    6, 7},              /* 22 bands */
};





/*********************************************************************
 * nonlinear quantization of xr 
 * More accurate formula than the ISO formula.  Takes into account
 * the fact that we are quantizing xr -> ix, but we want ix^4/3 to be 
 * as close as possible to x^4/3.  (taking the nearest int would mean
 * ix is as close as possible to xr, which is different.)
 *
 * From Segher Boessenkool <segher@eastsite.nl>  11/1999
 *
 * 09/2000: ASM code removed in favor of IEEE754 hack by Takehiro
 * Tominaga. If you need the ASM code, check CVS circa Aug 2000.
 *
 * 01/2004: Optimizations by Gabriel Bouvigne
 *********************************************************************/





static void
quantize_lines_xrpow_01(unsigned int l, FLOAT istep, const FLOAT * xr, int *ix)
{
    const FLOAT compareval0 = (1.0f - 0.4054f) / istep;
    unsigned int i;

    assert(l > 0);
    assert(l % 2 == 0);
    for (i = 0; i < l; i += 2) {
        FLOAT const xr_0 = xr[i+0];
        FLOAT const xr_1 = xr[i+1];
        int const ix_0 = (compareval0 > xr_0) ? 0 : 1;
        int const ix_1 = (compareval0 > xr_1) ? 0 : 1;
        ix[i+0] = ix_0;
        ix[i+1] = ix_1;
    }
}



#ifdef TAKEHIRO_IEEE754_HACK

typedef union {
    float   f;
    int     i;
} fi_union;

#define MAGIC_FLOAT (65536*(128))
#define MAGIC_INT 0x4b000000


static void
quantize_lines_xrpow(unsigned int l, FLOAT istep, const FLOAT * xp, int *pi)
{
    fi_union *fi;
    unsigned int remaining;

    assert(l > 0);

    fi = (fi_union *) pi;

    l = l >> 1;
    remaining = l % 2;
    l = l >> 1;
    while (l--) {
        double  x0 = istep * xp[0];
        double  x1 = istep * xp[1];
        double  x2 = istep * xp[2];
        double  x3 = istep * xp[3];

        x0 += MAGIC_FLOAT;
        fi[0].f = x0;
        x1 += MAGIC_FLOAT;
        fi[1].f = x1;
        x2 += MAGIC_FLOAT;
        fi[2].f = x2;
        x3 += MAGIC_FLOAT;
        fi[3].f = x3;

        fi[0].f = x0 + adj43asm[fi[0].i - MAGIC_INT];
        fi[1].f = x1 + adj43asm[fi[1].i - MAGIC_INT];
        fi[2].f = x2 + adj43asm[fi[2].i - MAGIC_INT];
        fi[3].f = x3 + adj43asm[fi[3].i - MAGIC_INT];

        fi[0].i -= MAGIC_INT;
        fi[1].i -= MAGIC_INT;
        fi[2].i -= MAGIC_INT;
        fi[3].i -= MAGIC_INT;
        fi += 4;
        xp += 4;
    };
    if (remaining) {
        double  x0 = istep * xp[0];
        double  x1 = istep * xp[1];

        x0 += MAGIC_FLOAT;
        fi[0].f = x0;
        x1 += MAGIC_FLOAT;
        fi[1].f = x1;

        fi[0].f = x0 + adj43asm[fi[0].i - MAGIC_INT];
        fi[1].f = x1 + adj43asm[fi[1].i - MAGIC_INT];

        fi[0].i -= MAGIC_INT;
        fi[1].i -= MAGIC_INT;
    }

}


#else

/*********************************************************************
 * XRPOW_FTOI is a macro to convert floats to ints.  
 * if XRPOW_FTOI(x) = nearest_int(x), then QUANTFAC(x)=adj43asm[x]
 *                                         ROUNDFAC= -0.0946
 *
 * if XRPOW_FTOI(x) = floor(x), then QUANTFAC(x)=asj43[x]   
 *                                   ROUNDFAC=0.4054
 *
 * Note: using floor() or (int) is extremely slow. On machines where
 * the TAKEHIRO_IEEE754_HACK code above does not work, it is worthwile
 * to write some ASM for XRPOW_FTOI().  
 *********************************************************************/
#define XRPOW_FTOI(src,dest) ((dest) = (int)(src))
#define QUANTFAC(rx)  adj43[rx]
#define ROUNDFAC 0.4054


static void
quantize_lines_xrpow(unsigned int l, FLOAT istep, const FLOAT * xr, int *ix)
{
#if __ALTIVEC__
    vector float v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,va,vb,vistep,vzero;
    vector signed int vx1,vx2,vx3,vx4,vprev;
    vector unsigned char vperm1,vperm2;
    const vector float const1 = (vector float)VINIT4(0.4053964553387788,3.404263724373839,5.465086767819913,1.0);
    const vector float const2 = (vector float)VINIT4(7.719205369637751,10.93017829043677,0,0);
#ifndef _ARCH_PPC64
    unsigned int temp[4] __attribute__ ((aligned (16)));
#endif
    float temp2[4] __attribute__ ((aligned (16)));
    temp2[0] = istep;
    vistep = vec_ld(0,temp2);
    vzero = vec_xor(vzero,vzero);
    vistep = vec_splat(vistep,0);
    
    l = l >> 1;
    
    vperm1 = vec_lvsl(0,xr);
    vperm2 = vec_lvsr(0,ix);
    v1 = vec_ld(0,xr);
    vx1 = vec_ld(-16,ix);
    vx2 = vec_ld(0,ix);
    vprev = vec_perm(vx1,vx2,vec_lvsl(0,ix));
    for(;l>3;l-=4) {
        v2 = vec_ld(16,xr);
        v3 = vec_ld(32,xr);
        v4 = vec_perm(v1,v2,vperm1);
        v5 = vec_perm(v2,v3,vperm1);
        va = vec_madd(v4,vistep,vzero);
        vb = vec_madd(v5,vistep,vzero);
        v1 = v3;
        
        v2 = vec_floor(va);
        v3 = vec_floor(vb);
        v4 = vec_splat(const1,2);
        v5 = vec_splat(const1,1);
        v6 = vec_splat(const2,1);
        v7 = vec_splat(const2,0);
        v8 = vec_madd(v2,v4,v5);
        v9 = vec_madd(v3,v4,v5);
        v10 = vec_madd(v2,v6,v7);
        v11 = vec_madd(v3,v6,v7);
        v4 = vec_splat(const1,0);
        v5 = vec_splat(const1,3);
        v8 = vec_madd(v8,v2,v4);
        v9 = vec_madd(v9,v3,v4);
        v10 = vec_madd(v10,v2,v5);
        v11 = vec_madd(v11,v3,v5);
        v6 = vec_re(v10);
        v7 = vec_re(v11);
        v10 = vec_nmsub(v10,v6,v5);
        v11 = vec_nmsub(v11,v7,v5);
        v10 = vec_madd(v10,v6,v6);
        v11 = vec_madd(v11,v7,v7);
        va = vec_madd(v8,v10,va);
        vb = vec_madd(v9,v11,vb);
        
        vx1 = vec_cts(va,0);
        vx2 = vec_cts(vb,0);
        
        vx3 = vec_perm(vprev,vx1,vperm2);
        vx4 = vec_perm(vx1,vx2,vperm2);
        vec_st(vx3,0,ix);
        vec_st(vx4,16,ix);
        vprev = vx2;
        xr += 8;
        ix += 8;
    }
    vx1 = vec_ld(0,ix);
    vx2 = vec_ld(16,ix);
    vx3 = vec_perm(vx1,vx2,vec_lvsl(0,ix));
    vx4 = vec_perm(vprev,vx3,vperm2);
    vec_st(vx4,0,ix);
    
#if _ARCH_PPC64
    for(;l>1;l-=2) {
        FLOAT   x0, x1, x2, x3;
        int     rx0, rx1, rx2, rx3;

        x0 = *xr++ * istep;
        x1 = *xr++ * istep;
        XRPOW_FTOI(x0, rx0);
        x2 = *xr++ * istep;
        XRPOW_FTOI(x1, rx1);
        x3 = *xr++ * istep;
        XRPOW_FTOI(x2, rx2);
        x0 += QUANTFAC(rx0);
        XRPOW_FTOI(x3, rx3);
        x1 += QUANTFAC(rx1);
        XRPOW_FTOI(x0, *ix++);
        x2 += QUANTFAC(rx2);
        XRPOW_FTOI(x1, *ix++);
        x3 += QUANTFAC(rx3);
        XRPOW_FTOI(x2, *ix++);
        XRPOW_FTOI(x3, *ix++);
    }
#else
    for(;l>1;l-=2) {
        v2 = vec_ld(16,xr);
        v4 = vec_perm(v1,v2,vperm1);
        v1 = v2;
        va = vec_madd(v4,vistep,vzero);
        vx1 = vec_cts(va,0);
        vec_st((vector unsigned int)vx1,0,temp);
        v2 = vec_lde(0,adj43+temp[0]);
        v3 = vec_lde(0,adj43+temp[1]);
        v4 = vec_lde(0,adj43+temp[2]);
        v5 = vec_lde(0,adj43+temp[3]);
        v6 = vec_perm(v2,v2,vec_lvsl(0,adj43+temp[0]));
        v7 = vec_perm(v3,v3,vec_lvsl(-4,adj43+temp[1]));
        v8 = vec_perm(v4,v4,vec_lvsl(-8,adj43+temp[2]));
        v9 = vec_perm(v5,v5,vec_lvsl(-12,adj43+temp[3]));
        v6 = vec_or(v6,v7);
        v6 = vec_or(v6,v8);
        v6 = vec_or(v6,v9);
        va = vec_add(va,v6);
        vx1 = vec_cts(va,0);
        vx3 = vec_perm(vprev,vx1,vperm2);
        vec_st(vx3,0,ix);
        vprev = vx1;
        xr += 4;
        ix += 4;
    }
    vx1 = vec_ld(0,ix);
    vx2 = vec_ld(16,ix);
    vx3 = vec_perm(vx1,vx2,vec_lvsl(0,ix));
    vx4 = vec_perm(vprev,vx3,vperm2);
    vec_st(vx4,0,ix);
#endif
    
    if (l) {
        FLOAT   x0, x1;
        int     rx0, rx1;

        x0 = *xr++ * istep;
        x1 = *xr++ * istep;
        XRPOW_FTOI(x0, rx0);
        XRPOW_FTOI(x1, rx1);
        x0 += QUANTFAC(rx0);
        x1 += QUANTFAC(rx1);
        XRPOW_FTOI(x0, *ix++);
        XRPOW_FTOI(x1, *ix++);
    }
#else
    unsigned int remaining;

    assert(l > 0);

    l = l >> 1;
    remaining = l % 2;
    l = l >> 1;
    while (l--) {
        FLOAT   x0, x1, x2, x3;
        int     rx0, rx1, rx2, rx3;

        x0 = *xr++ * istep;
        x1 = *xr++ * istep;
        XRPOW_FTOI(x0, rx0);
        x2 = *xr++ * istep;
        XRPOW_FTOI(x1, rx1);
        x3 = *xr++ * istep;
        XRPOW_FTOI(x2, rx2);
        x0 += QUANTFAC(rx0);
        XRPOW_FTOI(x3, rx3);
        x1 += QUANTFAC(rx1);
        XRPOW_FTOI(x0, *ix++);
        x2 += QUANTFAC(rx2);
        XRPOW_FTOI(x1, *ix++);
        x3 += QUANTFAC(rx3);
        XRPOW_FTOI(x2, *ix++);
        XRPOW_FTOI(x3, *ix++);
    };
    if (remaining) {
        FLOAT   x0, x1;
        int     rx0, rx1;

        x0 = *xr++ * istep;
        x1 = *xr++ * istep;
        XRPOW_FTOI(x0, rx0);
        XRPOW_FTOI(x1, rx1);
        x0 += QUANTFAC(rx0);
        x1 += QUANTFAC(rx1);
        XRPOW_FTOI(x0, *ix++);
        XRPOW_FTOI(x1, *ix++);
    }
#endif
}



#endif



/*********************************************************************
 * Quantization function
 * This function will select which lines to quantize and call the
 * proper quantization function
 *********************************************************************/

static void
quantize_xrpow(const FLOAT * xp, int *pi, FLOAT istep, gr_info const *const cod_info,
               calc_noise_data const *prev_noise)
{
    /* quantize on xr^(3/4) instead of xr */
    int     sfb;
    int     sfbmax;
    int     j = 0;
    int     prev_data_use;
    int    *iData;
    int     accumulate = 0;
    int     accumulate01 = 0;
    int    *acc_iData;
    const FLOAT *acc_xp;

    iData = pi;
    acc_xp = xp;
    acc_iData = iData;


    /* Reusing previously computed data does not seems to work if global gain
       is changed. Finding why it behaves this way would allow to use a cache of 
       previously computed values (let's 10 cached values per sfb) that would 
       probably provide a noticeable speedup */
    prev_data_use = (prev_noise && (cod_info->global_gain == prev_noise->global_gain));

    if (cod_info->block_type == SHORT_TYPE)
        sfbmax = 38;
    else
        sfbmax = 21;

    for (sfb = 0; sfb <= sfbmax; sfb++) {
        int     step = -1;

        if (prev_data_use || cod_info->block_type == NORM_TYPE) {
            step =
                cod_info->global_gain
                - ((cod_info->scalefac[sfb] + (cod_info->preflag ? pretab[sfb] : 0))
                   << (cod_info->scalefac_scale + 1))
                - cod_info->subblock_gain[cod_info->window[sfb]] * 8;
        }
        assert(cod_info->width[sfb] >= 0);
        if (prev_data_use && (prev_noise->step[sfb] == step)) {
            /* do not recompute this part,
               but compute accumulated lines */
            if (accumulate) {
                quantize_lines_xrpow(accumulate, istep, acc_xp, acc_iData);
                accumulate = 0;
            }
            if (accumulate01) {
                quantize_lines_xrpow_01(accumulate01, istep, acc_xp, acc_iData);
                accumulate01 = 0;
            }
        }
        else {          /*should compute this part */
            int     l;
            l = cod_info->width[sfb];

            if ((j + cod_info->width[sfb]) > cod_info->max_nonzero_coeff) {
                /*do not compute upper zero part */
                int     usefullsize;
                usefullsize = cod_info->max_nonzero_coeff - j + 1;
                memset(&pi[cod_info->max_nonzero_coeff], 0,
                       sizeof(int) * (576 - cod_info->max_nonzero_coeff));
                l = usefullsize;

                if (l < 0) {
                    l = 0;
                }

                /* no need to compute higher sfb values */
                sfb = sfbmax + 1;
            }

            /*accumulate lines to quantize */
            if (!accumulate && !accumulate01) {
                acc_iData = iData;
                acc_xp = xp;
            }
            if (prev_noise &&
                prev_noise->sfb_count1 > 0 &&
                sfb >= prev_noise->sfb_count1 &&
                prev_noise->step[sfb] > 0 && step >= prev_noise->step[sfb]) {

                if (accumulate) {
                    quantize_lines_xrpow(accumulate, istep, acc_xp, acc_iData);
                    accumulate = 0;
                    acc_iData = iData;
                    acc_xp = xp;
                }
                accumulate01 += l;
            }
            else {
                if (accumulate01) {
                    quantize_lines_xrpow_01(accumulate01, istep, acc_xp, acc_iData);
                    accumulate01 = 0;
                    acc_iData = iData;
                    acc_xp = xp;
                }
                accumulate += l;
            }

            if (l <= 0) {
                /*  rh: 20040215
                 *  may happen due to "prev_data_use" optimization 
                 */
                if (accumulate01) {
                    quantize_lines_xrpow_01(accumulate01, istep, acc_xp, acc_iData);
                    accumulate01 = 0;
                }
                if (accumulate) {
                    quantize_lines_xrpow(accumulate, istep, acc_xp, acc_iData);
                    accumulate = 0;
                }

                break;  /* ends for-loop */
            }
        }
        if (sfb <= sfbmax) {
            iData += cod_info->width[sfb];
            xp += cod_info->width[sfb];
            j += cod_info->width[sfb];
        }
    }
    if (accumulate) {   /*last data part */
        quantize_lines_xrpow(accumulate, istep, acc_xp, acc_iData);
        accumulate = 0;
    }
    if (accumulate01) { /*last data part */
        quantize_lines_xrpow_01(accumulate01, istep, acc_xp, acc_iData);
        accumulate01 = 0;
    }

}




/*************************************************************************/
/*	      ix_max							 */
/*************************************************************************/

#if __ALTIVEC__
int
ix_max_vec(const int *ix, const int *end)
{
    int vresult[4] __attribute__ ((aligned (16)));
    int max1=0, max2=0;
    vector signed int v1, v2, v3, v4, v5, v6, v7, vmax;
    vector unsigned char vmask,vc1,vc2,vc3,vc4;
    
    if(end - ix < 8) goto normal;
    int i = (end-ix)/4;
    int remain = (end-ix)%4;
    vc1 = vec_splat_u8(1);
    vc2 = vec_splat_u8(5);
    vc3 = vec_sl(vc1,vc2);
    vc4 = vec_sl(vc3,vc1);
    
    v1 = vec_ld(0, ix);
    vmask = vec_lvsl(0, ix);
    vmax = vec_xor(vmax, vmax);
    
    while(i--) {
        v2 = vec_ld(16, ix);
        v3 = vec_perm(v1, v2, vmask);
        v1 = v2;
        vmax = vec_max(vmax,v3);
        ix += 4;
    }
    
    v4 = vec_slo(vmax,vc3);
    v5 = vec_max(vmax,v4);
    v6 = vec_slo(v5,vc4);
    v7 = vec_max(v5,v6);
    vec_st(v7,0,vresult);
    
    max1 = vresult[0];
    if(!remain) return max1;
    //max2 = vresult[2];
    /*if(vresult[2] > max1) max1 = vresult[2];
    if(vresult[3] > max2) max2 = vresult[3];*/
    
  normal:
    
    do{
        int x1 = *ix++;
        int x2 = *ix++;
        if (max1 < x1) max1 = x1;
        if (max2 < x2) max2 = x2;
    } while (ix < end);
    if(max1 < max2) max1 = max2;
    
    return max1;
}
#else
static int
ix_max(const int *ix, const int *end)
{
    int     max1 = 0, max2 = 0;

    do {
        int const x1 = *ix++;
        int const x2 = *ix++;
        if (max1 < x1)
            max1 = x1;

        if (max2 < x2)
            max2 = x2;
    } while (ix < end);
    if (max1 < max2)
        max1 = max2;
    return max1;
}
#endif






#if !defined(__ALTIVEC__) || (defined(__ALTIVEC__) && !defined(_ARCH_PPC64))
static int
count_bit_ESC(const int *ix, const int *const end, int t1, const int t2, unsigned int *const s)
{
    /* ESC-table is used */
    unsigned int const linbits = ht[t1].xlen * 65536u + ht[t2].xlen;
    unsigned int sum = 0, sum2;

    do {
        unsigned int x = *ix++;
        unsigned int y = *ix++;

        if (x >= 15u) {
            x = 15u;
            sum += linbits;
        }
        if (y >= 15u) {
            y = 15u;
            sum += linbits;
        }
        x <<= 4u;
        x += y;
        sum += largetbl[x];
    } while (ix < end);

    sum2 = sum & 0xffffu;
    sum >>= 16u;

    if (sum > sum2) {
        sum = sum2;
        t1 = t2;
    }

    *s += sum;
    return t1;
}
#endif


static int
count_bit_noESC(const int *ix, const int *end, int mx, unsigned int *s)
{
    /* No ESC-words */
    unsigned int sum1 = 0;
    const uint8_t *const hlen1 = ht[1].hlen;
    (void) mx;

    do {
        unsigned int const x0 = *ix++;
        unsigned int const x1 = *ix++;
        sum1 += hlen1[ x0+x0 + x1 ];
    } while (ix < end);

    *s += sum1;
    return 1;
}


static const int huf_tbl_noESC[] = {
    1, 2, 5, 7, 7, 10, 10, 13, 13, 13, 13, 13, 13, 13, 13
};


#if !defined(__ALTIVEC__)
static int
count_bit_noESC_from2(const int *ix, const int *end, int max, unsigned int *s)
{
    int t1 = huf_tbl_noESC[max - 1];
    /* No ESC-words */
    const unsigned int xlen = ht[t1].xlen;
    uint32_t const* table = (t1 == 2) ? &table23[0] : &table56[0];
    unsigned int sum = 0, sum2;

    do {
        unsigned int const x0 = *ix++;
        unsigned int const x1 = *ix++;
        sum += table[ x0 * xlen + x1 ];
    } while (ix < end);

    sum2 = sum & 0xffffu;
    sum >>= 16u;

    if (sum > sum2) {
        sum = sum2;
        t1++;
    }

    *s += sum;
    return t1;
}
#endif


inline static int
count_bit_noESC_from3(const int *ix, const int *end, int max, unsigned int * s)
{
    int t1 = huf_tbl_noESC[max - 1];
    /* No ESC-words */
    unsigned int sum1 = 0;
    unsigned int sum2 = 0;
    unsigned int sum3 = 0;
    const unsigned int xlen = ht[t1].xlen;
    const uint8_t *const hlen1 = ht[t1].hlen;
    const uint8_t *const hlen2 = ht[t1 + 1].hlen;
    const uint8_t *const hlen3 = ht[t1 + 2].hlen;
    int     t;

    do {
        unsigned int x0 = *ix++;
        unsigned int x1 = *ix++;
        unsigned int x = x0 * xlen + x1;
        sum1 += hlen1[x];
        sum2 += hlen2[x];
        sum3 += hlen3[x];
    } while (ix < end);

    t = t1;
    if (sum1 > sum2) {
        sum1 = sum2;
        t++;
    }
    if (sum1 > sum3) {
        sum1 = sum3;
        t = t1 + 2;
    }
    *s += sum1;

    return t;  
}

#if __ALTIVEC__
#if _ARCH_PPC64
static int
count_bit_ESC_altivec(const int *ix, const int *const end, int t1, const int t2, int *const s)
{
    /* ESC-table is used */
    int const linbits = ht[t1].xlen * 65536 + ht[t2].xlen;
    int     sum = 0, sum2;
    vector signed int v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16;
    vector unsigned int vsum;
    vector unsigned char vmask,vperm1,vperm2,vshamt;
    vector unsigned char vzero,vs1,vs2,vs3,vs4,vs5,vs6,vlimit1,vlimit2,vone;
    unsigned char tmp[16] __attribute__ ((aligned (16)));
    unsigned int tmp2[4] __attribute__ ((aligned (16)));
    
    vperm1 = (vector unsigned char)VINIT16(0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27);
    vperm2 = (vector unsigned char)VINIT16(4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31);
    vlimit1 = vec_splat_u8(14);
    vlimit2 = vec_splat_u8(15);
    vone = vec_splat_u8(1);
    vshamt = vec_splat_u8(4);
    vzero = vec_xor(vzero,vzero);
    vsum = vec_xor(vsum,vsum);
    
    if((int)(end - ix) < 32) goto normal;
    v0 = vec_ld(0,ix);
    vmask = vec_lvsl(0,ix);
    do {
        v1 = vec_ld(16,ix);
        v2 = vec_ld(32,ix);
        v3 = vec_ld(48,ix);
        v4 = vec_ld(64,ix);
        v5 = vec_ld(80,ix);
        v6 = vec_ld(96,ix);
        v7 = vec_ld(112,ix);
        v8 = vec_ld(128,ix);
        v9 = vec_perm(v0,v1,vmask);
        v10 = vec_perm(v1,v2,vmask);
        v11 = vec_perm(v2,v3,vmask);
        v12 = vec_perm(v3,v4,vmask);
        v13 = vec_perm(v4,v5,vmask);
        v14 = vec_perm(v5,v6,vmask);
        v15 = vec_perm(v6,v7,vmask);
        v16 = vec_perm(v7,v8,vmask);
        v0 = v8;
        v1 = vec_perm(v9,v10,vperm1);
        v2 = vec_perm(v9,v10,vperm2);
        v3 = vec_perm(v11,v12,vperm1);
        v4 = vec_perm(v11,v12,vperm2);
        v5 = vec_perm(v13,v14,vperm1);
        v6 = vec_perm(v13,v14,vperm2);
        v7 = vec_perm(v15,v16,vperm1);
        v8 = vec_perm(v15,v16,vperm2);
        
        v1 = (vector signed int)vec_packs(v1,v3);
        v2 = (vector signed int)vec_packs(v2,v4);
        v3 = (vector signed int)vec_packs(v5,v7);
        v4 = (vector signed int)vec_packs(v6,v8);
        vs1 = vec_packs((vector unsigned short)v1,(vector unsigned short)v3);
        vs2 = vec_packs((vector unsigned short)v2,(vector unsigned short)v4);
        vs3 = vec_sel(vs1,vlimit2,vec_cmpgt(vs1,vlimit1));
        vs4 = vec_sel(vs2,vlimit2,vec_cmpgt(vs2,vlimit1));
        vs5 = vec_sel(vzero,vone,vec_cmpgt(vs1,vlimit1));
        vs6 = vec_sel(vzero,vone,vec_cmpgt(vs2,vlimit1));
        vs5 = vec_add(vs5,vs6);
        vsum = vec_sum4s(vs5,vsum);
        vs3 = vec_sl(vs3,vshamt);
        vs3 = vec_add(vs3,vs4);
        vec_st(vs3,0,tmp);
        
        sum += largetbl[tmp[0]];
        sum += largetbl[tmp[1]];
        sum += largetbl[tmp[2]];
        sum += largetbl[tmp[3]];
        sum += largetbl[tmp[4]];
        sum += largetbl[tmp[5]];
        sum += largetbl[tmp[6]];
        sum += largetbl[tmp[7]];
        sum += largetbl[tmp[8]];
        sum += largetbl[tmp[9]];
        sum += largetbl[tmp[10]];
        sum += largetbl[tmp[11]];
        sum += largetbl[tmp[12]];
        sum += largetbl[tmp[13]];
        sum += largetbl[tmp[14]];
        sum += largetbl[tmp[15]];
        
        ix += 32;
    } while(ix < end-31);
    
    vsum = (vector unsigned int)vec_sums((vector signed int)vsum,(vector signed int)vzero);
    vec_st(vsum,0,tmp2);
    sum += tmp2[3] * linbits;
    
    while (ix < end) {
        unsigned int x = *ix++;
        unsigned int y = *ix++;

        if (x >= 15u) {
            x = 15u;
            sum += linbits;
        }
        if (y >= 15u) {
            y = 15u;
            sum += linbits;
        }
        x <<= 4u;
        x += y;
        sum += largetbl[x];
    }
    goto end;
    
normal:
    do {
        unsigned int x = *ix++;
        unsigned int y = *ix++;

        if (x >= 15u) {
            x = 15u;
            sum += linbits;
        }
        if (y >= 15u) {
            y = 15u;
            sum += linbits;
        }
        x <<= 4u;
        x += y;
        sum += largetbl[x];
    } while (ix < end);

end:
    sum2 = sum & 0xffffu;
    sum >>= 16u;

    if (sum > sum2) {
        sum = sum2;
        t1 = t2;
    }

    *s += sum;
    return t1;
}
#endif

inline static int
count_bit_noESC_from2_altivec1(const int *ix, const int *end, int max, unsigned int *s)
{
    int t1 = huf_tbl_noESC[max - 1];
    /* No ESC-words */
    unsigned int sum = 0;
    int sum1, sum2;
    const unsigned int xlen = 3;
    const unsigned int *table = table23;
    vector signed int v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16;
    vector signed int vx1,vx2,vx3,vx4,vx5,vx6,vxlen,vzero,vsum1,vsum2;
    vector unsigned char vmask,vperm1,vperm2,vx;
    vector unsigned char vhlen1,vhlen2;
    vector signed char vs1,vs2;
    
    vhlen1 = (vector unsigned char)VINIT16(1,4,7,4,5,7,6,7,8,0,0,0,0,0,0,0);
    vhlen2 = (vector unsigned char)VINIT16(2,3,7,4,4,7,6,7,8,0,0,0,0,0,0,0);
    vperm1 = (vector unsigned char)VINIT16(0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27);
    vperm2 = (vector unsigned char)VINIT16(4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31);
    vxlen = vec_splat_s32(3);
    vzero = vec_xor(vzero,vzero);
    vsum1 = vec_xor(vsum1,vsum1);
    vsum2 = vec_xor(vsum2,vsum2);
    
    if((int)(end - ix) < 32) goto normal;
    v0 = vec_ld(0,ix);
    vmask = vec_lvsl(0,ix);
    do {
        v1 = vec_ld(16,ix);
        v2 = vec_ld(32,ix);
        v3 = vec_ld(48,ix);
        v4 = vec_ld(64,ix);
        v5 = vec_ld(80,ix);
        v6 = vec_ld(96,ix);
        v7 = vec_ld(112,ix);
        v8 = vec_ld(128,ix);
        v9 = vec_perm(v0,v1,vmask);
        v10 = vec_perm(v1,v2,vmask);
        v11 = vec_perm(v2,v3,vmask);
        v12 = vec_perm(v3,v4,vmask);
        v13 = vec_perm(v4,v5,vmask);
        v14 = vec_perm(v5,v6,vmask);
        v15 = vec_perm(v6,v7,vmask);
        v16 = vec_perm(v7,v8,vmask);
        v0 = v8;
        v1 = vec_perm(v9,v10,vperm1);
        v2 = vec_perm(v9,v10,vperm2);
        v3 = vec_perm(v11,v12,vperm1);
        v4 = vec_perm(v11,v12,vperm2);
        v5 = vec_perm(v13,v14,vperm1);
        v6 = vec_perm(v13,v14,vperm2);
        v7 = vec_perm(v15,v16,vperm1);
        v8 = vec_perm(v15,v16,vperm2);
        vx1 = (vector signed int)vec_mladd((vector unsigned short)v1,(vector unsigned short)vxlen,(vector unsigned short)v2);
        vx2 = (vector signed int)vec_mladd((vector unsigned short)v3,(vector unsigned short)vxlen,(vector unsigned short)v4);
        vx3 = (vector signed int)vec_pack(vx1,vx2);
        vx4 = (vector signed int)vec_mladd((vector unsigned short)v5,(vector unsigned short)vxlen,(vector unsigned short)v6);
        vx5 = (vector signed int)vec_mladd((vector unsigned short)v7,(vector unsigned short)vxlen,(vector unsigned short)v8);
        vx6 = (vector signed int)vec_pack(vx4,vx5);
        vx = (vector unsigned char)vec_pack((vector unsigned short)vx3,(vector unsigned short)vx6);
        
        vs1 = (vector signed char)vec_perm(vhlen1,vhlen1,vx);
        vs2 = (vector signed char)vec_perm(vhlen2,vhlen2,vx);
        
        vsum1 = vec_sum4s(vs1,vsum1);
        vsum2 = vec_sum4s(vs2,vsum2);
        
        ix += 32;
    } while(ix < end-31);
    
    vsum1 = vec_sums(vsum1,vzero);
    vsum2 = vec_sums(vsum2,vzero);
    
    vsum1 = vec_perm(vsum1,vsum1,vec_lvsr(4,&sum1));
    vsum2 = vec_perm(vsum2,vsum2,vec_lvsr(4,&sum2));
    vec_ste(vsum1,0,&sum1);
    vec_ste(vsum2,0,&sum2);
    
    while (ix < end) {
        unsigned int const x0 = *ix++;
        unsigned int const x1 = *ix++;
        sum += table[ x0 * xlen + x1 ];
    }
    
    sum2 += sum & 0xffffu;
    sum = (sum>>16u) + sum1;
    
    goto end;
    
normal:
    do {
        unsigned int const x0 = *ix++;
        unsigned int const x1 = *ix++;
        sum += table[ x0 * xlen + x1 ];
    } while (ix < end);

    sum2 = sum & 0xffffu;
    sum >>= 16u;

end:
    if (sum > sum2) {
        sum = sum2;
        t1++;
    }

    *s += sum;
    return t1;
}

inline static int
count_bit_noESC_from2_altivec2(const int *ix, const int *end, int max, unsigned int *s)
{
    int t1 = huf_tbl_noESC[max - 1];
    /* No ESC-words */
    unsigned int sum = 0;
    int sum1, sum2;
    const unsigned int xlen = 4;
    const unsigned int *table = table56;
    vector signed int v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16;
    vector signed int vx1,vx2,vx3,vx4,vx5,vx6,vxlen,vzero,vsum1,vsum2;
    vector unsigned char vmask,vperm1,vperm2,vx;
    vector unsigned char vhlen1,vhlen2;
    vector signed char vs1,vs2;
    
    vhlen1 = (vector unsigned char)VINIT16(1,4,7,8,4,5,8,9,7,8,9,10,8,8,9,10);
    vhlen2 = (vector unsigned char)VINIT16(3,4,6,8,4,4,6,7,5,6,7,8,7,7,8,9);
    vperm1 = (vector unsigned char)VINIT16(0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27);
    vperm2 = (vector unsigned char)VINIT16(4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31);
    vxlen = vec_splat_s32(4);
    vzero = vec_xor(vzero,vzero);
    vsum1 = vec_xor(vsum1,vsum1);
    vsum2 = vec_xor(vsum2,vsum2);
    
    if((int)(end - ix) < 32) goto normal;
    v0 = vec_ld(0,ix);
    vmask = vec_lvsl(0,ix);
    do {
        v1 = vec_ld(16,ix);
        v2 = vec_ld(32,ix);
        v3 = vec_ld(48,ix);
        v4 = vec_ld(64,ix);
        v5 = vec_ld(80,ix);
        v6 = vec_ld(96,ix);
        v7 = vec_ld(112,ix);
        v8 = vec_ld(128,ix);
        v9 = vec_perm(v0,v1,vmask);
        v10 = vec_perm(v1,v2,vmask);
        v11 = vec_perm(v2,v3,vmask);
        v12 = vec_perm(v3,v4,vmask);
        v13 = vec_perm(v4,v5,vmask);
        v14 = vec_perm(v5,v6,vmask);
        v15 = vec_perm(v6,v7,vmask);
        v16 = vec_perm(v7,v8,vmask);
        v0 = v8;
        v1 = vec_perm(v9,v10,vperm1);
        v2 = vec_perm(v9,v10,vperm2);
        v3 = vec_perm(v11,v12,vperm1);
        v4 = vec_perm(v11,v12,vperm2);
        v5 = vec_perm(v13,v14,vperm1);
        v6 = vec_perm(v13,v14,vperm2);
        v7 = vec_perm(v15,v16,vperm1);
        v8 = vec_perm(v15,v16,vperm2);
        
        vx1 = (vector signed int)vec_mladd((vector unsigned short)v1,(vector unsigned short)vxlen,(vector unsigned short)v2);
        vx2 = (vector signed int)vec_mladd((vector unsigned short)v3,(vector unsigned short)vxlen,(vector unsigned short)v4);
        vx3 = (vector signed int)vec_pack(vx1,vx2);
        vx4 = (vector signed int)vec_mladd((vector unsigned short)v5,(vector unsigned short)vxlen,(vector unsigned short)v6);
        vx5 = (vector signed int)vec_mladd((vector unsigned short)v7,(vector unsigned short)vxlen,(vector unsigned short)v8);
        vx6 = (vector signed int)vec_pack(vx4,vx5);
        vx = (vector unsigned char)vec_pack((vector unsigned short)vx3,(vector unsigned short)vx6);
        
        vs1 = (vector signed char)vec_perm(vhlen1,vhlen1,vx);
        vs2 = (vector signed char)vec_perm(vhlen2,vhlen2,vx);
        
        vsum1 = vec_sum4s(vs1,vsum1);
        vsum2 = vec_sum4s(vs2,vsum2);
        
        ix += 32;
    } while(ix < end-31);
    
    vsum1 = vec_sums(vsum1,vzero);
    vsum2 = vec_sums(vsum2,vzero);
    
    vsum1 = vec_perm(vsum1,vsum1,vec_lvsr(4,&sum1));
    vsum2 = vec_perm(vsum2,vsum2,vec_lvsr(4,&sum2));
    vec_ste(vsum1,0,&sum1);
    vec_ste(vsum2,0,&sum2);

    while (ix < end) {
        unsigned int const x0 = *ix++;
        unsigned int const x1 = *ix++;
        sum += table[ x0 * xlen + x1 ];
    }
    
    sum2 += sum & 0xffffu;
    sum = (sum>>16u) + sum1;
    
    goto end;
    
normal:
    do {
        unsigned int const x0 = *ix++;
        unsigned int const x1 = *ix++;
        sum += table[ x0 * xlen + x1 ];
    } while (ix < end);

    sum2 = sum & 0xffffu;
    sum >>= 16u;

end:
    if (sum > sum2) {
        sum = sum2;
        t1++;
    }

    *s += sum;
    return t1;
}

inline static int
count_bit_noESC_from3_altivec1(const int *ix, const int *const end, int max, unsigned int *s)
{
    int t1 = huf_tbl_noESC[max - 1];
    /* No ESC-words */
    unsigned int sum1 = 0;
    unsigned int sum2 = 0;
    unsigned int sum3 = 0;
    const unsigned int xlen = 6;
    const uint8_t *const hlen1 = ht[7].hlen;
    const uint8_t *const hlen2 = ht[8].hlen;
    const uint8_t *const hlen3 = ht[9].hlen;
    int     t;
    vector signed int v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16;
    vector signed int vx1,vx2,vx3,vx4,vx5,vx6,vxlen,vzero,vsum1,vsum2,vsum3;
    vector unsigned char vmask,vperm1,vperm2,vx,v31;
    vector unsigned char vhlen11,vhlen12,vhlen13,vhlen21,vhlen22,vhlen23,vhlen31,vhlen32,vhlen33;
    vector signed char vs1,vs2,vs3;
    
    vhlen11 = (vector unsigned char)VINIT16(1,4,7,9,9,10,4,6,8,9,9,10,7,7,9,10);
    vhlen12 = (vector unsigned char)VINIT16(10,11,8,9,10,11,11,11,8,9,10,11,11,12,9,10);
    vhlen13 = (vector unsigned char)VINIT16(11,12,12,12,0,0,0,0,0,0,0,0,0,0,0,0);
    vhlen21 = (vector unsigned char)VINIT16(2,4,7,9,9,10,4,4,6,10,10,10,7,6,8,10);
    vhlen22 = (vector unsigned char)VINIT16(10,11,9,10,10,11,11,12,9,9,10,11,12,12,10,10);
    vhlen23 = (vector unsigned char)VINIT16(11,11,13,13,0,0,0,0,0,0,0,0,0,0,0,0);
    vhlen31 = (vector unsigned char)VINIT16(3,4,6,7,9,10,4,5,6,7,8,10,5,6,7,8);
    vhlen32 = (vector unsigned char)VINIT16(9,10,7,7,8,9,9,10,8,8,9,9,10,11,9,9);
    vhlen33 = (vector unsigned char)VINIT16(10,10,11,11,0,0,0,0,0,0,0,0,0,0,0,0);
    vperm1 = (vector unsigned char)VINIT16(0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27);
    vperm2 = (vector unsigned char)VINIT16(4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31);
    v31 = (vector unsigned char)VINIT16ALL(31);
    vxlen = vec_splat_s32(6);
    vzero = vec_xor(vzero,vzero);
    vsum1 = vec_xor(vsum1,vsum1);
    vsum2 = vec_xor(vsum2,vsum2);
    vsum3 = vec_xor(vsum3,vsum3);
    
    if((int)(end - ix) < 32) goto normal;
    //int *end2 = ix + 32*((int)(end - ix)/32);
    v0 = vec_ld(0,ix);
    vmask = vec_lvsl(0,ix);
    do {
        v1 = vec_ld(16,ix);
        v2 = vec_ld(32,ix);
        v3 = vec_ld(48,ix);
        v4 = vec_ld(64,ix);
        v5 = vec_ld(80,ix);
        v6 = vec_ld(96,ix);
        v7 = vec_ld(112,ix);
        v8 = vec_ld(128,ix);
        v9 = vec_perm(v0,v1,vmask);
        v10 = vec_perm(v1,v2,vmask);
        v11 = vec_perm(v2,v3,vmask);
        v12 = vec_perm(v3,v4,vmask);
        v13 = vec_perm(v4,v5,vmask);
        v14 = vec_perm(v5,v6,vmask);
        v15 = vec_perm(v6,v7,vmask);
        v16 = vec_perm(v7,v8,vmask);
        v0 = v8;
        v1 = vec_perm(v9,v10,vperm1);
        v2 = vec_perm(v9,v10,vperm2);
        v3 = vec_perm(v11,v12,vperm1);
        v4 = vec_perm(v11,v12,vperm2);
        v5 = vec_perm(v13,v14,vperm1);
        v6 = vec_perm(v13,v14,vperm2);
        v7 = vec_perm(v15,v16,vperm1);
        v8 = vec_perm(v15,v16,vperm2);
        vx1 = (vector signed int)vec_mladd((vector unsigned short)v1,(vector unsigned short)vxlen,(vector unsigned short)v2);
        vx2 = (vector signed int)vec_mladd((vector unsigned short)v3,(vector unsigned short)vxlen,(vector unsigned short)v4);
        vx3 = (vector signed int)vec_pack(vx1,vx2);
        vx4 = (vector signed int)vec_mladd((vector unsigned short)v5,(vector unsigned short)vxlen,(vector unsigned short)v6);
        vx5 = (vector signed int)vec_mladd((vector unsigned short)v7,(vector unsigned short)vxlen,(vector unsigned short)v8);
        vx6 = (vector signed int)vec_pack(vx4,vx5);
        vx = (vector unsigned char)vec_pack((vector unsigned short)vx3,(vector unsigned short)vx6);
        
        v1 = (vector signed int)vec_perm(vhlen11,vhlen12,vx);
        v2 = (vector signed int)vec_perm(vhlen13,vhlen13,vx);
        v3 = (vector signed int)vec_perm(vhlen21,vhlen22,vx);
        v4 = (vector signed int)vec_perm(vhlen23,vhlen23,vx);
        v5 = (vector signed int)vec_perm(vhlen31,vhlen32,vx);
        v6 = (vector signed int)vec_perm(vhlen33,vhlen33,vx);
        v7 = (vector signed int)vec_cmpgt(vx,v31);
        vs1 = (vector signed char)vec_sel(v1,v2,(vector unsigned int)v7);
        vs2 = (vector signed char)vec_sel(v3,v4,(vector unsigned int)v7);
        vs3 = (vector signed char)vec_sel(v5,v6,(vector unsigned int)v7);
        
        vsum1 = vec_sum4s(vs1,vsum1);
        vsum2 = vec_sum4s(vs2,vsum2);
        vsum3 = vec_sum4s(vs3,vsum3);
        
        ix += 32;
    } while(ix < end-31);
    
    vsum1 = vec_sums(vsum1,vzero);
    vsum2 = vec_sums(vsum2,vzero);
    vsum3 = vec_sums(vsum3,vzero);
    
    vsum1 = vec_perm(vsum1,vsum1,vec_lvsr(4,&sum1));
    vsum2 = vec_perm(vsum2,vsum2,vec_lvsr(4,&sum2));
    vsum3 = vec_perm(vsum3,vsum3,vec_lvsr(4,&sum3));
    vec_ste(vsum1,0,(signed int *)&sum1);
    vec_ste(vsum2,0,(signed int *)&sum2);
    vec_ste(vsum3,0,(signed int *)&sum3);
    
    while (ix < end) {
        int x = ix[0] * xlen + ix[1];
        ix += 2;
        sum1 += hlen1[x];
        sum2 += hlen2[x];
        sum3 += hlen3[x];
    }
    goto end;
    
  normal:
    
    do {
        int x = ix[0] * xlen + ix[1];
        ix += 2;
        sum1 += hlen1[x];
        sum2 += hlen2[x];
        sum3 += hlen3[x];
    } while (ix < end);
    
  end:
    
    t = t1;
    if (sum1 > sum2) {
        sum1 = sum2;
        t++;
    }
    if (sum1 > sum3) {
        sum1 = sum3;
        t = t1+2;
    }
    *s += sum1;
    
    return t;
}

inline static int
count_bit_noESC_from3_altivec2(const int *ix, const int *const end, int max, unsigned int *s)
{
    int t1 = huf_tbl_noESC[max - 1];
    /* No ESC-words */
    unsigned int sum1 = 0;
    unsigned int sum2 = 0;
    unsigned int sum3 = 0;
    const unsigned int xlen = 8;
    const uint8_t *const hlen1 = ht[10].hlen;
    const uint8_t *const hlen2 = ht[11].hlen;
    const uint8_t *const hlen3 = ht[12].hlen;
    int     t;
    vector signed int v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16;
    vector signed int vx1,vx2,vx3,vx4,vx5,vx6,vxlen,vzero,vsum1,vsum2,vsum3;
    vector unsigned char vmask,vperm1,vperm2,vx,v31;
    vector unsigned char vhlen11,vhlen12,vhlen13,vhlen14,vhlen21,vhlen22,vhlen23,vhlen24,vhlen31,vhlen32,vhlen33,vhlen34;
    vector signed char vs1,vs2,vs3;
    
    vhlen11 = (vector unsigned char)VINIT16( 1,  4,  7,  9, 10, 10, 10, 11, 4,  6,  8,  9, 10, 11, 10, 10);
    vhlen12 = (vector unsigned char)VINIT16( 7,  8,  9, 10, 11, 12, 11, 11, 8,  9, 10, 11, 12, 12, 11, 12);
    vhlen13 = (vector unsigned char)VINIT16( 9, 10, 11, 12, 12, 12, 12, 12,10, 11, 12, 12, 13, 13, 12, 13);
    vhlen14 = (vector unsigned char)VINIT16( 9, 10, 11, 12, 12, 12, 13, 13,10, 10, 11, 12, 12, 13, 13, 13);
    vhlen21 = (vector unsigned char)VINIT16( 2,  4,  6,  8,  9, 10,  9, 10, 4,  5,  6,  8, 10, 10,  9, 10);
    vhlen22 = (vector unsigned char)VINIT16( 6,  7,  8,  9, 10, 11, 10, 10, 8,  8,  9, 11, 10, 12, 10, 11);
    vhlen23 = (vector unsigned char)VINIT16( 9, 10, 10, 11, 11, 12, 11, 12, 9, 10, 11, 12, 12, 13, 12, 13);
    vhlen24 = (vector unsigned char)VINIT16( 9,  9,  9, 10, 11, 12, 12, 12, 9,  9, 10, 11, 12, 12, 12, 12);
    vhlen31 = (vector unsigned char)VINIT16( 4,  4,  6,  8,  9, 10, 10, 10, 4,  5,  6,  7,  9,  9, 10, 10);
    vhlen32 = (vector unsigned char)VINIT16( 6,  6,  7,  8,  9, 10,  9, 10, 7,  7,  8,  8,  9, 10, 10, 10);
    vhlen33 = (vector unsigned char)VINIT16( 8,  8,  9,  9, 10, 10, 10, 11, 9,  9, 10, 10, 10, 11, 10, 11);
    vhlen34 = (vector unsigned char)VINIT16( 9,  9,  9, 10, 10, 11, 11, 12,10, 10, 10, 11, 11, 11, 11, 12);
    vperm1 = (vector unsigned char)VINIT16(0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27);
    vperm2 = (vector unsigned char)VINIT16(4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31);
    v31 = (vector unsigned char)VINIT16ALL(31);
    vxlen = vec_splat_s32(8);
    vzero = vec_xor(vzero,vzero);
    vsum1 = vec_xor(vsum1,vsum1);
    vsum2 = vec_xor(vsum2,vsum2);
    vsum3 = vec_xor(vsum3,vsum3);
    
    if((int)(end - ix) < 32) goto normal;
    //int *end2 = ix + 32*((int)(end - ix)/32);
    v0 = vec_ld(0,ix);
    vmask = vec_lvsl(0,ix);
    do {
        v1 = vec_ld(16,ix);
        v2 = vec_ld(32,ix);
        v3 = vec_ld(48,ix);
        v4 = vec_ld(64,ix);
        v5 = vec_ld(80,ix);
        v6 = vec_ld(96,ix);
        v7 = vec_ld(112,ix);
        v8 = vec_ld(128,ix);
        v9 = vec_perm(v0,v1,vmask);
        v10 = vec_perm(v1,v2,vmask);
        v11 = vec_perm(v2,v3,vmask);
        v12 = vec_perm(v3,v4,vmask);
        v13 = vec_perm(v4,v5,vmask);
        v14 = vec_perm(v5,v6,vmask);
        v15 = vec_perm(v6,v7,vmask);
        v16 = vec_perm(v7,v8,vmask);
        v0 = v8;
        v1 = vec_perm(v9,v10,vperm1);
        v2 = vec_perm(v9,v10,vperm2);
        v3 = vec_perm(v11,v12,vperm1);
        v4 = vec_perm(v11,v12,vperm2);
        v5 = vec_perm(v13,v14,vperm1);
        v6 = vec_perm(v13,v14,vperm2);
        v7 = vec_perm(v15,v16,vperm1);
        v8 = vec_perm(v15,v16,vperm2);
        
        vx1 = (vector signed int)vec_mladd((vector unsigned short)v1,(vector unsigned short)vxlen,(vector unsigned short)v2);
        vx2 = (vector signed int)vec_mladd((vector unsigned short)v3,(vector unsigned short)vxlen,(vector unsigned short)v4);
        vx3 = (vector signed int)vec_pack(vx1,vx2);
        vx4 = (vector signed int)vec_mladd((vector unsigned short)v5,(vector unsigned short)vxlen,(vector unsigned short)v6);
        vx5 = (vector signed int)vec_mladd((vector unsigned short)v7,(vector unsigned short)vxlen,(vector unsigned short)v8);
        vx6 = (vector signed int)vec_pack(vx4,vx5);
        vx = (vector unsigned char)vec_pack((vector unsigned short)vx3,(vector unsigned short)vx6);
        
        v1 = (vector signed int)vec_perm(vhlen11,vhlen12,vx);
        v2 = (vector signed int)vec_perm(vhlen13,vhlen14,vx);
        v3 = (vector signed int)vec_perm(vhlen21,vhlen22,vx);
        v4 = (vector signed int)vec_perm(vhlen23,vhlen24,vx);
        v5 = (vector signed int)vec_perm(vhlen31,vhlen32,vx);
        v6 = (vector signed int)vec_perm(vhlen33,vhlen34,vx);
        v7 = (vector signed int)vec_cmpgt(vx,v31);
        vs1 = (vector signed char)vec_sel(v1,v2,(vector unsigned int)v7);
        vs2 = (vector signed char)vec_sel(v3,v4,(vector unsigned int)v7);
        vs3 = (vector signed char)vec_sel(v5,v6,(vector unsigned int)v7);
        
        vsum1 = vec_sum4s(vs1,vsum1);
        vsum2 = vec_sum4s(vs2,vsum2);
        vsum3 = vec_sum4s(vs3,vsum3);
        
        ix += 32;
    } while(ix < end-31);
    
    vsum1 = vec_sums(vsum1,vzero);
    vsum2 = vec_sums(vsum2,vzero);
    vsum3 = vec_sums(vsum3,vzero);
    
    vsum1 = vec_perm(vsum1,vsum1,vec_lvsr(4,&sum1));
    vsum2 = vec_perm(vsum2,vsum2,vec_lvsr(4,&sum2));
    vsum3 = vec_perm(vsum3,vsum3,vec_lvsr(4,&sum3));
    vec_ste(vsum1,0,(signed int *)&sum1);
    vec_ste(vsum2,0,(signed int *)&sum2);
    vec_ste(vsum3,0,(signed int *)&sum3);
    
    while (ix < end) {
        int x = ix[0] * xlen + ix[1];
        ix += 2;
        sum1 += hlen1[x];
        sum2 += hlen2[x];
        sum3 += hlen3[x];
    }
    goto end;
    
  normal:
    
    do {
        int x = ix[0] * xlen + ix[1];
        ix += 2;
        sum1 += hlen1[x];
        sum2 += hlen2[x];
        sum3 += hlen3[x];
    } while (ix < end);
    
  end:
    
    t = t1;
    if (sum1 > sum2) {
        sum1 = sum2;
        t++;
    }
    if (sum1 > sum3) {
        sum1 = sum3;
        t = t1+2;
    }
    *s += sum1;
    
    return t;
}
#endif

/*************************************************************************/
/*	      choose table						 */
/*************************************************************************/

/*
  Choose the Huffman table that will encode ix[begin..end] with
  the fewest bits.

  Note: This code contains knowledge about the sizes and characteristics
  of the Huffman tables as defined in the IS (Table B.7), and will not work
  with any arbitrary tables.
*/
static int count_bit_null(const int* ix, const int* end, int max, unsigned int* s)
{
    (void) ix;
    (void) end;
    (void) max;
    (void) s;
    return 0;
}

typedef int (*count_fnc)(const int* ix, const int* end, int max, unsigned int* s);
  
static const count_fnc count_fncs[] = 
{ &count_bit_null
, &count_bit_noESC
#if __ALTIVEC__
, &count_bit_noESC_from2_altivec1
, &count_bit_noESC_from2_altivec2
, &count_bit_noESC_from3_altivec1
, &count_bit_noESC_from3_altivec1
, &count_bit_noESC_from3_altivec2
, &count_bit_noESC_from3_altivec2
#else
, &count_bit_noESC_from2
, &count_bit_noESC_from2
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
#endif
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
, &count_bit_noESC_from3
};

static int
choose_table_nonMMX(const int *ix, const int *const end, int *const _s)
{
    unsigned int* s = (unsigned int*)_s;
    unsigned int  max;
    int     choice, choice2;
#if __ALTIVEC__
    max = ix_max_vec(ix, end);
#else
    max = ix_max(ix, end);
#endif

    if (max <= 15) {
      return count_fncs[max](ix, end, max, s);
    }
    /* try tables with linbits */
    if (max > IXMAX_VAL) {
        *s = LARGE_BITS;
        return -1;
    }
    max -= 15u;
    for (choice2 = 24; choice2 < 32; choice2++) {
        if (ht[choice2].linmax >= max) {
            break;
        }
    }

    for (choice = choice2 - 8; choice < 24; choice++) {
        if (ht[choice].linmax >= max) {
            break;
        }
    }
#if defined(__ALTIVEC__) && defined(_ARCH_PPC64)
    return count_bit_ESC_altivec(ix, end, choice, choice2, s);
#else
    return count_bit_ESC(ix, end, choice, choice2, s);
#endif
}



/*************************************************************************/
/*	      count_bit							 */
/*************************************************************************/
int
noquant_count_bits(lame_internal_flags const *const gfc,
                   gr_info * const gi, calc_noise_data * prev_noise)
{
    SessionConfig_t const *const cfg = &gfc->cfg;
    int     bits = 0;
    int     i, a1, a2;
    int const *const ix = gi->l3_enc;

    i = Min(576, ((gi->max_nonzero_coeff + 2) >> 1) << 1);

    if (prev_noise)
        prev_noise->sfb_count1 = 0;

    /* Determine count1 region */
    for (; i > 1; i -= 2)
        if (ix[i - 1] | ix[i - 2])
            break;
    gi->count1 = i;

    /* Determines the number of bits to encode the quadruples. */
    a1 = a2 = 0;
    for (; i > 3; i -= 4) {
        int x4 = ix[i-4];
        int x3 = ix[i-3];
        int x2 = ix[i-2];
        int x1 = ix[i-1];
        int     p;
        /* hack to check if all values <= 1 */
        if ((unsigned int) (x4 | x3 | x2 | x1) > 1)
            break;

        p = ((x4 * 2 + x3) * 2 + x2) * 2 + x1;
        a1 += t32l[p];
        a2 += t33l[p];
    }

    bits = a1;
    gi->count1table_select = 0;
    if (a1 > a2) {
        bits = a2;
        gi->count1table_select = 1;
    }

    gi->count1bits = bits;
    gi->big_values = i;
    if (i == 0)
        return bits;

    if (gi->block_type == SHORT_TYPE) {
        a1 = 3 * gfc->scalefac_band.s[3];
        if (a1 > gi->big_values)
            a1 = gi->big_values;
        a2 = gi->big_values;

    }
    else if (gi->block_type == NORM_TYPE) {
        assert(i <= 576); /* bv_scf has 576 entries (0..575) */
        a1 = gi->region0_count = gfc->sv_qnt.bv_scf[i - 2];
        a2 = gi->region1_count = gfc->sv_qnt.bv_scf[i - 1];

        assert(a1 + a2 + 2 < SBPSY_l);
        a2 = gfc->scalefac_band.l[a1 + a2 + 2];
        a1 = gfc->scalefac_band.l[a1 + 1];
        if (a2 < i)
            gi->table_select[2] = gfc->choose_table(ix + a2, ix + i, &bits);

    }
    else {
        gi->region0_count = 7;
        /*gi->region1_count = SBPSY_l - 7 - 1; */
        gi->region1_count = SBMAX_l - 1 - 7 - 1;
        a1 = gfc->scalefac_band.l[7 + 1];
        a2 = i;
        if (a1 > a2) {
            a1 = a2;
        }
    }


    /* have to allow for the case when bigvalues < region0 < region1 */
    /* (and region0, region1 are ignored) */
    a1 = Min(a1, i);
    a2 = Min(a2, i);

    assert(a1 >= 0);
    assert(a2 >= 0);

    /* Count the number of bits necessary to code the bigvalues region. */
    if (0 < a1)
        gi->table_select[0] = gfc->choose_table(ix, ix + a1, &bits);
    if (a1 < a2)
        gi->table_select[1] = gfc->choose_table(ix + a1, ix + a2, &bits);
    if (cfg->use_best_huffman == 2) {
        gi->part2_3_length = bits;
        best_huffman_divide(gfc, gi);
        bits = gi->part2_3_length;
    }


    if (prev_noise) {
        if (gi->block_type == NORM_TYPE) {
            int     sfb = 0;
            while (gfc->scalefac_band.l[sfb] < gi->big_values) {
                sfb++;
            }
            prev_noise->sfb_count1 = sfb;
        }
    }

    return bits;
}

int
count_bits(lame_internal_flags const *const gfc,
           const FLOAT * const xr, gr_info * const gi, calc_noise_data * prev_noise)
{
    int    *const ix = gi->l3_enc;

    /* since quantize_xrpow uses table lookup, we need to check this first: */
    FLOAT const w = (IXMAX_VAL) / IPOW20(gi->global_gain);

    if (gi->xrpow_max > w)
        return LARGE_BITS;

    quantize_xrpow(xr, ix, IPOW20(gi->global_gain), gi, prev_noise);

    if (gfc->sv_qnt.substep_shaping & 2) {
        int     sfb, j = 0;
        /* 0.634521682242439 = 0.5946*2**(.5*0.1875) */
        int const gain = gi->global_gain + gi->scalefac_scale;
        const FLOAT roundfac = 0.634521682242439 / IPOW20(gain);
        for (sfb = 0; sfb < gi->sfbmax; sfb++) {
            int const width = gi->width[sfb];
            assert(width >= 0);
            if (!gfc->sv_qnt.pseudohalf[sfb]) {
                j += width;
            }
            else {
                int     k;
                for (k = j, j += width; k < j; ++k) {
                    ix[k] = (xr[k] >= roundfac) ? ix[k] : 0;
                }
            }
        }
    }
    return noquant_count_bits(gfc, gi, prev_noise);
}

/***********************************************************************
  re-calculate the best scalefac_compress using scfsi
  the saved bits are kept in the bit reservoir.
 **********************************************************************/


inline static void
recalc_divide_init(const lame_internal_flags * const gfc,
                   gr_info const *cod_info,
                   int const *const ix, int r01_bits[], int r01_div[], int r0_tbl[], int r1_tbl[])
{
    int     r0, r1, bigv, r0t, r1t, bits;

    bigv = cod_info->big_values;

    for (r0 = 0; r0 <= 7 + 15; r0++) {
        r01_bits[r0] = LARGE_BITS;
    }

    for (r0 = 0; r0 < 16; r0++) {
        int const a1 = gfc->scalefac_band.l[r0 + 1];
        int     r0bits;
        if (a1 >= bigv)
            break;
        r0bits = 0;
        r0t = gfc->choose_table(ix, ix + a1, &r0bits);

        for (r1 = 0; r1 < 8; r1++) {
            int const a2 = gfc->scalefac_band.l[r0 + r1 + 2];
            if (a2 >= bigv)
                break;

            bits = r0bits;
            r1t = gfc->choose_table(ix + a1, ix + a2, &bits);
            if (r01_bits[r0 + r1] > bits) {
                r01_bits[r0 + r1] = bits;
                r01_div[r0 + r1] = r0;
                r0_tbl[r0 + r1] = r0t;
                r1_tbl[r0 + r1] = r1t;
            }
        }
    }
}

inline static void
recalc_divide_sub(const lame_internal_flags * const gfc,
                  const gr_info * cod_info2,
                  gr_info * const gi,
                  const int *const ix,
                  const int r01_bits[], const int r01_div[], const int r0_tbl[], const int r1_tbl[])
{
    int     bits, r2, a2, bigv, r2t;

    bigv = cod_info2->big_values;

    for (r2 = 2; r2 < SBMAX_l + 1; r2++) {
        a2 = gfc->scalefac_band.l[r2];
        if (a2 >= bigv)
            break;

        bits = r01_bits[r2 - 2] + cod_info2->count1bits;
        if (gi->part2_3_length <= bits)
            break;

        r2t = gfc->choose_table(ix + a2, ix + bigv, &bits);
        if (gi->part2_3_length <= bits)
            continue;

        memcpy(gi, cod_info2, sizeof(gr_info));
        gi->part2_3_length = bits;
        gi->region0_count = r01_div[r2 - 2];
        gi->region1_count = r2 - 2 - r01_div[r2 - 2];
        gi->table_select[0] = r0_tbl[r2 - 2];
        gi->table_select[1] = r1_tbl[r2 - 2];
        gi->table_select[2] = r2t;
    }
}




void
best_huffman_divide(const lame_internal_flags * const gfc, gr_info * const gi)
{
    SessionConfig_t const *const cfg = &gfc->cfg;
    int     i, a1, a2;
    gr_info cod_info2;
    int const *const ix = gi->l3_enc;

    int     r01_bits[7 + 15 + 1];
    int     r01_div[7 + 15 + 1];
    int     r0_tbl[7 + 15 + 1];
    int     r1_tbl[7 + 15 + 1];


    /* SHORT BLOCK stuff fails for MPEG2 */
    if (gi->block_type == SHORT_TYPE && cfg->mode_gr == 1)
        return;


    memcpy(&cod_info2, gi, sizeof(gr_info));
    if (gi->block_type == NORM_TYPE) {
        recalc_divide_init(gfc, gi, ix, r01_bits, r01_div, r0_tbl, r1_tbl);
        recalc_divide_sub(gfc, &cod_info2, gi, ix, r01_bits, r01_div, r0_tbl, r1_tbl);
    }

    i = cod_info2.big_values;
    if (i == 0 || (unsigned int) (ix[i - 2] | ix[i - 1]) > 1)
        return;

    i = gi->count1 + 2;
    if (i > 576)
        return;

    /* Determines the number of bits to encode the quadruples. */
    memcpy(&cod_info2, gi, sizeof(gr_info));
    cod_info2.count1 = i;
    a1 = a2 = 0;

    assert(i <= 576);

    for (; i > cod_info2.big_values; i -= 4) {
        int const p = ((ix[i - 4] * 2 + ix[i - 3]) * 2 + ix[i - 2]) * 2 + ix[i - 1];
        a1 += t32l[p];
        a2 += t33l[p];
    }
    cod_info2.big_values = i;

    cod_info2.count1table_select = 0;
    if (a1 > a2) {
        a1 = a2;
        cod_info2.count1table_select = 1;
    }

    cod_info2.count1bits = a1;

    if (cod_info2.block_type == NORM_TYPE)
        recalc_divide_sub(gfc, &cod_info2, gi, ix, r01_bits, r01_div, r0_tbl, r1_tbl);
    else {
        /* Count the number of bits necessary to code the bigvalues region. */
        cod_info2.part2_3_length = a1;
        a1 = gfc->scalefac_band.l[7 + 1];
        if (a1 > i) {
            a1 = i;
        }
        if (a1 > 0)
            cod_info2.table_select[0] =
                gfc->choose_table(ix, ix + a1, (int *) &cod_info2.part2_3_length);
        if (i > a1)
            cod_info2.table_select[1] =
                gfc->choose_table(ix + a1, ix + i, (int *) &cod_info2.part2_3_length);
        if (gi->part2_3_length > cod_info2.part2_3_length)
            memcpy(gi, &cod_info2, sizeof(gr_info));
    }
}

static const int slen1_n[16] = { 1, 1, 1, 1, 8, 2, 2, 2, 4, 4, 4, 8, 8, 8, 16, 16 };
static const int slen2_n[16] = { 1, 2, 4, 8, 1, 2, 4, 8, 2, 4, 8, 2, 4, 8, 4, 8 };
const int slen1_tab[16] = { 0, 0, 0, 0, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4 };
const int slen2_tab[16] = { 0, 1, 2, 3, 0, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 3 };

static void
scfsi_calc(int ch, III_side_info_t * l3_side)
{
    unsigned int i;
    int     s1, s2, c1, c2;
    int     sfb;
    gr_info *const gi = &l3_side->tt[1][ch];
    gr_info const *const g0 = &l3_side->tt[0][ch];

    for (i = 0; i < (sizeof(scfsi_band) / sizeof(int)) - 1; i++) {
        for (sfb = scfsi_band[i]; sfb < scfsi_band[i + 1]; sfb++) {
            if (g0->scalefac[sfb] != gi->scalefac[sfb]
                && gi->scalefac[sfb] >= 0)
                break;
        }
        if (sfb == scfsi_band[i + 1]) {
            for (sfb = scfsi_band[i]; sfb < scfsi_band[i + 1]; sfb++) {
                gi->scalefac[sfb] = -1;
            }
            l3_side->scfsi[ch][i] = 1;
        }
    }

    s1 = c1 = 0;
    for (sfb = 0; sfb < 11; sfb++) {
        if (gi->scalefac[sfb] == -1)
            continue;
        c1++;
        if (s1 < gi->scalefac[sfb])
            s1 = gi->scalefac[sfb];
    }

    s2 = c2 = 0;
    for (; sfb < SBPSY_l; sfb++) {
        if (gi->scalefac[sfb] == -1)
            continue;
        c2++;
        if (s2 < gi->scalefac[sfb])
            s2 = gi->scalefac[sfb];
    }

    for (i = 0; i < 16; i++) {
        if (s1 < slen1_n[i] && s2 < slen2_n[i]) {
            int const c = slen1_tab[i] * c1 + slen2_tab[i] * c2;
            if (gi->part2_length > c) {
                gi->part2_length = c;
                gi->scalefac_compress = (int)i;
            }
        }
    }
}

/*
Find the optimal way to store the scalefactors.
Only call this routine after final scalefactors have been
chosen and the channel/granule will not be re-encoded.
 */
void
best_scalefac_store(const lame_internal_flags * gfc,
                    const int gr, const int ch, III_side_info_t * const l3_side)
{
    SessionConfig_t const *const cfg = &gfc->cfg;
    /* use scalefac_scale if we can */
    gr_info *const gi = &l3_side->tt[gr][ch];
    int     sfb, i, j, l;
    int     recalc = 0;

    /* remove scalefacs from bands with ix=0.  This idea comes
     * from the AAC ISO docs.  added mt 3/00 */
    /* check if l3_enc=0 */
    j = 0;
    for (sfb = 0; sfb < gi->sfbmax; sfb++) {
        int const width = gi->width[sfb];
        assert(width >= 0);
        for (l = j, j += width; l < j; ++l) {
            if (gi->l3_enc[l] != 0)
                break;
        }
        if (l == j)
            gi->scalefac[sfb] = recalc = -2; /* anything goes. */
        /*  only best_scalefac_store and calc_scfsi 
         *  know--and only they should know--about the magic number -2. 
         */
    }

    if (!gi->scalefac_scale && !gi->preflag) {
        int     s = 0;
        for (sfb = 0; sfb < gi->sfbmax; sfb++)
            if (gi->scalefac[sfb] > 0)
                s |= gi->scalefac[sfb];

        if (!(s & 1) && s != 0) {
            for (sfb = 0; sfb < gi->sfbmax; sfb++)
                if (gi->scalefac[sfb] > 0)
                    gi->scalefac[sfb] >>= 1;

            gi->scalefac_scale = recalc = 1;
        }
    }

    if (!gi->preflag && gi->block_type != SHORT_TYPE && cfg->mode_gr == 2) {
        for (sfb = 11; sfb < SBPSY_l; sfb++)
            if (gi->scalefac[sfb] < pretab[sfb] && gi->scalefac[sfb] != -2)
                break;
        if (sfb == SBPSY_l) {
            for (sfb = 11; sfb < SBPSY_l; sfb++)
                if (gi->scalefac[sfb] > 0)
                    gi->scalefac[sfb] -= pretab[sfb];

            gi->preflag = recalc = 1;
        }
    }

    for (i = 0; i < 4; i++)
        l3_side->scfsi[ch][i] = 0;

    if (cfg->mode_gr == 2 && gr == 1
        && l3_side->tt[0][ch].block_type != SHORT_TYPE
        && l3_side->tt[1][ch].block_type != SHORT_TYPE) {
        scfsi_calc(ch, l3_side);
        recalc = 0;
    }
    for (sfb = 0; sfb < gi->sfbmax; sfb++) {
        if (gi->scalefac[sfb] == -2) {
            gi->scalefac[sfb] = 0; /* if anything goes, then 0 is a good choice */
        }
    }
    if (recalc) {
        (void) scale_bitcount(gfc, gi);
    }
}


#ifndef NDEBUG
static int
all_scalefactors_not_negative(int const *scalefac, int n)
{
    int     i;
    for (i = 0; i < n; ++i) {
        if (scalefac[i] < 0)
            return 0;
    }
    return 1;
}
#endif


/* number of bits used to encode scalefacs */

/* 18*slen1_tab[i] + 18*slen2_tab[i] */
static const int scale_short[16] = {
    0, 18, 36, 54, 54, 36, 54, 72, 54, 72, 90, 72, 90, 108, 108, 126
};

/* 17*slen1_tab[i] + 18*slen2_tab[i] */
static const int scale_mixed[16] = {
    0, 18, 36, 54, 51, 35, 53, 71, 52, 70, 88, 69, 87, 105, 104, 122
};

/* 11*slen1_tab[i] + 10*slen2_tab[i] */
static const int scale_long[16] = {
    0, 10, 20, 30, 33, 21, 31, 41, 32, 42, 52, 43, 53, 63, 64, 74
};


/*************************************************************************/
/*            scale_bitcount                                             */
/*************************************************************************/

/* Also calculates the number of bits necessary to code the scalefactors. */

static int
mpeg1_scale_bitcount(const lame_internal_flags * gfc, gr_info * const cod_info)
{
    int     k, sfb, max_slen1 = 0, max_slen2 = 0;

    /* maximum values */
    const int *tab;
    int    *const scalefac = cod_info->scalefac;

    (void) gfc;
    assert(all_scalefactors_not_negative(scalefac, cod_info->sfbmax));

    if (cod_info->block_type == SHORT_TYPE) {
        tab = scale_short;
        if (cod_info->mixed_block_flag)
            tab = scale_mixed;
    }
    else {              /* block_type == 1,2,or 3 */
        tab = scale_long;
        if (!cod_info->preflag) {
            for (sfb = 11; sfb < SBPSY_l; sfb++)
                if (scalefac[sfb] < pretab[sfb])
                    break;

            if (sfb == SBPSY_l) {
                cod_info->preflag = 1;
                for (sfb = 11; sfb < SBPSY_l; sfb++)
                    scalefac[sfb] -= pretab[sfb];
            }
        }
    }

    for (sfb = 0; sfb < cod_info->sfbdivide; sfb++)
        if (max_slen1 < scalefac[sfb])
            max_slen1 = scalefac[sfb];

    for (; sfb < cod_info->sfbmax; sfb++)
        if (max_slen2 < scalefac[sfb])
            max_slen2 = scalefac[sfb];

    /* from Takehiro TOMINAGA <tominaga@isoternet.org> 10/99
     * loop over *all* posible values of scalefac_compress to find the
     * one which uses the smallest number of bits.  ISO would stop
     * at first valid index */
    cod_info->part2_length = LARGE_BITS;
    for (k = 0; k < 16; k++) {
        if (max_slen1 < slen1_n[k] && max_slen2 < slen2_n[k]
            && cod_info->part2_length > tab[k]) {
            cod_info->part2_length = tab[k];
            cod_info->scalefac_compress = k;
        }
    }
    return cod_info->part2_length == LARGE_BITS;
}



/*
  table of largest scalefactor values for MPEG2
*/
static const int max_range_sfac_tab[6][4] = {
    {15, 15, 7, 7},
    {15, 15, 7, 0},
    {7, 3, 0, 0},
    {15, 31, 31, 0},
    {7, 7, 7, 0},
    {3, 3, 0, 0}
};




/*************************************************************************/
/*            scale_bitcount_lsf                                         */
/*************************************************************************/

/* Also counts the number of bits to encode the scalefacs but for MPEG 2 */
/* Lower sampling frequencies  (24, 22.05 and 16 kHz.)                   */

/*  This is reverse-engineered from section 2.4.3.2 of the MPEG2 IS,     */
/* "Audio Decoding Layer III"                                            */

static int
mpeg2_scale_bitcount(const lame_internal_flags * gfc, gr_info * const cod_info)
{
    int     table_number, row_in_table, partition, nr_sfb, window, over;
    int     i, sfb, max_sfac[4];
    const int *partition_table;
    int const *const scalefac = cod_info->scalefac;

    /*
       Set partition table. Note that should try to use table one,
       but do not yet...
     */
    if (cod_info->preflag)
        table_number = 2;
    else
        table_number = 0;

    for (i = 0; i < 4; i++)
        max_sfac[i] = 0;

    if (cod_info->block_type == SHORT_TYPE) {
        row_in_table = 1;
        partition_table = &nr_of_sfb_block[table_number][row_in_table][0];
        for (sfb = 0, partition = 0; partition < 4; partition++) {
            nr_sfb = partition_table[partition] / 3;
            for (i = 0; i < nr_sfb; i++, sfb++)
                for (window = 0; window < 3; window++)
                    if (scalefac[sfb * 3 + window] > max_sfac[partition])
                        max_sfac[partition] = scalefac[sfb * 3 + window];
        }
    }
    else {
        row_in_table = 0;
        partition_table = &nr_of_sfb_block[table_number][row_in_table][0];
        for (sfb = 0, partition = 0; partition < 4; partition++) {
            nr_sfb = partition_table[partition];
            for (i = 0; i < nr_sfb; i++, sfb++)
                if (scalefac[sfb] > max_sfac[partition])
                    max_sfac[partition] = scalefac[sfb];
        }
    }

    for (over = 0, partition = 0; partition < 4; partition++) {
        if (max_sfac[partition] > max_range_sfac_tab[table_number][partition])
            over++;
    }
    if (!over) {
        /*
           Since no bands have been over-amplified, we can set scalefac_compress
           and slen[] for the formatter
         */
        static const int log2tab[] = { 0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4 };

        int     slen1, slen2, slen3, slen4;

        cod_info->sfb_partition_table = nr_of_sfb_block[table_number][row_in_table];
        for (partition = 0; partition < 4; partition++)
            cod_info->slen[partition] = log2tab[max_sfac[partition]];

        /* set scalefac_compress */
        slen1 = cod_info->slen[0];
        slen2 = cod_info->slen[1];
        slen3 = cod_info->slen[2];
        slen4 = cod_info->slen[3];

        switch (table_number) {
        case 0:
            cod_info->scalefac_compress = (((slen1 * 5) + slen2) << 4)
                + (slen3 << 2)
                + slen4;
            break;

        case 1:
            cod_info->scalefac_compress = 400 + (((slen1 * 5) + slen2) << 2)
                + slen3;
            break;

        case 2:
            cod_info->scalefac_compress = 500 + (slen1 * 3) + slen2;
            break;

        default:
            ERRORF(gfc, "intensity stereo not implemented yet\n");
            break;
        }
    }
#ifdef DEBUG
    if (over)
        ERRORF(gfc, "---WARNING !! Amplification of some bands over limits\n");
#endif
    if (!over) {
        assert(cod_info->sfb_partition_table);
        cod_info->part2_length = 0;
        for (partition = 0; partition < 4; partition++)
            cod_info->part2_length +=
                cod_info->slen[partition] * cod_info->sfb_partition_table[partition];
    }
    return over;
}


int
scale_bitcount(const lame_internal_flags * gfc, gr_info * cod_info)
{
    if (gfc->cfg.mode_gr == 2) {
        return mpeg1_scale_bitcount(gfc, cod_info);
    }
    else {
        return mpeg2_scale_bitcount(gfc, cod_info);
    }
}


#ifdef MMX_choose_table
extern int choose_table_MMX(const int *ix, const int *const end, int *const s);
#endif

void
huffman_init(lame_internal_flags * const gfc)
{
    int     i;

    gfc->choose_table = choose_table_nonMMX;

#ifdef MMX_choose_table
    if (gfc->CPU_features.MMX) {
        gfc->choose_table = choose_table_MMX;
    }
#endif

    for (i = 2; i <= 576; i += 2) {
        int     scfb_anz = 0, bv_index;
        while (gfc->scalefac_band.l[++scfb_anz] < i);

        bv_index = subdv_table[scfb_anz].region0_count;
        while (gfc->scalefac_band.l[bv_index + 1] > i)
            bv_index--;

        if (bv_index < 0) {
            /* this is an indication that everything is going to
               be encoded as region0:  bigvalues < region0 < region1
               so lets set region0, region1 to some value larger
               than bigvalues */
            bv_index = subdv_table[scfb_anz].region0_count;
        }

        gfc->sv_qnt.bv_scf[i - 2] = bv_index;

        bv_index = subdv_table[scfb_anz].region1_count;
        while (gfc->scalefac_band.l[bv_index + gfc->sv_qnt.bv_scf[i - 2] + 2] > i)
            bv_index--;

        if (bv_index < 0) {
            bv_index = subdv_table[scfb_anz].region1_count;
        }

        gfc->sv_qnt.bv_scf[i - 1] = bv_index;
    }
}
