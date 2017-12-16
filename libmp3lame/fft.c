/*
** FFT and FHT routines
**  Copyright 1988, 1993; Ron Mayer
**      Copyright (c) 1999-2000 Takehiro Tominaga
**
**  fht(fz,n);
**      Does a hartley transform of "n" points in the array "fz".
**
** NOTE: This routine uses at least 2 patented algorithms, and may be
**       under the restrictions of a bunch of different organizations.
**       Although I wrote it completely myself; it is kind of a derivative
**       of a routine I once authored and released under the GPL, so it
**       may fall under the free software foundation's restrictions;
**       it was worked on as a Stanford Univ project, so they claim
**       some rights to it; it was further optimized at work here, so
**       I think this company claims parts of it.  The patents are
**       held by R. Bracewell (the FHT algorithm) and O. Buneman (the
**       trig generator), both at Stanford Univ.
**       If it were up to me, I'd say go do whatever you want with it;
**       but it would be polite to give credit to the following people
**       if you use this anywhere:
**           Euler     - probable inventor of the fourier transform.
**           Gauss     - probable inventor of the FFT.
**           Hartley   - probable inventor of the hartley transform.
**           Buneman   - for a really cool trig generator
**           Mayer(me) - for authoring this particular version and
**                       including all the optimizations in one package.
**       Thanks,
**       Ron Mayer; mayer@acuson.com
** and added some optimization by
**           Mather    - idea of using lookup table
**           Takehiro  - some dirty hack for speed up
*/

/* $Id: fft.c,v 1.39 2017/09/06 15:07:29 robert Exp $ */

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#if __ALTIVEC__
#include <altivec.h>
#endif

#include "lame.h"
#include "machine.h"
#include "encoder.h"
#include "util.h"
#include "fft.h"

#include "vector/lame_intrin.h"



#define TRI_SIZE (5-1)  /* 1024 =  4**5 */

/* fft.c    */

static const FLOAT costab[TRI_SIZE * 2] = {
    9.238795325112867e-01, 3.826834323650898e-01,
    9.951847266721969e-01, 9.801714032956060e-02,
    9.996988186962042e-01, 2.454122852291229e-02,
    9.999811752826011e-01, 6.135884649154475e-03
};

static void
fht(FLOAT * fz, int n)
{
    const FLOAT *tri = costab;
    int     k4;
    FLOAT  *fi, *gi;
    FLOAT const *fn;
#if __ALTIVEC__
    float csvec[16] __attribute__ ((aligned (16)));
    vector float v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16;
    vector float vfi0,vfi1,vfi2,vfi3,vgi0,vgi1,vgi2,vgi3,vf0,vf1,vf2,vf3,vg0,vg1,vg2,vg3;
    vector float vprev1,vprev2,vprev3,vprev4,vc1,vc2,vs1,vs2,vzero;
    vector unsigned char vperm1,vperm2;
    
    vperm1 = (vector unsigned char)VINIT16(16,17,18,19,12,13,14,15,8,9,10,11,4,5,6,7);
    vperm2 = (vector unsigned char)VINIT16(16,17,18,19,4,5,6,7,8,9,10,11,12,13,14,15);
    vzero = vec_xor(vzero,vzero);
#endif

    n <<= 1;            /* to get BLKSIZE, because of 3DNow! ASM routine */
    fn = fz + n;
    k4 = 4;
    do {
        FLOAT   s1, c1;
        int     i, k1, k2, k3, kx;
        kx = k4 >> 1;
        k1 = k4;
        k2 = k4 << 1;
        k3 = k2 + k1;
        k4 = k2 << 1;
        fi = fz;
        gi = fi + kx;
        do {
            FLOAT   f0, f1, f2, f3;
            f1 = fi[0] - fi[k1];
            f0 = fi[0] + fi[k1];
            f3 = fi[k2] - fi[k3];
            f2 = fi[k2] + fi[k3];
            fi[k2] = f0 - f2;
            fi[0] = f0 + f2;
            fi[k3] = f1 - f3;
            fi[k1] = f1 + f3;
            f1 = gi[0] - gi[k1];
            f0 = gi[0] + gi[k1];
            f3 = SQRT2 * gi[k3];
            f2 = SQRT2 * gi[k2];
            gi[k2] = f0 - f2;
            gi[0] = f0 + f2;
            gi[k3] = f1 - f3;
            gi[k1] = f1 + f3;
            gi += k4;
            fi += k4;
        } while (fi < fn);
        c1 = tri[0];
        s1 = tri[1];
#if __ALTIVEC__
        if(kx < 4) {
            for (i = 1; i < kx; i++) {
                FLOAT   c2, s2;
                c2 = 1 - (2 * s1) * s1;
                s2 = (2 * s1) * c1;
                fi = fz + i;
                gi = fz + k1 - i;
                do {
                    FLOAT   a, b, g0, f0, f1, g1, f2, g2, f3, g3;
                    b = s2 * fi[k1] - c2 * gi[k1];
                    a = c2 * fi[k1] + s2 * gi[k1];
                    f1 = fi[0] - a;
                    f0 = fi[0] + a;
                    g1 = gi[0] - b;
                    g0 = gi[0] + b;
                    b = s2 * fi[k3] - c2 * gi[k3];
                    a = c2 * fi[k3] + s2 * gi[k3];
                    f3 = fi[k2] - a;
                    f2 = fi[k2] + a;
                    g3 = gi[k2] - b;
                    g2 = gi[k2] + b;
                    b = s1 * f2 - c1 * g3;
                    a = c1 * f2 + s1 * g3;
                    fi[k2] = f0 - a;
                    fi[0] = f0 + a;
                    gi[k3] = g1 - b;
                    gi[k1] = g1 + b;
                    b = c1 * g2 - s1 * f3;
                    a = s1 * g2 + c1 * f3;
                    gi[k2] = g0 - a;
                    gi[0] = g0 + a;
                    fi[k3] = f1 - b;
                    fi[k1] = f1 + b;
                    gi += k4;
                    fi += k4;
                } while (fi < fn);
                c2 = c1;
                c1 = c2 * tri[0] - s1 * tri[1];
                s1 = c2 * tri[1] + s1 * tri[0];
            }
        }
        else {
            FLOAT   c2, s2;
            for(i = 1; i < 4; i++) {
                c2 = 1 - (2*s1)*s1;
                s2 = (2*s1)*c1;
                csvec[i] = c1;
                csvec[i+4] = c2;
                csvec[i+8] = s1;
                csvec[i+12] = s2;
                c2 = c1;
                c1 = c2 * tri[0] - s1 * tri[1];
                s1 = c2 * tri[1] + s1 * tri[0];
            }
            vc1 = vec_ld(0,csvec);
            vc2 = vec_ld(16,csvec);
            vs1 = vec_ld(32,csvec);
            vs2 = vec_ld(48,csvec);
            fi = fz;
            gi = fz + k1;
            do {
                vfi0 = vec_ld(0,fi);
                vfi1 = vec_ld(0,fi+k1);
                vfi2 = vec_ld(0,fi+k2);
                vfi3 = vec_ld(0,fi+k3);
                vprev1 = vec_ld(0,gi-4);
                vprev2 = vec_ld(0,gi+k1-4);
                vprev3 = vec_ld(0,gi+k2-4);
                vprev4 = vec_ld(0,gi+k3-4);
                vgi0 = vec_perm(vprev1,vprev1,vperm1);
                vgi1 = vec_perm(vprev2,vprev2,vperm1);
                vgi2 = vec_perm(vprev3,vprev3,vperm1);
                vgi3 = vec_perm(vprev4,vprev4,vperm1);
                
                v1 = vec_madd(vfi1,vc2,vzero);
                v2 = vec_madd(vfi1,vs2,vzero);
                v3 = vec_madd(vfi3,vc2,vzero);
                v4 = vec_madd(vfi3,vs2,vzero);
                v5 = vec_madd(vgi1,vs2,v1);
                v6 = vec_nmsub(vgi1,vc2,v2);
                v7 = vec_madd(vgi3,vs2,v3);
                v8 = vec_nmsub(vgi3,vc2,v4);
                
                vf0 = vec_add(vfi0,v5);
                vf1 = vec_sub(vfi0,v5);
                vg0 = vec_add(vgi0,v6);
                vg1 = vec_sub(vgi0,v6);
                vf2 = vec_add(vfi2,v7);
                vf3 = vec_sub(vfi2,v7);
                vg2 = vec_add(vgi2,v8);
                vg3 = vec_sub(vgi2,v8);
                
                v1 = vec_madd(vf2,vc1,vzero);
                v2 = vec_madd(vf2,vs1,vzero);
                v3 = vec_madd(vg2,vs1,vzero);
                v4 = vec_madd(vg2,vc1,vzero);
                v5 = vec_madd(vg3,vs1,v1);
                v6 = vec_nmsub(vg3,vc1,v2);
                v7 = vec_madd(vf3,vc1,v3);
                v8 = vec_nmsub(vf3,vs1,v4);
                
                v9 = vec_add(vf0,v5);
                v10 = vec_sub(vf0,v5);
                v11 = vec_add(vg1,v6);
                v12 = vec_sub(vg1,v6);
                v13 = vec_add(vg0,v7);
                v14 = vec_sub(vg0,v7);
                v15 = vec_add(vf1,v8);
                v16 = vec_sub(vf1,v8);
                
                v1 = vec_perm(v9,vfi0,vperm2);
                v2 = vec_perm(v10,vfi2,vperm2);
                v3 = vec_perm(v15,vfi1,vperm2);
                v4 = vec_perm(v16,vfi3,vperm2);
                vec_st(v1,0,fi);
                vec_st(v2,0,fi+k2);
                vec_st(v3,0,fi+k1);
                vec_st(v4,0,fi+k3);
                
                v1 = vec_perm(v11,vprev2,vperm1);
                v2 = vec_perm(v12,vprev4,vperm1);
                v3 = vec_perm(v13,vprev1,vperm1);
                v4 = vec_perm(v14,vprev3,vperm1);
                vec_st(v1,0,gi+k1-4);
                vec_st(v2,0,gi+k3-4);
                vec_st(v3,0,gi-4);
                vec_st(v4,0,gi+k2-4);
                
                gi += k4;
                fi += k4;
            } while (fi<fn);
            
            /* rest loop */
            
            for (i = 4; i < kx; i+=4) {
                int j;
                for(j = 0; j < 4; j++) {
                    c2 = 1 - (2*s1)*s1;
                    s2 = (2*s1)*c1;
                    csvec[j] = c1;
                    csvec[j+4] = c2;
                    csvec[j+8] = s1;
                    csvec[j+12] = s2;
                    c2 = c1;
                    c1 = c2 * tri[0] - s1 * tri[1];
                    s1 = c2 * tri[1] + s1 * tri[0];
                }
                vc1 = vec_ld(0,csvec);
                vc2 = vec_ld(16,csvec);
                vs1 = vec_ld(32,csvec);
                vs2 = vec_ld(48,csvec);
                fi = fz + i;
                gi = fz + k1 - i;
                do {
                    vfi0 = vec_ld(0,fi);
                    vfi1 = vec_ld(0,fi+k1);
                    vfi2 = vec_ld(0,fi+k2);
                    vfi3 = vec_ld(0,fi+k3);
                    vprev1 = vec_ld(0,gi-4);
                    v1 = vec_ld(0,gi);
                    vprev2 = vec_ld(0,gi+k1-4);
                    v2 = vec_ld(0,gi+k1);
                    vprev3 = vec_ld(0,gi+k2-4);
                    v3 = vec_ld(0,gi+k2);
                    vprev4 = vec_ld(0,gi+k3-4);
                    v4 = vec_ld(0,gi+k3);
                    vgi0 = vec_perm(vprev1,v1,vperm1);
                    vgi1 = vec_perm(vprev2,v2,vperm1);
                    vgi2 = vec_perm(vprev3,v3,vperm1);
                    vgi3 = vec_perm(vprev4,v4,vperm1);
                    
                    v1 = vec_madd(vfi1,vc2,vzero);
                    v2 = vec_madd(vfi1,vs2,vzero);
                    v3 = vec_madd(vfi3,vc2,vzero);
                    v4 = vec_madd(vfi3,vs2,vzero);
                    v5 = vec_madd(vgi1,vs2,v1);
                    v6 = vec_nmsub(vgi1,vc2,v2);
                    v7 = vec_madd(vgi3,vs2,v3);
                    v8 = vec_nmsub(vgi3,vc2,v4);
                    
                    vf0 = vec_add(vfi0,v5);
                    vf1 = vec_sub(vfi0,v5);
                    vg0 = vec_add(vgi0,v6);
                    vg1 = vec_sub(vgi0,v6);
                    vf2 = vec_add(vfi2,v7);
                    vf3 = vec_sub(vfi2,v7);
                    vg2 = vec_add(vgi2,v8);
                    vg3 = vec_sub(vgi2,v8);
                    
                    v1 = vec_madd(vf2,vc1,vzero);
                    v2 = vec_madd(vf2,vs1,vzero);
                    v3 = vec_madd(vg2,vs1,vzero);
                    v4 = vec_madd(vg2,vc1,vzero);
                    v5 = vec_madd(vg3,vs1,v1);
                    v6 = vec_nmsub(vg3,vc1,v2);
                    v7 = vec_madd(vf3,vc1,v3);
                    v8 = vec_nmsub(vf3,vs1,v4);
                    
                    v9 = vec_add(vf0,v5);
                    v10 = vec_sub(vf0,v5);
                    v11 = vec_add(vg1,v6);
                    v12 = vec_sub(vg1,v6);
                    v13 = vec_add(vg0,v7);
                    v14 = vec_sub(vg0,v7);
                    v15 = vec_add(vf1,v8);
                    v16 = vec_sub(vf1,v8);
                    
                    vec_st(v9,0,fi);
                    vec_st(v10,0,fi+k2);
                    vec_st(v15,0,fi+k1);
                    vec_st(v16,0,fi+k3);
                    
                    v1 = vec_perm(v11,vprev2,vperm1);
                    v2 = vec_perm(v12,vprev4,vperm1);
                    v3 = vec_perm(v13,vprev1,vperm1);
                    v4 = vec_perm(v14,vprev3,vperm1);
                    vec_st(v1,0,gi+k1-4);
                    vec_ste(v11,0,gi+k1);
                    vec_st(v2,0,gi+k3-4);
                    vec_ste(v12,0,gi+k3);
                    vec_st(v3,0,gi-4);
                    vec_ste(v13,0,gi);
                    vec_st(v4,0,gi+k2-4);
                    vec_ste(v14,0,gi+k2);
                    
                    gi += k4;
                    fi += k4;
                } while (fi<fn);
            }
        }
#else
        for (i = 1; i < kx; i++) {
            FLOAT   c2, s2;
            c2 = 1 - (2 * s1) * s1;
            s2 = (2 * s1) * c1;
            fi = fz + i;
            gi = fz + k1 - i;
            do {
                FLOAT   a, b, g0, f0, f1, g1, f2, g2, f3, g3;
                b = s2 * fi[k1] - c2 * gi[k1];
                a = c2 * fi[k1] + s2 * gi[k1];
                f1 = fi[0] - a;
                f0 = fi[0] + a;
                g1 = gi[0] - b;
                g0 = gi[0] + b;
                b = s2 * fi[k3] - c2 * gi[k3];
                a = c2 * fi[k3] + s2 * gi[k3];
                f3 = fi[k2] - a;
                f2 = fi[k2] + a;
                g3 = gi[k2] - b;
                g2 = gi[k2] + b;
                b = s1 * f2 - c1 * g3;
                a = c1 * f2 + s1 * g3;
                fi[k2] = f0 - a;
                fi[0] = f0 + a;
                gi[k3] = g1 - b;
                gi[k1] = g1 + b;
                b = c1 * g2 - s1 * f3;
                a = s1 * g2 + c1 * f3;
                gi[k2] = g0 - a;
                gi[0] = g0 + a;
                fi[k3] = f1 - b;
                fi[k1] = f1 + b;
                gi += k4;
                fi += k4;
            } while (fi < fn);
            c2 = c1;
            c1 = c2 * tri[0] - s1 * tri[1];
            s1 = c2 * tri[1] + s1 * tri[0];
        }
#endif
        tri += 2;
    } while (k4 < n);
}


static const unsigned char rv_tbl[] = {
    0x00, 0x80, 0x40, 0xc0, 0x20, 0xa0, 0x60, 0xe0,
    0x10, 0x90, 0x50, 0xd0, 0x30, 0xb0, 0x70, 0xf0,
    0x08, 0x88, 0x48, 0xc8, 0x28, 0xa8, 0x68, 0xe8,
    0x18, 0x98, 0x58, 0xd8, 0x38, 0xb8, 0x78, 0xf8,
    0x04, 0x84, 0x44, 0xc4, 0x24, 0xa4, 0x64, 0xe4,
    0x14, 0x94, 0x54, 0xd4, 0x34, 0xb4, 0x74, 0xf4,
    0x0c, 0x8c, 0x4c, 0xcc, 0x2c, 0xac, 0x6c, 0xec,
    0x1c, 0x9c, 0x5c, 0xdc, 0x3c, 0xbc, 0x7c, 0xfc,
    0x02, 0x82, 0x42, 0xc2, 0x22, 0xa2, 0x62, 0xe2,
    0x12, 0x92, 0x52, 0xd2, 0x32, 0xb2, 0x72, 0xf2,
    0x0a, 0x8a, 0x4a, 0xca, 0x2a, 0xaa, 0x6a, 0xea,
    0x1a, 0x9a, 0x5a, 0xda, 0x3a, 0xba, 0x7a, 0xfa,
    0x06, 0x86, 0x46, 0xc6, 0x26, 0xa6, 0x66, 0xe6,
    0x16, 0x96, 0x56, 0xd6, 0x36, 0xb6, 0x76, 0xf6,
    0x0e, 0x8e, 0x4e, 0xce, 0x2e, 0xae, 0x6e, 0xee,
    0x1e, 0x9e, 0x5e, 0xde, 0x3e, 0xbe, 0x7e, 0xfe
};

#define ch01(index)  (buffer[chn][index])

#define ml00(f) (window[i        ] * f(i))
#define ml10(f) (window[i + 0x200] * f(i + 0x200))
#define ml20(f) (window[i + 0x100] * f(i + 0x100))
#define ml30(f) (window[i + 0x300] * f(i + 0x300))

#define ml01(f) (window[i + 0x001] * f(i + 0x001))
#define ml11(f) (window[i + 0x201] * f(i + 0x201))
#define ml21(f) (window[i + 0x101] * f(i + 0x101))
#define ml31(f) (window[i + 0x301] * f(i + 0x301))

#define ms00(f) (window_s[i       ] * f(i + k))
#define ms10(f) (window_s[0x7f - i] * f(i + k + 0x80))
#define ms20(f) (window_s[i + 0x40] * f(i + k + 0x40))
#define ms30(f) (window_s[0x3f - i] * f(i + k + 0xc0))

#define ms01(f) (window_s[i + 0x01] * f(i + k + 0x01))
#define ms11(f) (window_s[0x7e - i] * f(i + k + 0x81))
#define ms21(f) (window_s[i + 0x41] * f(i + k + 0x41))
#define ms31(f) (window_s[0x3e - i] * f(i + k + 0xc1))

void
fft_short(lame_internal_flags const *const gfc,
          FLOAT x_real[3][BLKSIZE_s], int chn, const sample_t *const buffer[2])
{
    int     i;
    int     j;
    int     b;

#define window_s gfc->cd_psy->window_s
#define window gfc->cd_psy->window

    for (b = 0; b < 3; b++) {
        FLOAT  *x = &x_real[b][BLKSIZE_s / 2];
        short const k = (576 / 3) * (b + 1);
        j = BLKSIZE_s / 8 - 1;
        do {
            FLOAT   f0, f1, f2, f3, w;

            i = rv_tbl[j << 2];

            f0 = ms00(ch01);
            w = ms10(ch01);
            f1 = f0 - w;
            f0 = f0 + w;
            f2 = ms20(ch01);
            w = ms30(ch01);
            f3 = f2 - w;
            f2 = f2 + w;

            x -= 4;
            x[0] = f0 + f2;
            x[2] = f0 - f2;
            x[1] = f1 + f3;
            x[3] = f1 - f3;

            f0 = ms01(ch01);
            w = ms11(ch01);
            f1 = f0 - w;
            f0 = f0 + w;
            f2 = ms21(ch01);
            w = ms31(ch01);
            f3 = f2 - w;
            f2 = f2 + w;

            x[BLKSIZE_s / 2 + 0] = f0 + f2;
            x[BLKSIZE_s / 2 + 2] = f0 - f2;
            x[BLKSIZE_s / 2 + 1] = f1 + f3;
            x[BLKSIZE_s / 2 + 3] = f1 - f3;
        } while (--j >= 0);

#undef window
#undef window_s

        gfc->fft_fht(x, BLKSIZE_s / 2);
        /* BLKSIZE_s/2 because of 3DNow! ASM routine */
    }
}

void
fft_long(lame_internal_flags const *const gfc,
         FLOAT x[BLKSIZE], int chn, const sample_t *const buffer[2])
{
    int     i;
    int     jj = BLKSIZE / 8 - 1;
    x += BLKSIZE / 2;

#define window_s gfc->cd_psy->window_s
#define window gfc->cd_psy->window

    do {
        FLOAT   f0, f1, f2, f3, w;

        i = rv_tbl[jj];
        f0 = ml00(ch01);
        w = ml10(ch01);
        f1 = f0 - w;
        f0 = f0 + w;
        f2 = ml20(ch01);
        w = ml30(ch01);
        f3 = f2 - w;
        f2 = f2 + w;

        x -= 4;
        x[0] = f0 + f2;
        x[2] = f0 - f2;
        x[1] = f1 + f3;
        x[3] = f1 - f3;

        f0 = ml01(ch01);
        w = ml11(ch01);
        f1 = f0 - w;
        f0 = f0 + w;
        f2 = ml21(ch01);
        w = ml31(ch01);
        f3 = f2 - w;
        f2 = f2 + w;

        x[BLKSIZE / 2 + 0] = f0 + f2;
        x[BLKSIZE / 2 + 2] = f0 - f2;
        x[BLKSIZE / 2 + 1] = f1 + f3;
        x[BLKSIZE / 2 + 3] = f1 - f3;
    } while (--jj >= 0);

#undef window
#undef window_s

    gfc->fft_fht(x, BLKSIZE / 2);
    /* BLKSIZE/2 because of 3DNow! ASM routine */
}

#ifdef HAVE_NASM
extern void fht_3DN(FLOAT * fz, int n);
extern void fht_SSE(FLOAT * fz, int n);
#endif

void
init_fft(lame_internal_flags * const gfc)
{
    int     i;

    /* The type of window used here will make no real difference, but */
    /* in the interest of merging nspsytune stuff - switch to blackman window */
    for (i = 0; i < BLKSIZE; i++)
        /* blackman window */
        gfc->cd_psy->window[i] = 0.42 - 0.5 * cos(2 * PI * (i + .5) / BLKSIZE) +
            0.08 * cos(4 * PI * (i + .5) / BLKSIZE);

    for (i = 0; i < BLKSIZE_s / 2; i++)
        gfc->cd_psy->window_s[i] = 0.5 * (1.0 - cos(2.0 * PI * (i + 0.5) / BLKSIZE_s));

    gfc->fft_fht = fht;
#ifdef HAVE_NASM
    if (gfc->CPU_features.AMD_3DNow) {
        gfc->fft_fht = fht_3DN;
    }
    else if (gfc->CPU_features.SSE) {
        gfc->fft_fht = fht_SSE;
    }
    else {
        gfc->fft_fht = fht;
    }
#else
#ifdef HAVE_XMMINTRIN_H
#ifdef MIN_ARCH_SSE
    gfc->fft_fht = fht_SSE2;
#endif
#endif
#endif
}
