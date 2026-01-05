#include <math.h>

/* Note regard 'long double':
   On some platforms, CompCert does not support 128-bit long doubles,
   because on those target architectures the ABI for long-double is
   horrible.  See the CompCert reference manual.  However, math.h
   contains many mentions of 'long double'.  The workaround is
   to use clightgen with -flongdouble, which will treat long double
   as if it were just double.  Therefore any call to an external
   function that expects (or returns) long double will not work
   properly, and we must omit them here.
*/

int math_placeholder (void) {
  return 
    &acos,    /* double      acos(double); */
    &acosf,    /* float       acosf(float); */
    &acosh,    /* double      acosh(double); */
    &acoshf,    /* float       acoshf(float); */
    /*    &acoshl,     long double acoshl(long double); */
    /*    &acosl,     long double acosl(long double); */
    &asin,    /* double      asin(double); */
    &asinf,    /* float       asinf(float); */
    &asinh,    /* double      asinh(double); */
    &asinhf,    /* float       asinhf(float); */
    /*    &asinhl,     long double asinhl(long double); */
    /*    &asinl,     long double asinl(long double); */
    &atan,    /* double      atan(double); */
    &atan2,    /* double      atan2(double, double); */
    &atan2f,    /* float       atan2f(float, float); */
    /*    &atan2l,     long double atan2l(long double, long double); */
    &atanf,    /* float       atanf(float); */
    &atanh,    /* double      atanh(double); */
    &atanhf,    /* float       atanhf(float); */
    /*    &atanhl,     long double atanhl(long double); */
    /*    &atanl,     long double atanl(long double); */
    &cbrt,    /* double      cbrt(double); */
    &cbrtf,    /* float       cbrtf(float); */
    /*    &cbrtl,     long double cbrtl(long double); */
    &ceil,    /* double      ceil(double); */
    &ceilf,    /* float       ceilf(float); */
    /*    &ceill,     long double ceill(long double); */
    &copysign,    /* double      copysign(double, double); */
    &copysignf,    /* float       copysignf(float, float); */
    /*    &copysignl,     long double copysignl(long double, long double); */
    &cos,    /* double      cos(double); */
    &cosf,    /* float       cosf(float); */
    &cosh,    /* double      cosh(double); */
    &coshf,    /* float       coshf(float); */
    /*    &coshl,     long double coshl(long double); */
    /*    &cosl,     long double cosl(long double); */
    &erf,    /* double      erf(double); */
    &erfc,    /* double      erfc(double); */
    &erfcf,    /* float       erfcf(float); */
    /*    &erfcl,     long double erfcl(long double); */
    &erff,    /* float       erff(float); */
    /*    &erfl,     long double erfl(long double); */
    &exp,    /* double      exp(double); */
    &exp2,    /* double      exp2(double); */
    &exp2f,    /* float       exp2f(float); */
    /*    &exp2l,     long double exp2l(long double); */
    &expf,    /* float       expf(float); */
    /*    &expl,     long double expl(long double); */
    &expm1,    /* double      expm1(double); */
    &expm1f,    /* float       expm1f(float); */
    /*    &expm1l,     long double expm1l(long double); */
    &fabs,    /* double      fabs(double); */
    &fabsf,    /* float       fabsf(float); */
    /*    &fabsl,     long double fabsl(long double); */
    &fdim,    /* double      fdim(double, double); */
    &fdimf,    /* float       fdimf(float, float); */
    /*    &fdiml,     long double fdiml(long double, long double); */
    &floor,    /* double      floor(double); */
    &floorf,    /* float       floorf(float); */
    /*    &floorl,     long double floorl(long double); */
    &fma,    /* double      fma(double, double, double); */
    &fmaf,    /* float       fmaf(float, float, float); */
    /*    &fmal,     long double fmal(long double, long double, long double); */
    &fmax,    /* double      fmax(double, double); */
    &fmaxf,    /* float       fmaxf(float, float); */
    /*    &fmaxl,     long double fmaxl(long double, long double); */
    &fmin,    /* double      fmin(double, double); */
    &fminf,    /* float       fminf(float, float); */
    /*    &fminl,     long double fminl(long double, long double); */
    &fmod,    /* double      fmod(double, double); */
    &fmodf,    /* float       fmodf(float, float); */
    /*    &fmodl,     long double fmodl(long double, long double); */
    &frexp,    /* double      frexp(double, int *); */
    &frexpf,    /* float       frexpf(float, int *); */
    /*    &frexpl,     long double frexpl(long double, int *); */
    &hypot,    /* double      hypot(double, double); */
    &hypotf,    /* float       hypotf(float, float); */
    /*    &hypotl,     long double hypotl(long double, long double); */
    &ilogb,    /* int         ilogb(double); */
    &ilogbf,    /* int         ilogbf(float); */
    &ilogbl,    /* int         ilogbl(long double); */
    &ldexp,    /* double      ldexp(double, int); */
    &ldexpf,    /* float       ldexpf(float, int); */
    /*    &ldexpl,     long double ldexpl(long double, int); */
    &lgamma,    /* double      lgamma(double); */
    &lgammaf,    /* float       lgammaf(float); */
    /*    &lgammal,     long double lgammal(long double); */
    &llrint,    /* long long   llrint(double); */
    &llrintf,    /* long long   llrintf(float); */
    &llrintl,    /* long long   llrintl(long double); */
    &llround,    /* long long   llround(double); */
    &llroundf,    /* long long   llroundf(float); */
    &llroundl,    /* long long   llroundl(long double); */
    &log,    /* double      log(double); */
    &log10,    /* double      log10(double); */
    &log10f,    /* float       log10f(float); */
    /*    &log10l,     long double log10l(long double); */
    &log1p,    /* double      log1p(double); */
    &log1pf,    /* float       log1pf(float); */
    /*    &log1pl,     long double log1pl(long double); */
    &log2,    /* double      log2(double); */
    &log2f,    /* float       log2f(float); */
    /*    &log2l,     long double log2l(long double); */
    &logb,    /* double      logb(double); */
    &logbf,    /* float       logbf(float); */
    /*    &logbl,     long double logbl(long double); */
    &logf,    /* float       logf(float); */
    /*    &logl,     long double logl(long double); */
    &lrint,    /* long        lrint(double); */
    &lrintf,    /* long        lrintf(float); */
    &lrintl,    /* long        lrintl(long double); */
    &lround,    /* long        lround(double); */
    &lroundf,    /* long        lroundf(float); */
    &lroundl,    /* long        lroundl(long double); */
    &modf,    /* double      modf(double, double *); */
    &modff,    /* float       modff(float, float *); */
    &modfl,    /* long double modfl(long double, long double *); */
    &nan,    /* double      nan(const char *); */
    &nanf,    /* float       nanf(const char *); */
    /*    &nanl,     long double nanl(const char *); */
    &nearbyint,    /* double      nearbyint(double); */
    &nearbyintf,    /* float       nearbyintf(float); */
    /*    &nearbyintl,     long double nearbyintl(long double); */
    &nextafter,    /* double      nextafter(double, double); */
    &nextafterf,    /* float       nextafterf(float, float); */
    /*    &nextafterl,     long double nextafterl(long double, long double); */
    &nexttoward,    /* double      nexttoward(double, long double); */
    &nexttowardf,    /* float       nexttowardf(float, long double); */
    /*    &nexttowardl,     long double nexttowardl(long double, long double); */
    &pow,    /* double      pow(double, double); */
    &powf,    /* float       powf(float, float); */
    /*    &powl,     long double powl(long double, long double); */
    &remainder,    /* double      remainder(double, double); */
    &remainderf,    /* float       remainderf(float, float); */
    /*    &remainderl,     long double remainderl(long double, long double); */
    &remquo,    /* double      remquo(double, double, int *); */
    &remquof,    /* float       remquof(float, float, int *); */
    /*    &remquol,     long double remquol(long double, long double, int *); */
    &rint,    /* double      rint(double); */
    &rintf,    /* float       rintf(float); */
    /*    &rintl,     long double rintl(long double); */
    &round,    /* double      round(double); */
    &roundf,    /* float       roundf(float); */
    /*    &roundl,     long double roundl(long double); */
    &scalbln,    /* double      scalbln(double, long); */
    &scalblnf,    /* float       scalblnf(float, long); */
    /*    &scalblnl,     long double scalblnl(long double, long); */
    &scalbn,    /* double      scalbn(double, int); */
    &scalbnf,    /* float       scalbnf(float, int); */
    /*    &scalbnl,     long double scalbnl(long double, int); */
    &sin,    /* double      sin(double); */
    &sinf,    /* float       sinf(float); */
    &sinh,    /* double      sinh(double); */
    &sinhf,    /* float       sinhf(float); */
    /*    &sinhl,     long double sinhl(long double); */
    /*    &sinl,     long double sinl(long double); */
    &sqrt,    /* double      sqrt(double); */
    &sqrtf,    /* float       sqrtf(float); */
    /*    &sqrtl,     long double sqrtl(long double); */
    &tan,    /* double      tan(double); */
    &tanf,    /* float       tanf(float); */
    &tanh,    /* double      tanh(double); */
    &tanhf,    /* float       tanhf(float); */
    /*    &tanhl,     long double tanhl(long double); */
    /*    &tanl,     long double tanl(long double); */
    &tgamma,    /* double      tgamma(double); */
    &tgammaf,    /* float       tgammaf(float); */
    /*    &tgammal,     long double tgammal(long double); */
    &trunc,    /* double      trunc(double); */
    &truncf,    /* float       truncf(float); */
    /*    &truncl,     long double truncl(long double); */
    0;
}
