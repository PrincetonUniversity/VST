#ifdef COMPCERT
/* still Starting with CompCert 3.15 (and VST 2.15), don't need this hack
   any more, but still here for VSTlib compatibility with older versions
   of CompCert/VST */
typedef float _Float16;  /* _Float16 is a MacOS thing that CompCert doesn't support */
#endif
#include <math.h>

double f(double t) {
  double x = cos(t);
  double y = sin(t);
  return x*x+y*y;
}
