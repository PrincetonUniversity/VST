#ifdef COMPCERT
typedef float _Float16;  /* _Float16 is a MacOS thing that CompCert doesn't support */
#endif
#include <math.h>

double f(double t) {
  double x = cos(t);
  double y = sin(t);
  return x*x+y*y;
}
