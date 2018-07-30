#include <stddef.h>

unsigned sumarray(unsigned a[], int n) {
  int i; unsigned s;
  s=0;
  for (i=-1; i< n - 1; i++)
    s += a[i + 1];
  return s;
}
