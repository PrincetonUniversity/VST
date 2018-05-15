#include <stddef.h>

unsigned sumarray(unsigned a[], int n) {
  int i; unsigned s;
  s=0;
  for (i=0; i<n; i++)
    s += a[i];
  return s;
}

unsigned four[4] = {1,2,3,4};

int main(void) {
  unsigned s;
  s = sumarray(four+2,2);
  return (int)s;
}

