#include <stddef.h>

unsigned sumarray(unsigned a[], int n) {
  int i; unsigned s;
  i=0;
  s=0;
  while (i<n) {
    s+=a[i];
    i++;
  }
  return s;
}

unsigned four[4] = {1,2,3,4};

int main(void) {
  unsigned int s;
  s = sumarray(four,4);
  return (int)s;
}

