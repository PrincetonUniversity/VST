#include <stddef.h>

void reverse(int a[], int n) {
  int lo, hi, s, t;
  lo=0;
  hi=n;
  while (lo<hi-1) {
    t = a[lo];
    s = a[hi-1];
    a[hi-1] = t;
    a[lo] = s;
    lo++; hi--;
  }
}

int four[4] = {1,2,3,4};

int main(void) {
  int i;
  reverse(four,4);
  reverse(four,4);
  return 0;
}

