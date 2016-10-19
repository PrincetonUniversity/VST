#include <stddef.h>

int sumarray(int a[], int n) {
  int i,s,x;
  s=0;
  for (i=0; i<n; i++) {
    x = a[i];
    s += x;
  }
  return s;
}

int four[4] = {1,2,3,4};

int main(void) {
  int s;
  s = sumarray(four+2,2);
  return s;
}

