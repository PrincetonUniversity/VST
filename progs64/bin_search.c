#include <stddef.h>

int search(int a[], int tgt, int lo, int hi){
  int mid, val;
  while(lo < hi){
    mid = (lo + hi) >> 1; /* (hi - lo) >> 1 + lo ? */
    val = a[mid];
    if (val == tgt) return mid;
    else if (val < tgt) lo = mid + 1;
    else hi = mid;
  }
  return -1;
}

int four[4] = {1, 2, 3, 4};

int main(void){
  int s;
  s = search(four, 3, 0, 4);
  return s;
}
