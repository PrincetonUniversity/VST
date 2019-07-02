#include <stddef.h>
#include "apile.h"
#include "onepile.h"
#include "triang.h"

int main(void) {
  int i, c1, c2, c3;
  Onepile_init();
  for (i=0; i<10; i++) {
    Onepile_add(i+1);
    Apile_add(i+1);
  }
  c1 = Onepile_count();
  c2 = Apile_count();
  c3 = Triang_nth(10);
  return c1+c2-2*c3;
}
