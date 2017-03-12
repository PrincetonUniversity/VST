//Example from Adam Langley

#include <stdint.h>

typedef int64_t limb;
typedef int32_t s32;

void product(limb out[19], const limb *a, const limb *b) {
  s32 t1, t2;
  limb t3;

  t1 = a[0];
  t2 = b[0];
  t3 = t1 * t2;
  out[0] = t3;
  return;
}
