#include <stddef.h>

union p_or_i {
  size_t choice_i;
  void *choice_p;
};

size_t g(size_t i) {
  union p_or_i x;
  x.choice_i = i;
  return x.choice_i;
}

void *h(void *p) {
  union p_or_i x;
  x.choice_p = p;
  return x.choice_p;
}


/* the next function is more crazy . . . */

float fabs_single (float x) {
  union {float f; unsigned int i; } u;
  u.f = x;
  u.i = u.i & 0x7fffffff;
  return u.f;
}
