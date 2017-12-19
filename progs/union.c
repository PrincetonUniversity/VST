
float fabs_single (float x) {
  union {float f; unsigned int i; } u;
  u.f = x;
  u.i = u.i & 0x7fffffff;
  return u.f;
}
