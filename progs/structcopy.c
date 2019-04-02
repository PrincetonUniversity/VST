struct foo {unsigned int a,b;};

unsigned int f(struct foo *p) {
  struct foo q;
  q = *p;
  return q.a + q.b;
}
