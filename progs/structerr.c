struct foo {int x,y;} p;

struct foo f(void) {
  /*  return p; */
}

void g (struct foo p) {
}

int main(void) {
  g(p);
  return 0;
}
