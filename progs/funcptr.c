#include <stddef.h>

int myfunc (int i) { return i+1; }

int main (void) {
  int (*f)(int);
  int j;
  f = &myfunc;
  j = f(3);
  return j;
}
