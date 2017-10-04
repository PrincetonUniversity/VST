#include <stddef.h>

int myfunc (int i) { return i+1; }

void *a[] = {myfunc}; /* TODO: fix start_function so this isn't 
                          necessary to get the gvar for _myfunc */
int main (void) {
  int (*f)(int);
  int j;
  f = &myfunc;
  j = f(3);
  return j;
}
