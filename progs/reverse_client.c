#include <stddef.h>

struct list {unsigned head; struct list *tail;};

struct list *reverse (struct list *p);

unsigned int last_foo(struct list * p) {
  unsigned int res;
  p = reverse (p);
  res = p -> head;
  return res;
}

int main (void) {
}

