#include <stddef.h>

struct list {int head; struct list *tail;};

void head_pointer_switch(struct list * l, int * p)
{
  int h, i;
  h = l -> head;
  i = * p;
  l -> head = i;
  * p = h;
}

void head_head_switch(struct list * l1, struct list * l2)
{
  int h1, h2;
  h1 = l1 -> head;
  h2 = l2 -> head;
  l1 -> head = h2;
  l2 -> head = h1;
}
