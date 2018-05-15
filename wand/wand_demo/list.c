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

struct list * append1 (struct list * x, struct list * y) {
  struct list * t, * u;
  if (x == NULL)
    return y;
  else {
    t = x;
    u = t -> tail;
    while (u != NULL) {
      t = u;
      u = t -> tail;
    }
    t -> tail = y;
    return x;
  }
}

struct list * append2 (struct list * x, struct list * y) {
  struct list * head, * * retp, * ret, * * curp, * cur;
  head = x;
  curp = & head;
  cur = x;
  retp = & head;
  while (cur != NULL) {
    curp = & (cur -> tail);
    cur = * curp;
  }
  * curp = y;
  ret = * retp;
  return ret;
}

struct list * append3 (struct list * x, struct list * y) {
  struct list * t;
  if (x == NULL)
    return y;
  else {
    t = x -> tail;
    t = append3(t, y);
    x -> tail = t;
    return x;
  }
}

