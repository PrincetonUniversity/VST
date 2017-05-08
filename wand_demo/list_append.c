#include <stddef.h>

struct list {int head; struct list *tail;};

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
  struct list * * retp, * * curp, * ret, * cur;
  cur = x;
  curp = & cur;
  retp = & cur;
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

