#include <stddef.h>

/* merges two sorted linked lists */

struct list {int head; struct list *tail;};

struct list *merge(struct list *a, struct list *b){
  struct list* ret;
  struct list* temp; /* returned value, as ret can be addressed */
  struct list** x;
  int va, vb, cond;
  x = &ret;
  cond = a != NULL && b != NULL;
  while (cond) {
    va = a->head;
    vb = b->head;
    if (va <= vb) {
      *x = a;
      x = &(a->tail);
      a = a->tail;
    } else {
      *x = b;
      x = &(b->tail);
      b = b->tail;
    }
    /* the expression below contains a load;
       we transformed it into &(a->tail) and &(b->tail) in the if above
    x = &((*x)->tail); */
    cond = a != NULL && b != NULL;
  }

  if (a != NULL) {
    *x = a;
  } else {
    *x = b;
  }
  temp = ret;
  return temp;
}
