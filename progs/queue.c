#include <stddef.h>

extern void *mallocN (int n);
extern void freeN(void *p, int n);

struct elem {
  int a, b;
  struct elem *next;
};

struct fifo {
  struct elem *head;
  struct elem **tail;
};

struct fifo *fifo_new(void) {
  struct fifo *Q = (struct fifo *)mallocN(sizeof (*Q));
  Q->tail = &(Q->head);
  return Q;
}

void fifo_put (struct fifo *Q, struct elem *p) {
  *(Q->tail) = p;
  Q->tail = &p->next;
}

struct elem *fifo_get (struct fifo *Q) {
  struct elem *p;
  if (Q->tail== &(Q->head))
    return NULL;
  else {
    p=Q->head;
    Q->head=p->next;
  }
}

struct elem *make_elem(int a, int b) {
  struct elem *p;
  p = mallocN(sizeof (*p));
  p->a=a;
  p->b=b;
  return p;
}

int main(void) {
  int i;
  struct fifo *Q;
  struct elem *p;
  Q = fifo_new();
  p = make_elem(1,10);
  fifo_put(Q,p);
  p = make_elem(2,20);
  fifo_put(Q,p);
  p = fifo_get(Q);
  i = p->a+p->b;
  freeN(p, sizeof(*p));
  return i;
}
