#include <stddef.h>

extern void *mallocN (int n);
extern void freeN(void *p, int n);

struct elem {
  int a, b;
  struct elem *next;
};

struct fifo {
  struct elem *head;
  struct elem *tail;
};

struct fifo *fifo_new(void) {
  struct fifo *Q = (struct fifo *)mallocN(sizeof (*Q));
  Q->head = NULL;
  Q->tail = NULL;
  return Q;
}

void fifo_put (struct fifo *Q, struct elem *p) {
  struct elem *h, *t;
  p->next=NULL;
  h = Q->head;
  if (h==NULL) {
    Q->head=p;
    Q->tail=p;
  }
  else {
    t = Q->tail;
    t->next=p;
    Q->tail=p;
  }
}

int fifo_empty (struct fifo *Q) {
  struct elem *h;
  h = Q->head;
  return (h == NULL);
}

struct elem *fifo_get (struct fifo *Q) {
  struct elem *h, *n;
  h=Q->head;
  n=h->next;
  Q->head=n;
  return h;
}

struct elem *make_elem(int a, int b) {
  struct elem *p;
  p = mallocN(sizeof (*p));
  p->a=a;
  p->b=b;
  return p;
}

int main(void) {
  int i, j;
  struct fifo *Q;
  struct elem *p;
  Q = fifo_new();
  p = make_elem(1,10);
  fifo_put(Q,p);
  p = make_elem(2,20);
  fifo_put(Q,p);
  p = fifo_get(Q);
  i = p->a; 
  j = p->b;
  freeN(p, sizeof(*p));
  return i+j;
}
