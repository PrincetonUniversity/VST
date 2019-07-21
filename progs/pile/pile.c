#include <stddef.h>
#include "stdlib.h"
#include "pile.h"
#include "pile_private.h"

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

Pile Pile_new(void) {
  Pile p = (Pile)surely_malloc(sizeof *p);
  p->head=NULL;
  return p;
}

void Pile_add(Pile p, int n) {
  struct list *head = (struct list *)surely_malloc(sizeof *head);
  head->n=n;
  head->next=p->head;
  p->head=head;
}

int Pile_count(Pile p) {
  struct list *q;
  int c=0;
  for(q=p->head; q; q=q->next)
    c += q->n;
  return c;
}

void Pile_free(Pile p) {
  struct list *q, *r;
   q=p->head;
   while (q) {
     r = q->next;
     free(q);
     q = r;
   }
   free(p);
}


