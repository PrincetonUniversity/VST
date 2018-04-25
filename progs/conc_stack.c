#include <stddef.h>
#include "threads.h"

extern void * malloc (size_t n);
extern void free (void *p);
extern void exit(int n);

struct cons {
  int value;
  struct cons *next;
};

struct stack {
  struct cons *top;
};

struct lstack {
  struct stack d;
  lock_t *lock;
};

struct lstack *newstack(void) {
  struct lstack *p;
  p = (struct lstack *) malloc (sizeof (struct lstack));
  if (!p) exit(1);
  p->d.top = NULL;
  lock_t *l = (lock_t *) malloc (sizeof (lock_t));
  if (!l) exit(1);
  makelock(l);
  p->lock = l;
  release(l);
  return p;
}

void push (struct lstack *p, int i) {
  struct cons *q;
  q = (struct cons *) malloc (sizeof (struct cons));
  if (!q) exit(1);
  q->value = i;
  acquire(p->lock);
  struct stack *s = &(p->d);
  q->next = s->top;
  s->top = q;
  release(p->lock);
}

int pop (struct lstack *p) {
  struct cons *q;
  int i;
  /* pop now has to wait for the stack to be non-empty. */
  while(1){
    acquire(p->lock);
    struct stack *s = &(p->d);
    q = s->top;
    if(!q){ release(p->lock); continue; }
    s->top = q->next;
    release(p->lock);
    i = q->value;
    free(q);
    return i;
  }
}


