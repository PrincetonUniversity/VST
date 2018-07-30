#include "ptr_atomics.h"

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

typedef struct atomic_loc { void *val; lock_t *lock; } atomic_loc;

atomic_loc *make_atomic(void *v){
  atomic_loc *a = surely_malloc(sizeof(atomic_loc));
  lock_t *l = surely_malloc(sizeof(lock_t));
  a->val = v;
  a->lock = l;
  makelock(l);
  release(l);
  return a;
}

void *free_atomic(atomic_loc *tgt){
  lock_t *l = tgt->lock;
  acquire(l);
  freelock(l);
  free(l);
  void *v = tgt->val;
  free(tgt);
  return v;
}

void *load_SC(atomic_loc *tgt){
  void *x;
  lock_t *l = tgt->lock;
  acquire(l);
  x = tgt->val;
  release(l);
  return x;
}

void store_SC(atomic_loc *tgt, void *v){
  void *x;
  lock_t *l = tgt->lock;
  acquire(l);
  tgt->val = v;
  release(l);
}

int CAS_SC(atomic_loc *tgt, void *c, void *v){
  int r;
  lock_t *l = tgt->lock;
  acquire(l);
  void *x = tgt->val;
  if(x == c){
    tgt->val = v;
    r = 1;
  }
  else r = 0;
  release(l);
  return r;
}
