#include "atomics.h"

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

typedef struct atomic_loc { int val; lock_t *lock; } atomic_loc;

atomic_loc *make_atomic(int i){
  atomic_loc *a = surely_malloc(sizeof(atomic_loc));
  lock_t *l = surely_malloc(sizeof(lock_t));
  a->val = i;
  a->lock = l;
  makelock(l);
  release(l);
  return a;
}

int free_atomic(atomic_loc *tgt){
  lock_t *l = tgt->lock;
  acquire(l);
  freelock(l);
  free(l);
  int i = tgt->val;
  free(tgt);
  return i;
}

int load_SC(atomic_loc *tgt){
  int x;
  lock_t *l = tgt->lock;
  acquire(l);
  x = tgt->val;
  release(l);
  return x;
}

void store_SC(atomic_loc *tgt, int v){
  int x;
  lock_t *l = tgt->lock;
  acquire(l);
  tgt->val = v;
  release(l);
}

int CAS_SC(atomic_loc *tgt, int c, int v){
  int x;
  lock_t *l = tgt->lock;
  acquire(l);
  x = tgt->val;
  if(x == c){
    tgt->val = v;
    x = 1;
  }
  else x = 0;
  release(l);
  return x;
}

int atomic_exchange_SC(int *tgt, int v){
  int x;
  lock_t *l = tgt->lock;
  acquire(l);
  x = tgt->val;
  tgt->val = v;
  release(l);
  return x;
}

int load_relaxed(atomic_loc *tgt){
  int x;
  lock_t *l = tgt->lock;
  acquire(l);
  x = tgt->val;
  release(l);
  return x;
}
