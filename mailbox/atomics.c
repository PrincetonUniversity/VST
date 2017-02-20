#include "atomics.h"
//package tgt and l into a struct?

int simulate_atomic_load(int *tgt, lock_t *l){
  int x;
  acquire(l);
  x = *tgt;
  release(l);
  return x;
}

void simulate_atomic_store(int *tgt, lock_t *l, int v){
  int x;
  acquire(l);
  *tgt = v;
  release(l);
}

int simulate_atomic_CAS(int *tgt, lock_t *l, int c, int v){
  int x;
  acquire(l);
  x = *tgt;
  if(x == c) *tgt = v;
  release(l);
  return x;
}
