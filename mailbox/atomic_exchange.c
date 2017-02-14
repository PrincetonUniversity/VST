#include "atomic_exchange.h"

//This could be replaced by an external call.
int simulate_atomic_exchange(int *tgt, lock_t *l, int v){
  int x;
  acquire(l);
  x = *tgt;
  *tgt = v;
  release(l);
  return x;
}
