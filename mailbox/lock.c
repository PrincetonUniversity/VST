#include <stdlib.h>
#include <stdio.h>
#include "atomic_exchange.h"

void my_acquire(int *l, lock_t *ll){
  int r = 1;
  while(r)
    r = simulate_atomic_exchange(l, ll, 1);
}

void my_release(int *l, lock_t *ll){
  simulate_atomic_exchange(l, ll, 0);
}
