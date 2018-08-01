#include "atomics.h"
#include <stdatomic.h>

typedef struct atomic_loc { atomic_int ai; } atomic_loc;

atomic_loc *make_atomic(int i){
  atomic_loc *a = malloc(sizeof(atomic_loc));
  atomic_init(&(a->ai), i);
  return a;
}

int free_atomic(atomic_loc *tgt){
  int i = atomic_load(&(tgt->ai));
  free(tgt);
  return i;
}

int load_SC(atomic_loc *tgt){
  return atomic_load(&(tgt->ai));
}

void store_SC(atomic_loc *tgt, int v){
  atomic_store(&(tgt->ai), v);
}

//The C builtin only returns a boolean.
int CAS_SC(atomic_loc *tgt, int c, int v){
  return atomic_compare_exchange_strong(&(tgt->ai), &c, v);
}

int load_relaxed(atomic_loc *tgt){
  return atomic_load_explicit(&(tgt->ai), memory_order_relaxed);
}
