#include <stdatomic.h>

int load_SC(int *tgt){
  return atomic_load(tgt);
}

void store_SC(int *tgt, int v){
  atomic_store(tgt, v);
}

int CAS_SC(int *tgt, int c, int v){
  return atomic_compare_exchange_strong(tgt, c, v);
}

int atomic_exchange_SC(int *tgt, int v){
  return atomic_exchange(tgt, v);
}

int load_acq(int *tgt){
  return atomic_load_explicit(tgt, memory_order_acquire);
}

void store_rel(int *tgt, int v){
  atomic_store_explicit(tgt, v, memory_order_release);
}

int CAS_RA(int *tgt, int c, int v){
  return atomic_compare_exchange_strong_explicit(tgt, c, v, memory_order_acq_rel,
						 memory_order_acquire);
}
