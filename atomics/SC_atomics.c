#include <stdatomic.h>
#include "SC_atomics.h"

struct atom_int { atomic_int i; };
struct atom_ptr { _Atomic(void *) p; };

atom_int *make_atomic(int v){
  atom_int *r = malloc(sizeof(atom_int));
  r->i = v;
  return r;
}

int atom_load(atom_int *tgt){
  return atomic_load(&tgt->i);
}

void atom_store(atom_int *tgt, int v){
  atomic_store(&tgt->i, v);
}

int atom_CAS(atom_int *tgt, int *c, int v){
  return atomic_compare_exchange_strong(&tgt->i, c, v);
}

int atom_exchange(atom_int *tgt, int v){
  return atomic_exchange(&tgt->i, v);
}

/*
atom_ptr make_atom_ptr(void *v){
  atom_ptr r;
  r.p = v;
  return r;
}

void* atomic_load_ptr(atom_ptr *tgt){
  return atomic_load(&tgt->p);
}

void atomic_store_ptr(atom_ptr *tgt, void *v){
  atomic_store(&tgt->p, v);
}

int atomic_CAS_ptr(atom_ptr *tgt, void **c, void *v){
  return atomic_compare_exchange_strong(&tgt->p, c, v);
}

void* atomic_exchange_ptr(atom_ptr *tgt, void *v){
  return atomic_exchange(&tgt->p, v);
}
*/