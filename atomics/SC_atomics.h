#include <stdlib.h>
#include "threads.h"

// define some special cases of the C11 atomics, since it's hard to specify them in general

typedef struct atom_int atom_int;

// names can't conflict with names of builtins
atom_int *make_atomic(int v);
int atom_load(atom_int *tgt);
void atom_store(atom_int *tgt, int v);
int atom_CAS(atom_int *tgt, int *c, int v); // returns a bool
int atom_exchange(atom_int *tgt, int v);

/*atom_ptr make_atom_ptr(void *v);
void* atomic_load_ptr(atom_ptr *tgt);
void atomic_store_ptr(atom_ptr *tgt, void *v);
int atomic_CAS_ptr(atom_ptr *tgt, void **c, void *v); // returns a bool
void* atomic_exchange_ptr(atom_ptr *tgt, void *v);*/
