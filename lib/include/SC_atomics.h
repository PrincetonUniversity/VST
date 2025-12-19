/* C11-style atomic loads and stores (etc.), sequentially consistent mode,
   specified by Mansky et al. using the Verified Software Toolchain. */

#ifndef _SC_ATOMIC_H_
#define _SC_ATOMIC_H_
#include <stdlib.h>

// define some special cases of the C11 atomics, since it's hard to specify them in general

typedef struct atom_int atom_int;
typedef struct atom_ptr atom_ptr;


// names can't conflict with names of builtins
atom_int *make_atomic(int v);
extern int atom_load(atom_int *tgt);
extern void atom_store(atom_int *tgt, int v);
extern int atom_CAS(atom_int *tgt, int *c, int v); // returns a bool
extern int atom_exchange(atom_int *tgt, int v);
extern void free_atomic(atom_int *tgt);

extern atom_ptr *make_atomic_ptr(void * v);
extern void* atomic_load_ptr(atom_ptr *tgt);
extern void atomic_store_ptr(atom_ptr *tgt, void *v);
extern int atomic_CAS_ptr(atom_ptr *tgt, void **c, void *v); // returns a bool
extern void* atomic_exchange_ptr(atom_ptr *tgt, void *v);
extern void free_atomic_ptr(atom_ptr *tgt);

#endif
