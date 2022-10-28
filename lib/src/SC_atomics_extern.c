/* C11-style atomic loads and stores (etc.), sequentially consistent mode,
   specified by Mansky et al. using the Verified Software Toolchain. */


#include <SC_atomics.h>

int SC_atomics_placeholder (void) {
  return &make_atomic, &atom_load, &atom_store, &atom_CAS,
    &atom_exchange, &free_atomic, 
    &make_atomic_ptr, &atomic_load_ptr, &atomic_store_ptr, &atomic_CAS_ptr,
    &atomic_exchange_ptr, &free_atomic_ptr,
    0;
}
