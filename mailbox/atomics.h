#include "threads.h"

int simulate_atomic_load(int *tgt, lock_t *l);
void simulate_atomic_store(int *tgt, lock_t *l, int v);
int simulate_atomic_CAS(int *tgt, lock_t *l, int c, int v);
