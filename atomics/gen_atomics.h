#include <stdlib.h>
#include "threads.h"

void *surely_malloc(size_t n);

int load_SC(int *tgt);
void store_SC(int *tgt, int v);
int CAS_SC(int *tgt, int c, int v);
//returns a bool, because that's all C11 has
int atomic_exchange_SC(int *tgt, int v);
int load_acq(int *tgt);
void store_rel(int *tgt, int v);
int CAS_RA(int *tgt, int c, int v);

//int load_relaxed(atomic_loc *tgt);
