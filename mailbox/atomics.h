#include <stdlib.h>
#include "threads.h"

void *surely_malloc(size_t n);

struct atomic_loc;
typedef struct atomic_loc atomic_loc;

atomic_loc *make_atomic(int i);
int free_atomic(atomic_loc *tgt);

int load_SC(atomic_loc *tgt);
void store_SC(atomic_loc *tgt, int v);
int CAS_SC(atomic_loc *tgt, int c, int v);
//returns a bool, because that's all C11 has

int load_relaxed(atomic_loc *tgt);
