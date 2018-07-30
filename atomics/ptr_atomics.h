#include <stdlib.h>
#include "threads.h"

void *surely_malloc(size_t n);

struct atomic_loc;
typedef struct atomic_loc atomic_loc;

atomic_loc *make_atomic(void *v);
void *free_atomic(atomic_loc *tgt);

void *load_SC(atomic_loc *tgt);
void store_SC(atomic_loc *tgt, void *v);
int CAS_SC(atomic_loc *tgt, void *c, void *v);
//returns a bool, because that's all C11 has
