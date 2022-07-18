#include "mmap0.h"

/* About format and alignment:
malloc returns a pointer aligned modulo ALIGN*WORD, preceded by the chunk
size as an unsigned integer in WORD bytes.  Given a well aligned large block
from the operating system, the first (WORD*ALIGN - WORD) bytes are wasted
in order to achieve the alignment.  The chunk size is at least the size
given as argument to malloc.
*/

/* TODO WASTE and ALIGN probably not needed here */ 

enum {WORD = sizeof(size_t)};

enum {ALIGN = 2};

enum {WASTE = WORD*ALIGN - WORD}; 

enum {BIGBLOCK = (2<<16)*WORD};

enum {BINS = 50};

void *malloc(size_t);

void free(void *);


/* Pre-fill the free list for chunks of size n, adding as many
chunks as can be obtained from the provided big block.
Assumes 0 <= n <= maxSmallChunk. 
Assumes p points to a well aligned block of size BIGBLOCK bytes. 
*/
void pre_fill(size_t n, void *p);

/* Try to add at least r chunks to the free list for size n.
Returns the actual number added.
Assumes 0 <= n and 0 <= r.
*/
int try_pre_fill(size_t n, int r);

