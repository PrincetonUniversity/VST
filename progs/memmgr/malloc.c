#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <sys/mman.h> 
#include "malloc.h"
#include <limits.h>

/* max data size for blocks in bin b (not counting header),
   assuming 0<=b<BINS */
static size_t bin2size(int b) {
    return ((b+1)*ALIGN - 1)*WORD; 
}

/* bin index for blocks of size s (allowing for header and alignment) */
static int size2bin(size_t s) {
  if (s > bin2size(BINS-1))
    return -1;
  else
    return (s+(WORD*(ALIGN-1)-1))/(WORD*ALIGN); 
}

/* for 0 <= b < BINS, bin[b] is null or points to 
   the first 'link field' of a list of blocks (sz,lnk,dat) 
   where sz is the length in bytes of (lnk,dat)
   and the link pointers point to lnk field not to sz.
*/
static void *bin[BINS]; /* initially nulls */

/* assuming p points to well aligned chunk of size BIGBLOCK and s in range for bin sizes
   and tl points to a null-terminated lisk of s-chunks, 
   return a list of s-chunks from p followed by those of tl. 
*/
static void *list_from_block(size_t s, char *p, void *tl) {
  int Nblocks = (BIGBLOCK-WASTE) / (s+WORD);   
  char *q = p + WASTE; /* align q+WORD, wasting WASTE bytes */  
  int j = 0; 
  while (j != Nblocks - 1) {
    /* q points to start of (sz,lnk,dat), q+WORD (i.e., lnk) is aligned, q+s+WORD is allocated, and  0 <= j < Nblocks 
    */
    ((size_t *)q)[0] = s;
    *((void **)(((size_t *)q)+1)) = q+WORD+(s+WORD); /* addr of next nxt field */
    q += s+WORD; 
    j++; 
  }
  /* finish last block, avoiding expression q+(s+WORD) going out of bounds */
  ((size_t *)q)[0] = s; 
  *((void **)(((size_t *)q)+1)) = tl; /* set lnk of last block */
  return (void*)(p+WASTE+WORD); /* lnk of first block */
}

/* require p points to well aligned chunk of size BIGBLOCK 
   and 0 <= n <= maxSmallChunk
   ensure updated memmgr_res with additional chunks of size n available 
The fixed size BIGBLOCK is a simplification that facilitated verification. 
*/
void pre_fill(size_t n, void *p) {
  int b = size2bin(n);
  bin[b] = list_from_block(bin2size(b), p, bin[b]);
}

/* requires 0 <= n and 0 <= req; only useful if n <= maxSmallChunk
   ensures 0 <= result 
           and result is how many chunks of size n have been pre-allocated 
*/
int try_pre_fill(size_t n, int req) {
  if (bin2size(BINS-1) < n) 
    return 0;
  int b = size2bin(n);
  int ful = 0; /* fulfilled part of request */
  int chunks = (BIGBLOCK - WASTE) / (bin2size(b) + WORD); 
  /* loop can be written with disjunctive guard but clight turns that into for(;;)/break */
  while (0 < req - ful) {
    if (INT_MAX - ful < chunks) /* would wrap */
      return ful;  
    char *p = (char *) mmap0(NULL, BIGBLOCK, -1);
    if (p==NULL) 
      return ful; 
    else {
      pre_fill(n,p);
      ful += chunks; 
    }
  }
  return ful; 
}

/* returns pointer to a null-terminated list of free blocks for bin b, obtained from mmap0 */
static void *fill_bin(int b) {
  size_t s = bin2size(b);
  char *p = (char *) mmap0(NULL, BIGBLOCK, -1);
  if (p==NULL) 
    return NULL;
  else 
    return list_from_block(s, p, NULL);
}     


static void *malloc_small(size_t nbytes) {
  int b = size2bin(nbytes);
  void *q;
  void *p = bin[b];
  if (!p) {
    p = fill_bin(b);
    if (!p) 
      return NULL;
    else 
      bin[b] = p;
  }
  q = *((void **)p);
  bin[b] = q;
  return p;
}

static void *malloc_large(size_t nbytes) {
  char *p = (char *)mmap0(NULL, nbytes+WASTE+WORD, -1); 
  if (p==NULL) 
    return NULL;
  else { 
    ((size_t *)(p+WASTE))[0] = nbytes; 
   return (void*) (p+WASTE+WORD);
  }
}


static void free_small(void *p, size_t s) {
  int b = size2bin(s);
  void *q = bin[b];
  *((void **)p) = q;
  bin[b]=p;
}

static void free_large(void *p, size_t s) {
    munmap( ((char*)p) - (WASTE + WORD), s+WASTE+WORD );
}

void free(void *p) {
  if (p != NULL) {
    size_t s = (size_t)(((size_t *)p)[-1]);
    if (s <= bin2size(BINS-1))
      free_small(p,s);
    else
      free_large(p,s);
  }
}

void *malloc(size_t nbytes) {
  if (nbytes > bin2size(BINS-1))
    return malloc_large(nbytes);
  else 
    return malloc_small(nbytes);
}
