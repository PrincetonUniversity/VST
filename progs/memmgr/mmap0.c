#include <stddef.h>
#include <sys/mman.h> 

/* mmap0 - same as mmap except returns NULL on failure instead of MAP_FAILED.
Because: MAP_FAILED is ((void*)-1) but the C standard disallows comparison 
with -1.  This is enforced by Verifiable C.  So we verify the memory manager 
against the spec of mmap0 and do not verify the body of mmap0.
*/
/*void* mmap0(void *addr, size_t len, int prot, int flags, int fildes, off_t off) {
  void* p = mmap(addr,len,prot,flags,fildes,off);
  if (p == MAP_FAILED) return NULL;
  else return p;
  }*/
/*Specialization using platform-dependent values - previously hardcoded in mmap0_spec*/
void* mmap0(void *addr, size_t len, int fildes) {
  void* p = mmap(addr,len, 3, 4098, fildes,0);
  if (p == MAP_FAILED) return NULL;
  else return p;
  }

/* to convince clightgen to include these identifiers */
int mmap0_placeholder(void) {
  return &munmap,  &mmap0, 0;
}
