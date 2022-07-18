/* restricted spec for our purposes
precond: addr == NULL 
         prot == PROT_READ|PROT_WRITE
         off == 0
         flags == MAP_PRIVATE|MAP_ANONYMOUS 
         fildes == -1 
postcond: 
  if ret != MAP_FAILED then ret points to page-aligned block of size len bytes 
*/ 
extern void *mmap(void *addr, size_t len, int prot, int flags, int fildes, off_t off);

/* shim for mmap that uses null in place of MAP_FAILED */
/*void* mmap0(void *addr, size_t len, int prot, int flags, int fildes, off_t off);*/
void* mmap0(void *addr, size_t len, int fildes);

/* restricted spec for our purposes
precond: addr through addr+len was allocated by mmap and is a multiple of PAGESIZE
postcond: if ret==0 then the memory was freed.
*/ 
extern int munmap(void *addr, size_t len);
