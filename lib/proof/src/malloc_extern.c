#include <stddef.h>

extern void *malloc(size_t);
extern void free(void *);

int malloc_placeholder (void) {
  return &malloc, &free, 0;
}
