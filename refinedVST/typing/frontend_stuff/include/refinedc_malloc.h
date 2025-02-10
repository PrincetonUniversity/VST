
/**
 * RefinedC support for malloc
 */
#ifndef REFINEDC_MALLOC_H
#define REFINEDC_MALLOC_H

#include <stddef.h>
#include <assume.h>

//@rc::import malloc from refinedc.typing

//@rc::context `{!mallocG Σ}

/** Specifications for standard library allocation and deallocation functions */
[[rc::parameters("n : Z")]]
[[rc::args("n @ int<size_t>")]]
[[rc::returns("optional<&own<malloced<n, uninit<{ly_max_align (Z.to_nat n)}>>>, null>")]]
void *malloc(size_t sz);

// TODO: In theory we can weaken [ly_max_align (Z.to_nat n)] to
// [ly_with_align (Z.to_nat n) 1] since [malloc_block] guarantees the
// alignment of the location, but the automation currently does not like that
[[rc::parameters("n : Z")]]
[[rc::args("&own<malloced_early<n, uninit<{ly_max_align (Z.to_nat n)}>>>")]]
void free(void *p);

/** Commonly used wrappers for malloc and free */
[[rc::parameters("n : Z")]]
[[rc::args("n @ int<size_t>")]]
[[rc::returns("&own<malloced<n, uninit<{ly_max_align (Z.to_nat n)}>>>")]]
void *xmalloc(size_t sz) {
  void *p = malloc(sz);
  if(p == NULL) { safe_exit(); }
  return p;
}

#endif
