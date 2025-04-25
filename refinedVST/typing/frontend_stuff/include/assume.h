#ifndef ASSUME_H
#define ASSUME_H

#include <assert.h>

// TODO: Add void op_type and let this return void instead of int
[[rc::ensures("False")]]
static inline int safe_exit() {
#if defined (__refinedc__)
  while(1){}
#else
  // TODO: Should this be something else?
  assert(0);
#endif
  return 0;
}

// TODO: use gcc statement expressions with ({ }) here?
#define assume(x) ((!x) ? safe_exit(), 0 : 0)

#endif
