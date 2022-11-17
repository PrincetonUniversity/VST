/* threads library specified for the Verified Software Toolchain */

#include <stdlib.h>
#include <threads.h>
#include <SC_atomics.h>
#include <VSTthreads.h>

void spawn(int (*f)(void*), void* args) {
  thrd_t t;
  if(thrd_create(&t, f, args) != thrd_success)
    exit(1);
  return;
}

void exit_thread(int r) {
  thrd_exit(r);
}
