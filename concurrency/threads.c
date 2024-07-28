/* Lock-based threads library specified and verified by Mansky et al.
   using the Verified Software Toolchain */

#include <stdlib.h>
// MacOS is never going to implement C11 threads
#ifdef __STDC_NO_THREADS__
#include <pthread.h>
#else
#include <threads.h>
#endif
#include "../atomics/SC_atomics.h"
#include "threads.h"

lock_t makelock(void) {
  return make_atomic(1);
}

void freelock(lock_t lock) {
  free_atomic(lock);
}

void acquire(lock_t lock) { // to really be efficient, this should use futex, at least on Linux
  int b = 0;
  int expected;
  do {
    //atomic_wait(lock, 1); This exists in C++20 but not in C right now.
    expected = 0;
    b = atom_CAS(lock, &expected, 1);
  } while (b == 0);
}

void release(lock_t lock) {
  atom_store(lock, 0);
  //atomic_notify_one(lock);
}



void spawn(int (*f)(void*), void* args) {
#ifdef __STDC_NO_THREADS__
  pthread_t t;
  if (pthread_create(&t, NULL, f, args) != 0) {
    exit(1);
  }
#else
  thrd_t t;
  if(thrd_create(&t, f, args) != thrd_success)
    exit(1);
#endif
}

void exit_thread(int r) {
#ifdef __STDC_NO_THREADS__
  pthread_exit(NULL);
#else
  thrd_exit(r);
#endif
}

/*void makecond(cond_t *cond) {
  pthread_cond_init((pthread_cond_t*)cond, NULL);
}

void freecond(cond_t *cond) {
  pthread_cond_destroy((pthread_cond_t*)cond);
}

void waitcond(cond_t *cond, void *mutex) {
  pthread_cond_wait((pthread_cond_t*)cond, (pthread_mutex_t*)mutex);
}

void signalcond(cond_t *cond) {
  pthread_cond_signal((pthread_cond_t*)cond);
}
*/
