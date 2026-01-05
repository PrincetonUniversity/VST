/* threads library specified for the Verified Software Toolchain */

#include <stdlib.h>
#ifdef __STDC_NO_THREADS__
#include <pthread.h>
#else
#include <threads.h>
#endif
#include <VSTthreads.h>

#ifdef __STDC_NO_THREADS__
void spawn(int (*f)(void*), void* args) {
  pthread_t t;
  pthread_create(&t, NULL, (void* (*)(void*))f, args);
  pthread_detach(t);
  return;
}

void exit_thread(int r) {
  pthread_exit(NULL);
  return;
}
#else
void spawn(int (*f)(void*), void* args) {
  thrd_t t;
  if(thrd_create(&t, f, args) != thrd_success)
    exit(1);
  return;
}

void exit_thread(int r) {
  thrd_exit(r);
}
#endif
