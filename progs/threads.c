#include <stdlib.h>
#include <pthread.h>
#include "threads.h"

lock_t* makelock(void) {
    return make_atomic(1);
}

void freelock(lock_t *lock) {
    free_atomic(lock);
}

void acquire(lock_t *lock) {
    int b = 0;
    int expected;
    do {
        expected = 0;
        b = atom_CAS(lock, &expected, 1);
    } while (b == 0);
}

void release(lock_t *lock) {
    atom_store(lock, 0);
}

void freelock(void *lock) {
  free_atomic(lock);
  return;
}

void acquire2(void *lock) {
  pthread_mutex_lock((pthread_mutex_t*)lock);
  return;
}

void release(void *lock) {
  pthread_mutex_unlock((pthread_mutex_t*)lock);
  return;
}

void makelock2(void *lock) {
  pthread_mutex_init((pthread_mutex_t*)lock, NULL);
  pthread_mutex_lock((pthread_mutex_t*)lock);
}

void freelock2(void *lock) {
  pthread_mutex_destroy((pthread_mutex_t*)lock);
  return;
}

void release2(void *lock) {
  pthread_mutex_unlock((pthread_mutex_t*)lock);
  return;
}

// is there a non-Pthread way we want to do this?
void spawn(void* (*f)(void*), void* args) {
  pthread_t t;
  pthread_create(&t, NULL, f, args);
  pthread_detach(t);
  return;
}

void exit_thread(void) {
  pthread_exit(NULL);
  return;
}

void makecond(cond_t *cond) {
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
