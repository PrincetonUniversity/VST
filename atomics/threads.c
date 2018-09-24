#include <stdlib.h>
#include <pthread.h>
#include "threads.h"

/* gcc -Wall -pthread */

void makelock(void *lock) {
  pthread_mutex_init((pthread_mutex_t*)lock, NULL);
  pthread_mutex_lock((pthread_mutex_t*)lock);
}

void freelock(void *lock) {
  pthread_mutex_destroy((pthread_mutex_t*)lock);
  return;
}

void acquire(void *lock) {
  pthread_mutex_lock((pthread_mutex_t*)lock);
  return;
}

int try_acquire(void *lock) {
  int err = pthread_mutex_trylock((pthread_mutex_t*)lock);
  return(err == 0);
}

void release(void *lock) {
  pthread_mutex_unlock((pthread_mutex_t*)lock);
  return;
}

void freelock2(void *lock) {
  pthread_mutex_destroy((pthread_mutex_t*)lock);
  return;
}

void release2(void *lock) {
  pthread_mutex_unlock((pthread_mutex_t*)lock);
  return;
}

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
