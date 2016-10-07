#include <pthread.h>
#include <semaphore.h>
#include "threads.h"

/* gcc -Wall -pthread */

void makelock(lock_t *lock) {
  sem_init((sem_t*)lock, 0, 0);
}

void freelock(lock_t *lock) {
  sem_destroy((sem_t*)lock);
}

void acquire(lock_t *lock) {
  sem_wait((sem_t*)lock);
}

void release(lock_t *lock) {
  sem_post((sem_t*)lock);
}

void freelock2(lock_t *lock) {
  sem_destroy((sem_t*)lock);
}

void release2(lock_t *lock) {
  sem_post((sem_t*)lock);
}

void makethread(thread_t *thread) {
}

void freethread(thread_t *thread) {
}

void spawn(void* (*f)(void*), void* args) {
  pthread_t t;
  pthread_create(&t, NULL, f, args);
  pthread_detach(t);
  return;
}

void join(thread_t *thread) {
  pthread_join((pthread_t)*thread, NULL);
}

/* void exit_thread(void) { */
/*   pthread_exit(NULL); */
/* } */

void makecond(cond_t *cond) {
  pthread_cond_init((pthread_cond_t*)cond, NULL);
}

void freecond(cond_t *cond) {
  pthread_cond_destroy((pthread_cond_t*)cond);
}

void waitcond(cond_t *cond, lock_t *mutex) {
  //  pthread_cond_wait((pthread_cond_t*)cond), (pthread_mutex_t*)mutex);
}

void signalcond(cond_t *cond) {
  //  pthread_cond_signal((pthread_cond_t*)cond);
}
