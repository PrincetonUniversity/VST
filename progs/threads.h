#ifndef _THREADS_H_
#define _THREADS_H_

#include "SC_atomics.h"

typedef atom_int lock_t;

lock_t* makelock(void);

void makelock(void *lock);

void freelock(void *lock);

void acquire(void *lock);

void release(void *lock);

void makelock2(void *lock); //for recursive locks

void freelock2(void *lock); //for recursive locks

void acquire2(void *lock);

void release2(void *lock); //consumes the lock

void spawn(void* (*f)(void*), void* args);

/*void makecond(cond_t *cond);

void freecond(cond_t *cond);

void waitcond(cond_t *cond, void *mutex);
//Pthreads only requires a mutex for wait

void signalcond(cond_t *cond);*/

/* For now, to abstract over the actual type used,
   all functions take void* arguments. */

#endif
