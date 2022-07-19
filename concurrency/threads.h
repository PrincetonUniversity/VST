#ifndef _VST_THREADS_H_
#define _VST_THREADS_H_

#include "../atomics/SC_atomics.h"

typedef atom_int lock_t;

lock_t* makelock(void);

void freelock(lock_t *lock);

void acquire(lock_t *lock);

void release(lock_t *lock);



void spawn(int (*f)(void*), void* args);

/*void makecond(cond_t *cond);

void freecond(cond_t *cond);

void waitcond(cond_t *cond, void *mutex);
//Pthreads only requires a mutex for wait

void signalcond(cond_t *cond);*/

#endif
