#ifndef _LOCK_H_
#define _LOCK_H_

#include "SC_atomics.h"

typedef atom_int lock_t;

lock_t* makelock();
void freelock(lock_t *lock);
void acquire(lock_t *lock);
void release(lock_t *lock);

#endif
