#include "threads.h"
//#include <stdio.h>
//#include <stdlib.h>

#define NULL 0

lock_t mutex, tlock;
cond_t cond;
int data;

void *thread_func(void *args) {
  lock_t *l = &mutex;
  lock_t *t = &tlock;
  cond_t *c = &cond;
  acquire((void*)l);
  data = 1;
  signalcond(c);
  release((void*)l);
  release2((void*)t);
  return (void *)NULL;
}

int main(void)
{
  data = 0;
  lock_t *l = &mutex;
  lock_t *t = &tlock;
  cond_t *c = &cond;
  makecond(c);
  makelock((void*)l);
  makelock((void*)t);
  spawn((void *)&thread_func, (void *)NULL);

  int v = 0;
  while(!v){
    waitcond(c, (void*)l);
    v = data;
  }

  acquire((void*)t);
  freelock2((void*)t);
  freelock((void*)l);
  freecond(c);

  //  printf("I'm done with a final counter of: %d\n", v);
  return v;
}
