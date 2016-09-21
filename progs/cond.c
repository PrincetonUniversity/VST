#include "threads.h"
//#include <stdio.h>
#include <stdlib.h>

lock_t mutex, tlock;
cond_t cond;
int data[1];

void *thread_func(void *args) {
  lock_t *l = &mutex;
  lock_t *t = &tlock;
  cond_t *c = &cond;
  acquire(l);
  data[0] = 1;
  signal(c);
  release(l);
  release2(t);
  return (void *)NULL;
}

int main(void)
{
  data[0] = 0;
  lock_t *l = &mutex;
  lock_t *t = &tlock;
  cond_t *c = &cond;
  makecond(c);
  makelock(l);
  makelock(t);
  spawn_thread((void *)&thread_func, (void *)NULL);

  int v = 0;
  while(!v){
    wait(c, l);
    v = data[0];
  }

  acquire(t);
  freelock2(t);
  freelock(l);
  freecond(c);

  //  printf("I'm done with a final counter of: %d\n", v);
  return v;
}
