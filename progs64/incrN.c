#include "threads.h"
//#include <stdio.h>
//#include <stdlib.h>

#define NULL 0

#define N 5

lock_t ctr_lock;
unsigned ctr;

lock_t thread_lock[N];

void init_ctr(){
  ctr = 0;
  lock_t *lockc = &ctr_lock;
  makelock((void*)lockc);
  release((void*)lockc);
}

void dest_ctr(){
  lock_t *lockc = &ctr_lock;
  acquire((void*)ctr_lock);
  freelock((void*)ctr_lock);
}

void incr() {
  lock_t *l = &ctr_lock;
  acquire((void*)l);
  unsigned t = ctr;
  ctr = t + 1;
  release((void*)l);
}

void *thread_func(void *args) {
  lock_t *l = (lock_t*)args;
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release2((void*)l);
  return (void *)NULL;
}

int main(void)
{
  init_ctr();

  for(int i = 0; i < N; i++){
    lock_t *l = &(thread_lock[i]);
    makelock((void*)l);
    spawn((void*)&thread_func, (void*)l);
  }
  
  /*JOIN */
  for(int i = 0; i < N; i++){
    lock_t *l = &(thread_lock[i]);
    acquire((void*)l);
    freelock2((void*)l);
  }

  dest_ctr();
  unsigned t = ctr;
  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}
