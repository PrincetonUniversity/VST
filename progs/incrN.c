#include "../concurrency/threads.h"
//#include <stdio.h>

#define N 5

lock_t *ctr_lock;
unsigned ctr;

lock_t *thread_lock[N];

void init_ctr(){
  ctr = 0;
  ctr_lock = makelock();
  release(ctr_lock);
}

void dest_ctr(){
  acquire(ctr_lock);
  freelock(ctr_lock);
}

void incr() {
  acquire(ctr_lock);
  unsigned t = ctr;
  ctr = t + 1;
  release(ctr_lock);
}

void *thread_func(void *args) {
  lock_t *l = (lock_t*)args;
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release2(l);
  return 0;
}

int main(void)
{
  init_ctr();

  for(int i = 0; i < N; i++){
    thread_lock[i] = makelock();
    spawn((void*)&thread_func, (void*)thread_lock[i]);
  }
  
  /*JOIN */
  for(int i = 0; i < N; i++){
    acquire(thread_lock[i]);
    freelock2(thread_lock[i]);
  }

  dest_ctr();
  unsigned t = ctr;
  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}
