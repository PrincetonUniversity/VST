#include "../concurrency/threads.h"
//#include <stdio.h>

#define N 5

typedef struct counter { unsigned ctr; lock_t *lock; } counter;
counter c;

void init_ctr(){
  c.ctr = 0;
  c.lock = makelock();
  release(c.lock);
}

void dest_ctr(){
  acquire(c.lock);
  freelock(c.lock);
}

void incr() {
  acquire(c.lock);
  c.ctr = c.ctr + 1;
  release(c.lock);
}

int thread_func(void *args) {
  lock_t *l = (lock_t*)args;
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release(l);
  return 0;
}

int main(void)
{
  init_ctr();

  lock_t *thread_lock[N];
  for(int i = 0; i < N; i++){
    thread_lock[i] = makelock();
    spawn((void*)&thread_func, (void*)thread_lock[i]);
  }
  
  /*JOIN */
  for(int i = 0; i < N; i++){
    acquire(thread_lock[i]);
    freelock(thread_lock[i]);
  }

  dest_ctr();
  unsigned t = c.ctr;
  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}
