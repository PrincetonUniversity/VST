#include "../concurrency/threads.h"
//#include <stdio.h>

lock_t *ctr_lock;
lock_t *thread_lock;
unsigned ctr;

void incr() {
  acquire(ctr_lock);
  ctr = ctr + 1;
  release(ctr_lock);
}

unsigned read() {
  acquire(ctr_lock);
  unsigned t = ctr;
  release (ctr_lock);
  return t;
}

int thread_func(void *args) {
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release2(thread_lock);
  return 0;
}

int main(void)
{
  ctr = 0;
  ctr_lock = makelock();
  release(ctr_lock);
  thread_lock = makelock();
  /* Spawn */
  spawn((void *)&thread_func, (void *)NULL);

  //Increment the counter
  incr();

  /*JOIN */
  acquire(thread_lock);
  unsigned t = read();
  acquire(ctr_lock);
  /* free the locks */
  freelock2(thread_lock);
  freelock(ctr_lock);

  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}
