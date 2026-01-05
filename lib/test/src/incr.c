#include <VSTthreads.h>

typedef struct counter { unsigned ctr; lock_t lock; } counter;
counter c;

void incr() {
  acquire(c.lock);
  c.ctr = c.ctr + 1;
  release(c.lock);
}

unsigned read() {
  acquire(c.lock);
  unsigned t = c.ctr;
  release (c.lock);
  return t;
}

int thread_func(void *thread_lock) {
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release((lock_t )thread_lock);
  return 0;
}

int compute2(void)
{
  c.ctr = 0;
  c.lock = makelock();
  release(c.lock);
  lock_t thread_lock = makelock();
  /* Spawn */
  spawn((void *)&thread_func, (void *)thread_lock);

  //Increment the counter
  incr();

  /*JOIN */
  acquire(thread_lock);
  unsigned t = read();
  acquire(c.lock);
  /* free the locks */
  freelock(thread_lock);
  freelock(c.lock);

  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}

/*
int main(void) {
 return compute2();
}
*/

