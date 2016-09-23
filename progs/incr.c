#include "threads.h"
/*#include <stdio.h>*/
#include <stdlib.h>

lock_t ctr_lock;
lock_t thread_lock;
int ctr[1];

/* The counter part */

/*void reset(int *ctr) {
  *ctr = 0;
  }*/

void incr() {
  lock_t *l = &ctr_lock;
  acquire(l);
  int t = ctr[0];
  ctr[0] = t + 1;
  release(l);  
}

int read() {
  acquire( &ctr_lock );
  int t = ctr[0];
  release ( &ctr_lock );
  return t;
}

void *thread_func(void *args) {
  lock_t *l = &thread_lock;
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release2(l);
  return (void *)NULL;
}

int main(void)
{
  ctr[0] = 0;
  lock_t *lockc = &ctr_lock;
  lock_t *lockt = &thread_lock;
  makelock(lockc);
  release(lockc);
  makelock(lockt);
  /* Spawn */
  spawn_thread((void *)&thread_func, (void *)NULL);
   
  //Increment the counter
  incr();

  /*JOIN */
  acquire(lockt);
  int t = read();
  acquire(lockc);
  /* free the locks */
  freelock2(lockt);
  freelock(lockc);
   
  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}
