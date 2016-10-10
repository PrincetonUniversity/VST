#include "threads.h"
/*#include <stdio.h>*/
#include <stdlib.h>

lock_t ctr_lock;
lock_t thread_lock;
int ctr[1];

void incr() {
  lock_t *l = &ctr_lock;
  acquire((void*)l);
  int t = ctr[0];
  ctr[0] = t + 1;
  release((void*)l);  
}

int read() {
  acquire( (void*)&ctr_lock );
  int t = ctr[0];
  release ( (void*)&ctr_lock );
  return t;
}

void *thread_func(void *args) {
  lock_t *l = &thread_lock;
  //Increment the counter
  incr();
  //Yield: 'ready to join'.
  release2((void*)l);
  return (void *)NULL;
}

int main(void)
{
  ctr[0] = 0;
  lock_t *lockc = &ctr_lock;
  lock_t *lockt = &thread_lock;
  makelock((void*)lockc);
  release((void*)lockc);
  makelock((void*)lockt);
  /* Spawn */
  spawn((void *)&thread_func, (void *)NULL);
   
  //Increment the counter
  incr();

  /*JOIN */
  acquire((void*)lockt);
  int t = read();
  acquire((void*)lockc);
  /* free the locks */
  freelock2((void*)lockt);
  freelock((void*)lockc);
   
  /*printf("I'm done with a final counter of: %d\n", t);*/

  return t;
}
