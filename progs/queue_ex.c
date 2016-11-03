/*#include <stdio.h>
#include <stdlib.h>
#include "threads.h"*/
#include "conc_queue.c" //for now

queue_t *q0;
lock_t *thread_locks[3];
int results[3][3];

void *f(void *arg){
  int t = *(int *)arg;
  queue_t *q1 = q0;

  for(int i = 0; i < 3; i++){
    int *d = (int *)q_remove(q1);
    int v = *d;
    free(d);
    results[t][i] = v;
  }
  
  lock_t *l = thread_locks[t];
  release2(l);
  return NULL;
}

int main(void){
  int tid[3] = {0, 1, 2};
  queue_t *q1 = q0;
  
  q0 = q_new();

  for(int i = 0; i < 3; i++){
    lock_t *l = (lock_t *) malloc(sizeof(lock_t));
    thread_locks[i] = l;
    makelock((void *)l);
    void *t = &tid[i];
    spawn((void *)&f, t);
  }
  
  for(int i = 0; i < 9; i++){
    int *d = (int *)malloc(sizeof(int));
    *d = i;
    q_add(q1, d);
  }

  for(int i = 0; i < 3; i++){
    lock_t *l = thread_locks[i];
    acquire(l);
    freelock2(l);
    free(l);
  }

  q_del(q1);

  /*  for(int i = 0; i < 3; i++)
    for(int j = 0; j < 3; j++)
    printf("%d ", results[i][j]);*/
      
  //results should merge to input
}
