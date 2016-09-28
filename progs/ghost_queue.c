#include "threads.h"
//#include <stdio.h>
#include <stdlib.h>

// Derived from Example 6-11 in
// Multithreaded Programming with Pthreads, Lewis & Berg

typedef struct request_t {int data;} request_t;

lock_t requests_lock;
lock_t thread_locks[3];
int length[1];
cond_t requests_consumer, requests_producer;
request_t *buf[10];
int next[1];

request_t *get_request(){
  request_t *request;
  request = (request_t *) malloc(sizeof(request_t));
  acquire(&requests_lock);
  int n = next[0];
  next[0] = n + 1;
  request->data = n;
  release(&requests_lock);
  return (request);
}

int process_request(request_t *request){
  int d = request->data;
  free(request);
  return d;
}

void add(request_t *request){
  acquire(&requests_lock);
  int len = length[0];
  while(len >= 10){
    wait(&requests_producer, &requests_lock);
    len = length[0];
  }
  buf[len] = request;
  length[0] = len + 1;
  signal(&requests_consumer);
  release(&requests_lock);
}

request_t *remove(void){
  acquire(&requests_lock);
  int len = length[0];
  while(len == 0){
    wait(&requests_consumer, &requests_lock);
    len = length[0];
  }
  request_t *r = buf[len - 1];
  buf[len - 1] = NULL;
  length[0] = len - 1;
  signal(&requests_producer);
  release(&requests_lock);
  return r;
}

void *f(void *arg){
  request_t *request;
  int res[3];
  int j, last;
  lock_t *l = (lock_t *)arg;
  for(int i = 0; i < 3; i++){
    request = get_request();
    last = request->data;
    add(request);
  }
  for(i = 0; i < 3; i++){
    request = remove();
    j = process_request(request);
    res[i] = j;
  }
  // result: last < res[0] < res[1] < res[2]
  release2(l);
}

int main(void)
{
  for(int i = 0; i < 10; i++)
    buf[i] = NULL;
  length[0] = 0;
  makelock(&requests_lock);
  release(&requests_lock);
  makecond(&requests_producer);
  makecond(&requests_consumer);
  
  for(i = 0; i < 3; i++){
    makelock(&thread_locks[i]);
    spawn_thread((void *)&f, (void *)&thread_locks[i]);
  }

  for(i = 0; i < 3; i++){
    acquire(&thread_locks[i]);
    freelock2(&thread_locks[i]);
  }

  acquire(&requests_lock);
  freelock(&requests_lock);
  freecond(&requests_producer);
  freecond(&requests_consumer);
  
  return 0;
}
