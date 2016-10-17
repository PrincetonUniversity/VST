#include "threads.h"
//#include <stdio.h>
#include <stdlib.h>

// Derived from Example 6-11 in
// Multithreaded Programming with Pthreads, Lewis & Berg

typedef struct request_t {int data;} request_t;

lock_t requests_lock;
int length[1];
cond_t requests_consumer, requests_producer;
request_t *buf[10];

void process(int data){ return; }

request_t *get_request(){
  request_t *request;
  request = (request_t *) malloc(sizeof(request_t));
  request->data = 1; //input
  return (request);
}

void process_request(request_t *request){
  int d = request->data;
  process(d);
  free(request);
}

void add(request_t *request){
  int len = length[0];
  buf[len] = request;
  return;
}

request_t *remove(void){
  int len = length[0];
  request_t *r = buf[len - 1];
  buf[len - 1] = NULL;
  return r;
}

void *producer(void *arg){
  request_t *request;

  while(1){
    request = get_request();
    acquire((void*)&requests_lock);
    int len = length[0];
    while(len >= 10){
      waitcond(&requests_producer, (void*)&requests_lock);
      len = length[0];
    }
    add(request);
    length[0] = len + 1;
    release((void*)&requests_lock);
    signalcond(&requests_consumer);
  }
}

void *consumer(void *arg){
  request_t *request;

  while(1){
    acquire((void*)&requests_lock);
    int len = length[0];
    while(len == 0){
      waitcond(&requests_consumer, (void*)&requests_lock);
      len = length[0];
    }
    request = remove();
    length[0] = len - 1;
    release((void*)&requests_lock);
    signalcond(&requests_producer);
    process_request(request);
  }
}

int main(void)
{
  for(int i = 0; i < 10; i++)
    buf[i] = NULL;
  length[0] = 0;
  makelock((void*)&requests_lock);
  release((void*)&requests_lock);
  makecond(&requests_producer);
  makecond(&requests_consumer);
  
  spawn((void *)&consumer, (void *)NULL);
  acquire(&requests_lock);

  int len = length[0];
  while(len != 0){
    waitcond(&requests_producer, (void*)&requests_lock);
    len = length[0];
  }

  release((void*)&requests_lock);
  spawn((void *)&producer, (void *)NULL);

  while(1);
  return 0;
}
