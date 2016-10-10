#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

// concurrent queue implemented with a circular buffer

typedef struct request_t {int data; int timestamp;} request_t;

lock_t requests_lock;
lock_t thread_locks[3];
int length[1];
int ends[2];
cond_t requests_consumer, requests_producer;
request_t *buf[10];
int next[1];

request_t *get_request(){
  request_t *request;
  request = (request_t *) malloc(sizeof(request_t));
  request->data = 1;
  return (request);
}

int process_request(request_t *request){
  int d = request->timestamp;
  free(request);
  return d;
}

void q_add(request_t *request){
  acquire((void *)&requests_lock);
  int len = length[0];
  while(len >= 10){
    waitcond(&requests_producer, (void *)&requests_lock);
    len = length[0];
  }
  int n = next[0];
  request->timestamp = n;
  next[0] = n + 1;
  int tail = ends[1];
  buf[tail] = request;
  ends[1] = (tail + 1) % 10;
  length[0] = len + 1;
  signalcond(&requests_consumer);
  release((void *)&requests_lock);
}

request_t *q_remove(void){
  acquire(&requests_lock);
  int len = length[0];
  while(len == 0){
    waitcond(&requests_consumer, (void *)&requests_lock);
    len = length[0];
  }
  int head = ends[0];
  request_t *r = buf[head];
  buf[head] = NULL;
  ends[0] = (head + 1) % 10;
  length[0] = len - 1;
  signalcond(&requests_producer);
  release((void *)&requests_lock);
  return r;
}

void *f(void *arg){
  request_t *request;
  int res[3];
  int j;
  for(int i = 0; i < 3; i++){
    request = get_request();
    q_add(request);
  }
  for(int i = 0; i < 3; i++){
    request = q_remove();
    j = process_request(request);
    res[i] = j;
    //    scanf("%d", &j);
  }
  //printf("%d %d %d\n", res[0], res[1], res[2]);
  // result: res[0] < res[1] < res[2]
  release2(arg);
  return (void *)NULL;
}

int main(void)
{
  for(int i = 0; i < 10; i++)
    buf[i] = NULL;
  length[0] = 0;
  ends[0] = 0;
  ends[1] = 0;
  next[0] = 0;
  makelock((void *)&requests_lock);
  release((void *)&requests_lock);
  makecond(&requests_producer);
  makecond(&requests_consumer);
  
  for(int i = 0; i < 3; i++){
    makelock((void *)&thread_locks[i]);
    spawn((void *)&f, (void *)&thread_locks[i]);
    //printf("Spawned %d\n", i + 1);
  }

  for(int i = 0; i < 3; i++){
    acquire((void *)&thread_locks[i]);
    freelock2((void *)&thread_locks[i]);
    //printf("Joined %d\n", i + 1);
  }

  acquire((void *)&requests_lock);
  freelock((void *)&requests_lock);
  freecond(&requests_producer);
  freecond(&requests_consumer);
}
