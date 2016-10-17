#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

// concurrent queue implemented with a circular buffer

typedef struct request_t {int data; int timestamp;} request_t;

typedef struct queue {request_t *buf[10]; int length; int head; int tail;
  int next; cond_t *addc; cond_t *remc;} queue;
typedef struct queue_t {queue d; lock_t *lock;} queue_t;

queue_t *q0;
lock_t thread_locks[6];

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

queue_t *q_new(){
  queue_t *newq = (queue_t *) malloc(sizeof(queue_t));
  queue q = newq->d;
  for(int i = 0; i < 10; i++)
    q.buf[i] = NULL;
  q.length = 0;
  q.head = 0;
  q.tail = 0;
  q.next = 0;
  q.addc = (cond_t *) malloc(sizeof(cond_t));
  makecond(q.addc);
  q.remc = (cond_t *) malloc(sizeof(cond_t));
  makecond(q.remc);
  newq->lock = (lock_t *) malloc(sizeof(lock_t));
  makelock(newq->lock);
  return newq;
}

void q_del(queue_t *tgt){
  acquire(tgt->lock);
  queue q = tgt->d;
  free(q.buf);
  freecond(q.addc);
  freecond(q.remc);
  freelock(tgt->lock);
}

void q_add(queue_t *tgt, request_t *request){
  void *l = tgt->lock;
  acquire(l);
  queue *q = &(tgt->d);
  int len = q->length;
  while(len >= 10){
    cond_t* c = q->addc;
    waitcond(c, l);
    len = q->length;
  }
  int n = q->next;
  request->timestamp = n;
  q->next = n + 1;
  int t = q->tail;
  q->buf[t] = request;
  q->tail = (t + 1) % 10;
  q->length = len + 1;
  signalcond(q->remc);
  release(l);
}

request_t *q_remove(queue_t *tgt){
  void *l = tgt->lock;
  acquire(l);
  queue q = tgt->d;
  int len = q.length;
  while(len == 0){
    waitcond(q.remc, l);
    len = q.length;
  }
  int h = q.head;
  request_t *r = q.buf[h];
  q.buf[h] = NULL;
  q.head = (h + 1) % 10;
  q.length = len - 1;
  signalcond(q.addc);
  release(l);
  return r;
}

void *f(void *arg){
  request_t *request;
  for(int i = 0; i < 3; i++){
    request = get_request();
    q_add(q0, request);
  }
  release2(arg);
  return NULL;
}

void *g(void *arg){
  request_t *request;
  int res[3];
  int j;
  for(int i = 0; i < 3; i++){
    request_t *request = q_remove(q0);
    j = process_request(request);
  }
  release2(arg);
  return NULL;
}
    
int main(void)
{
  q0 = q_new();
  
  for(int i = 0; i < 3; i++){
    makelock((void *)&thread_locks[i]);
    spawn((void *)&f, (void *)&thread_locks[i]);
    //printf("Spawned producer %d\n", i + 1);
  }

  for(int i = 0; i < 3; i++){
    makelock((void *)&thread_locks[i+3]);
    spawn((void *)&g, (void *)&thread_locks[i+3]);
    //printf("Spawned consumer %d\n", i + 1);
  }

  for(int i = 0; i < 6; i++){
    acquire((void *)&thread_locks[i]);
    freelock2((void *)&thread_locks[i]);
    //printf("Joined %d\n", i + 1);
  }
  
  q_del(q0);
}
