#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

// concurrent queue implemented with a circular buffer

typedef struct request_t {int data; int timestamp;} request_t;

typedef struct queue {request_t *buf[10]; int length; int head; int tail;
  int next; cond_t *addc; cond_t *remc;} queue;
typedef struct queue_t {queue d; lock_t *lock;} queue_t;

queue_t *q0;

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
  queue *q = &(newq->d);
  for(int i = 0; i < 10; i++)
    q->buf[i] = NULL;
  q->length = 0;
  q->head = 0;
  q->tail = 0;
  q->next = 0;
  cond_t *c = (cond_t *) malloc(sizeof(cond_t));
  makecond(c);
  q->addc = c;
  c = (cond_t *) malloc(sizeof(cond_t));
  makecond(c);
  q->remc = c;
  lock_t *l = (lock_t *) malloc(sizeof(lock_t));
  makelock(l);
  newq->lock = l;
  release(l);
  return newq;
}

// Precondition: tgt is empty
void q_del(queue_t *tgt){
  void *l = tgt->lock;
  acquire(l);
  freelock(l);
  free(l);
  queue *q = &(tgt->d);
  cond_t *c = q->addc;
  freecond(c);
  free(c);
  c = q->remc;
  freecond(c);
  free(c);
  free(tgt);
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
  cond_t* c = q->remc;
  signalcond(c);
  release(l);
}

request_t *q_remove(queue_t *tgt){
  void *l = tgt->lock;
  acquire(l);
  queue *q = &(tgt->d);
  int len = q->length;
  while(len == 0){
    cond_t* c = q->remc;
    waitcond(c, l);
    len = q->length;
  }
  int h = q->head;
  request_t *r = q->buf[h];
  q->buf[h] = NULL;
  q->head = (h + 1) % 10;
  q->length = len - 1;
  cond_t *c = q->addc;
  signalcond(c);
  release(l);
  return r;
}

void *f(void *arg){
  request_t *request;
  queue_t *q1 = q0;
  for(int i = 0; i < 3; i++){
    request = get_request();
    q_add(q1, request);
  }
  release2(arg);
  return NULL;
}

void *g(void *arg){
  request_t *request;
  int res[3];
  int j;
  queue_t *q1 = q0;
  for(int i = 0; i < 3; i++){
    request_t *request = q_remove(q1);
    j = process_request(request);
    res[i] = j;
  }
  release2(arg);
  return NULL;
}

int main(void)
{
  q0 = q_new();
  lock_t *thread_locks[6];

  for(int i = 0; i < 3; i++){
    lock_t *l = (lock_t *) malloc(sizeof(lock_t));
    thread_locks[i] = l;
    makelock((void *)l);
    spawn((void *)&f, (void *)l);
    //printf("Spawned producer %d\n", i + 1);
  }

  for(int i = 0; i < 3; i++){
    lock_t *l = (lock_t *) malloc(sizeof(lock_t));
    thread_locks[i + 3] = l;
    makelock((void *)l);
    spawn((void *)&g, (void *)l);
    //printf("Spawned consumer %d\n", i + 1);
  }

  for(int i = 0; i < 6; i++){
    lock_t *l = thread_locks[i];
    acquire((void *)l);
    freelock2((void *)l);
    free(l);
    //printf("Joined %d\n", i + 1);
  }

  queue_t *q1 = q0;
  q_del(q1);
}
