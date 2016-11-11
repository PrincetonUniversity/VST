#include <stdio.h>
#include <stdlib.h>
#include "threads.h"
#include "conc_queue.h"

extern void exit(int code);

#define SIZE 10

typedef struct queue {void *buf[SIZE]; int length; int head; int tail;
  cond_t *addc; cond_t *remc;} queue;
typedef struct queue_t {queue d; lock_t *lock;} queue_t;

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

queue_t *q_new(){
  queue_t *newq = (queue_t *) surely_malloc(sizeof(queue_t));
  queue *q = &(newq->d);
  for(int i = 0; i < SIZE; i++)
    q->buf[i] = NULL;
  q->length = 0;
  q->head = 0;
  q->tail = 0;
  cond_t *c = (cond_t *) surely_malloc(sizeof(cond_t));
  makecond(c);
  q->addc = c;
  c = (cond_t *) surely_malloc(sizeof(cond_t));
  makecond(c);
  q->remc = c;
  lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
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

void q_add(queue_t *tgt, void *r){
  void *l = tgt->lock;
  acquire(l);
  queue *q = &(tgt->d);
  int len = q->length;
  while(len >= SIZE){
    cond_t* c = q->addc;
    waitcond(c, l);
    len = q->length;
  }
  int t = q->tail;
  q->buf[t] = r;
  q->tail = (t + 1) % SIZE;
  q->length = len + 1;
  cond_t* c = q->remc;
  signalcond(c);
  release(l);
}

/*Sometimes we don't want to block on remove,
  e.g., if we don't know that something will
  eventually be added. */
void *q_tryremove(queue_t *tgt){
  void *l = tgt->lock;
  acquire(l);
  queue *q = &(tgt->d);
  int len = q->length;
  if(len == 0){
    release(l);
    return NULL;
  }

  int h = q->head;
  void *r = q->buf[h];
  q->buf[h] = NULL;
  q->head = (h + 1) % SIZE;
  q->length = len - 1;
  cond_t *c = q->addc;
  signalcond(c);
  release(l);
  return r;
}

void *q_remove(queue_t *tgt){
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
  void *r = q->buf[h];
  q->buf[h] = NULL;
  q->head = (h + 1) % SIZE;
  q->length = len - 1;
  cond_t *c = q->addc;
  signalcond(c);
  release(l);
  return r;
}

