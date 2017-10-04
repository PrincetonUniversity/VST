//Fine-grained pessimistic list-based set from
//Proving Correctness of Highly-Concurrent Linearisable Objects, Vafeiadis et al.

#include <stdlib.h>
#include "threads.h"

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

typedef struct node { int val; struct node *next; lock_t *lock; } node_t;

typedef struct node_pair { node_t *fst; node_t *snd; } node_pair;

node_t *head;

node_t *new_node(int e){
  node_t *n = surely_malloc(sizeof(node_t));
  lock_t *l = surely_malloc(sizeof(lock_t));
  n->val = e;
  n->lock = l;
  makelock(l);
  release(l);
  return n;
}

void del_node(node_t *n){
  lock_t *l = n->lock;
  acquire(l);
  freelock(l);
  free(l);
  free(n);
}

node_pair *locate(int e){
  node_t *pred = head;
  lock_t *l1 = pred->lock;
  acquire(l1);
  node_t *curr = pred->next;
  lock_t *l2 = curr->lock;
  acquire(l2);
  int v = curr->val;
  while(v < e){
    release(l1);
    pred = curr;
    l1 = l2;
    curr = curr->next;
    l2 = curr->lock;
    acquire(l2);
    v = curr->val;
  }
  node_pair *result = surely_malloc(sizeof(node_pair));
  result->fst = pred;
  result->snd = curr;
  return result;
}

int add(int e){
  node_pair *r = locate(e);
  node_t *n1 = r->fst;
  node_t *n3 = r->snd;
  int v = n3->val;
  int result;
  lock_t *l;
  free(r);
  if(v != e){
    node_t *n2 = new_node(e);
    n2->next = n3;
    n1->next = n2;
    result = 1;
  }
  else result = 0;
  l = n1->lock;
  release(l);
  l = n3->lock;
  release(l);
  return result;
}

int remove(int e){
  node_pair *r = locate(e);
  node_t *n1 = r->fst;
  node_t *n2 = r->snd;
  int v = n2->val;
  int result;
  lock_t *l;
  free(r);
  if(v == e){
    node_t *n3 = n2->next;
    n1->next = n3;
    del_node(n2);
    result = 1;
  }
  else result = 0;
  l = n1->lock;
  release(l);
  l = n2->lock;
  release(l);
  return result;
}
