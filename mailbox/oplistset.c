#include "ptr_atomics.h"

typedef struct node { int val; atomic_loc *next; lock_t *lock; } node;

node *head;

node *new_node(int e){
  node *r = surely_malloc(sizeof(node));
  r->val = e;
  r->next = make_atomic(NULL);
  lock_t *l = surely_malloc(sizeof(lock_t));
  makelock(l);
  r->lock = l;
  return r;
}

void del_node(node *n){
  atomic_loc *p = n->next;
  free_atomic(p);
  lock_t *l = n->lock;
  freelock(l);
  free(l);
  free(n);
}

int validate(int e, node *pred, node *curr){
  node *succ = head;
  int v = succ->val;
  atomic_loc *n;
  while(v < e){
    n = succ->next;
    succ = (node*)load_SC(n);
    v = succ->val;
  }
  n = pred->next;
  node *p = load_SC(n);
  return(succ == curr && p == curr);
}

void locate(int e, node **r1, node **r2){
  while(1){
    node *pred = head;
    atomic_loc *n = pred->next;
    node *curr = (node *)load_SC(n);
    int v = curr->val;
    while(v < e){
      pred = curr;
      n = curr->next;
      curr = (node *)load_SC(n);
      v = curr->val;
    }
    lock_t *l1 = pred->lock;
    lock_t *l2 = curr->lock;
    acquire(l1);
    acquire(l2);
    if(validate(e, pred, curr)){
      *r1 = pred;
      *r2 = curr;
      return;
    }
    else{
      release(l1);
      release(l2);
    }
  }
}

int add(int e){
  node *n1, *n3;
  locate(e, &n1, &n3);
  int v = n3->val;
  int result;
  if(v != e){
    node *n2 = new_node(e);
    atomic_loc *n = n2->next;
    store_SC(n, n3);
    n = n1->next;
    store_SC(n, n2);
    result = 1;
  }
  else result = 0;
  lock_t *l = n1->lock;
  release(l);
  l = n3->lock;
  release(l);
  return result;
}

int remove(int e){
  node *n1, *n2;
  locate(e, &n1, &n2);
  int v = n2->val;
  int result;
  if(v == e){
    atomic_loc *n = n2->next;
    node *n3 = load_SC(n);
    n = n1->next;
    store_SC(n, n3);
    result = 1;
  }
  else result = 0;
  lock_t *l = n1->lock;
  release(l);
  l = n2->lock;
  release(l);
  return result;
}
  
