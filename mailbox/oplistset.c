#include "ptr_atomics.h"

typedef struct node { int val; atomic_loc *next; lock_t *lock; } node;

node *head;

//To ensure that the atomic_loc invariant holds to start with, we need to provide the
//next node at creation.
node *new_node(int e, node *nnext){
  node *r = surely_malloc(sizeof(node));
  r->val = e;
  lock_t *l = surely_malloc(sizeof(lock_t));
  makelock(l);
  r->lock = l;
  release(l);
  atomic_loc *n = make_atomic(nnext);
  r->next = n;
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
  int r = (succ == curr);
  r = r && (p == curr);
  return r;
}

typedef struct node_pair { node *first; node *second; } node_pair;

node_pair *locate(int e){
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
      node_pair *r = surely_malloc(sizeof(node_pair));
      r->first = pred;
      r->second = curr;
      return r;
    }
    else{
      release(l1);
      release(l2);
    }
  }
}

int add(int e){
  //node *n1, *n3;
  //locate(e, &n1, &n3); This doesn't seem to work in Verifiable C.
  node_pair *r = locate(e);
  node *n1 = r->first;
  node *n3 = r->second;
  free(r);
  int v = n3->val;
  int result;
  if(v != e){
    node *n2 = new_node(e, n3);
    atomic_loc *n = n1->next;
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
  /*  node *n1, *n2;
      locate(e, &n1, &n2);*/
  node_pair *r = locate(e);
  node *n1 = r->first;
  node *n2 = r->second;
  free(r);
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
  
