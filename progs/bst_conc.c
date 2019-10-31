#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

extern void *mallocN (int n);
extern void freeN(void *p, int n);

typedef struct tree {int key; void *value; struct tree_t *left, *right;} tree;
typedef struct tree_t {tree *t; lock_t *lock;} tree_t;

typedef struct tree_t **treebox;


treebox treebox_new(void) {
  treebox p = (treebox) mallocN(sizeof (*p));
  tree_t *newt = (tree_t *) mallocN(sizeof(tree_t));
  *p = newt;
  lock_t *l = (lock_t *) mallocN(sizeof(lock_t));
  makelock(l);
  newt->lock = l;
  newt->t = NULL;
  release(l);
  return p;
}


void tree_free(struct tree_t *tgp) {
  struct tree_t *pa, *pb;
  tree* p;
  void *l = tgp->lock;
  acquire(l);
  p = tgp->t;
  if (p!=NULL) {
    pa=p->left;
    pb=p->right;
    freeN(p, sizeof (*p));
    tree_free(pa);
    tree_free(pb);
    release(l);
  }
}

void treebox_free(treebox b) {
  struct tree_t *t = *b;
  tree_free(t);
  freeN(b, sizeof (*b));
}

void insert (treebox t, int x, void *value) {
  struct tree_t *tgt;
  struct tree *p;
  for(;;) {
    tgt = *t;
    void *l = tgt->lock;
    acquire(l);
    p = tgt->t;
    if (p==NULL) {
      tree_t *p1 = (struct tree_t *) mallocN (sizeof *tgt);
      tree_t *p2 = (struct tree_t *) mallocN (sizeof *tgt);
      p1 ->t = NULL;
      p2 ->t = NULL;
      lock_t *l1 = (lock_t *) mallocN(sizeof(lock_t));
      makelock(l1);
      p1->lock = l1;
      release(l1);
      lock_t *l2 = (lock_t *) mallocN(sizeof(lock_t));
      makelock(l2);
      p2->lock = l2;
      release(l2);
      p = (struct tree *) mallocN (sizeof *p);
      tgt->t = p; 
      p->key=x; p->value=value; p->left=p1; p->right=p2;
      *t=tgt;
      release(l);
      return;
    } else {
      int y = p->key;
      if (x<y){
	t= &p->left;
  release(l);
}else if (y<x){
	t= &p->right;
  release(l);
}else {
	p->value=value;
  release(l);
	return;
      }
    }
  }
}


void *lookup (treebox t, int x) {
  struct tree *p; void *v;
  struct tree_t *tgt;
  tgt = *t;
  void *l = tgt->lock;
  acquire(l);
  p = tgt->t;
  while (p!=NULL) {
    int y = p->key;
    if (x<y){
      tgt=p->left;
      void *l1 = tgt->lock;
      acquire(l1);
      p=tgt->t;
      release(l);
    }else if (y<x){
      tgt=p->right;
      void *l1 = tgt->lock;
      acquire(l1);
      p=tgt->t;
      release(l);
    }else {
      v = p->value;
      release(l);
      return v;
    }
  }
  release(l);
  return NULL;
}

void turn_left(treebox _l, struct tree_t * tgl, struct tree_t * tgr) {
  struct tree_t * mid;
  struct tree * r, *l;
  r = tgr->t;
  mid = r->left;
  void *l1 = mid->lock;
  acquire(l1);
  l = tgl->t;
  l->right = mid;
  r->left = tgl;
  *_l = tgr;
  release(l1);
}

void pushdown_left (treebox t) {
  struct tree *p, *q;
  struct tree_t *tgp, *tgq;
  for(;;) {
    tgp = *t;
    void *lp = tgp->lock;
    acquire(lp);
    p = tgp->t;
    tgq = p->right;
    void *lq = tgq->lock;
    acquire(lq);
    q = tgq->t;
    if (q==NULL) {
      tgq = p->left;
      *t = tgq;
      freeN(p, sizeof (*p));
      release(lp);
      release(lq);
      return;
    } else {
      turn_left(t, tgp, tgq);
      t = &q->left;
      release(lp);
      release(lq);
    }
  }
}

void delete (treebox t, int x) {
  struct tree *p;
  struct tree_t *tgt;
  for(;;) {
    tgt = *t;
    void *l = tgt->lock;
    acquire(l);
    p = tgt->t;
    if (p==NULL) {
      release(l);
      return;
    } else {
      int y = p->key;
      if (x<y){
	t= &p->left;
  release(l);
}else if (y<x){
	t= &p->right;
  release(l);
}else {
  release(l);
	pushdown_left(t);
	return;
      }
    }
  }
}




int main (void) {
  treebox p;
  p = treebox_new();
  insert(p,3,"three");
  insert(p,1,"one");
  insert(p,4,"four");
  insert(p,1,"ONE");
  treebox_free(p);
  return 0;
}
