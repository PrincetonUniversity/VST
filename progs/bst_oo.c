#include <stddef.h>

extern void *mallocN (int n);
extern void freeN(void *p, int n);

struct tree {int key; void *value; struct tree *left, *right;};

typedef struct tree **treebox;

treebox treebox_new(void) {
  treebox p = (treebox) mallocN(sizeof (*p));
  *p=NULL;
  return p;
}

void tree_free(struct tree *p) {
  struct tree *pa, *pb;
  if (p!=NULL) {
    pa=p->left;
    pb=p->right;
    freeN(p, sizeof (*p));
    tree_free(pa);
    tree_free(pb);
  }
}

void treebox_free(treebox b) {
  struct tree *t = *b;
  tree_free(t);
  freeN(b, sizeof (*b));
}

void * * subscr (treebox t, int key) {
  struct tree *p;
  for(;;) {
    p = *t;
    if (p==NULL) {
      p = (struct tree *) mallocN (sizeof *p);
      p->key=key; p->value=NULL; p->left=NULL; p->right=NULL;
      *t=p;
      return (&p->value);
    } else {
      int y = p->key;
      if (key<y)
	t= &p->left;
      else if (y<key)
	t= &p->right;
      else {
	return (&p->value);
      }
    }
  }
}

void set (treebox t, int x, void *value) {
  void * * p = subscr(t, x);
  * p = value;
}

void * get (treebox t, int x) {
  void * * p = subscr(t, x);
  void * v = * p;
  return v;
}

void turn_left(treebox _l, struct tree * l, struct tree * r) {
  struct tree * mid;
  mid = r->left;
  l->right = mid;
  r->left = l;
  *_l = r;
}

void pushdown_left (treebox t) {
  struct tree *p, *q;
  for(;;) {
    p = *t;
    q = p->right;
    if (q==NULL) {
      q = p->left;
      *t = q;
      freeN(p, sizeof (*p));
      return;
    } else {
      turn_left(t, p, q);
      t = &q->left;
    }
  }
}

void delete (treebox t, int x) {
  struct tree *p;
  for(;;) {
    p = *t;
    if (p==NULL) {
      return;
    } else {
      int y = p->key;
      if (x<y)
	t= &p->left;
      else if (y<x)
	t= &p->right;
      else {
	pushdown_left(t);
	return;
      }
    }
  }
}

int main (void) {
  treebox p;
  p = treebox_new();
  set(p,3,"three");
  set(p,1,"one");
  set(p,4,"four");
  set(p,1,"ONE");
  treebox_free(p);
  return 0;
}

