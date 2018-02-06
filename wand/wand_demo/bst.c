#include <stddef.h>

extern void *mallocN (int n);
extern void freeN(void *p, int n);

struct tree {int key; void *value; struct tree *left, *right;};

typedef struct tree **treebox;

void insert (treebox p, int x, void *value) {
  struct tree *q;
  for(;;) {
    q = * p;
    if (q == NULL) {
      q = (struct tree *) mallocN (sizeof * q);
      q -> key = x; q -> value = value; q -> left = NULL; q -> right = NULL;
      * p = q;
      return;
    } else {
      int y = q -> key;
      if (x < y)
	p = & q -> left;
      else if (y<x)
	p = & q -> right;
      else {
	q -> value = value;
	return;
      }
    }
  }
}

void *lookup (tree * p, int x) {
  void * v;
  while (p != NULL) {
    int y = p -> key;
    if (x < y)
      p = p -> left;
    else if (y<x)
      p = p -> right;
    else {
      v = p -> value;
      return v;
    }
  }
  return NULL;
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

