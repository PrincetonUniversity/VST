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
  if (p!=NULL) {
    tree_free(p->left);
    tree_free(p->right);
    freeN(p, sizeof (*p));
  }
}

void treebox_free(treebox b) {
  struct tree *t = *b;
  tree_free(t);
  freeN(b, sizeof (*b));
}

void insert (treebox t, int x, void *value) {
  struct tree *p;
  for(;;) {
    p = *t;
    if (p==NULL) {
      p = (struct tree *) mallocN (sizeof *p);
      p->key=x; p->value=value; p->left=NULL; p->right=NULL;
      *t=p;
      return;
    } else {
      int y = p->key;
      if (x<y)
	t= &p->left;
      else if (y<x)
	t= &p->right;
      else {
	p->value=value;
	return;
      }
    }
  }
}

void *lookup (treebox t, int x) {
  struct tree *p; void *v;
  p = *t;
  while (p!=NULL) {
    int y = p->key;
    if (x<y)
      p=p->left;
    else if (y<x)
      p=p->right;
    else {
      v = p->value;
      return v;
    }
  }
  return NULL;
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

