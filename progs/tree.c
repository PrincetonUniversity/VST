#include <stddef.h>

struct Xnode {
  struct XList * list;
  unsigned int v;
};

struct XList {
  struct Xnode * node;
  struct XList * next;
};

struct Ynode {
  struct YList * list;
  unsigned int v;
};

struct YList {
  struct BinaryTree * tree;
  struct YList * next;
};

struct BinaryTree {
  struct Ynode * node;
  struct BinaryTree * left;
  struct BinaryTree * right;
};

void Xnode_add(struct Xnode * p) {
  struct XList * q;
  if (p == NULL)
    return;
  p -> v ++;
  for (q = p -> list; q != NULL; q = q -> next)
    Xnode_add(q -> node);
}

void Ynode_add(struct Ynode * p);
void YList_add(struct YList * p);
void YTree_add(struct BinaryTree * p);

void Ynode_add(struct Ynode * p) {
  if (p == NULL)
    return;
  p -> v ++;
  YList_add (p -> list);
}

void YList_add(struct YList * p) {
  if (p == NULL)
    return;
  YTree_add(p -> tree);
  YList_add(p -> next);
}

void YTree_add(struct BinaryTree * p) {
  if (p == NULL)
    return;
  Ynode_add(p -> node);
  YTree_add(p -> left);
  YTree_add(p -> right);
}

void Xfoo(struct Xnode * p) {
  struct Xnode q;
  if (p == NULL)
    return;
  q.list = p -> list;
  q.v = p -> v;
  Xnode_add (&q);
  p -> list = q.list;
  p -> v = q.v;
}

int main () {
}

  
