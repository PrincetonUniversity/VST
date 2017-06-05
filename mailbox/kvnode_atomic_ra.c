#include "gen_atomics.h"

typedef struct node { int *version; int *data[8]; } node;

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

void read(node *n, int *out){
  while(1){
    int *ver = n->version;
    int snap = load_acq(ver);
    if(snap & 1 == 1) continue; //already dirty
    for(int i = 0; i < 8; i++){
      int *l = n->data[i];
      out[i] = load_acq(l);
    }
    int v = load_acq(ver);
    if(v == snap) return;
  }
}

//We can make this work for multiple writers by enclosing it in a similar loop.
void write(node *n, int *in){
  int *ver = n->version;
  int v = load_acq(ver);
  store_rel(ver, v + 1);
  for(int i = 0; i < 8; i++){
    int *l = n->data[i];
    int d = in[i];
    store_rel(l, d);
  }
  store_rel(ver, v + 2);
}

node *make_node(){
  node *n = surely_malloc(sizeof(node));
  int *p = surely_malloc(sizeof(int));
  *p = 0;
  n->version = p;
  for(int i = 0; i < 8; i++){
    p = surely_malloc(sizeof(int));
    *p = 0;
    n->data[i] = p;
  }
  return n;
}

void *writer(void *n){
  int data[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  for(int i = 0; i < 3; i++){
    for(int j = 0; j < 8; j++){
      int v = data[j];
      data[j] = v + 1;
    }
    write(n, data);
  }
  return NULL;
}

void *reader(void *n){
  int data[8];
  read(n, data);
  return NULL;
}
