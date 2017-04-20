#include "atomics.h"

typedef struct node { atomic_loc *version; atomic_loc *data[8]; } node;

void read(node *n, int *out){
  while(1){
    atomic_loc *ver = n->version;
    int snap = load_SC(ver);
    if(snap & 1 == 1) continue; //already dirty
    for(int i = 0; i < 8; i++){
      atomic_loc *l = n->data[i];
      out[i] = load_SC(l);
    }
    int v = load_SC(ver);
    if(v == snap) return;
  }
}

//We can make this work for multiple writers by enclosing it in a similar loop.
void write(node *n, int *in){
  atomic_loc *ver = n->version;
  int v = load_SC(ver);
  store_SC(ver, v + 1);
  for(int i = 0; i < 8; i++){
    atomic_loc *l = n->data[i];
    int d = in[i];
    store_SC(l, d);
  }
  store_SC(ver, v + 2);
}
