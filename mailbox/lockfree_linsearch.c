#include <stdlib.h>
//#include "threads.h"
#include "atomics.h"
//#include <stdatomic.h>

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

typedef struct entry { int key; lock_t *lkey; int value; lock_t *lvalue; } entry;
entry *m_entries[20];

void set_item(int key, int value){
  for(int idx = 0;; idx++){
    entry *e = m_entries[idx];
    int *i = &(e->key);
    lock_t *l = e->lkey;
    int prev_key = simulate_atomic_CAS(i, l, 0, key);
    if((prev_key == 0) || (prev_key == key)){
      i = &(e->value);
      l = e->lvalue;
      simulate_atomic_store(i, l, value);
      return;
    }
  }
}

int get_item(int key){
  for(int idx = 0;; idx++){
    entry *e = m_entries[idx];
    int *i = &(e->key);
    lock_t *l = e->lkey;
    int probed_key = simulate_atomic_load(i, l);
    if(probed_key == key){
      i = &(e->value);
      l = e->lvalue;
      return simulate_atomic_load(i, l);
    }
    if (probed_key == 0)
      return 0;
  }
}

      
