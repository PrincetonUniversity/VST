#include "gen_atomics.h"

typedef struct entry { int *key; int *value; } entry;

#define ARRAY_SIZE 16384

entry m_entries[ARRAY_SIZE];
lock_t *thread_locks[3];
int *results[3];

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

int integer_hash(int i){
  return (unsigned int) i * (unsigned int) 654435761;
}

void set_item(int key, int value){
  for(int idx = integer_hash(key);; idx++){
    idx &= ARRAY_SIZE - 1;
    int *i = m_entries[idx].key;
    int probed_key = load_SC(i);
    if(probed_key != key){
      //The entry was either free, or contains another key.
      if (probed_key != 0)
	continue;
      int result = CAS_SC(i, 0, key);
      //This bit is a little different, since C11 doesn't have a CAS that returns the old value.
      if(!result){
	//CAS failed, so a key has been added. Is it the one we're looking for?
	probed_key = load_SC(i);
	if(probed_key != key) continue; //Another thread just stole the slot for a different key.
      }
    }
    i = m_entries[idx].value;
    store_SC(i, value);
    return;
  }
}

int get_item(int key){
  for(int idx = integer_hash(key);; idx++){
    idx &= ARRAY_SIZE - 1;
    int *i = m_entries[idx].key;
    int probed_key = load_SC(i);
    if(probed_key == key){
      i = m_entries[idx].value;
      return load_SC(i);
    }
    if (probed_key == 0)
      return 0;
  }
}

//If we want this to be linearizable, then we have to be careful.
//For instance, if an add and a set race, then either the add happens first (and the set's
//value wins), or the add happens second (and fails). So we can't allow an add to
//overwrite a set's value. In other words, the version in hashtable1.c isn't linearizable
//wrt set (and we discovered this through atomicity proofs!).
int add_item(int key, int value){
  for(int idx = integer_hash(key);; idx++){
    idx &= ARRAY_SIZE - 1;
    int *i = m_entries[idx].key;
    int probed_key = load_SC(i);
    if (probed_key != key){
      if (probed_key != 0)
	continue;
      int result = CAS_SC(i, 0, key);
      if(!result){
	probed_key = load_SC(i);
	if(probed_key != key) continue;
      }
    }
    i = m_entries[idx].value;
    return CAS_SC(i, 0, value); //only add if no one else has set the value
  }
}

void init_table(){
  for(int i = 0; i < ARRAY_SIZE; i++){
    int *p = surely_malloc(sizeof(int));
    *p = 0;
    m_entries[i].key = p;
    p = surely_malloc(sizeof(int));
    *p = 0;
    m_entries[i].value = p;
  }
}

/*void freeze_table(int *keys, int *values){
  for(int i = 0; i < ARRAY_SIZE; i++){
    int *l = m_entries[i].key;
    keys[i] = free_atomic(l);
    l = m_entries[i].value;
    values[i] = free_atomic(l);
  }
  }*/

void *f(void *arg){
  int t = *(int *)arg;
  lock_t *l = thread_locks[t];
  int *res = results[t];
  int total = 0;
  free(arg);

  for(int i = 0; i < 3; i++){
    int r = add_item(i + 1, 1);
    if(r) total++;
  }

  *res = total;
  release2(l);
  return NULL;
}

int main(void){
  int total = 0;

  init_table();
  
  for(int i = 0; i < 3; i++){
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    thread_locks[i] = l;
    results[i] = (int *) surely_malloc (sizeof(int));
    makelock((void *)l);
  }

  for(int i = 0; i < 3; i++){
    int *t = (int *) surely_malloc(sizeof(int));
    *t = i;
    spawn((void *)&f, (void *)t);
  }

  for(int i = 0; i < 3; i++){
    lock_t *l = thread_locks[i];
    acquire(l);
    freelock2(l);
    free(l);
    int *r = results[i];
    int i = *r;
    free(r);
    total += i;
  }

  //total should be equal to 3
}
