#include "atomics.h"

typedef struct entry { atomic_loc *key; atomic_loc *value; } entry;

#define ARRAY_SIZE 16384

entry m_entries[ARRAY_SIZE];

void set_item(int key, int value){
  for(int idx = 0;; idx++){
    atomic_loc *i = m_entries[idx].key;
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
  for(int idx = 0;; idx++){
    atomic_loc *i = m_entries[idx].key;
    int probed_key = load_SC(i);
    if(probed_key == key){
      i = m_entries[idx].value;
      return load_SC(i);
    }
    if (probed_key == 0)
      return 0;
  }
}

      
