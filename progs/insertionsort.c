#include <stddef.h>

struct list {int head; struct list *tail;};

struct list *insert(struct list *insert_node, struct list *sorted){
  struct list *index, *previous;
  int sortedvalue, guard, insert_value;

  previous = NULL;
  insert_value = insert_node -> head;
  index = sorted;
  if(index){
    sortedvalue = index -> head;
  }
  guard = index && (insert_value > sortedvalue);

  while(guard){
    previous = index;
    index = index -> tail;
    if(index) {
      sortedvalue = index -> head;
    }
    guard = index && (insert_value > sortedvalue);
  }

  insert_node -> tail = index;
  if(previous){
    previous->tail = insert_node;
    return sorted;
  }

  return insert_node;
}


struct list *insertionsort (struct list *p) {
  struct list *index, *sorted, *next;

  sorted = NULL;
  index = p;

  while(index){
    next = index -> tail;
    index -> tail = NULL;
    sorted = insert(index, sorted);
    index = next;
  }

  return sorted;
}

int main(){
  return 0;
}
