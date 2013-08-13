#include <stddef.h>

struct list {int head; struct list *tail;};

struct list *insert(int value, struct list *sorted){
  struct list *index, *previous, newitem;
  int sortedvalue, guard;
  
  index = sorted;
  sortedvalue = index -> head;
  
  guard = index && (value > sortedvalue); 
  //sorted list at sorted, list at item, value at index greater than all
  //items we have gone past
  while(guard){
    previous = index;
    index = sorted -> tail;
    sortedvalue = index -> head;
    guard = index && (value > sortedvalue);
  }
  
  newitem.head = value;
  newitem.tail = index;
  if(previous){
    previous->tail = &newitem;
    return sorted;
  }
  
  return &newitem;
}
//sorted list at sorted

struct list *insertionsort (struct list *p) {
  struct list *index, *sorted;
  int value;
  
  sorted = p;
  sorted -> tail = NULL;
  index = p -> tail;
  while(index){
    value = index->head;
    sorted = insert(value, sorted);
    index = index -> tail;
  }

  return sorted;
}

int main(){
  return 0;
}
