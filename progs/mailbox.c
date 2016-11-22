#include <stdlib.h>
#include <stdio.h>
#include "threads.h"

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

//This will be replaced by an external call eventually.
void *memset(void *s, int c, size_t n){
  unsigned char *p = (unsigned char *)s;
  for(size_t i = 0; i < n; i++)
    p[i] = (unsigned char)c;
  return s;
}

//general data
#define N 3 //number of readers
#define B (N + 2) //number of buffers
#define Empty (-1)
#define First 0
typedef int buf_id;

typedef struct buffer {int data;} buffer;
buffer *bufs[B];
lock_t *lock[N];
buf_id *comm[N];

//This could be replaced by an external call once we figure out the right spec.
int simulate_atomic_exchange(int *tgt, lock_t *l, int v){
  int x;
  acquire(l);
  x = *tgt;
  *tgt = v;
  release(l);
  return x;
}

//The initial state as written is slightly inconsistent:
//last_read is First, but comm[r] is also First as if it
//hasn't been read yet. Either last_read or comm[r] should
//start as Empty instead. comm[r] starting Empty is a bit
//simpler (although it implies that the readers start with
//access to bufs[0] as if they've received the first communication).

//registrar function
void initialize_channels(){
  for(int r = 0; r < N; r++){
    buf_id *c = surely_malloc(sizeof(buf_id));
    *c = Empty;
    comm[r] = c;
    lock_t *l = surely_malloc(sizeof(lock_t));
    lock[r] = l;
    makelock(l);
    release(l);
  }
  for(int i = 0; i < B; i++){
    buffer *b = surely_malloc(sizeof(buffer));
    bufs[i] = b;
  }
  memset(bufs[First], 0, sizeof(buffer));
}

//reader functions
buf_id reading[N], last_read[N]; //these should actually be separate and private to each reader

void initialize_reader(int r){
  reading[r] = Empty;
  last_read[r] = First;
}

buf_id start_read(int r){
  buf_id b;
  b = simulate_atomic_exchange(comm[r], lock[r], Empty);
  if(b >= 0 && b < B)
    last_read[r] = b;
  else
    b = last_read[r];
  reading[r] = b;
  return b;
}

void finish_read(int r){
  //r is no longer using the buffer
  reading[r] = Empty;
}

//writer functions
buf_id last_taken[N];
buf_id writing, last_given;

void initialize_writer(){
  last_given = First;
  writing = Empty;
  for(int i = 0; i < N; i++)
    last_taken[i] = Empty;
}

buf_id start_write(){
  //get a buffer not in use by any reader
  int available[B];
  for(int i = 0; i < B; i++)
    available[i] = 1;
  buf_id last = last_given;
  available[last] = 0;
  for(int r = 0; r < N; r++){
    last = last_taken[r];
    if(last != Empty)
      available[last] = 0;
  }
  for(int i = 0; i < B; i++){
    int avail = available[i];
    if(avail){
      writing = i;
      return i;
    }
  }
  exit(1); //no available buffer, should be impossible
}

void finish_write(){
  //make current buffer available to all readers
  buf_id last = last_given;
  for(int r = 0; r < N; r++){
    buf_id b = simulate_atomic_exchange(comm[r], lock[r], writing);
    if(b == Empty)
      last_taken[r] = last;
  }
  last_given = writing;
  writing = Empty;
}

void *reader(void *arg){
  int r = *(int *)arg;
  initialize_reader(r);
  while(1){
    buf_id b = start_read(r);
    int v = bufs[b]->data;
    //printf("Reader %d read %d\n", r, v);
    finish_read(r);
  }
  return NULL;
}

void *writer(void *arg){
  initialize_writer();
  int v = 0;
  while(1){
    buf_id b = start_write();
    bufs[b]->data = v;
    finish_write();
    v++;
  }
  return NULL;
}

int main(){
  initialize_channels();

  spawn((void *)&writer, NULL);
  
  for(int i = 0; i < N; i++){
    int *d = surely_malloc(sizeof(int));
    *d = i;
    spawn((void *)&reader, (void *)d);
  }

  while(1);
}
  
