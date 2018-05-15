//#include <stdlib.h>
#include "stdlib.h"
//#include <stdio.h>
#include "atomic_exchange.h"
//#include "threads.h"
//#include <stdatomic.h>



void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

//This will be replaced by an external call eventually.
void *memset(void *s, int c, size_t n){
  int *p = (int *)s;
  for(size_t i = 0; i < n / 4; i++)
    p[i] = c;
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

//registrar function
buf_id *reading[N], *last_read[N];

void initialize_channels(){
  for(int i = 0; i < B; i++){
    buffer *b = surely_malloc(sizeof(buffer));
    memset(b, 0, sizeof(buffer));
    bufs[i] = b;
  }
  for(int r = 0; r < N; r++){
    buf_id *c = surely_malloc(sizeof(buf_id));
    *c = First;
    comm[r] = c;
    c = surely_malloc(sizeof(buf_id));
    reading[r] = c;
    c = surely_malloc(sizeof(buf_id));
    last_read[r] = c;
    lock_t *l = surely_malloc(sizeof(lock_t));
    lock[r] = l;
    makelock(l);
    release(l);
  }
}

//reader functions
void initialize_reader(int r){
  buf_id *rr = reading[r];
  buf_id *lr = last_read[r];
  *rr = Empty;
  *lr = 1;
}

buf_id start_read(int r){
  buf_id b;
  buf_id *c = comm[r];
  lock_t *l = lock[r];
  buf_id *rr = reading[r];
  buf_id *lr = last_read[r];
  b = simulate_atomic_exchange(c, l, Empty);
  if(b >= 0 && b < B)
    *lr = b;
  else
    b = *lr;
  *rr = b;
  return b;
}

void finish_read(int r){
  //r is no longer using the buffer
  buf_id *rr = reading[r];
  *rr = Empty;
}

//writer functions
buf_id last_taken[N];
buf_id writing, last_given;

void initialize_writer(){
  last_given = First;
  writing = Empty;
  for(int i = 0; i < N; i++)
    last_taken[i] = 1;
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
  buf_id w = writing;
  for(int r = 0; r < N; r++){
    buf_id *c = comm[r];
    lock_t *l = lock[r];
    buf_id b = simulate_atomic_exchange(c, l, w);
    if(b == Empty)
      last_taken[r] = last;
  }
  last_given = w;
  writing = Empty;
}

void *reader(void *arg){
  int r = *(int *)arg;
  initialize_reader(r);
  while(1){
    buf_id b = start_read(r);
    buffer *buf = bufs[b];
    int v = buf->data;
    //   printf("Reader %d read %d\n", r, v);
    finish_read(r);
  }
  return NULL;
}

void *writer(void *arg){
  initialize_writer();
  unsigned v = 0;
  while(1){
    buf_id b = start_write();
    buffer *buf = bufs[b];
    buf->data = v;
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

