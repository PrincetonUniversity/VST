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
typedef int buf_id;
const buf_id Empty = -1;
const buf_id First = 0;

typedef struct buffer {int data;} buffer;
buffer bufs[B];
lock_t *lock[N];
buf_id comm[N];

//This could be replaced by an external call once we figure out the right spec.
buf_id simulate_atomic_exchange(int r, buf_id v){
  buf_id x;
  lock_t *l = lock[r];
  acquire(l);
  x = comm[r];
  comm[r] = v;
  release(l);
  return x;
}

//registrar function
void initialize_channels(){
  for(int r = 0; r < N; r++){
    comm[r] = First;
    lock_t *l = surely_malloc(sizeof(lock_t));
    lock[r] = l;
    makelock(l);
    release(l);
  }
  memset(&bufs[First], 0, sizeof (bufs[First]));
}

//reader functions
buf_id reading[N], last_read[N]; //these should actually be separate and private to each reader

void initialize_reader(int r){
  reading[r] = Empty;
  last_read[r] = First;
}

buf_id start_read(int r){
  buf_id b;
  //  b = atomic_exchange(&comm[r], Empty);
  b = simulate_atomic_exchange(r, Empty);
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
  available[last_given] = 0;
  for(int r = 0; r < N; r++){
    if(last_taken[r] != Empty)
      available[last_taken[r]] = 0;
  }
  for(int i = 0; i < B; i++){
    if(available[i]){
      writing = i;
      return i;
    }
  }
  exit(1); //no available buffer, should be impossible
}

void finish_write(){
  //make current buffer available to all readers
  for(int r = 0; r < N; r++){
    //    buf_id b = atomic_exchange(&comm[r], writing);
    buf_id b = simulate_atomic_exchange(r, writing);
    if(b == Empty)
      last_taken[r] = last_given;
  }
  last_given = writing;
  writing = Empty;
}

void *reader(void *arg){
  int r = *(int *)arg;
  initialize_reader(r);
  while(1){
    buf_id b = start_read(r);
    int v = bufs[b].data;
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
    buffer buf = {.data = v};
    bufs[b] = buf;
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
  
