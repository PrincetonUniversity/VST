#include "threads.h"

#define N 3

struct task {
  lock_t l;
  int arg;
  int result;
} tasks[N];

int f(int i) {
  return i*i;
}

void *g(void *p) {
  struct task *t;
  t=(struct task *)p;
  t->result=f(t->arg);
  release (&t->l);
  return 0;
}

int main(void) {
  int i, s;

  for (i=0; i<N; i++) {
    makelock(&tasks[i].l);
    tasks[i].arg=i;
    spawn(&g,tasks+i);
  }
  s=0;
  for (i=0; i<N; i++) {
    acquire(&tasks[i].l);
    s+=tasks[i].result;
  }
  return s;
}
