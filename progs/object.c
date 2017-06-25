#include <stddef.h>

extern void *malloc (size_t n);
extern void exit(int code);

struct object;

struct methods {
  void (*reset) (struct object *self);
  int (*twiddle) (struct object *self, int i);
};

struct object {
  struct methods *mtable;
};

struct foo_object {
  struct methods *mtable;
  int data;
};


void foo_reset (struct foo_object *self) {
  self -> data = 0;
}

int foo_twiddle (struct foo_object *self, int i) {
  int d = self->data;
  self -> data = d+2*i;
  return d+i;
}

struct methods foo_methods = {foo_reset, foo_twiddle};

struct object *make_foo(void) {
  struct foo_object *p;
  p = (struct foo_object *) malloc (sizeof (struct foo_object));
  if (!p) exit(1);
  p->mtable = &foo_methods;
  p->data = 0;
  return (struct object *) p;
}

int main(void) {
  struct object *p;
  struct methods *mtable;
  void (*p_reset) (struct object *self);
  int (*p_twiddle) (struct object *self, int i);
  int i;
  p = make_foo();
  mtable = p->mtable;
  p_reset = mtable->reset;
  p_reset(p);
  mtable = p->mtable;
  p_twiddle = mtable->twiddle;
  i = p_twiddle(p,3);
  return i;
}

  
    
  
