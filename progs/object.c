#include <stddef.h>

/* This program illustrates object-oriented programming.
  There is an abstract class [object] with methods [reset] and [twiddle].
  The subclass [foo_object] has private field (instance variable) [data],
  and instantiations of the methods, [foo_reset] and [foo_twiddle].
  Every class has its own method table, such as [foo_methods],
  and every object's first field is a pointer to the class's method table.
*/

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

/* Create an instance object of class [foo].  
   Malloc, then initialize the method-table-pointer, then
   initialize the [data] field. 
*/
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

  /* Create a [foo] object */
  p = make_foo();

  /* Do a dynamic method call to the [reset] method */  
  mtable = p->mtable;
  p_reset = mtable->reset;
  p_reset(p);

  /* Do a dynamic method call to the [twiddle] method */  
  mtable = p->mtable;
  p_twiddle = mtable->twiddle;
  i = p_twiddle(p,3);

  /* Done. */
  return i;
}

  
    
  
