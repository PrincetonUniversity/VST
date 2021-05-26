#include <stddef.h>

/*Adds color to foo object, with new setcolor/getcolor methods.
  This implementation duplicates the function definitions for
  reset/twiddle/twiddleR for fancyobjects, and lets the global method struct of
  fancy objects point to these duplicated definitions. This enables the
  spec of fancy object to contain specs for reset/twiddle/twiddleR that
  can be applied to a fancyfooinvariant and allows Gprog to contain entries
  for both versions of reset/twiddle/twiddleR.*/


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
  int (*twiddleR) (struct object *self, int i);
};

struct object {
  struct methods *mtable;
};

struct foo_object {
  struct methods *mtable;
  int data;
};


void foo_reset (struct object *self) {
  ((struct foo_object *)self) -> data = 0;
}

int foo_twiddle (struct object *self, int i) {
  int d = ((struct foo_object *)self)->data;
  ((struct foo_object *)self) -> data = d+2*i;
  return d+i;
}

int foo_twiddleR (struct object *self, int i) {
  struct methods *mtable;
  void (*s_reset) (struct object *self);

  int d = ((struct foo_object *)self)->data;
   
  mtable = self->mtable;
  s_reset = mtable->reset;
  s_reset(self);

  ((struct foo_object *)self) -> data = d+2*i;
  return d+i;
}

struct methods foo_methods = {foo_reset, foo_twiddle, foo_twiddleR};

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

/******************A fancy subclass that adds color, but resetting also 
  resets the color - this behavior is thus also observed by (the not
  explicitly overridden but implicitly affect twiddleR but not by twiddle ****************/
struct fancymethods {
  void (*reset) (struct object *self);
  int (*twiddle) (struct object *self, int i);
  int (*twiddleR) (struct object *self, int i);
  void (*setcolor) (struct object *self, int c);
  int (*getcolor) (struct object *self);
};

struct fancyfoo_object {
  struct fancymethods *mtable;
  int data;
  int color;
};

/*Here's the overriding reset method*/
void fancy_reset (struct object *self) {
  ((struct foo_object *)self) -> data = 0;
  ((struct fancyfoo_object *)self)->color = 0;
}


void setcolor (struct object *self, int c) {
  ((struct fancyfoo_object *)self)->color = c;
}

int getcolor (struct object *self) {
  return (((struct fancyfoo_object *)self)->color);
}

struct fancymethods fancyfoo_methods = {fancy_reset, foo_twiddle, foo_twiddleR, setcolor, getcolor};

/* Create an instance object of class [fancyfoo].  
   Malloc, then initialize the method-table-pointer, then
   initialize the [data] and the [color] field. 
*/
struct object *make_fancyfoo(int c) {
  struct fancyfoo_object *p;
  p = (struct fancyfoo_object *) malloc (sizeof (struct fancyfoo_object));
  if (!p) exit(1);
  p->mtable = &fancyfoo_methods;
  p->data = 0;
  p->color = c;
  return ((struct object *) p); 

  /*Doing the casting here and having return type struct object means
    clients can't do any typechecking; this is ok since we're
    verifying everything and that ensures safety. But they need to
    cast to fancyobject when accessing the mtable - see "CAST Q"
    below. So below is an alternative */
}

struct fancyfoo_object *make_fancyfooTyped(int c) {
  struct fancyfoo_object *p;
  p = (struct fancyfoo_object *) malloc (sizeof (struct fancyfoo_object));
  if (!p) exit(1);
  p->mtable = &fancyfoo_methods;
  p->data = 0;
  p->color = c;
  return p; 
}

int main(void) {
  struct object *p;
  struct methods *pmtable;
  void (*p_reset) (struct object *self);
  int (*p_twiddle) (struct object *self, int i);
  int i;
  struct object *q;
  struct fancymethods *qmtable;
  void (*q_reset) (struct object *self); /*Could in fact share with p_reset*/
  void (*q_setcolor) (struct object *self, int c);
  int (*q_getcolor) (struct object *self);
   /*maybe these declarations should take fancyobject arguments; But then, the entries in methods
     took objects arguments, too, rather than foo_objects*/

  /* Create a [foo] object */
  p = make_foo();

  /* Create a [fancyfoo] object */
  q = make_fancyfoo(4);

  /* Do a dynamic method call to the [reset] method on p*/  
  pmtable = p->mtable;
  p_reset = pmtable->reset;
  p_reset(p);

  /* Do a dynamic method call to the [reset] method on q*/
  qmtable = (struct fancymethods *)(q->mtable); /*Cast Q*/
  /*This alternative is not handled quite as well in VST: qmtable = ((struct fancyfoo_object *)q)->mtable;*/

  q_reset = qmtable->reset;
  q_reset(q);

  /* Do a dynamic method call to the [getcolor] method on q*/  
  qmtable = (struct fancymethods *)(q->mtable); /*Cast Q*/
  q_getcolor = qmtable->getcolor;
  int col = q_getcolor(q);

  /* Do a dynamic method call to the [twiddleR] method on p*/  
  pmtable = p->mtable;
  p_twiddle = pmtable->twiddleR; /*In objectSelf.c, we called twiddle here*/
  i = p_twiddle(p,3);

  /* Create a typed [fancyfoo] object */
  struct fancyfoo_object *u;
  struct fancymethods *umtable;
  void (*u_reset) (struct object *self); /*maybe these declarations again should take fancyobject arguments?*/
  int (*u_getcolor) (struct object *self);

  u = make_fancyfooTyped(9);

  /* Do a dynamic method call to the [reset] method on u*/  
  umtable = (struct fancymethods *)(((struct object *)u)->mtable); /*Again, explicit casts here help VST*/
  u_reset = umtable->reset;
  u_reset((struct object *)u); /*CAST U1/

  /* Do a dynamic method call to the [getcolor] method on u*/  
  umtable = (struct fancymethods *)(((struct object *)u)->mtable);
  u_getcolor = umtable->getcolor;
  int colU = u_getcolor((struct object *)u); /*CAST U2/
     /*is CAST-U better than CAST-Q? If so, can we now change the
       declaration of the getcolor to express that we can only pass
       fancy objects? Or shoudl argument types always remain struct object **/

  /* Done. */
  return (i+col+colU);
}

  
    
  
