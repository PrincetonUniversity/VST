#include <stddef.h>

/* This example illustrates a C module that implements an 
   abstract data type (ADT) in its global variables.
   In this illustraction we put everything in a single .c file,
   but normally there would be a header file that looks like this:
*/

/* LG.h */
void LG_init (void);
void LG_bump (void);
int LG_get (void);

/* Then there would be an implementation of the ADT, like this: */

/* LG.c */
int LG_n = 3;

struct foo {
  int initialized;
  int m;
} LG_foo = {0};

void LG_init (void) {
  if (!LG_foo.initialized) {
    LG_foo.m = 3;
    LG_foo.initialized=1;
  }
}

void LG_bump (void) {
  LG_init();
  LG_n++;
  LG_foo.m++;
}

int LG_get (void) {
  int i;
  LG_init();
  i = LG_n;
  if (i&1)
    return i;
  else return LG_foo.m;
}

/* A separate module, in another .c file, would be a client of the ADT: */

/* client.c */

int client_var;

int client(void) {
  LG_bump();
  LG_bump();
  return LG_get();
}

/* And finally, there might be a main function, like this */

/* main.c */
int main(void) {
  return client();
}

    
