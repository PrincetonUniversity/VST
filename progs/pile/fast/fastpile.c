#include <stddef.h>
#include <limits.h>
#include "../stdlib.h"
#include "../pile.h"
#include "fastpile_private.h"

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

Pile Pile_new(void) {
  Pile p = (Pile)surely_malloc(sizeof *p);
  p->sum=0;
  return p;
}

void Pile_add(Pile p, int n) {
  int s = p->sum;
  if (0<=n && n<=(INT_MAX-s)) p->sum = s+n;
}

int Pile_count(Pile p) {
  return p->sum;
}

void Pile_free(Pile p) {
   free(p);
}


