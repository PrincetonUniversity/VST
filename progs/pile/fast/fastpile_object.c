#include <stddef.h>
#include <limits.h>
#include "stdlib.h"
#include "object.h"

struct fastpile {
  int sum;
};

static void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

struct fastpile * Fastpile_new(void) {
  struct fastpile * p = (struct fastpile *)surely_malloc(sizeof *p);
  p->sum=0;
  return p;
}

void Fastpile_add(struct fastpile * p, int n) {
  int s = p->sum;
  if (0<=n && n<=(INT_MAX-s)) p->sum = s+n;
}

int Fastpile_count(struct fastpile * p) {
  return p->sum;
}

void Fastpile_free(struct fastpile * p) {
   free(p);
}

struct pile_methods pile_pm =
  {(struct pile_data *(*)(void))&Fastpile_new,
   (void(*)(struct pile_data *, int))&Fastpile_add,
   (int (*)(struct pile_data *))&Fastpile_count, 
   (void (*)(struct pile_data *))&Fastpile_free};
