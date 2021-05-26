#include <stddef.h>
#include "pile.h"
#include "pile_private.h"
#include "apile.h"

struct pile a_pile = {NULL};

void Apile_add(int n) {
  Pile_add(&a_pile, n);
}

int Apile_count(void) {
  return Pile_count(&a_pile);
}
