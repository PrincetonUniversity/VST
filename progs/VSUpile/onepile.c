#include <stddef.h>
#include "pile.h"

Pile the_pile;

void Onepile_init(void) {
    the_pile = Pile_new();
}

void Onepile_add(int n) {
  Pile_add(the_pile, n);
}

int Onepile_count(void) {
  return Pile_count(the_pile);
}
