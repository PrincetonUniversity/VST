#include <stddef.h>
#include "../pile.h"
#include "fastpile_private.h"
#include "../apile.h"

struct pile a_pile = {0};

void Apile_add(int n) {
  Pile_add(&a_pile, n);
}

int Apile_count(void) {
  return Pile_count(&a_pile);
}
