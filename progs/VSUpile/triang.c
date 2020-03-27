#include <stdlib.h>
#include "pile.h"

int Triang_nth(int n) {
  int i,c;
  Pile p = Pile_new();
  for (i=0; i<n; i++)
    Pile_add(p,i+1);
  c = Pile_count(p);
  Pile_free(p);
  return c;
}
