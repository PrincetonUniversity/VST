#include <stddef.h>
#include "stdlib.h"

int placeholder(void) {
  return &malloc,  &free,  &exit, 0;
}

