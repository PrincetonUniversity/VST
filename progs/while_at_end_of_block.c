#include<stdbool.h>

unsigned int identity(unsigned int v, bool by_counting) {
  unsigned int result = 0;
  if (by_counting) {
    while (result < v) result++;
  } else {
    result = v;
  }
  return result;
}

