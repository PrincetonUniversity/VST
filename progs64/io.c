#include <stddef.h>
#include <limits.h>

#define EOF (-1)
extern int getchar(void);
extern int putchar(int c);

int getchar_blocking(){
  int r = -1;
  while(r == -1) r = getchar();
  return r;
}

int putchar_blocking(int c){
  int r = -1;
  while(r == -1) r = putchar(c);
  return r;
}

void print_intr(unsigned int i) {
  unsigned int q,r;
  if (i!=0) {
    q=i/10u;
    r=i%10u;
    print_intr(q);
    putchar_blocking(r+'0');
  }
}

void print_int(unsigned int i) {
  if (i==0)
    putchar_blocking('0');
  else print_intr(i);
}

/* Specification:
   reads a sequence of characters, each in the range '0'..'9';
   after each one (and before the next one) prints a decimal
   representation of their cumulative sum, followed by a newline.
   When the cumulative sum >=1000, or when EOF is reached, stops.
*/

int main(void) {
  unsigned int n, d; unsigned char c;

  n=0;
  c=getchar_blocking();
  while (n<1000) {
    d = c-(unsigned)'0';
    if (d>=10) break;
    n+=d;
    print_int(n);
    putchar_blocking('\n');
    c=getchar_blocking();
  }
  return 0;
}
