#include <stddef.h>
#include <limits.h>
#include <stdlib.h>

#define EOF (-1)
extern int getchars(unsigned char *buf);
extern int putchars(unsigned char *buf);


int print_intr(unsigned int i, unsigned char *buf, int j) {
  unsigned char q,r;
  int k = 0;
  if (i!=0) {
    q=i/10u;
    r=i%10u;
    k = print_intr(q, buf, j);
    buf[k] = r+'0';
  }
  return k + 1;
}

void print_int(unsigned int i) {
  unsigned char *buf = malloc(5);
  if (!buf) exit(1);
  if (i==0){
    buf[0] = '0';
    buf[1] = '\n';
  }
  else{
    int k = print_intr(i, buf, 0);
    buf[k] = '\n';
  }
  putchars(buf);
  free(buf);
}

/* Specification:
   reads a sequence of characters, each in the range '0'..'9';
   after each one (and before the next one) prints a decimal
   representation of their cumulative sum, followed by a newline.
   When the cumulative sum >=1000, or when EOF is reached, stops.
*/

int main(void) {
  unsigned int n, d; char c;
  unsigned char *buf;
  int i, j;

  n=0;
  buf = malloc(4);
  if (!buf) exit(1);
  i = getchars(buf);
  while (n<1000) {
    for(j = 0; j < i; j++){
      c = buf[j];
      d = ((unsigned)c)-(unsigned)'0';
      if (d>=10) break;
      n+=d;
      print_int(n);
    }
    i = getchars(buf);
  }
  free(buf);
  return 0;
}

  

  
