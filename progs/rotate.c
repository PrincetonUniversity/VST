#include <stddef.h>

extern void *malloc (size_t n);
extern void free (void *p);
extern void exit(int code);

void rotate(int *a, int n, int k) {
  int *b = malloc(sizeof (int) * n);
  if(!b)
    exit(-1);
  for(int i = 0; i < n-k; i++)
    b[i] = a[i+k];
  for(int i = n-k; i < n; i++)
    b[i] = a[i+k-n];
  for(int i = 0; i < n; i++)
    a[i] = b[i];
  free(b);
}

void sorted_rotate(int *a, int n, int k, int N)
//requires sorted(a) && forall i, 0 <= i < n -> 0 <= a[i] < N
//ensures sorted(a)
{
  rotate(a, n, k);
  for(int i = n-k; i < n; i++)
    a[i] += N;
}
