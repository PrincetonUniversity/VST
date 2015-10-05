#include <stddef.h>

// extern void * malloc(unsigned int);
extern void *mallocN (int n);

int strcspn_kmp(const char * s1, const char * s2, int n1, int n2)
{
  int i, j;
  int * next = (int *) mallocN (n2 * sizeof (int));
  i = 0;
  j = -1;
  next [0] = -1;
  while (i < n2)
  {
    if (s2[i + 1] == s2[j + 1])
      {
	i ++;
	j ++;
	next[i] = j;
      }
    else
      if (j == -1)
	{
	  i ++;
	  next[i] = -1;
	}
      else
	j = next [j];
  }
  i = -1;
  j = -1;
  while (i < n1)
    {
      if (s1[i + 1] == s2[j + 1])
	{
	  i ++;
	  j ++;
	  if (j == n2 - 1)
	    return i - n2 + 1;
	}
      else
	if (j == -1)
	    i ++;
	else
	  j = next[j];
    }
  return -1;
}
