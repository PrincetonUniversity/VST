int minimum(int a[ ], long long n) {
  long long i;
  int min;
  min=a[0];
  for (i=0; i<n; i++) {
    int j = a[i];
    a[i]=j;  /* This is here just to test array-store with 64-bit subscript */
    if (j<min)
        min=j;
  }
  return min;
}
