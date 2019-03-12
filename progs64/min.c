int minimum(int a[ ], int n) {
  int i, min;
  min=a[0];
  for (i=0; i<n; i++) {
    int j = a[i];
    if (j<min)
        min=j;
  }
  return min;
}
