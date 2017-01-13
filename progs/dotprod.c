#define N 3

void add (double x[], double y[], double z[]) {
  int i;
  for (i=0; i<N; i++)
      x[i] = y[i] + z[i];
}

double dotprod (int n, double x[], double y[]) {
  int i;
  double sum = 0.0;
  for (i=0; i<n; i++)
      sum += x[i] * y[i];
  return sum;
}

