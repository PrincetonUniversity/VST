int fib_loop(int n) {
  int a0 = 0, a1 = 1, a2;
  int i;
  for (i = 0; i < n; ++ i) {
    a2 = a0 + a1;
    a0 = a1;
    a1 = a2;
  }
  return a0;
}

int fib_loop_save_var(int n) {
  int a0 = 0, a1 = 1;
  for (; n > 0; -- n) {
    a1 = a0 + a1;
    a0 = a1 - a0;
  }
  return a0;
}

int fib_loop_mod(int n, int mod) {
  int a0 = 0, a1 = 1, a2;
  int i;
  for (i = 0; i < n; ++ i) {
    a2 = (a0 + a1) % mod;
    a0 = a1;
    a1 = a2;
  }
  return a0;
}

int fib_rec(int n) {
  if (n == 0)
    return 0;
  if (n == 1)
    return 1;
  return fib_rec(n - 2) + fib_rec(n - 1);
}

void swap_int(int * x, int * y) {
  int a, b;
  a = * x;
  b = * y;
  if (a == b)
    return;
  * x = b;
  * y = a;
}

int main () {
}

