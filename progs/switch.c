int twice (int n) {
  switch (n) {
  case 0: return 0;
  case 1: n=2; break;
  case 3: n=n+0;
  default: n=n+n; break;
  }
  return n;
}
