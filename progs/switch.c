int twice (int n) {
  switch (n) {
  case 0: return 0;
  case 1: n=2; break;
  case 3: n=6; break;
  default: n=n+n; break;
  }
  return n;
}
