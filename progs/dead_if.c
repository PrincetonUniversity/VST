/* Test deadvars tactic on if statement */

int f(int x, int y, int z) {
  int a, b, c, d;
  d=2;
  b=1;
  c=0;
  a=x+1;
  if (a>0) {
    b=x+y;
  }
  else {
    b=x;
    c=z;
  }
  return c+b;
}

int g(int x, int y, int z) {
  int a, b, c, d;
  d=2;
  b=1;
  c=0;
  a=x+1;
  while (a>0) {
    b=x;
  }
  return c+b;
}

    
    
