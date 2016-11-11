int g = 7;

int f(void) {
  int x;
  x = g;
  return x;
}

int main(void) {
  int y;
  y = f();
  return y;
}
