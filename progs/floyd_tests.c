
int test_sizeof(int* p) {
  int a = sizeof(*p);
  int b = 1 + sizeof(*p);
  return a + b;
}

int main(void) {
  int x = 0;
  return test_sizeof(&x);
}

