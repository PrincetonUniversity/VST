int odd(unsigned int n);

int even(unsigned int n)
{
  if (n == 0) {
    return 1;
  }
  return odd(n-1);
}

int main(void)
{
  return even(42);
}

