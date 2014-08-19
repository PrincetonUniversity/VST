int even(unsigned int n);

int odd(unsigned int n)
{
  if (n == 0) {
    return 0;
  }
  return even(n-1);
}
