typedef unsigned char u8;
typedef long long i64;

u8 test(const i64 n)
{
  i64 b,c;
  u8 d;
  b = n * 2;
  c = 2 * n;
  
  b = b + 4;
  b = (-4) + b;
  
  c = c - 4;
  c = 4 - c;
  
  b = b >> 8;
  c = c << 8;
  
  d = c & 0xff;
  d = d & b;
  return d;
}
