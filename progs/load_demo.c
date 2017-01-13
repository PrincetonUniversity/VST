
typedef struct int_pair {
  int fst;
  int snd;
} int_pair_t;

typedef struct pair_pair {
  int_pair_t left;
  int_pair_t right;
} pair_pair_t;

int get22(pair_pair_t* pps, int i) {
  int_pair_t* p = &pps[i].right;
  int res = p->snd;
  return res;
}

int fiddle (unsigned int *p) {
  unsigned int sum, size, i;
  unsigned int tagword = p[-1];
  sum = tagword & 0xff;
  size = tagword >> 10;
  for (i=0; i<size; i++) {
    unsigned int r = p[i];
    sum += r;
  }
  return sum;
}

unsigned int get_little_endian(unsigned char input[4]) {
  unsigned int b0 = (unsigned int) input[0];
  unsigned int b1 = (unsigned int) input[1];
  unsigned int b2 = input[2];
  unsigned int b3 = input[3];
  return (b0 | (b1 << 8) | (b2 << 16) | (b3 << 24));
}

int main(void) {
  int_pair_t onetwo = {1,2};
  int_pair_t threefour = {3,4};
  pair_pair_t pp = {onetwo, threefour};
  pair_pair_t pps[1] = {pp};

  // object starts with header storing size & flags, followed by members
  unsigned int obj[3] = { 2 << 10, 11, 12 };
  unsigned int *p = &(obj[1]);

  unsigned char v[4] = { 10, 20, 30, 40 };

  int res1 = get22(pps, 0);
  int res2 = fiddle(p);
  unsigned int res3 = get_little_endian(v);
  return res1 + res2 + (res3 >> 24);
}

