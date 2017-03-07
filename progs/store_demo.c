
typedef struct int_pair {
  int fst;
  int snd;
} int_pair_t;

typedef struct pair_pair {
  int_pair_t left;
  int_pair_t right;
} pair_pair_t;

void set22(pair_pair_t* pps, int i, int v) {
  pps[i].right.snd = 0;
  int_pair_t* p = &pps[i].right;
  p->snd = v;
}

void fiddle (unsigned int *p) {
  p[-1] = 3;
}

int main(void) {
  int_pair_t onetwo = {1,2};
  int_pair_t threefour = {3,4};
  pair_pair_t pp = {onetwo, threefour};
  pair_pair_t pps[1] = {pp};

  // object starts with header storing size & flags, followed by members
  unsigned int obj[3] = { 2 << 10, 11, 12 };
  unsigned int *p = &(obj[1]);

  set22(pps, 0, 4);
  fiddle(p);
  int res1 = pps[0].right.snd;
  int res2 = obj[0];
  return res1 + res2;
}

