
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

int main(void) {
  int_pair_t onetwo = {1,2};
  int_pair_t threefour = {3,4};
  pair_pair_t pp = {onetwo, threefour};
  pair_pair_t pps[1] = {pp};

  int res = get22(pps, 0);
  return res;
}

