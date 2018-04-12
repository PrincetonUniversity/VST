struct foo {int x; char a[2];};

struct foo *p;

struct foo a;

struct foo b = {5,{6,7}};

struct foo c = {5};

struct foo d = {5,6};

struct foo e[3];

struct foo f[3] = {{1,{2,3}},{4,{5,6}},{7,"x"}};

int g = 7;


int h(void) {
  int x;
  x = g;
  return x;
}

int main(void) {
  int y;
  y = h();
  return y;
}

