struct a {double x1; int x2;};
struct b {int y1; struct a y2;};

struct b p;

int get(void) {
  int i;
  i = p.y2.x2;
  return i;
}

void set(int i) {
  p.y2.x2 = i;
}

int main()
{
}
