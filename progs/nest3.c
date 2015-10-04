struct a {int x1,x2;};
struct b {struct a y1, y2;};
struct c {struct b z1,z2;};

struct c p;
int p0, p1, p2, p3, p4, p5, p6, p7;

int get(void) {
  int i;
  i = p.z2.y2.x2;
  return i;
}

void set(int i) {
  p.z2.y2.x2 = i;
}

void multi_command(void) {
  int i;
  i = p.z1.y1.x1;
  p.z2.y2.x2 = i + 1;
  i = p.z1.y1.x2;
  p.z2.y2.x1 = i + 2;
  i = p.z1.y2.x1;
  p.z2.y1.x2 = i + 3;
  i = p.z1.y2.x2;
  p.z2.y1.x1 = i + 4;
}

void multi_command_s(void) {
  int i;
  i = p0;
  p7 = i + 1;
  i = p1;
  p6 = i + 2;
  i = p2;
  p5 = i + 3;
  i = p3;
  p4 = i + 4;
}