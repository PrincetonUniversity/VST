

struct foo {int x; float y; double z;};

struct foo s = {5, 3.41, 0.0};

double a[] = {0.0,1.1};

int main() {
 double y1 = s.y;
 int x1 = s.x;
 int y2 = s.y;
 y1 = s.z;
 a[0]=a[1];
 return 0;
}
