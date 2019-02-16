

struct foo {int x; float y; double z;};

struct foo s = {5, 3.41, 0.0};

int main() {
 double y1 = s.y;
 int x1 = s.x;
 int y2 = s.y;
 y1 = s.z;
 return 0;
}