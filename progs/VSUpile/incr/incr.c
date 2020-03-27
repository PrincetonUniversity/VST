int incr1(int i, unsigned int *auxdata) {
  auxdata[i%10] += 1;
  return i+1;
}

int incr2(int i, unsigned int *auxdata) {
  return i+1;
}

unsigned int global_auxdata[10];
int incr3(int i) {
  global_auxdata[i%10] += 1;
  return i+1;
}

int incr4(int i) {
  return i+1;
}
