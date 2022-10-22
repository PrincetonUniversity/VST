int foo(int *p, long *q) {
  *p = 1;
  *q = 0;
  return *p;
}
int main() {
  long x;
  return foo(&x, &x);
}

/*
The usage in this example is essential systems programming but has undefined
behavior according to ISO C due to the strict aliasing restriction.

It returns 0 in the following invocations of clang 14.0.6 and gcc 12.2.0:

clang -O0 -w alias.c -o alias && ./alias; echo $?
gcc   -O0 -w alias.c -o alias && ./alias; echo $?
gcc   -O1 -w alias.c -o alias && ./alias; echo $?
clang -fno-strict-aliasing -O1 -w alias.c -o alias && ./alias; echo $?
clang -fno-strict-aliasing -O2 -w alias.c -o alias && ./alias; echo $?
clang -fno-strict-aliasing -O3 -w alias.c -o alias && ./alias; echo $?
gcc   -fno-strict-aliasing -O2 -w alias.c -o alias && ./alias; echo $?
gcc   -fno-strict-aliasing -O3 -w alias.c -o alias && ./alias; echo $?
clang -m32 -O0 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O0 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O1 -w alias.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O1 -w alias.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O2 -w alias.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O3 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -fno-strict-aliasing -O2 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -fno-strict-aliasing -O3 -w alias.c -o alias && ./alias; echo $?

It also returns 0 with CompCert a1f01c844aaa0ff41aa9095e9d5d01606a0e90c9 (3.11++):

../../CompCert/ccomp alias.c -c alias.o && gcc -m32 alias.o -o alias && ./alias; echo $?

It returns 1 in the following invocations of clang 14.0.6 and gcc 12.2.0:

clang -O1 -w alias.c -o alias && ./alias; echo $?
clang -O2 -w alias.c -o alias && ./alias; echo $?
clang -O3 -w alias.c -o alias && ./alias; echo $?
gcc   -O2 -w alias.c -o alias && ./alias; echo $?
gcc   -O3 -w alias.c -o alias && ./alias; echo $?
clang -m32 -O1 -w alias.c -o alias && ./alias; echo $?
clang -m32 -O2 -w alias.c -o alias && ./alias; echo $?
clang -m32 -O3 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O2 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O3 -w alias.c -o alias && ./alias; echo $?

alias.v was generated using the following invocation:

../../CompCert/clightgen -normalize -nostdinc -P -std=c11 alias.c
*/
