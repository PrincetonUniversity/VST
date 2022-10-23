int foo(int *p, void **q) {
  *p = 1;
  *q = 0;
  return *p;
}
int main() {
  int x;
  return foo(&x, &x);
}

/*
The usage in this example is essential systems programming but has undefined
behavior according to ISO C due to the strict aliasing restriction.

It returns 0 in the following invocations of clang 14.0.6 and gcc 12.2.0:

clang -m32 -O0 -w alias2.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O0 -w alias2.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O1 -w alias2.c -o alias2 && ./alias2; echo $?
clang -m32 -fno-strict-aliasing -O1 -w alias2.c -o alias2 && ./alias2; echo $?
clang -m32 -fno-strict-aliasing -O2 -w alias2.c -o alias2 && ./alias2; echo $?
clang -m32 -fno-strict-aliasing -O3 -w alias2.c -o alias2 && ./alias2; echo $?
gcc   -m32 -fno-strict-aliasing -O2 -w alias2.c -o alias2 && ./alias2; echo $?
gcc   -m32 -fno-strict-aliasing -O3 -w alias2.c -o alias2 && ./alias2; echo $?

It also returns 0 with CompCert a1f01c844aaa0ff41aa9095e9d5d01606a0e90c9 (3.11++):

../../CompCert/ccomp alias2.c -c alias2.o && gcc -m32 alias2.o -o alias2 && ./alias2; echo $?

It returns 1 in the following invocations of clang 14.0.6 and gcc 12.2.0:

clang -m32 -O1 -w alias2.c -o alias2 && ./alias2; echo $?
clang -m32 -O2 -w alias2.c -o alias2 && ./alias2; echo $?
clang -m32 -O3 -w alias2.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O2 -w alias2.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O3 -w alias2.c -o alias2 && ./alias2; echo $?

alias2.v was generated using the following invocation:

../../CompCert/clightgen -dall -normalize -nostdinc -P -std=c11 alias2.c

The corresponding clight file returns 0 in all invocations where the input file returned 0:

clang -m32 -O0 -w alias2.light.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O0 -w alias2.light.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O1 -w alias2.light.c -o alias2 && ./alias2; echo $?
clang -m32 -fno-strict-aliasing -O1 -w alias2.light.c -o alias2 && ./alias2; echo $?
clang -m32 -fno-strict-aliasing -O2 -w alias2.light.c -o alias2 && ./alias2; echo $?
clang -m32 -fno-strict-aliasing -O3 -w alias2.light.c -o alias2 && ./alias2; echo $?
gcc   -m32 -fno-strict-aliasing -O2 -w alias2.light.c -o alias2 && ./alias2; echo $?
gcc   -m32 -fno-strict-aliasing -O3 -w alias2.light.c -o alias2 && ./alias2; echo $?

... and returns 1 in all invocations where the input file returned 1:

clang -m32 -O1 -w alias2.light.c -o alias2 && ./alias2; echo $?
clang -m32 -O2 -w alias2.light.c -o alias2 && ./alias2; echo $?
clang -m32 -O3 -w alias2.light.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O2 -w alias2.light.c -o alias2 && ./alias2; echo $?
gcc   -m32 -O3 -w alias2.light.c -o alias2 && ./alias2; echo $?
*/
