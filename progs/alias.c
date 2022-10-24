long foo(long *p, void **q) {
  *p = 1;
  *q = 0;
  return *p;
}
int main() {
  long x;
  return foo(&x, &x);
}

/*
The usage in this canonical example is essential to systems programming but has
undefined behavior according to ISO C due to the strict aliasing restriction.

From the perspective that pointers are addresses and memory maps addresses to
bytes, we have two writes and one read of the same 4-byte memory region, and
main returns 0. Yet ISO C17 § 6.5.7 limits the lvalue types through which the
value of a declared object can be accessed to a fixed list of variations on the
declared type plus char. Here the declared type is long, so the modification
through *p is consistent with these rules, but the modification through *q (of
type void*) is not, even though long and void* have the same size and alignment.
The ubiquitous compiler flag -fno-strict-aliasing lifts these restrictions.

To show that this complication is relevant in practice, the example was tested
using clang 14.0.6, gcc 12.2.0, and CompCert a1f01c84 (3.11++).

It returns 0 in the following invocations:

clang -m32 -O0 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O0 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O1 -w alias.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O1 -w alias.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O2 -w alias.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O3 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -fno-strict-aliasing -O2 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -fno-strict-aliasing -O3 -w alias.c -o alias && ./alias; echo $?

It also returns 0 with CompCert:

../../CompCert/ccomp alias.c -c alias.o && gcc -m32 alias.o -o alias && ./alias; echo $?
../../CompCert/ccomp -interp alias.c

It returns 1 in the following invocations:

clang -m32 -O1 -w alias.c -o alias && ./alias; echo $?
clang -m32 -O2 -w alias.c -o alias && ./alias; echo $?
clang -m32 -O3 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O2 -w alias.c -o alias && ./alias; echo $?
gcc   -m32 -O3 -w alias.c -o alias && ./alias; echo $?

alias.v was generated using the following invocation:

../../CompCert/clightgen -dclight -normalize -nostdinc -P -std=c11 alias.c

The corresponding clight file returns 0 in all invocations where the input file returned 0:

clang -m32 -O0 -w alias.light.c -o alias && ./alias; echo $?
gcc   -m32 -O0 -w alias.light.c -o alias && ./alias; echo $?
gcc   -m32 -O1 -w alias.light.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O1 -w alias.light.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O2 -w alias.light.c -o alias && ./alias; echo $?
clang -m32 -fno-strict-aliasing -O3 -w alias.light.c -o alias && ./alias; echo $?
gcc   -m32 -fno-strict-aliasing -O2 -w alias.light.c -o alias && ./alias; echo $?
gcc   -m32 -fno-strict-aliasing -O3 -w alias.light.c -o alias && ./alias; echo $?

... and returns 1 in all invocations where the input file returned 1:

clang -m32 -O1 -w alias.light.c -o alias && ./alias; echo $?
clang -m32 -O2 -w alias.light.c -o alias && ./alias; echo $?
clang -m32 -O3 -w alias.light.c -o alias && ./alias; echo $?
gcc   -m32 -O2 -w alias.light.c -o alias && ./alias; echo $?
gcc   -m32 -O3 -w alias.light.c -o alias && ./alias; echo $?
*/
