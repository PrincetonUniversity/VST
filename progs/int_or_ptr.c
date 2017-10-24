#include <stddef.h>

typedef void  * int_or_ptr
#ifdef COMPCERT
  _Alignas (void *)
#endif
  ;

extern int putchar(int);

/* The following 5 functions should (in practice) compile correctly in CompCert,
   but the CompCert correctness specification does not _require_ that
   they compile correctly:  their semantics is "undefined behavior" in
   CompCert C (and in C11), but in practice they will work in any compiler. */

int test_int_or_ptr (int_or_ptr x) /* returns 1 if int, 0 if aligned ptr */
{return (int)(((size_t)x)&1);}
extern size_t int_or_ptr_to_int (int_or_ptr x) /* precondition: is int */
{return (size_t)x;}
extern void * int_or_ptr_to_ptr (int_or_ptr x) /* precond: is aligned ptr */
{return (void *)x;}
extern int_or_ptr int_to_int_or_ptr(size_t x) /* precondition: is odd */
{return (int_or_ptr)x;}  
extern int_or_ptr ptr_to_int_or_ptr(void *x) /* precondition: is aligned */
{return (int_or_ptr)x;}  


/* The following functions should work correctly, *and* they are will
  specified in CompCert C as well as Verifiable C, provided that we
  assume the axiom that the 5 functions above work as specified above. */

int leaf=0;

int_or_ptr arena[1000];

int_or_ptr *next=arena;

int_or_ptr maketree(int depth) {
  int_or_ptr r;
  if (depth==0) {
    r=int_to_int_or_ptr((leaf++<<1)|1);
    return r;
  }
  else {
    int_or_ptr p,q, *s;
    p=maketree(depth-1);
    q=maketree(depth-1);
    next[0]=p;
    next[1]=q;
    r = ptr_to_int_or_ptr(next);
    next += 2;
    return r;
  }
}

void print_intx(size_t i) {
  if (i>0) {
    print_intx(i/10);
    putchar('0'+i%10);
  }
}

void print_int (size_t i) {
  if (i==0)
    putchar('0');
  else print_intx (i);
}

void print(int_or_ptr p) {
  if (test_int_or_ptr(p)) {
    size_t i = int_or_ptr_to_int(p);
    print_int(i>>1);
  } else {
    int_or_ptr a,b, *q;
    q=(int_or_ptr*)int_or_ptr_to_ptr(p);
    a=q[0];
    b=q[1];
    putchar('(');
    print(a);
    putchar(',');
    print(b);
    putchar(')');
  }
}

int main(void) {
  int_or_ptr p = maketree(3);
  print(p);
  return 0;
}
