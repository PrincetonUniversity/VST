#include <stddef.h>

struct __sFILE;
typedef struct __sFILE FILE;

extern FILE _stdin, _stdout, _stderr;
#define stdin (&_stdin)
#define stdout (&_stdout)
#define stderr (&_stderr)

extern int fprintf (FILE *__restrict, const char *__restrict, ...)
               __attribute__ ((__format__ (__printf__, 2, 3)));

int main(void) {
  fprintf(stdout, "Hello, world!\n");
  fprintf(stdout, "This is line %d.\n", 2);
  return 0;
}
