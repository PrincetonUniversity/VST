#include <limits.h>
#include <stdlib.h>
#include <errno.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>

CAMLprim value c_realpath(value v) {
  // Conversion of the argument to a C value, and performing the C call.
  const char *input_path = String_val(v);
  char *output_path = realpath(input_path, NULL);

  // Checking for error.
  if (output_path == NULL){
    switch(errno){
      case EACCES:
        caml_invalid_argument("Extra.Filename.realpath (EACCESS)\0");
      case EINVAL:
        caml_invalid_argument("Extra.Filename.realpath (EINVAL)\0");
      case EIO:
        caml_invalid_argument("Extra.Filename.realpath (EIO)\0");
      case ELOOP:
        caml_invalid_argument("Extra.Filename.realpath (ELOOP)\0");
      case ENAMETOOLONG:
        caml_invalid_argument("Extra.Filename.realpath (ENAMETOOLONG)\0");
      case ENOENT:
        caml_invalid_argument("Extra.Filename.realpath (ENOENT)\0");
      case ENOMEM:
        caml_invalid_argument("Extra.Filename.realpath (ENOMEM)\0");
      case ENOTDIR:
        caml_invalid_argument("Extra.Filename.realpath (ENOTDIR)\0");
      default:
        // Should not be reachable.
        caml_invalid_argument("Extra.Filename.realpath (unknown)\0");
    }
  }

  // Preparing the result value.
  value res = caml_copy_string(output_path);

  // Free the memory allocated by [realpath] before returning.
  free(output_path);
  return res;
}
