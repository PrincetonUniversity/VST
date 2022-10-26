VSTlib

Standard Libraries for the Verified Software Toolchain,
in the form of Verified Software Units

In doing VST verifications of application software, one may want
to call upon library functions that have standard specifications.
The VSTlib provides these in the style of "Verified Software Units".
For an introduction to VSUs, see the second half of
_Software Foundations Volume 5: Verifiable C_.

Each component of VSTlib is envisioned to have a single header file
(something.h), which may be a standard system header file such as math.h
or a VSTlib-specific version such as memmgr.h.  Each component has one
or more .c files which must be linked with the application c files;
linking of .o files is done with the standard system linker and is not
foundationally verified.  In the VSU library, linking is foundationally 
_theorized_ at the C source level, with proofs.

Each VSTlib component may be _external and axiomatized_ (such as the
mmap system call), or _constructed and proved_ (such as the memmgr
construction of (subset of) the standard malloc/free interface.

The following VSUs are included now or envisioned.  Header files listed
with `<triangle brackets>` are standard system headers;
those with `"quotes"` are in VSTlib's include directory.


| Name | header | VSU | P/A | Done? | Comments | 
|------|--------|-----|-----|-------|----------|
| math | `<math.h>`| verif_math.MathVSU | Axiomized | partly | see below |
| memmgr| `"memmgr.h"`| | Proved | soon | custom, verified allocator |
| malloc| `"memmgr.h"`| | Axiomatized | soon | standard system allocator |
| atomics|            | | Axiomatized | soon | atomic load, store, CAS, etc.|
| locks |             | | Proved | soon | busy-wait locks based on atomics |

Additional details:
- math:  Each function in the system standard math.h library can be
   axiomatized with (1) special preconditions as needed, such as
   that the argument of sqrt must be nonnegative in order to guarantee
   any accuracy bounds; and (2) relative and absolute error bounds, which
   need not be the default bounds for the given floating-point type.
   (That is, the `sin` function might have more than 1 ulp of error.)
   In this commit, only 6 functions are axiomatized, to demonstrate how
   to do it.

- memmgr:  This is the "Verified Sequential Malloc/Free" published by Naumann and Appel.
- malloc:  This will be an axiomatized version of standard Posix malloc/free,
    with exactly the same spec as memmgr, for those users who want to call
    the standard library implementations.
