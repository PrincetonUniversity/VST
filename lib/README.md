# VSTlib

## Standard Libraries for the Verified Software Toolchain, in the form of Verified Software Units

In doing VST verifications of application software, one may want
to call upon library functions that have standard specifications.
The VSTlib provides these in the style of "Verified Software Units".
For an introduction to VSUs, see the second half of
[_Software Foundations Volume 5: Verifiable C_](https://softwarefoundations.cis.upenn.edu/vc-current/index.html).

Each component of VSTlib is envisioned to have a single header file
(something.h), which may be a standard system header file such as math.h
or a VSTlib-specific version such as SC_atomics.h.  Each component has one
or more .c files which must be linked with the application c files;
linking of .o files is done with the standard system linker and is not
foundationally verified.  In the VSU library, linking is foundationally 
_theorized_ at the level of Clight abstract syntax, with proofs.

Each VSTlib component may be _external and axiomatized_ (such as the
mmap system call), or _constructed and proved_ (such as the memmgr
construction of (subset of) the standard malloc/free interface.

The following VSUs are included now or envisioned.  Header files listed
with in **boldface** are standard system headers from /usr/include;
the others are in VSTlib's include directory.


| Name | header | ASI | VSU | P/A | Done? | Comments | 
|------|--------|-----|-----|-----|-------|----------|
| math | **math.h**| spec_math.MathASI | verif_math.MathVSU | Axiomized | mostly | see below |
| memmgr| memmgr.h |   |    | Proved | soon | custom, verified allocator |
| malloc| **stdlib.h**| spec_malloc.MallocASI | verif_malloc.MallocVSU | Axiomatized | Done | standard system allocator |
| atomics| **stdatomic.h**, SC_atomics.h | spec_SC_atomics.AtomicsASI | verif_SC_atomics.SCAVSU | Axiomatized | Done | atomic load, store, CAS, etc.|
| locks | **threads.h**, VSTthreads.h | spec_locks.LockASI | verif_locks.lockVSU | Proved | Done | busy-wait locks based on atomics |

Additional details:
- math:  Each function in the system standard math.h library can be
   axiomatized with (1) special preconditions as needed, such as
   that the argument of sqrt must be nonnegative in order to guarantee
   any accuracy bounds; and (2) relative and absolute error bounds, which
   need not be the default bounds for the given floating-point type.
   (That is, the `sin` function might have more than 1 ulp of error.)
   All the functions are axiomatized, but many of the error bounds are not reliable; we plan to update the error bounds based on [the GNU documentation](https://www.gnu.org/software/libc/manual/html_node/Errors-in-Math-Functions.html).  Also, the `long double` functions are not supported.

- memmgr:  This is the "[Verified Sequential Malloc/Free](https://dl.acm.org/doi/10.1145/3381898.3397211)" published by Naumann and Appel.
- malloc:  This is an axiomatized version of standard Posix malloc/free, for those users who want to call
    the standard library implementations.

## Testing and demonstration examples

Example clients that demonstrate how to use these VSUs can be found
in the VSTlib/test directory; see [test/README.md](test/README.md).

