# VSTlib/test

## Example clients that demonstrate how to use VSTlib

The library modules of VSTlib are in the form of Verified Software Units (VSU).
For library "foo", there will typically be the C code
(VSTlib/src/foo.c) and perhaps also a .h file;
(in VSTlib/include) or it may use standard system include files.

Along with the C code, there is also a specification and proof.
In VSTlib/proof there will typically be:
- spec_foo.v, the specification, containing (optionally) an APD
  and (always) an ASI.  APD stands for _Abstract Predicate Declaration_,
  and is present if this VSU uses data abstraction to provide
  operations on an opaque type.  ASI stands for _Abstract Specification
  Interface_, and is a `funspecs`, that is, a `list(ident*funspec)` that can
  be used as part of the Gprog when proving client function bodies.
- verif_foo.v, the proof that the C code satisfies the specification.
  In some cases this is really a proof, in other cases it is an
  axiomatization of unproved system libraries.

## The examples

In the test clients, unlike the library modules, we put the .c files and
the .v files into the same directory.

One limitation of the current VSU system is that the `main` function
must always be by itself in a separate .c file.


### incr
 This program initializes a global variable to 0,
 forks two threads, each of which increments the variable
 (with semaphore synchronization to avoid race conditions),
 then waits for both threads to finish.
- `incr.c` has everything except `main()`.
- `incr_main.c` has the main function.
- `verif_incr.v` has both the specification and verification of `incr.c`
- `verif_incr_main.v` has the specification and verification of
   `incr_main.c` _and_ it has the proof that these programs can be
   linked together to get an a.out with the specified behavior.

### other examples

 ... will be forthcoming
 