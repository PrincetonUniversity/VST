# RefinedVST

The RefinedVST project is adapted from [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/commits/ea6be6de7f27855a79c9ca18e6a54ba3bd5ed883).

This is still work in progress.

## Build Instructions

RefinedVST is installed in two parts: the backend is in the VST repository, and the frontend is a fork of CompCert. We will first install the backend.

Install VST builddep (VST project root directory):

```[bash]
opam repo add rocq-released "https://rocq-prover.org/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
opam update
opam pin add builddep/
```

Now we use the VST makefile to compile and install the RefinedVST files:

```[bash]
make refinedVST
make install_rc
```
This should install, for example, refinedVST/typing/typing.vo in the switch:
```[bash]
$ ls ${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/VST/typing/
... automation.vo ... typing.vo ...
```

### Install the Frontend
RefinedCC's frontend is modified from RefinedC's frontend and CompCert.
It parses annotations and emits the spec & proof files similar to RefinedC, but emits a Clight AST with syntactic sugars that also holds annotations.

Clone the frontend from
[compcert-mod](https://github.com/UIC-verif-group/compcert-mod/tree/modular) to any location, and follow the build instruction there.

### Check a file with RefinedCC
Once both frontend and backend of RefinedCC are installed, we can use the frontend binary `refinedcc` to check an annotated program. 

`refinedcc` will need to create a new Coq project, so we recommend doing it in an empty folder. Assuming `refinedcc` is already in the PATH:
```[bash]
mkdir check_progs; cd check_progs
refinedcc init
```

Then copy your C programs under this folder, and run
```
refinedcc check prog.c
```

The usage is the same as in RefinedC; for details, refer to the [RefinedC repository](https://github.com/PrincetonUniversity/VST/blob/92867829a0ac2a8b9ecfdd1b75cc3bffe085f4f5/RefinedVST.md).
