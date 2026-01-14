# RefinedVST

The refinedVST project is adapted from [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/commits/ea6be6de7f27855a79c9ca18e6a54ba3bd5ed883).

This is still work in progress.

## Build Instruction

We will need a slightly tweaked version of RefinedC and some part of VST (and for now, compcert 3.14 to generate the frontend).

Compile RefinedC and its dependencies (adapted from the RefinedC readme):

Install VST builddep (VST project root directory):

```[bash]
sudo apt-get install libmpfr-dev # Implicit Cerberus dependency.
opam repo add coq-released "https://coq.inria.fr/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
opam update
opam pin yojson 2.2.2 # 3.0.0 removed a feature that our version of cerberus-lib depends on, have to use older versions (or update cerberus-lib)
opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#6e3e8be7a3f75b1f1cb0704dca8ef3945be0e413"
opam pin add builddep/
```

Then clone RefinedC to any directory:

```[bash]
git clone https://github.com/UIC-verif-group/refinedC refinedc
opam pin ./refinedc -y
```

Now we use the VST makefile to compile and install the refinedVST files:

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

## Known differences with RefinedC

The names of C types are CompCert names. For instance:
| RefinedC name | RefinedCC name |
| ------------- | -------------- |
| `i32` | `tint` |
| `u32` | `tuint` |
| `i64` | `tlong` |
| `u64` | `tulong` |
| `i8` | `tchar` |
| `u8` | `tuchar` |
| `loc` | `address` |
