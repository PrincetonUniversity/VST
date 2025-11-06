# RefinedVST

The refinedVST project is adapted from [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/commits/ea6be6de7f27855a79c9ca18e6a54ba3bd5ed883).

This is still work in progress.

## Build Instruction

We will need a slightly tweaked version of RefinedC and some part of VST (and for now, compcert 3.14 to generate the frontend).

Compile RefinedC and its dependencies (adapted from the RefinedC readme):

Install VST builddep (VST project root directory):

```[bash]
opam pin add builddep/
```

```[bash]
sudo apt-get install libmpfr-dev # Implicit Cerberus dependency.
opam repo add coq-released "https://coq.inria.fr/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
opam update
opam pin yojson 2.2.2 # 3.0.0 removed a feature that our version of cerberus-lib depends on, have to use older versions (or update cerberus-lib)
opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#6e3e8be7a3f75b1f1cb0704dca8ef3945be0e413"
```

Then clone RefinedC to any directory:

```[bash]
git clone https://github.com/UIC-verif-group/refinedC refinedc
opam pin ./refinedc -y
```

Now we use the VST makefile to compile any refinedVST Coq file:

```[bash]
make refinedVST
```

### Install the Frontend
RefinedCC's frontend is modified from RefinedC's frontend and CompCert.
It parses annotations and emits the spec & proof files similar to RefinedC, but emits a Clight AST with syntactic sugars that also holds annotations.

Clone the frontend from
[github.com/UIC-verif-group/compcert-mod/tree/modular](github.com/UIC-verif-group/compcert-mod/tree/modular) to any location, and follow the build instruction there.

### Install Backend Files
Requires VST builddep (opam pin add builddep). Note that coq-vst-ora (included in builddep) must be installed in the opam switch. To check this:
```[bash]
$ opam info -f installed-version coq-vst-ora
1.0
```

Then install RefinedCC backend files to switch:
```[bash]
$ make install_rc
```
This should install, for example, refinedVST/typing/typing.vo in the switch:
```[bash]
$ ls ${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/VST/typing/
... automation.vo ... typing.vo ...
```

### Check a file with RefinedCC
Once both frontend and backend of RefinedCC are installed, we can use the frontend binary `refinedcc` to check an annotated program. The usage is the same as in RefinedC.

`refinedcc` will need to create a new Coq project, so we recommend doing it in an empty folder. Assuming `refinedcc` is already in the PATH:
```[bash]
mkdir check_progs; cd check_progs
refinedcc init
refinedcc check progs
```
