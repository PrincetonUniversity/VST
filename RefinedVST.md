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
opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#6e3e8be7a3f75b1f1cb0704dca8ef3945be0e413"
```

Then clone RefinedC to any directory:

```[bash]
git clone https://github.com/UIC-verif-group/refinedC refinedc
opam pin ./refinedc -y
```

Now we use the VST makefile to compile any refinedVST Coq file:

```[bash]
make refinedVST/typing/typing.vo -j <jobs>
```

## Running the frontend

The entry point for the frontend is in [./refinedVST/typing/frontend_stuff/Makefile](./refinedVST/typing/frontend_stuff/Makefile), adapted from the RefinedC frontend.

However the best way to use the frontend is to use the script [RefinedVST.sh](RefinedVST.sh):

```[bash]
./RefinedVST.sh
```

 The script checks [./refinedVST/typing/frontend_stuff/examples/test_f_temps.c](./refinedVST/typing/frontend_stuff/examples/test_f_temps.c) and generates proofs in [./refinedVST/typing/frontend_stuff/examples/proofs](./refinedVST/typing/frontend_stuff/examples/proofs).

To delete generated files:

```[bash]
make clean-refinedVST-frontend
```
