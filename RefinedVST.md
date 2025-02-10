# RefinedVST
The refinedVST project is adapted from [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc).

This is still work in progress.

## Build Instruction
We will need VST, Cerberus, and CompCert 3.15 to generate the frontend. We assume the dependency of VST is installed and an opam switch is set up.

TODO fix VST build instruction

### VST
The interface of the backend of RefinedVST is refinedVST/typing/typing.v:
```
make refinedVST/typing/typing.vo -j <jobs>
```

### Cerberus
You can either install Cerberus by installing [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc), or by following the Cerberus-specific lines of RefinedC's installation instructions, namely:
```
opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
```

## Running the frontend
The entry point for the frontend is in [./refinedVST/typing/frontend_stuff/Makefile](./refinedVST/typing/frontend_stuff/Makefile), adapted from the RefinedC frontend.

However the best way to use the frontend is to use the script [RefinedVST.sh](RefinedVST.sh):
```
./RefinedVST.sh
```
 The script checks [./refinedVST/typing/frontend_stuff/examples/test_f_temps.c](./refinedVST/typing/frontend_stuff/examples/test_f_temps.c) and generates proofs in [./refinedVST/typing/frontend_stuff/examples/proofs](./refinedVST/typing/frontend_stuff/examples/proofs).

To delete generated files:
```
make clean-refinedVST-frontend
```
