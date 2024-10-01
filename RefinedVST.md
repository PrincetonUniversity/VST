# RefinedVST
The refinedVST project is adapted from [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/commits/ea6be6de7f27855a79c9ca18e6a54ba3bd5ed883).

This is still work in progress.

## Build Instruction
We will need VST, RefinedC (and for now, compcert (3.13 or 3.14) to generate the frontend). We assume the dependency of VST is installed and an opam switch is set up.

TODO fix VST build instruction

### VST
The interface of the backend of RefinedVST is refinedVST/typing/typing.v:
```
make refinedVST/typing/typing.vo -j <jobs>
```

### RefinedC
RefinedC: VST is pinned to a slightly older version of Iris (dev.2024-03-12.0.c1e15cdc), and consequently a slightly older version of [RefinedC dev.2024-07-23.0.ea6be6de](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/ea6be6de7f27855a79c9ca18e6a54ba3bd5ed883).
I failed to pin RefinedC's gitlab repository, but installing it from source works:
```
git clone https://gitlab.mpi-sws.org/iris/refinedc.git refinedc
cd refinedc
git branch pin_refinedc ea6be6de
opam pin add refinedc . -y
```

## Running the frontend
The entry point for the frontend is in [./refinedVST/typing/frontend_stuff/Makefile](./refinedVST/typing/frontend_stuff/Makefile), adapted from the RefinedC frontend.

However the best way to use the frontend is to use the script [RefinedVST.sh](RefinedVST.sh):
```
./RefinedVST.sh
```
 The script checks [./refinedVST/typing/frontend_stuff/examples/test_f_temps.c](./refinedVST/typing/frontend_stuff/examples/test_f_temps.c) and generates proofs in [./refinedVST/typing/frontend_stuff/examples/proofs](./refinedVST/typing/frontend_stuff/examples/proofs).
