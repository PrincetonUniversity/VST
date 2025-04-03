# Notes on VST-on-Iris 
(beware: these instructions are now out of date)

## Building

Install opam:

```(bash)
opam switch create vst_on_iris ocaml-variants.4.14.1+options ocaml-option-flambda
```

Install dependencies:

```(bash)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add builddep/
```

At this point, we use [`Makefile`](./Makefile)
```(bash)
make
```
Addtionally, to generate `_CoqProject`:

```(bash)
make _CoqProject
```
