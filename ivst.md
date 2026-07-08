# Building VST-on-Iris (VST 3.x)

## Option 1: Use OPAM

VST-on-Iris releases are now available on OPAM as part of the `rocq-released` repo, and can be installed automatically -- look for versions numbered 3.x. It may take a few months for new versions to appear on OPAM.

## Option 2: Build from Source

You can either clone the current master branch, or download a release from the [Releases](https://github.com/PrincetonUniversity/VST/releases) page. Each release lists the major Iris version and CompCert version it has been tested with (CompCert is only necessary if you want to `clightgen` your own C files), and master will usually work with the same versions as the latest release. The code may also work with dev Iris versions, but probably not those any earlier than the listed version. You will also need to install `rocq-flocq`, probably via OPAM.

```(bash)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add builddep/
```

At this point, we use [`Makefile`](./Makefile)
```(bash)
make
```
Additionally, to generate `_CoqProject`:

```(bash)
make _CoqProject
```
