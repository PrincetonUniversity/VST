# POPL'18 lambda-Rust reference port

This directory contains a standalone Rocq 9 port of the operational core of
the POPL'18 lambda-Rust development.

## Pinned source

- Repository: <https://gitlab.mpi-sws.org/iris/lambda-rust>
- Revision: `eec05e0aa61e2e8346ab380d0930bbaca4cc1a31`
- Upstream branch/tag used for discovery: `popl18`
- Source files:
  - `theories/lang/lang.v`
  - the definitions at the beginning of `theories/lang/races.v`

The revision, rather than the movable branch name or the prose presentation
in the paper, is the equivalence target.

## Files

- `syntax.v` contains the shared syntax, values, substitution, evaluation
  contexts, and basic operations.
- `reference.v` contains the original combined value/race-state heap,
  `head_step`, an evaluation-context closure, and the concurrent thread-pool
  closure.
- `races.v` contains the original next-access and non-racing predicates.
- `LICENSE.lambda-rust` reproduces the upstream license.

Future files should define the new sequential event semantics, the
atomic-machine instantiation, and the equivalence proof. They should import
the syntax from this directory but must not silently change `reference.v`.

## Porting changes

The following changes are intended to be mechanical:

1. Imports use `Stdlib` and the current `stdpp` package.
2. The syntax and operational rules have been separated into two modules.
3. The old Iris `EctxiLanguage` packaging is replaced by explicit
   `prim_step` and thread-pool `step` relations with the same closures.
4. Proof-only helpers, typeclass instances not required by the semantics,
   Iris weakest-precondition infrastructure, and the proof of
   `safe_nonracing` are not included.
5. Constructor and variable names use ASCII where that improves
   compatibility; the rule premises and conclusions are unchanged.

Any later semantic deviation should be made in a new semantics module and
related to this reference by a theorem.
