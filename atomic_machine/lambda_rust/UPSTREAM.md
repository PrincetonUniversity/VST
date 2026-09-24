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
- `common.v` contains heap operations and heap-cell-polymorphic literal and
  binary-operation relations shared by both semantics.
- `reference.v` contains the original combined value/race-state heap,
  `head_step`, an evaluation-context closure, and the concurrent thread-pool
  closure.
- `event_semantics.v` contains the sequential event semantics used by the
  atomic-machine instantiation.
- `equivalence.v` proves the reachability equivalence theorem between stable
  configurations of the two semantics.
- `adequacy.v` instantiates generic `am_safe`, defines reference safety, and
  proves that AM safety implies reference progress at reachable stable
  configurations in the non-spawning fragment. It also gives a checked
  counterexample to transporting full safety through the existing forward
  relation without strengthening it.
- `races.v` contains the original next-access and non-racing predicates.
- `LICENSE.lambda-rust` reproduces the upstream license.

The equivalence theorem relates the event semantics and atomic machine to the
non-spawning reference transition system. The reference transition rules
remain frozen; generic definitions used by both semantics live in `common.v`.

## Safety and adequacy

`atomic_machine.v` defines `am_safe final` for an arbitrary `sqlang`. The
termination predicate is an explicit parameter, instantiated in `adequacy.v`
by `is_Some (to_val e)`. In every reachable machine configuration, each thread
must either have terminated with no pending events or be able to step with
the current shared memory and reservations. A singleton-pool reduction tests
the selected thread; `am_reducible_in_pool` proves that such a reduction can
be scheduled in any pool containing it. `StuckState` is never safe.

`lr_reference_safe` is the safety component of reference RustBelt/Iris
adequacy: every thread in every reachable reference configuration is a value
or can take a primitive step. This definition uses the full reference
semantics, including forks. It does not impose a result postcondition.

`lr_am_safe_reference_stable` is a partial connection to that property. It
uses `lambda_rust_reachability_equivalence` and a separate local progress
lemma. Its reference execution must be non-spawning, and the observed
configuration must have a stable match. It does **not** establish
`lr_am_safe mc -> lr_reference_safe rc` or the converse.

The existing simulations forget reservations and allow crashed threads to
match arbitrary thread states. `lr_forward_match_does_not_reflect_safety`
exhibits a safe AM configuration related to an unsafe reference configuration.
This witness is not a pair of stable initial states, so it does not refute
the desired safety correspondence from stable initial states. Proving that
correspondence requires additional reasoning about intermediate states,
crashes, and per-thread progress; stable reachability equivalence alone is
insufficient. Supporting full reference executions also requires a machine
thread-spawn rule.

Build the safety definitions and proofs with `make lambda-rust-adequacy`.

## Porting changes

The following changes are intended to be mechanical:

1. Imports use `Stdlib` and the current `stdpp` package.
2. The syntax and operational rules have been separated into two modules.
3. Heap-range operations and literal and binary-operation relations are
   generalized over the heap cell type so the reference and event semantics
   use the same definitions. Their specialization to the reference heap is
   unchanged.
4. The old Iris `EctxiLanguage` packaging is replaced by explicit
   `prim_step` and thread-pool `step` relations with the same closures.
5. Proof-only helpers, typeclass instances not required by the semantics,
   Iris weakest-precondition infrastructure, and the proof of
   `safe_nonracing` are not included.
6. Constructor and variable names use ASCII where that improves
   compatibility; the rule premises and conclusions are unchanged.

Any later semantic deviation should be made in a new semantics module and
related to this reference by a theorem.
