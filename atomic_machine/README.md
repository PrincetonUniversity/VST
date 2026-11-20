# Atomic machine

## Generic machine and logic

- [atomic_machine.v](atomic_machine.v) — Sequential language interface [sq_lang] where atomic primitives are modeled as external calls and internal steps are non-atomic. Also defines an event-based concurrent semantics that lifts [sq_lang] with a thread pool semantics and atomic memory operations, as well as a notion of data race and safety. Both languages use the same syntax.
- [sqex_logic.v](sqex_logic.v) and [sqex_adequacy.v](sqex_adequacy.v)  — The sqex logic's core definition is the weakest_pre `EXWP`. It is a logic on a generic [sq_lang], with parameterized external-call specifications. The adequacy theorem guarantees that a proof of ` ⊢ EXWP e Q` implies the race freedom, progress, and the return-value postcondition.
- [ext_call_impl.v](ext_call_impl.v) — Specs and soundness (as required by adequacy) proofs for atomic load, store, CAS, and spawn as external functions.

## `lambda_rust/`

**Needs fix** marks proofs that use `lr_step` with the old `Core_Try` and `Core_Commit` machine rules.

- [common.v](lambda_rust/common.v)
- [sq_sem.v](lambda_rust/sq_sem.v) — A single threaded version of lambda-Rust, without atomic operations. Defined as an `sqlang` instance.
- [equivalence.v](lambda_rust/equivalence.v) — **Needs fix** — 
- [adequacy.v](lambda_rust/adequacy.v) — **Needs fix** —
- [safety_reflection.v](lambda_rust/safety_reflection.v) — **Needs fix** -
- [machine_safety.v](lambda_rust/machine_safety.v) — **Needs fix** — 

## `lambda_rust/logic/`
The sqex logic instantiated with [lambda_rust/sq_sem.v](lambda_rust/sq_sem.v).

- [lr_lemmas.v](lambda_rust/logic/lr_lemmas.v) — Evaluation-context and redex lemmas for sequential steps and external calls.
- [sq_heap.v](lambda_rust/logic/sq_heap.v) — Lambda-Rust's heap model without reader-writer counting.
- [sqex_lr_inst.v](lambda_rust/logic/sqex_lr_inst.v) — Instantiates the generic EXWP heap interface and adequacy theorem for LambdaRust.
- [sqex_lr_logic.v](lambda_rust/logic/sqex_lr_logic.v) — EXWP rules for sequential steps of [lambda_rust/sq_sem.v](lambda_rust/sq_sem.v).
- [sqex_examples.v](lambda_rust/logic/sqex_examples.v) — Two example lambda-Rust programs and proofs in [sqex_lr_logic](lambda_rust/logic/sqex_lr_logic.v).

## `clight_am/`

- [clight_at_mach.v](clight_am/clight_at_mach.v) — Clight `sqlang` instance with byte-level memory events and atomic external calls.
- [theory/ClightAM_DRF.v](clight_am/theory/ClightAM_DRF.v) — Locates CASCompCert’s Clight semantics (`Clight_IS_2`) and data-race-freedom predicate (`drf`).
