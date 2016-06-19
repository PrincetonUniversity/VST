Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.mem_obs_eq.
Require Import concurrency.x86_inj.
Require Import concurrency.compcert_threads_lemmas.
Require Import concurrency.dry_context.
Require Import sepcomp.closed_safety.

Import dry_context SEM mySchedule DryMachine DryMachine.ThreadPool.

(** ** Safety for X86 interleaving semantics *)
Module X86Safe.

  Module SimDefs := SimDefs X86Inj.
  Module SimProofs := SimProofs X86Inj.
  Import SimDefs SimProofs X86Inj dry_machine_lemmas.
  Import Renamings MemObsEq ValObsEq.

  Context {cspec: CoreLanguage.corestepSpec}.

  Definition csafe (tp : thread_pool) m sched :=
    forall n, safeN coarse_semantics the_ge n (sched,tp) m.

  Definition fsafe (tp : thread_pool) m sched :=
    forall n, safeN fine_semantics the_ge n (sched,tp) m.

  Import Asm Asm_coop.

  Instance x86Spec : CoreLanguage.corestepSpec.
  Proof.
    split.
    intros m m' m'' ge c c' c'' Hstep Hstep'.
    (*TODO: The proofs. *)
  Admitted.
  
  
  