(**
  Statement of the equivalence between the lambda-Rust reference semantics
  and its atomic-machine implementation.

  The two systems expose different administrative states: the atomic machine
  reserves and commits events, while the reference semantics uses [Na2Ord].
  We therefore compare reflexive-transitive reachability between stable
  configurations, where neither representation has an access in flight.

  The atomic machine does not yet provide a thread-spawn rule, so the
  reference transition below is restricted to steps that spawn no threads.
*)

From Stdlib Require Import List.
From stdpp Require Import gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.event_semantics.
Require Import VST.atomic_machine.lambda_rust.reference.

Import ListNotations.

Set Default Proof Using "Type".

(** The atomic machine specialized to lambda-Rust. *)

Definition lr_rw_map : Type := @rw_map loc _ _.

Definition lr_tstate : Type :=
  @tstate loc val _ _ lr_mem lr_layout lr_memory lr_language.

Definition lr_tpool : Type :=
  @tpool loc val _ _ lr_mem lr_layout lr_memory lr_language.

Record lr_machine_configuration : Type := {
  lr_machine_threads : lr_tpool;
  lr_machine_mem : lr_mem;
  lr_machine_rw : lr_rw_map;
}.

Definition lr_machine_step
    (c1 c2 : lr_machine_configuration) : Prop :=
  @at_step loc val _ _ lr_mem lr_layout lr_memory lr_language
    (lr_machine_threads c1) (lr_machine_mem c1) (lr_machine_rw c1)
    (lr_machine_threads c2) (lr_machine_mem c2) (lr_machine_rw c2).

(** The non-spawning fragment of the reference transition relation. *)

Inductive lr_reference_step : configuration -> configuration -> Prop :=
| LRReferenceStep t1 e1 t2 sigma1 e2 sigma2 :
    prim_step e1 sigma1 e2 sigma2 [] ->
    lr_reference_step
      (t1 ++ e1 :: t2, sigma1)
      (t1 ++ e2 :: t2, sigma2).

(** Reflexive-transitive closure, used to hide administrative steps. *)

Inductive lr_steps {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| LRStepsRefl x : lr_steps R x x
| LRStepsStep x y z : R x y -> lr_steps R y z -> lr_steps R x z.

(** Correspondence of stable thread and heap states. *)

Inductive lr_stable_thread_match : expr -> lr_tstate -> Prop :=
| LRStableRunning e :
    lr_stable_thread_match e (Running e [])
| LRStableStuck :
    lr_stable_thread_match stuck_term StuckState.

Definition lr_stable_pools_match
    (threads : thread_pool) (tp : lr_tpool) : Prop :=
  forall i,
    match threads !! i, tp !! i with
    | Some e, Some c => lr_stable_thread_match e c
    | None, None => True
    | _, _ => False
    end.

Definition lr_stable_heaps_match
    (sigma : state) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  forall l,
    match m !! l with
    | Some v =>
        sigma !! l = Some (RSt 0, v) /\
        mu !! l = Some (Rst 0)
    | None => sigma !! l = None /\ mu !! l = None
    end.

Definition lr_stable_configuration_match
    (rc : configuration) (mc : lr_machine_configuration) : Prop :=
  let '(threads, sigma) := rc in
  lr_stable_pools_match threads (lr_machine_threads mc) /\
  lr_stable_heaps_match sigma (lr_machine_mem mc) (lr_machine_rw mc).

(**
  Reachability agrees between corresponding stable configurations.  A proof
  may pass through the administrative states omitted by
  [lr_stable_configuration_match].
*)
Theorem lambda_rust_reachability_equivalence rc1 mc1 rc2 mc2 :
  lr_stable_configuration_match rc1 mc1 ->
  lr_stable_configuration_match rc2 mc2 ->
  (lr_steps lr_reference_step rc1 rc2 <->
   lr_steps lr_machine_step mc1 mc2).
Proof. Admitted.
