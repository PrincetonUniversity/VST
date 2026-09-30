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

From Stdlib Require Import List Lia.
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

Definition lr_mem_ev : Type := @mem_ev loc.

(** Explicitly instantiated constructors: elaborating [Running] inside a
    record literal leaves its [sqlang] instance undetermined. *)

Definition lr_running (e : expr) (T : list lr_mem_ev) : lr_tstate :=
  @Running loc val _ _ lr_mem lr_layout lr_memory lr_language e T.

Definition lr_stuck : lr_tstate :=
  @StuckState loc val _ _ lr_mem lr_layout lr_memory lr_language.

Set Primitive Projections.

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

Lemma lr_steps_one {A : Type} (R : A -> A -> Prop) x y :
  R x y -> lr_steps R x y.
Proof. intros H. apply LRStepsStep with y; [ exact H | apply LRStepsRefl ]. Qed.

Lemma lr_steps_two {A : Type} (R : A -> A -> Prop) x y z :
  R x y -> R y z -> lr_steps R x z.
Proof. intros H1 H2. apply LRStepsStep with y; [ exact H1 | apply lr_steps_one; exact H2 ]. Qed.

Lemma lr_steps_trans {A : Type} (R : A -> A -> Prop) x y z :
  lr_steps R x y -> lr_steps R y z -> lr_steps R x z.
Proof.
  intros H1 H2. induction H1 as [ | x y z' Hxy _ IH ]; [ exact H2 | ].
  apply LRStepsStep with y; [ exact Hxy | apply IH; exact H2 ].
Qed.
