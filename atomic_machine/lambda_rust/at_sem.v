(** The atomic machine specialized to lambda-Rust: the machine of
    [atomic_machine.v] run with the language instance [lr_language] of
    [sq_sem.v]. *)

From stdpp Require Import base gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.

Set Default Proof Using "Type".

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

Definition lr_at_step
    (c1 c2 : lr_machine_configuration) : Prop :=
  @at_step loc val _ _ lr_mem lr_layout lr_memory lr_language
    (lr_machine_threads c1) (lr_machine_mem c1) (lr_machine_rw c1)
    (lr_machine_threads c2) (lr_machine_mem c2) (lr_machine_rw c2).
