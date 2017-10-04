(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_mach_defs.v: some simple definitions that sit right on top of the TCB. *)

Require Import lam_ref_tcb.
Require Import msl.msl_standard.

(* Some custom tactics, maybe move into msl in base.v *)

Tactic Notation "omegac" :=
  (elimtype False; omega).

Lemma IF_then_else_True:
  forall a b c : Prop, a -> (IF a then b else c) = b.
Proof.
  unfold IF_then_else.
  intros.
  apply prop_ext; split; tauto.
Qed.
Lemma IF_then_else_False:
  forall a b c : Prop, ~a -> (IF a then b else c) = c.
Proof.
  unfold IF_then_else.
  intros.
  apply prop_ext; split; tauto.
Qed.

Ltac IF_tac :=
match goal with |- context [IF ?a then _ else _] =>
   cut (a \/ ~a);
   [ let H := fresh "H" in intro H; destruct H;
     [try (rewrite IF_then_else_True;[|auto]) | try (rewrite IF_then_else_False; [|auto])]
   | ]
end.

Ltac IF_tac_in H :=
match type of H with context [IF ?a then _ else _] =>
   cut (a \/ ~a);
   [ let H' := fresh "H" in intro H'; destruct H';
     [try (rewrite IF_then_else_True in H ;[|auto]) | try (rewrite IF_then_else_False in H; [|auto])]
   | ]
end.

(* Coerce from values to exprs... *)
Lemma isvNat: forall n,
  isValue (Nat n).
Proof.
  firstorder.
Qed.

Lemma isvLoc: forall l,
  isValue (Loc l).
Proof.
  firstorder.
Qed.

Lemma isvLam: forall e,
  closed' 1 e ->
  isValue (Lam e).
Proof.
  firstorder.
Qed.

Definition v_Nat (n : nat) : value :=
  exp_to_val (Nat n) (isvNat n).

Definition v_Loc (l : addr) : value :=
  exp_to_val (Loc l) (isvLoc l).

Definition v_Lam (e : expr) (H: closed' 1 e) : value :=
  exp_to_val (Lam e) (isvLam e H).

(* Stopped = value or stuck *)
Definition stopped (m : mem) (e : expr) : Prop :=
  ~ exists m', exists e', step (m, e) (m', e').

(* substition environments, needed for typing lambdas *)
Definition env : Type := list value.

Fixpoint subst_env' (n : nat) (rho : env) (exp : expr) : expr :=
  match rho with
   | nil => exp
   | v :: vx => subst n v (subst_env' (n + 1) vx exp)
  end.

Definition subst_env (rho : env) (exp : expr) : expr :=
  subst_env' 0 rho exp.

Definition empty_mem : mem := (0, fun _ => v_Nat 0).

(* Standard indexed composition *)
Inductive stepn : nat -> state -> state -> Prop :=
 | step0 : forall st,
   stepn 0 st st
 | stepS : forall n st st' st'',
   step st st' ->
   stepn n st' st'' ->
   stepn (S n) st st''.


Definition safen (n : nat) (st : state) : Prop :=
  forall n', n' < n ->
    forall st',
      stepn n' st st' ->
        can_step st' \/ at_value st'.
