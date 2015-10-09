Require Import compcert.lib.Coqlib.
Require Import Integers.
Require Import EqNat.
Require Import msl.Coqlib2.
Require Import Relations.
Require Export msl.eq_dec.
Require Import Coq.Sets.Ensembles.
Set Implicit Arguments.

Definition Ensemble_join {A} (X Y Z: Ensemble A): Prop :=
  (forall a, Z a <-> X a \/ Y a) /\ (forall a, X a -> Y a -> False).

Lemma nat_of_Z_eq: forall i, nat_of_Z (Z_of_nat i) = i.
Proof.
intros.
apply inj_eq_rev.
rewrite nat_of_Z_eq; auto.
omega.
Qed.

Lemma nth_error_length:
  forall {A} i (l: list A), nth_error l i = None <-> (i >= length l)%nat.
Proof.
induction i; destruct l; simpl; intuition.
inv H.
inv H.
rewrite IHi in H. omega.
rewrite IHi. omega.
Qed.

