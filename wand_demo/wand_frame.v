Require Import msl.seplog.
Require Import msl.log_normalize.
Local Open Scope logic.

Lemma wf_intro {A} {ND: NatDed A} {SL: SepLog A}: forall (P Q: A),
  Q |-- P -* P * Q.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm; auto.
Qed.

Lemma wf_elim {A} {ND: NatDed A} {SL: SepLog A}: forall (P Q: A),
  P * (P -* Q) |-- Q.
Proof.
  intros.
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint; auto.
Qed.
