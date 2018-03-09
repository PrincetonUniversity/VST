Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Local Open Scope logic.

Lemma wand_frame_intro {A} {ND: NatDed A} {SL: SepLog A}: forall (P Q: A),
  Q |-- P -* P * Q.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm; auto.
Qed.

Lemma wand_frame_elim {A} {ND: NatDed A} {SL: SepLog A}: forall (P Q: A),
  P * (P -* Q) |-- Q.
Proof.
  intros.
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint; auto.
Qed.

Lemma wand_frame_elim' {A} {ND: NatDed A} {SL: SepLog A}: forall (P P' Q: A),
  P |-- P' -> P * (P' -* Q) |-- Q.
Proof.
  intros.
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint; auto.
  apply wand_derives; auto.
Qed.

Lemma wand_frame_ver {A} {ND: NatDed A} {SL: SepLog A}: forall (P Q R: A),
  (P -* Q) * (Q -* R) |-- P -* R.
Proof.
  intros.
  apply -> wand_sepcon_adjoint.
  rewrite (sepcon_comm _ P), <- sepcon_assoc.
  eapply derives_trans.
  + eapply sepcon_derives; [apply wand_frame_elim | apply derives_refl].
  + apply wand_frame_elim.
Qed.

Lemma wand_frame_hor {A} {ND: NatDed A} {SL: SepLog A}: forall (P1 P2 Q1 Q2: A),
  (P1 -* Q1) * (P2 -* Q2) |-- P1 * P2 -* Q1 * Q2.
Proof.
  intros.
  apply -> wand_sepcon_adjoint.
  rewrite <- (sepcon_assoc _ P1), (sepcon_comm _ P1), <- (sepcon_assoc P1), (sepcon_assoc _ _ P2), (sepcon_comm _ P2).
  apply sepcon_derives; apply wand_frame_elim.
Qed.

Lemma wand_frame_frame {A} {ND: NatDed A} {SL: SepLog A}: forall (P Q F: A),
  P -* Q |-- P * F -* Q * F.
Proof.
  intros.
  apply -> wand_sepcon_adjoint.
  rewrite <- sepcon_assoc, (sepcon_comm _ P).
  apply sepcon_derives; [apply wand_frame_elim | auto].
Qed.

