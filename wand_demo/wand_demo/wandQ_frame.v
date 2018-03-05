Require Import VST.msl.seplog.
Require Import VST.msl.alg_seplog.
Require Import VST.msl.log_normalize.
Require Import WandDemo.wand_frame.
Local Open Scope logic.

Lemma wandQ_frame_refine {A} {ND: NatDed A} {SL: SepLog A}: forall B C (P: B -> A) (f: C -> B),
  allp P |-- allp (fun c => P (f c)).
Proof.
  intros.
  apply allp_right; intros c.
  apply (allp_left _ (f c)).
  auto.
Qed.

Lemma wandQ_frame_intro {A} {ND: NatDed A} {SL: SepLog A}: forall B (P: B -> A) (Q: A),
  Q |-- allp (P -* P * (fun _ => Q)).
Proof.
  intros. simpl.
  apply allp_right; intros a.
  apply wand_frame_intro.
Qed.

Lemma wandQ_frame_elim {A} {ND: NatDed A} {SL: SepLog A}: forall B (P Q: B -> A) (a: B),
  P a * allp (P -* Q) |-- Q a.
Proof.
  intros.
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  apply (allp_left _ a); simpl. auto.
Qed.

Lemma wandQ_frame_ver {A} {ND: NatDed A} {SL: SepLog A}: forall B (P Q R: B -> A),
  allp (P -* Q) * allp (Q -* R) |-- allp (P -* R).
Proof.
  intros.
  apply allp_right; intros a.
  apply <- wand_sepcon_adjoint.
  apply (allp_left _ a).
  apply -> wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply <- wand_sepcon_adjoint.
  apply (allp_left _ a).
  apply -> wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply wand_frame_ver.
Qed.

Lemma wandQ_frame_hor {A} {ND: NatDed A} {SL: SepLog A}: forall B (P1 P2 Q1 Q2: B -> A),
  allp (P1 -* Q1) * allp (P2 -* Q2) |-- allp (P1 * P2 -* Q1 * Q2).
Proof.
  intros.
  apply allp_right; intros a.
  apply <- wand_sepcon_adjoint.
  apply (allp_left _ a).
  apply -> wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply <- wand_sepcon_adjoint.
  apply (allp_left _ a).
  apply -> wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply wand_frame_hor.
Qed.

Lemma wandQ_frame_frame {A} {ND: NatDed A} {SL: SepLog A}: forall B (P Q F: B -> A),
  allp (P -* Q) |-- allp (P * F -* Q * F).
Proof.
  intros.
  apply allp_right; intros a.
  apply (allp_left _ a).
  apply wand_frame_frame.
Qed.
