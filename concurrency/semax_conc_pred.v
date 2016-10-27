Require Import msl.msl_standard.
Require Import msl.seplog.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.juicy_mem_ops.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.semax.
Require Import veric.semax_call.
Require Import veric.semax_ext.
Require Import veric.semax_ext_oracle.
Require Import veric.juicy_safety.
Require Import veric.Clight_new.
Require Import veric.res_predicates.
Require Import veric.SeparationLogic.
Require Import sepcomp.semantics.
Require Import sepcomp.extspec.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import floyd.nested_field_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import concurrency.lksize.

Definition positive_mpred (R : mpred) :=
  forall phi, app_pred R phi -> exists l sh rsh k p, phi @ l = YES sh rsh k p.

Program Definition weak_positive_mpred (P: mpred): mpred :=
  fun w => positive_mpred (approx (S (level w)) P).
Next Obligation.
  intros; hnf; intros.
  unfold positive_mpred in *.
  intros.
  apply H0.
  simpl in H1 |- *.
  destruct H1; split; auto.
  apply age_level in H.
  omega.
Defined.

Lemma positive_mpred_nonexpansive:
  nonexpansive weak_positive_mpred.
Proof.
  intros.
  hnf; intros.
  intros n ?.
  simpl in H |- *.
  assert (forall y, (n >= level y)%nat -> (P y <-> Q y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  clear H.
  intros; split; intros.
  + hnf in H2 |- *.
    intros.
    apply H2; clear H2.
    simpl in H3 |- *.
    destruct H3; split; auto.
    apply H0; auto.
    apply necR_level in H1.
    omega.
  + hnf in H2 |- *.
    intros.
    apply H2; clear H2.
    simpl in H3 |- *.
    destruct H3; split; auto.
    apply H0; auto.
    apply necR_level in H1.
    omega.
Qed.

Program Definition weak_precise_mpred (P: mpred): mpred :=
  fun w => precise (approx (S (level w)) P).
Next Obligation.
  intros; hnf; intros.
  hnf in H0 |- *.
  intros.
  apply (H0 w); auto.
  + simpl in H1 |- *; destruct H1; split; auto.
    apply age_level in H; omega.
  + simpl in H2 |- *; destruct H2; split; auto.
    apply age_level in H; omega.
Defined.

Lemma precise_mpred_nonexpansive: nonexpansive weak_precise_mpred.
Proof.
  hnf; intros.
  intros n ?.
  simpl in H |- *.
  assert (forall y, (n >= level y)%nat -> (P y <-> Q y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  clear H.
  intros.
  split; intros.
  + hnf in H2 |- *; intros; apply (H2 w); auto.
    - destruct H3; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
    - destruct H4; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
  + hnf in H2 |- *; intros; apply (H2 w); auto.
    - destruct H3; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
    - destruct H4; split; auto.
      apply H0; auto.
      apply necR_level in H1; omega.
Qed.

Definition lock_inv : share -> val -> mpred -> mpred :=
  fun sh v R =>
    (EX b : block, EX ofs : _,
      !!(v = Vptr b ofs) &&
      LKspec LKSIZE
        R
        (Share.unrel Share.Lsh sh)
        (Share.unrel Share.Rsh sh)
        (b, Int.unsigned ofs))%logic.

Definition rec_inv sh v (Q R: mpred): Prop :=
  (R = Q * lock_inv sh v (|> R))%logic.

Definition weak_rec_inv sh v (Q R: mpred): mpred :=
  (! (R <=> Q * lock_inv sh v (|> R)))%pred.

Lemma rec_inv1_nonexpansive: forall sh v Q,
  nonexpansive (weak_rec_inv sh v Q).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2 n H.
  assert (forall y, (n >= level y)%nat -> (P1 y <-> P2 y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  clear H.
Admitted. (* Obviously True *)

Lemma rec_inv2_nonexpansive: forall sh v R,
  nonexpansive (fun Q => weak_rec_inv sh v Q R).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2 n H.
  assert (forall y, (n >= level y)%nat -> (P1 y <-> P2 y)).
  Focus 1. {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  } Unfocus.
  clear H.
Admitted. (* Obviously True *)

Lemma positive_weak_positive: forall R,
  positive_mpred R ->
  TT |-- weak_positive_mpred R.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_positive_mpred R)).
  intros w _.
  hnf in H |- *.
  intros; apply H.
  eapply approx_p; eauto.
Qed.

Lemma precise_weak_precise: forall R,
  precise R ->
  TT |-- weak_precise_mpred R.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_precise_mpred R)).
  intros w _.
  hnf in H |- *.
  intros; apply (H w0); auto.
  + eapply approx_p; eauto.
  + eapply approx_p; eauto.
Qed.

Lemma rec_inv_weak_rec_inv: forall sh v Q R,
  rec_inv sh v Q R ->
  TT |-- weak_rec_inv sh v Q R.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_rec_inv sh v Q R)).
  intros w _.
  hnf in H |- *.
  intros.
  rewrite H at 1 4.
  split; intros; hnf; intros; auto.
Qed.


