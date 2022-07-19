Require Import VST.msl.msl_standard.
Require Import VST.msl.seplog.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Require Import VST.veric.semax_ext.
(*Require Import VST.veric.semax_ext_oracle.*)
Require Import VST.veric.juicy_safety.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SeparationLogic.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.floyd.base VST.floyd.seplog_tactics.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.jmeq_lemmas.

Lemma approx_derives_ge : forall n m P, (n <= m)%nat -> approx n P |-- approx m P.
Proof.
  intros; constructor. change (predicates_hered.derives (approx n P) (approx m P)).
  intros ? []; split; auto; lia.
Qed.

Lemma approx_derives : forall P n, approx n P |-- P.
Proof.
  constructor; intro; apply approx_p.
Qed.

(*Lemma unfash_fash_equiv: forall P Q: mpred,
  (P <=> Q)%pred |--
  ((subtypes.unfash (subtypes.fash P): mpred) <=> (subtypes.unfash (subtypes.fash Q): mpred))%pred.
Proof.
  intros.
  constructor; hnf; intros.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P y <-> app_pred Q y)).
  {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  }
  hnf; intros.
  split; simpl; hnf; intros.
  + apply necR_level in H2.
    rewrite <- H0 by lia.
    auto.
  + apply necR_level in H2.
    rewrite H0 by lia.
    auto.
Qed.

Lemma iffp_equiv: forall P1 Q1 P2 Q2: mpred,
  (((P1 <=> Q1) && (P2 <=> Q2))%pred |-- ((P1 <--> P2)%pred <=> (Q1 <--> Q2))%pred)%pred.
Proof.
  intros.
  constructor; hnf; intros.
  destruct H.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P1 y <-> app_pred Q1 y)).
  {
    intros; specialize (H y H1).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H2 y). spec H2; [auto |].
    tauto.
  }
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P2 y <-> app_pred Q2 y)).
  {
    intros; specialize (H0 y H2).
    destruct H0.
    specialize (H0 y). spec H0; [auto |].
    specialize (H3 y). spec H3; [auto |].
    tauto.
  }
  split; intros; hnf; intros.
  + split; [destruct H5 as [? _] | destruct H5 as [_ ?]]; intros ? HH; specialize (H5 _ HH).
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite <- H1, <- H2 by lia.
      auto.
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite <- H1, <- H2 by lia.
      auto.
  + split; [destruct H5 as [? _] | destruct H5 as [_ ?]]; intros ? HH; specialize (H5 _ HH).
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite H1, H2 by lia.
      auto.
    - apply necR_level in H4.
      apply necR_level in HH.
      rewrite H1, H2 by lia.
      auto.
Qed.

Lemma sepcon_equiv: forall P1 Q1 P2 Q2: mpred,
  ((P1 <=> Q1)%pred && (P2 <=> Q2)%pred |-- ((P1 * P2) <=> (Q1 * Q2))%pred)%pred.
Proof.
  intros.
  constructor; hnf; intros.
  destruct H.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P1 y <-> app_pred Q1 y)).
  {
    intros; specialize (H y H1).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H2 y). spec H2; [auto |].
    tauto.
  }
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P2 y <-> app_pred Q2 y)).
  {
    intros; specialize (H0 y H2).
    destruct H0.
    specialize (H0 y). spec H0; [auto |].
    specialize (H3 y). spec H3; [auto |].
    tauto.
  }
  split; intros; hnf; intros.
  + destruct H5 as [w1 [w2 [? [? ?]]]].
    exists w1, w2; split; [| split]; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite <- H1 by lia; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite <- H2 by lia; auto.
  + destruct H5 as [w1 [w2 [? [? ?]]]].
    exists w1, w2; split; [| split]; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite H1 by lia; auto.
    - apply necR_level in H4.
      apply join_level in H5.
      rewrite H2 by lia; auto.
Qed.

Lemma later_equiv: forall P Q: mpred,
  (P <=> Q)%pred |-- (|> P <=> |> Q)%pred.
Proof.
  intros.
  constructor; hnf; intros.
  assert (forall y: rmap, (a >= level y)%nat -> (app_pred P y <-> app_pred Q y)).
  {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  }
  hnf; intros.
  split; hnf; intros; simpl in *; intros.
  + specialize (H3 _ H4).
    apply necR_level in H2.
    apply laterR_level in H4.
    rewrite <- H0 by lia.
    auto.
  + specialize (H3 _ H4).
    apply necR_level in H2.
    apply laterR_level in H4.
    rewrite H0 by lia.
    auto.
Qed.*)
