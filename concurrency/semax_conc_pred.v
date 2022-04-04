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
(*Require Import VST.veric.Clight_new.*)
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
Require Import VST.concurrency.lksize.

(*Definition positive_mpred (R : mpred) :=
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
  lia.
Defined.

Lemma corable_weak_positive R : seplog.corable (weak_positive_mpred R).
Proof.
Admitted. (* corable_weak_positive *)

Lemma positive_mpred_nonexpansive:
  nonexpansive weak_positive_mpred.
Proof.
  intros.
  hnf; intros.
  intros n ?.
  simpl in H |- *.
  assert (forall y, (n >= level y)%nat -> (P y <-> Q y)).
  {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  }
  clear H.
  intros; split; intros.
  + hnf in H2 |- *.
    intros.
    apply H2; clear H2.
    simpl in H3 |- *.
    destruct H3; split; auto.
    apply H0; auto.
    apply necR_level in H1.
    lia.
  + hnf in H2 |- *.
    intros.
    apply H2; clear H2.
    simpl in H3 |- *.
    destruct H3; split; auto.
    apply H0; auto.
    apply necR_level in H1.
    lia.
Qed.

Program Definition weak_precise_mpred (P: mpred): mpred :=
  fun w => precise (approx (S (level w)) P).
Next Obligation.
  intros; hnf; intros.
  hnf in H0 |- *.
  intros.
  apply (H0 w); auto.
  + simpl in H1 |- *; destruct H1; split; auto.
    apply age_level in H; lia.
  + simpl in H2 |- *; destruct H2; split; auto.
    apply age_level in H; lia.
Defined.

Lemma corable_weak_precise R : seplog.corable (weak_precise_mpred R).
Proof.
Admitted. (* corable_weak_precise *)

Lemma precise_mpred_nonexpansive: nonexpansive weak_precise_mpred.
Proof.
  hnf; intros.
  intros n ?.
  simpl in H |- *.
  assert (forall y, (n >= level y)%nat -> (P y <-> Q y)).
  {
    intros; specialize (H y H0).
    destruct H.
    specialize (H y). spec H; [auto |].
    specialize (H1 y). spec H1; [auto |].
    tauto.
  }
  clear H.
  intros.
  split; intros.
  + hnf in H2 |- *; intros; apply (H2 w); auto.
    - destruct H3; split; auto.
      apply H0; auto.
      apply necR_level in H1; lia.
    - destruct H4; split; auto.
      apply H0; auto.
      apply necR_level in H1; lia.
  + hnf in H2 |- *; intros; apply (H2 w); auto.
    - destruct H3; split; auto.
      apply H0; auto.
      apply necR_level in H1; lia.
    - destruct H4; split; auto.
      apply H0; auto.
      apply necR_level in H1; lia.
Qed.*)

Lemma approx_derives_ge : forall n m P, (n <= m)%nat -> approx n P |-- approx m P.
Proof.
  intros; constructor. change (predicates_hered.derives (approx n P) (approx m P)).
  intros ? []; split; auto; lia.
Qed.

Lemma approx_derives : forall P n, approx n P |-- P.
Proof.
  constructor; intro; apply approx_p.
Qed.

Definition exclusive_mpred (R : mpred) :=
  (R * R |-- FF)%logic.

Create HintDb exclusive.

(*  (! (R <=> Q * |>lock_inv sh v R))%pred.

Program Definition weak_exclusive_mpred (P: mpred): mpred :=
  unfash (fun n => exclusive_mpred (approx (S n) P)).
Next Obligation.
  unfold exclusive_mpred; intros; hnf; intros.
  apply age_level in H; simpl in H; unfold natLevel in H; subst.
  eapply derives_trans, H0.
  apply sepcon_derives; apply approx_derives_ge; auto.
Defined.*)

Program Definition weak_exclusive_mpred (P: mpred): mpred :=
  (! (P * P >=> FF))%pred.

Lemma corable_weak_exclusive R : seplog.corable (weak_exclusive_mpred R).
Proof.
  apply assert_lemmas.corable_unfash, _.
Qed.

Lemma exclusive_mpred_nonexpansive:
  nonexpansive weak_exclusive_mpred.
Proof.
  unfold weak_exclusive_mpred, nonexpansive; intros.
  apply eqp_unfash, eqp_subp_subp, eqp_refl.
  apply eqp_sepcon; auto.
Qed.

Definition lock_inv : share -> val -> mpred -> mpred :=
  fun sh v R =>
    (EX b : block, EX ofs : _,
      !!(v = Vptr b ofs) &&
      LKspec LKSIZE
        R sh (b, Ptrofs.unsigned ofs))%logic.

Definition rec_inv sh v (Q R: mpred): Prop :=
  (R = Q * |>lock_inv sh v R)%logic.

Definition weak_rec_inv sh v (Q R: mpred): mpred :=
  (! (R <=> Q * |>lock_inv sh v R))%pred.

Lemma lockinv_isptr sh v R : lock_inv sh v R = (!! isptr v && lock_inv sh v R)%logic.
Proof.
  assert (D : isptr v \/ ~isptr v) by (destruct v; simpl; auto).
  destruct D.
  - rewrite prop_true_andp; auto.
  - rewrite prop_false_andp; auto.
    apply pred_ext.
    + unfold lock_inv. Transparent mpred. Intros b ofs. Opaque mpred. subst; simpl in *; tauto.
    + apply FF_left.
Qed.

Corollary lock_inv_saturate_local sh v R : lock_inv sh v R |-- (!! isptr v)%logic.
Proof.
  rewrite lockinv_isptr; Intros.
  apply prop_right; auto.
Qed.
#[export] Hint Resolve lock_inv_saturate_local : saturate_local.


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

Lemma nonexpansive_lock_inv : forall sh p, nonexpansive (lock_inv sh p).
Proof.
  intros.
  unfold lock_inv.
  apply @exists_nonexpansive.
  intros b.
  apply @exists_nonexpansive.
  intros y.
  apply @conj_nonexpansive.
  apply @const_nonexpansive.

  unfold LKspec.
  apply forall_nonexpansive; intros.
  hnf; intros.
  intros n ?.
  assert (forall y: rmap, (n >= level y)%nat -> (app_pred P y <-> app_pred Q y)).
  {
    clear - H.
    intros; specialize (H y H0).
    destruct H.
    specialize (H _ _ (necR_refl _) (ext_refl _)).
    specialize (H1 _ _ (necR_refl _) (ext_refl _)).
    tauto.
  }
  simpl; split; intros.
  + if_tac; auto.
    destruct H4 as [p0 ?].
    exists p0.
    rewrite H4; f_equal.
    f_equal.
    extensionality ts; clear ts.
    clear H4 H5 p0.
    apply ext_level in H3 as <-.
    apply predicates_hered.pred_ext; hnf; intros ? [? ?]; split; auto.
    - apply necR_level in H2.
      rewrite <- H0 by lia; auto.
    - apply necR_level in H2.
      rewrite H0 by lia; auto.
  + if_tac; auto.
    destruct H4 as [p0 ?].
    exists p0.
    rewrite H4; f_equal.
    f_equal.
    extensionality ts; clear ts.
    clear H4 H5 p0.
    apply ext_level in H3 as <-.
    apply predicates_hered.pred_ext; hnf; intros ? [? ?]; split; auto.
    - apply necR_level in H2.
      rewrite H0 by lia; auto.
    - apply necR_level in H2.
      rewrite <- H0 by lia; auto.
Qed.

Lemma rec_inv1_nonexpansive: forall sh v Q,
  nonexpansive (weak_rec_inv sh v Q).
Proof.
  unfold weak_rec_inv, nonexpansive; intros.
  apply eqp_unfash, eqp_eqp; auto.
  apply eqp_sepcon; [apply eqp_refl|].
  eapply predicates_hered.derives_trans, subtypes.eqp_later1.
  eapply predicates_hered.derives_trans, predicates_hered.now_later.
  apply nonexpansive_lock_inv.
Qed.

Lemma rec_inv2_nonexpansive: forall sh v R,
  nonexpansive (fun Q => weak_rec_inv sh v Q R).
Proof.
  unfold weak_rec_inv, nonexpansive; intros.
  apply eqp_unfash, eqp_eqp; [apply eqp_refl|].
  apply eqp_sepcon; auto.
  eapply predicates_hered.derives_trans, subtypes.eqp_later1.
  eapply predicates_hered.derives_trans, predicates_hered.now_later.
  apply eqp_refl.
Qed.

Lemma exclusive_weak_exclusive: forall R,
  exclusive_mpred R ->
  TT |-- weak_exclusive_mpred R.
Proof.
  intros.
  constructor; intros ?????????.
  eapply H; auto.
Qed.

Lemma rec_inv_weak_rec_inv: forall sh v Q R,
  rec_inv sh v Q R ->
  TT |-- weak_rec_inv sh v Q R.
Proof.
  intros.
  unfold weak_rec_inv.
  constructor. intros ? _ ??; split; intros ?????.
  - rewrite H in * |-; auto.
  - rewrite H; auto.
Qed.
