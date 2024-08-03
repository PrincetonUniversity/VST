Require Import VST.msl.msl_standard.
Require Import VST.msl.seplog.
Require Import VST.veric.base.
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
Require Import VST.veric.semax_ext_oracle.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.Clight_core.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SeparationLogic.
Require Import VST.sepcomp.extspec.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.conclib.

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

Lemma unfash_fash_equiv: forall P Q: mpred,
  (P <=> Q |--
  (subtypes.unfash (subtypes.fash P): mpred) <=> (subtypes.unfash (subtypes.fash Q): mpred))%pred.
Proof.
  intros.
  constructor; apply eqp_unfash.
  rewrite eqp_nat.
  apply predicates_hered.andp_right; eapply predicates_hered.derives_trans, subtypes.fash_K;
    apply subtypes.fash_derives.
  - apply predicates_hered.andp_left1; auto.
  - apply predicates_hered.andp_left2; auto.
Qed.

Lemma iffp_equiv: forall P1 Q1 P2 Q2: mpred,
  ((P1 <=> Q1) && (P2 <=> Q2) |-- (P1 <--> P2) <=> (Q1 <--> Q2))%pred.
Proof.
  intros.
  constructor; apply eqp_andp; apply subp_eqp; apply subtypes.subp_imp.
  - apply predicates_hered.andp_left1.
    rewrite eqp_comm; apply eqp_subp.
  - apply predicates_hered.andp_left2.
    apply eqp_subp.
  - apply predicates_hered.andp_left1.
    apply eqp_subp.
  - apply predicates_hered.andp_left2.
    rewrite eqp_comm; apply eqp_subp.
  - apply predicates_hered.andp_left2.
    rewrite eqp_comm; apply eqp_subp.
  - apply predicates_hered.andp_left1.
    apply eqp_subp.
  - apply predicates_hered.andp_left2.
    apply eqp_subp.
  - apply predicates_hered.andp_left1.
    rewrite eqp_comm; apply eqp_subp.
Qed.

Lemma sepcon_equiv: forall P1 Q1 P2 Q2: mpred,
  ((P1 <=> Q1) && (P2 <=> Q2) |-- (P1 * P2) <=> (Q1 * Q2))%pred.
Proof.
  intros.
  constructor; apply eqp_sepcon.
  - apply predicates_hered.andp_left1; auto.
  - apply predicates_hered.andp_left2; auto.
Qed.

Lemma later_equiv: forall P Q: mpred,
  (P <=> Q |-- |> P <=> |> Q)%pred.
Proof.
  intros.
  constructor; eapply predicates_hered.derives_trans, subtypes.eqp_later1.
  apply predicates_hered.now_later.
Qed.

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
    split; [eapply H | eapply H1]; eauto.
  }
  simpl; split; intros.
  + if_tac; auto.
    destruct H4 as [p0 ?].
    exists p0.
    rewrite H4; f_equal.
    f_equal.
    extensionality ts; clear ts.
    clear H4 H5 p0.
    apply ext_level in H3.
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
    apply ext_level in H3.
    apply predicates_hered.pred_ext; hnf; intros ? [? ?]; split; auto.
    - apply necR_level in H2.
      rewrite H0 by lia; auto.
    - apply necR_level in H2.
      rewrite <- H0 by lia; auto.
Qed.

Lemma rec_inv1_nonexpansive: forall sh v Q,
  nonexpansive (weak_rec_inv sh v Q).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2.
  eapply predicates_hered.derives_trans; [| apply unfash_fash_equiv].
  eapply predicates_hered.derives_trans; [| apply iffp_equiv].
  apply predicates_hered.andp_right; auto.
  eapply predicates_hered.derives_trans; [| apply sepcon_equiv].
  apply predicates_hered.andp_right.
  {
    intros n ?.
    split; intros; hnf; intros; auto.
  }
  eapply predicates_hered.derives_trans, subtypes.eqp_later1.
  eapply predicates_hered.derives_trans, predicates_hered.now_later.
  apply nonexpansive_lock_inv.
Qed.

Lemma rec_inv2_nonexpansive: forall sh v R,
  nonexpansive (fun Q => weak_rec_inv sh v Q R).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2.
  eapply predicates_hered.derives_trans; [| apply unfash_fash_equiv].
  eapply predicates_hered.derives_trans; [| apply iffp_equiv].
  apply predicates_hered.andp_right.
  {
    intros n ?.
    split; intros; hnf; intros; auto.
  }
  eapply predicates_hered.derives_trans; [| apply sepcon_equiv].
  apply predicates_hered.andp_right; auto.

  intros n ?.
  split; intros; hnf; intros; auto.
Qed.

Lemma rec_inv_weak_rec_inv: forall sh v Q R,
  rec_inv sh v Q R ->
  TT |-- weak_rec_inv sh v Q R.
Proof.
  intros.
  constructor.
  intros w _.
  hnf in H |- *.
  intros.
  rewrite H at 1 4.
  split; intros; hnf; intros; auto.
Qed.
