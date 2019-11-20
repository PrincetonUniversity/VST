From iris.bi Require Import interface.
From iris.proofmode Require Export tactics.

(* undo some "simpl never" settings from std++ *)
Arguments Pos.of_nat : simpl nomatch.
Arguments Pos.to_nat !x / .
Arguments N.add : simpl nomatch.
Arguments Z.of_nat : simpl nomatch.
Arguments Z.to_nat : simpl nomatch.

(* Conflicting notations:

  !!   PMap.get (level 1) vs lookup (level 20), fixed for now by not exporting compcert.lib.Maps
  |==> VST bupd (level 62) vs Iris bupd (level 99), fixed for now by changing to match Iris precedence
    (this is a bit annoying because of the difference in precedence of derives)
*)

Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.SeparationLogic.

Notation "'emp'" := seplog.emp.

Section cofe.
  Instance mpred_equiv : Equiv mpred := eq.
  Instance mpred_dist : Dist mpred := fun n P Q => approx (S n) P = approx (S n) Q.

  Lemma dist_equiv : forall (P Q : pred rmap), (∀ n : nat, P ≡{n}≡ Q) -> P = Q.
  Proof.
    intros; apply predicates_hered.pred_ext; repeat intro.
    - specialize (H (level a)); hnf in H.
      assert (approx (S (level a)) P a) as HP' by (split; auto).
      rewrite H in HP'; apply HP'.
    - specialize (H (level a)); hnf in H.
      assert (approx (S (level a)) Q a) as HP' by (split; auto).
      rewrite <- H in HP'; apply HP'.
  Qed.

  Definition mpred_ofe_mixin : OfeMixin mpred.
  Proof.
    split.
    - intros P Q; split.
      + intros HPQ n; hnf in *; subst; auto.
      + apply dist_equiv.
    - intros n; split; auto.
      congruence.
    - intros ? P Q ?; hnf in *.
      apply predicates_hered.pred_ext; intros ? []; split; auto.
      + assert (approx (S (S n)) P a) as HP by (split; auto; lia).
        rewrite H in HP; apply HP.
      + assert (approx (S (S n)) Q a) as HP by (split; auto; lia).
        rewrite <- H in HP; apply HP.
  Qed.
  Canonical Structure mpredC : ofeT := OfeT mpred mpred_ofe_mixin.

  Program Definition mpred_compl : Compl mpredC := fun c w => c (level w) w.
  Next Obligation.
  Proof.
    repeat intro; simpl in *.
    eapply pred_hereditary in H0; eauto.
    assert (approx (S (level a')) (c (level a)) a') as Ha by (split; auto).
    rewrite chain_cauchy in Ha; [apply Ha | apply age_level in H; lia].
  Qed.
  Global Program Instance mpred_cofe : Cofe mpredC := {| compl := mpred_compl |}.
  Next Obligation.
    intros; hnf.
    apply predicates_hered.pred_ext; intros ? []; split; auto; simpl in *.
    - assert (approx (S (level a)) (c (level a)) a) as Ha by (split; auto).
      rewrite <- (chain_cauchy c (level a) n) in Ha; [apply Ha | lia].
    - assert (approx (S (level a)) (c n) a) as Ha by (split; auto).
      rewrite chain_cauchy in Ha; [apply Ha | lia].
  Qed.
End cofe.
Arguments mpredC : clear implicits.

Lemma approx_imp : forall n P Q, approx n (P --> Q) = approx n (approx n P --> approx n Q).
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? Ha' HP.
  - destruct HP; split; auto.
  - apply Himp; auto; split; auto.
    pose proof (necR_level _ _ Ha'); omega.
Qed.

Lemma wand_nonexpansive_l: forall P Q n,
  approx n (P -* Q) = approx n (approx n P  -* Q).
Proof.
  repeat intro.
  apply predicates_hered.pred_ext; intros ? [? Hshift]; split; auto; intros ??????.
  - destruct H2; eauto.
  - eapply Hshift; eauto; split; auto.
    apply necR_level in H0; apply join_level in H1 as []; omega.
Qed.

Lemma wand_nonexpansive_r: forall P Q n,
  approx n (P -* Q) = approx n (P  -* approx n Q).
Proof.
  repeat intro.
  apply predicates_hered.pred_ext; intros ? [? Hshift]; split; auto; intros ??????.
  - split; eauto.
    apply necR_level in H0; apply join_level in H1 as []; omega.
  - eapply Hshift; eauto.
Qed.

Lemma wand_nonexpansive: forall P Q n,
  approx n (P -* Q) = approx n (approx n P  -* approx n Q).
Proof.
  intros; rewrite wand_nonexpansive_l wand_nonexpansive_r; reflexivity.
Qed.

Ltac unseal_derives := match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.

(*Program Definition persistently (P : mpred) : mpred := fun w => P (ghost_core2 w).
Next Obligation.
Proof.
  repeat intro.
  eapply pred_hereditary; eauto.
  apply age_ghost_core; auto.
Qed.

Lemma approx_persistently: forall P n, approx n (persistently P) = persistently (approx n P).
Proof.
  intros; apply predicates_hered.pred_ext; intros ??; simpl in *; intros.
  - rewrite level_ghost_core; auto.
  - rewrite -> level_ghost_core in *.
    destruct H as ([] & ?); repeat (split; auto).
Qed.

Lemma persistently_derives: forall P Q, P |-- Q -> persistently P |-- persistently Q.
Proof.
  intros.
  change (predicates_hered.derives (persistently P) (persistently Q)).
  change (predicates_hered.derives P Q) in H.
  repeat intro.
  apply H, H0; auto.
Qed.

Lemma persistently_persists : forall P, persistently P |-- persistently (persistently P).
Proof.
  intros.
  change (predicates_hered.derives (persistently P) (persistently (persistently P))).
  repeat intro; simpl in *.
  rewrite -> ghost_core_idem in *.
  apply H; eapply join_sub_trans; eauto.
Qed.

Lemma ghost_core_identity : forall w, identity w -> identity (ghost_core2 w).
Proof.
  intros.
  apply resource_at_empty2.
  - intros; rewrite resource_at_ghost_core.
    apply resource_at_core_identity.
  - rewrite ghost_of_ghost_core.
    apply ghost_of_identity in H.
    rewrite (identity_core H) R.ghost_core; simpl.
    rewrite <- (R.ghost_core nil); apply core_identity.
Qed.*)

Program Definition persistently (P : mpred) : mpred := fun w => P (core w).
Next Obligation.
Proof.
  repeat intro.
  eapply pred_hereditary; eauto.
  apply age_core; auto.
Qed.

Lemma approx_persistently: forall P n, approx n (persistently P) = persistently (approx n P).
Proof.
  intros; apply predicates_hered.pred_ext; intros ??; simpl in *; intros.
  - rewrite level_core; auto.
  - rewrite -> level_core in H; auto.
Qed.

Lemma persistently_derives: forall P Q, P |-- Q -> persistently P |-- persistently Q.
Proof.
  intros.
  unseal_derives; intros ??; simpl in *.
  change (predicates_hered.derives P Q) in H.
  apply H; auto.
Qed.

Lemma persistently_persists : forall P, persistently P |-- persistently (persistently P).
Proof.
  intros.
  unseal_derives; intros ??; simpl in *.
  rewrite core_idem; auto.
Qed.

Lemma mpred_bi_mixin :
  BiMixin
    derives emp prop andp orp imp (@allp _ _) (@exp _ _) sepcon wand persistently.
Proof.
  split.
  - constructor; auto. intro. apply derives_trans.
  - split; intros.
    + hnf in H; subst; auto.
    + apply pred_ext; tauto.
  - intros ????; hnf.
    f_equal; f_equal.
    apply prop_ext; auto.
  - intros ???????; hnf in *.
    rewrite !approx_andp; congruence.
  - intros ???????; hnf in *.
    rewrite !approx_orp; congruence.
  - intros ???????; hnf in *.
    rewrite approx_imp (approx_imp _ y). congruence.
  - intros ?? P Q ?; hnf in *.
    apply predicates_hered.pred_ext.
    + intros ? [? HP]; split; auto.
      change ((predicates_hered.allp Q) a).
      intro z; specialize (HP z).
      assert (approx (S n) (P z) a) as HP' by (split; auto).
      rewrite H in HP'; apply HP'.
    + intros ? [? HP]; split; auto.
      change ((predicates_hered.allp P) a).
      intro z; specialize (HP z).
      assert (approx (S n) (Q z) a) as HP' by (split; auto).
      rewrite <- H in HP'; apply HP'.
  - intros ?? P Q ?; hnf in *.
    rewrite !approx_exp; f_equal; extensionality.
    apply H.
  - intros ???????; hnf in *.
    rewrite !approx_sepcon; congruence.
  - intros ? P Q ????; hnf in *.
    rewrite wand_nonexpansive (wand_nonexpansive Q); congruence.
  - intros ????; hnf in *.
    rewrite !approx_persistently H; auto.
  - apply prop_right.
  - intros.
    apply prop_left; intro.
    eapply derives_trans; eauto.
  - intros; rewrite prop_forall; auto.
  - intros; apply andp_left1, derives_refl.
  - intros; apply andp_left2, derives_refl.
  - intros; apply andp_right; auto.
  - intros; apply orp_right1, derives_refl.
  - intros; apply orp_right2, derives_refl.
  - apply orp_left.
  - apply imp_andp_adjoint.
  - apply imp_andp_adjoint.
  - intros; apply allp_right; auto.
  - intros; eapply allp_left, derives_refl.
  - intros; eapply exp_right, derives_refl.
  - intros; apply exp_left; auto.
  - intros; apply sepcon_derives; auto.
  - intros; rewrite emp_sepcon; auto.
  - intros; rewrite emp_sepcon; auto.
  - intros; rewrite sepcon_comm; auto.
  - intros; rewrite sepcon_assoc; auto.
  - intros; rewrite <- wand_sepcon_adjoint; auto.
  - intros; rewrite wand_sepcon_adjoint; auto.
  - intros; apply persistently_derives; auto.
  - intros; apply persistently_persists.
  - unfold persistently.
    unseal_derives; intros ??; simpl.
    apply core_identity.
  - intros.
    unseal_derives; intros ??; simpl in *.
    change (` (predicates_hered.allp Ψ) (core a)); intro.
    apply (H b).
  - intros.
    unseal_derives; intros ??; simpl in *.
    destruct H as [b ?].
    exists b; auto.
  - intros.
    unseal_derives; intros ? (? & ? & J & ? & ?); simpl in *.
    apply join_core in J as <-; auto.
  - intros.
    unseal_derives; intros ? []; simpl in *.
    exists (core a), a; repeat (split; auto).
    apply core_unit.
Qed.

Lemma approx_later : forall n P, approx (S n) (|> P) = seplog.later (approx n P).
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? [].
    change ((|> approx n P)%pred a); intros ??; split; auto.
    apply laterR_level in H1; lia.
  - intros ??.
    destruct (level a) eqn: Hl.
    + split; [rewrite Hl; lia|].
      intros ??.
      apply laterR_level in H0; lia.
    + destruct (levelS_age _ _ (eq_sym Hl)) as (a' & ? & ?); subst.
      destruct (H a').
      { constructor; auto. }
      split; [lia|].
      intros ? HL; apply (H _ HL).
Qed.

Lemma approx_0 : forall P, approx 0 P = FF.
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? []; lia.
  - intros ??; contradiction.
Qed.

Program Definition internal_eq {A : ofeT} (a1 a2 : A) : mpred :=
  fun w => a1 ≡{level w}≡ a2.
Next Obligation.
Proof.
  repeat intro.
  apply age_level in H; rewrite H in H0.
  apply dist_S; auto.
Qed.

Lemma mpred_sbi_mixin : SbiMixin
  derives prop orp imp (@allp _ _) (@exp _ _) sepcon persistently (@internal_eq) seplog.later.
Proof.
  split.
  - repeat intro; hnf.
    rewrite !approx_later.
    destruct n; simpl in *; hnf.
    + rewrite !approx_0; auto.
    + f_equal; auto.
  - repeat intro.
    apply predicates_hered.pred_ext; intros ? []; split; auto; simpl in *.
    + transitivity x; [apply (dist_le n); auto; lia|].
      transitivity x0; eauto.
      apply (dist_le n); auto; lia.
    + transitivity y; [apply (dist_le n); auto; lia|].
      transitivity y0; eauto.
      apply (dist_le n); auto; lia.
  - intros.
    change (predicates_hered.derives P (internal_eq a a)).
    repeat intro; hnf.
    reflexivity.
  - intros.
    match goal with |- ?P |-- (?A --> ?B)%logic =>
      change (predicates_hered.derives P (predicates_hered.imp A B)) end.
    repeat intro; simpl in *.
    assert ((approx (S (level a')) (Ψ b)) a') as []; auto.
    rewrite <- H; [split; eauto|].
    eapply dist_le; eauto.
    apply necR_level in H1; lia.
  - intros.
    unseal_derives; repeat intro.
    specialize (H x); auto.
  - intros.
    unseal_derives; repeat intro.
    apply H.
  - intros.
    unseal_derives; repeat intro; simpl in *.
    rewrite discrete_iff; apply H0.
  - intros.
    match goal with |- ?P |-- (|> ?Q)%logic => change (predicates_hered.derives P (box laterM Q)) end.
    repeat intro; simpl in *.
    hnf in H; simpl in H.
    apply laterR_level in H0.
    destruct (level a); [lia|].
    eapply dist_le; eauto; lia.
  - intros.
    match goal with |- (|> ?P)%logic |-- ?Q => change (predicates_hered.derives (box laterM P) Q) end.
    repeat intro; simpl in *.
    hnf.
    destruct (level a) eqn: Ha; [auto | simpl].
    symmetry in Ha; apply levelS_age in Ha as (a' & ? & ?); subst.
    apply H.
    constructor; auto.
  - intros; apply later_derives; auto.
  - apply now_later.
  - intros. rewrite seplog.later_allp; auto.
  - intros. eapply derives_trans; [eapply (seplog.later_exp'')|].
    apply orp_left; [apply orp_right2 | apply orp_right1]; auto.
    apply later_derives, FF_left.
  - intros; rewrite later_sepcon; auto.
  - intros; rewrite later_sepcon; auto.
  - intros.
    unseal_derives; intros ??; simpl in *.
    match goal with |- context[(|> ?Q)%logic] => change (|>Q)%logic with (box laterM Q) end.
    intros ? Hlater.
    apply unlaterR_core in Hlater as (? & Hlater & ?); subst.
    apply (H _ Hlater).
  - intros.
    unseal_derives; intros ??; simpl in *.
    match goal with |- context[(|> ?Q)%logic] => change (|>Q)%logic with (box laterM Q) end.
    intros ? Hlater.
    apply laterR_core in Hlater.
    apply (H _ Hlater).
  - intros.
    change (predicates_hered.derives (box laterM P)
      (box laterM (prop False) || predicates_hered.imp (box laterM (prop False)) P)).
   repeat intro; simpl in *.
    destruct (level a) eqn: Ha.
    + left; intros ??%laterR_level; lia.
    + right; intros.
      apply H.
      apply nec_refl_or_later in H0 as [|]; auto; subst.
      symmetry in Ha; apply levelS_age in Ha as (? & ? & ?); exfalso; eapply H1.
      constructor; eauto.
Qed.

Canonical Structure mpredI : bi :=
  {| bi_ofe_mixin := mpred_ofe_mixin; bi_bi_mixin := mpred_bi_mixin |}.
Canonical Structure mpredSI : sbi :=
  {| sbi_ofe_mixin := mpred_ofe_mixin;
     sbi_bi_mixin := mpred_bi_mixin; sbi_sbi_mixin := mpred_sbi_mixin |}.

Lemma mpred_bupd_mixin : BiBUpdMixin mpredI own.bupd.
Proof.
  split.
  - repeat intro; hnf in *.
    rewrite !approx_bupd; congruence.
  - exact: own.bupd_intro.
  - exact: own.bupd_mono.
  - exact: own.bupd_trans.
  - exact: own.bupd_frame_r.
Qed.
Global Instance mpred_bi_bupd : BiBUpd mpredI := {| bi_bupd_mixin := mpred_bupd_mixin |}.

Open Scope Z.
Open Scope logic.
