From iris.bi Require Import interface.
From iris.proofmode Require Export tactics.

(* Conflicting notations:

  !!   PMap.get (level 1) vs lookup (level 20), fixed for now by not exporting compcert.lib.Maps
  |==> VST bupd (level 62) vs Iris bupd (level 99), fixed for now by changing to match Iris precedence
    (this is a bit annoying because of the difference in precedence of derives)
*)

Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.SeparationLogic.

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

(*Program Definition persistently (P : mpred) : mpred :=
  fun w => exists w1, join_sub w1 w /\ join w1 w1 w1 /\ P w1.
Next Obligation.
Proof.
  repeat intro.
  destruct H0 as (w1 & [] & ? & ?).
  eapply age1_join2 in H as (? & ? & ? & ? & ?); eauto.
  eexists; split; [eexists; eauto|].
  split.
  - eapply age1_join_eq in H1; eauto.
  - eapply pred_hereditary; eauto.
Qed.

Lemma approx_persistently: forall P n, approx n (persistently P) = persistently (approx n P).
Proof.
  intros; apply pred_ext; intros ??; hnf in *.
  - destruct H as (? & w1 & J & ? & ?); exists w1; repeat split; auto.
    destruct J as [? J]; apply join_level in J as []; omega.
  - destruct H as (w1 & J & ? & ? & ?); split; [|exists w1; auto].
    destruct J as [? J]; apply join_level in J as []; omega.
Qed.

Lemma persistently_derives: forall P Q, P |-- Q -> persistently P |-- persistently Q.
Proof.
  repeat intro; hnf in *.
  destruct H0 as (w1 & ? & ? & ?); eauto.
Qed.*)

(* try box? *)
Program Definition persistently (P : mpred) : mpred := fun w => P (core w).
Next Obligation.
Proof.
  repeat intro.
  eapply pred_hereditary; eauto.
  apply age_core; auto.
Qed.

Lemma approx_persistently: forall P n, approx n (persistently P) = persistently (approx n P).
Proof.
  intros; apply predicates_hered.pred_ext; intros ??; hnf in *.
  - rewrite level_core; auto.
  - rewrite level_core in H; auto.
Qed.

Lemma persistently_derives: forall P Q, P |-- Q -> persistently P |-- persistently Q.
Proof.
  intros.
  change (predicates_hered.derives (persistently P) (persistently Q)).
  change (predicates_hered.derives P Q) in H.
  repeat intro.
  apply H; auto.
Qed.

Lemma persistently_persists: forall P, persistently P |-- persistently (persistently P).
Proof.
  intros.
  change (predicates_hered.derives (persistently P) (persistently (persistently P))).
  repeat intro; hnf in *.
  rewrite core_idem; auto.
Qed.

Lemma mpred_bi_mixin :
  BiMixin
    derives seplog.emp prop andp orp imp (@allp _ _) (@exp _ _) sepcon wand persistently.
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
    rewrite !approx_persistently; congruence.
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
  - apply persistently_derives.
  - apply persistently_persists.
  - change (predicates_hered.derives seplog.emp (persistently seplog.emp)).
    intros ??; unfold persistently; simpl.
    apply core_identity.
  - intros.
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro; hnf in *.
    apply H.
  - intros.
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro; hnf in *.
    destruct H as [x ?]; exists x; auto.
  - intros.
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro; hnf in *.
    destruct H as (? & ? & J%join_core & ? & ?).
    rewrite <- J; auto.
  - intros.
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro; hnf in *.
    destruct H.
    exists (core a), a; repeat split; auto.
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

(* to msl.age_sepalg *)
Lemma laterR_core {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall x y : A, laterR x y -> laterR (core x) (core y).
Proof.
 induction 1.
 constructor 1; apply age_core; auto.
 constructor 2 with (core y); auto.
Qed.

Lemma unlaterR_core {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall x y : A, laterR (core x) y -> exists y0, laterR x y0 /\ y = core y0.
Proof.
  intros; remember (core x) as cx; revert dependent x; induction H; intros; subst.
  - pose proof (age_level _ _ H) as Hlevel.
    rewrite level_core in Hlevel.
    symmetry in Hlevel.
    destruct (levelS_age _ _ Hlevel) as (y0 & Hage & ?).
    exists y0; split; [constructor; auto|].
    apply age_core in Hage.
    unfold age in *; congruence.
  - edestruct IHclos_trans1 as (y0 & ? & ?); eauto; subst.
    edestruct IHclos_trans2 as (? & ? & ?); eauto; subst.
    eexists; split; [|reflexivity].
    econstructor 2; eauto.
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
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro.
    specialize (H x); auto.
  - intros.
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro.
    apply H.
  - intros.
    match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
    repeat intro; simpl in *.
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
    match goal with |- (|> ?P |-- persistently (|> ?Q))%logic =>
      change (predicates_hered.derives (box laterM P) (persistently (box laterM Q))) end.
    repeat intro; simpl in *.
    apply unlaterR_core in H0 as (? & ? & ?); subst.
    apply H; auto.
  - intros.
    match goal with |- (persistently (|> ?P) |-- |> ?Q)%logic =>
      change (predicates_hered.derives (persistently (box laterM P)) (box laterM Q)) end.
    repeat intro; simpl in *.
    apply H.
    apply laterR_core; auto.
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

Lemma approx_bupd: forall P n, (approx n (own.bupd P) = (own.bupd (approx n P)))%logic.
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? [? HP].
    change ((own.bupd (approx n P)) a).
    intros ? J.
    destruct (HP _ J) as (? & ? & m' & ? & ? & ? & ?);
      eexists; split; eauto; eexists; split; eauto; repeat split; auto; omega.
  - intros ? HP.
    destruct (HP nil) as (? & ? & m' & ? & ? & ? & []).
    { eexists; constructor. }
    split; [omega|].
    change ((own.bupd P) a).
    intros ? J.
    destruct (HP _ J) as (? & ? & m'' & ? & ? & ? & []);
      eexists; split; eauto; eexists; split; eauto; repeat split; auto.
Qed.

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
