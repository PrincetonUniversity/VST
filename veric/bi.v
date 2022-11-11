From iris.bi Require Import interface.
From iris.proofmode Require Export tactics.

(* undo some "simpl never" settings from std++ *)
#[global] Arguments Pos.of_nat : simpl nomatch.
#[global] Arguments Pos.to_nat !x / .
#[global] Arguments N.add : simpl nomatch.
#[global] Arguments Z.of_nat : simpl nomatch.
#[global] Arguments Z.to_nat : simpl nomatch.

(* Conflicting notations:

  !!   PMap.get (level 1) vs lookup (level 20), fixed for now by not exporting compcert.lib.Maps
  |==> VST bupd (level 62) vs Iris bupd (level 99), fixed for now by changing to match Iris precedence
    (this is a bit annoying because of the difference in precedence of derives)
*)

From VST.veric Require Import compcert_rmaps SeparationLogic.

Notation "'emp'" := seplog.emp.

Section cofe.
  #[local] Instance mpred_equiv : Equiv mpred := eq.
  #[local] Instance mpred_dist : Dist mpred := fun n P Q => approx (S n) P = approx (S n) Q.

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
  Canonical Structure mpredC : ofe := Ofe mpred mpred_ofe_mixin.

  Program Definition mpred_compl : Compl mpredC := fun c w => c (level w) w.
  Next Obligation.
  Proof.
    split; repeat intro; simpl in *.
    eapply pred_hereditary in H0; eauto.
    assert (approx (S (level a')) (c (level a)) a') as Ha by (split; auto).
    rewrite chain_cauchy in Ha; [apply Ha | apply age_level in H; lia].

    eapply pred_upclosed in H0; eauto.
    apply ext_level in H as <-; auto.
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

Lemma approx_imp : forall n P Q, approx n (P --> Q)%pred = approx n (approx n P --> approx n Q)%pred.
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? ? Ha' Hext HP.
  - destruct HP; split; eauto.
  - eapply Himp; eauto; split; auto.
    pose proof (necR_level _ _ Ha'); apply ext_level in Hext; lia.
Qed.

Lemma core_ext_ord : forall (a b : rmap), join_sub a b -> ext_order (core a) (core b).
Proof.
  intros.
  destruct H as [? J%join_core_sub].
  destruct J; rewrite rmap_order.
  split; [apply join_level in H as []; auto|].
  split.
  - extensionality l; apply (resource_at_join _ _ _ l) in H.
    eapply join_sub_same_identity; try apply resource_at_core_identity;
      try (rewrite <- core_resource_at; apply core_duplicable).
    rewrite !core_resource_at; eexists; eauto.
  - eexists; apply ghost_of_join; eauto.
Qed.

Lemma ext_ord_core : forall (a b : rmap), ext_order a b -> ext_order (core a) (core b).
Proof.
  intros.
  apply core_ext_ord, assert_lemmas.ext_join_sub; auto.
Qed.

Program Definition persistently (P : mpred) : mpred := fun w => P (core w).
Next Obligation.
Proof.
  split; repeat intro.
  eapply pred_hereditary; eauto.
  apply age_core; auto.

  eapply pred_upclosed, H0.
  apply ext_ord_core; auto.
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
  unseal_derives; unfold persistently; intros ??.
  apply H; auto.
Qed.

Lemma persistently_persists : forall P, persistently P |-- persistently (persistently P).
Proof.
  intros.
  unseal_derives; unfold persistently; intros ??; simpl.
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
    setoid_rewrite res_predicates.emp_no; intros l.
    apply resource_at_core_identity.
  - unfold persistently; intros.
    unseal_derives; intros ??; auto.
  - intros.
    unseal_derives; intros ??; simpl in *.
    destruct H as [b ?].
    exists b; auto.
  - intros.
    unseal_derives; intros ? (? & ? & J & ? & ?); simpl in *.
    eapply pred_upclosed, H.
    apply core_ext_ord; eexists; eauto.
  - intros.
    unseal_derives; intros ? []; simpl in *.
    exists (core a), a; repeat (split; auto).
    apply core_unit.
Qed.

Lemma approx_later : forall n P, approx (S n) (|> P)%pred = seplog.later (approx n P).
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

Lemma mpred_bi_later_mixin : BiLaterMixin
  derives prop orp imp (@allp _ _) (@exp _ _) sepcon persistently seplog.later.
Proof.
  split.
  - repeat intro. hnf. rewrite !approx_later. destruct n.
    + rewrite !approx_0; auto.
    + apply dist_S in H; f_equal; auto.
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
    unseal_derives.
    change (predicates_hered.derives (box laterM P)
      (box laterM (prop False) || predicates_hered.imp (box laterM (prop False)) P)%pred).
    repeat intro; simpl in *.
    destruct (level a) eqn: Ha.
    + left; intros ??%laterR_level; lia.
    + right; intros.
      eapply pred_upclosed; eauto.
      apply H.
      apply nec_refl_or_later in H0 as [|]; auto; subst.
      symmetry in Ha; apply levelS_age in Ha as (? & ? & ?); exfalso.
      eapply ext_age_compat in H1 as (? & ? & ?); eauto.
      eapply H2.
      constructor; eauto.
Qed.

Canonical Structure mpredI : bi :=
  {| bi_ofe_mixin := mpred_ofe_mixin; bi_bi_mixin := mpred_bi_mixin;
     bi_bi_later_mixin := mpred_bi_later_mixin |}.

(* an Iris extension that is satisfied by most but not all BI instances *)
Global Instance mpred_later_contractive : BiLaterContractive mpredI.
Proof.
  intros ????.
  unfold dist_later in H; change (approx (S n) (|> x) = approx (S n) (|> y))%logic.
  rewrite !approx_later.
  destruct n.
  - rewrite !approx_0; auto.
  - rewrite H; auto.
Qed.

(* updates *)
Lemma mpred_bupd_mixin : BiBUpdMixin mpredI ghost_seplog.bupd.
Proof.
  split.
  - repeat intro; hnf in *.
    rewrite !approx_bupd; congruence.
  - exact: bupd_intro.
  - exact: bupd_mono.
  - exact: bupd_trans.
  - exact: bupd_frame_r.
Qed.
Global Instance mpred_bi_bupd : BiBUpd mpredI := {| bi_bupd_mixin := mpred_bupd_mixin |}.

Definition coPset_to_Ensemble (E : coPset.coPset) : Ensembles.Ensemble nat := fun x => elem_of (Pos.of_nat (S x)) E.

Lemma coPset_to_Ensemble_union : forall E1 E2,
  coPset_to_Ensemble (E1 ∪ E2) = Ensembles.Union (coPset_to_Ensemble E1) (coPset_to_Ensemble E2).
Proof.
  intros.
  unfold coPset_to_Ensemble.
  extensionality; apply prop_ext; split; intro X.
  - apply elem_of_union in X as [|]; [left | right]; auto.
  - inv X; [apply elem_of_union_l | apply elem_of_union_r]; auto.
Qed.

Lemma coPset_to_Ensemble_disjoint : forall E1 E2,
  Ensembles.Disjoint (coPset_to_Ensemble E1) (coPset_to_Ensemble E2) <-> E1 ## E2.
Proof.
  split; intros.
  - inv H.
    intros x ??; contradiction (H0 (Nat.pred (Pos.to_nat x))); constructor; unfold Ensembles.In, coPset_to_Ensemble;
      rewrite -> Nat.succ_pred_pos, Pos2Nat.id by lia; auto.
  - constructor; intros ? X; inv X.
    unfold Ensembles.In, coPset_to_Ensemble in *.
    contradiction (H _ H0).
Qed.

Lemma mpred_fupd_mixin : BiFUpdMixin mpredI (fun E1 E2 => ghost_seplog.fupd (coPset_to_Ensemble E1) (coPset_to_Ensemble E2)).
Proof.
  split.
  - repeat intro; hnf in *.
    rewrite fupd_nonexpansive; setoid_rewrite fupd_nonexpansive at 2.
    rewrite H; auto.
  - intros; unfold updates.fupd.
    apply subseteq_disjoint_union_L in H as (E1' & ? & ?); subst.
    rewrite coPset_to_Ensemble_union invariants.Union_comm.
    apply fupd_mask_union, coPset_to_Ensemble_disjoint.
    symmetry; auto.
  - intros; apply except_0_fupd.
  - intros; apply fupd_mono; auto.
  - intros; apply fupd_trans.
  - intros; unfold updates.fupd.
    iIntros "H".
    rewrite !coPset_to_Ensemble_union.
    rewrite <- coPset_to_Ensemble_disjoint in H |- *.
    iApply fupd_mask_frame_r'; auto.
  - intros; apply fupd_frame_r.
Qed.
Global Instance mpred_bi_fupd : BiFUpd mpredI := {| bi_fupd_mixin := mpred_fupd_mixin |}.

Global Instance mpred_bi_bupd_fupd : BiBUpdFUpd mpredI.
Proof.
  hnf.
  intros; apply bupd_fupd.
Qed.

(*(* Lifted instance *)
Section lifted_cofe.
  #[local] Instance env_mpred_equiv : Equiv (environ -> mpred) := eq.
  #[local] Instance env_mpred_dist : Dist (environ -> mpred) := fun n P Q => forall rho, approx (S n) (P rho) = approx (S n) (Q rho).

  Lemma lift_dist_equiv : forall (P Q : environ -> pred rmap), (∀ n : nat, P ≡{n}≡ Q) -> P = Q.
  Proof.
    intros; extensionality rho.
    apply dist_equiv; intros.
    apply H.
  Qed.

  Definition env_mpred_ofe_mixin : OfeMixin (environ -> mpred).
  Proof.
    split.
    - intros P Q; split.
      + intros HPQ n; hnf in *; subst; auto.
      + apply lift_dist_equiv.
    - intros n; constructor; repeat intro; auto.
      congruence.
    - intros ? P Q ? rho.
      apply (mixin_dist_S _ mpred_ofe_mixin), H.
  Qed.
  Canonical Structure env_mpredC : ofeT := OfeT (environ -> mpred) env_mpred_ofe_mixin.

  Program Definition env_mpred_compl : Compl env_mpredC := fun c rho w => c (level w) rho w.
  Next Obligation.
  Proof.
    repeat intro.
    eapply pred_hereditary in H0; eauto.
    assert (approx (S (level a')) (c (level a) rho) a') as Ha by (split; auto).
    rewrite chain_cauchy in Ha; [apply Ha | apply age_level in H; lia].
  Qed.
  Global Program Instance env_mpred_cofe : Cofe env_mpredC := {| compl := env_mpred_compl |}.
  Next Obligation.
    intros; hnf; intro rho.
    apply predicates_hered.pred_ext; intros ? []; split; auto; simpl in *.
    - assert (approx (S (level a)) (c (level a) rho) a) as Ha by (split; auto).
      rewrite <- (chain_cauchy c (level a) n) in Ha; [apply Ha | lia].
    - assert (approx (S (level a)) (c n rho) a) as Ha by (split; auto).
      rewrite chain_cauchy in Ha; [apply Ha | lia].
  Qed.
End lifted_cofe.
Arguments env_mpredC : clear implicits.

Lemma env_mpred_bi_mixin :
  BiMixin(PROP := environ -> mpred)
    derives emp prop andp orp imp (@allp _ _) (@exp _ _) sepcon wand (lift persistently).
Proof.
  split.
  - constructor; auto. intro. apply derives_trans.
  - split; intros.
    + hnf in H; subst; auto.
    + apply pred_ext; tauto.
  - intros ????; hnf; intro rho.
    f_equal; f_equal.
    apply prop_ext; auto.
  - intros ????????; hnf in *.
    rewrite !approx_andp; congruence.
  - intros ????????; hnf in *.
    rewrite !approx_orp; congruence.
  - intros ????????; hnf in *; simpl.
    rewrite approx_imp (approx_imp _ (y rho)). congruence.
  - intros ?? P Q ??; hnf in *; simpl.
    apply (bi_mixin_forall_ne _ _ _ _ _ _ _ _ _ _ _ mpred_bi_mixin); hnf; intros.
    apply H.
  - intros ?? P Q ??; hnf in *.
    rewrite !approx_exp; f_equal; extensionality.
    apply H.
  - intros ????????; hnf in *.
    rewrite !approx_sepcon; congruence.
  - intros ? P Q ?????; hnf in *; simpl.
    rewrite wand_nonexpansive (wand_nonexpansive (Q rho)); congruence.
  - intros ?????; hnf in *.
    unfold lift.
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
  - intros; unfold lift; simpl.
    intro; apply persistently_derives; auto.
  - intros; unfold lift; simpl.
    intro; apply persistently_persists.
  - unfold persistently, lift; intro rho.
    unseal_derives; intros ??; simpl.
    apply core_identity.
  - intros; intro rho.
    unfold lift; simpl; apply (bi_mixin_persistently_forall_2 _ _ _ _ _ _ _ _ _ _ _ mpred_bi_mixin).
  - intros; intro rho.
    unfold lift; simpl; apply (bi_mixin_persistently_exist_1 _ _ _ _ _ _ _ _ _ _ _ mpred_bi_mixin).
  - intros; intro rho.
    unfold lift; simpl; apply (bi_mixin_persistently_absorbing _ _ _ _ _ _ _ _ _ _ _ mpred_bi_mixin).
  - intros; intro rho.
    unfold lift; simpl; apply (bi_mixin_persistently_and_sep_elim _ _ _ _ _ _ _ _ _ _ _ mpred_bi_mixin).
Qed.

Lemma env_mpred_sbi_mixin : SbiMixin(PROP := environ -> mpred)
  derives prop orp imp (@allp _ _) (@exp _ _) sepcon (lift persistently) (fun a b c _ => @internal_eq a b c) seplog.later.
Proof.
  split.
  - repeat intro; hnf.
    simpl; apply (sbi_mixin_later_contractive _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
    destruct n; simpl in *; hnf; auto.
  - repeat intro; apply (sbi_mixin_internal_eq_ne _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin); auto.
  - intros; intro rho.
    apply (sbi_mixin_internal_eq_refl _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
  - intros; intro rho; simpl.
    match goal with |- ?P |-- (?A --> ?B)%logic =>
      change (predicates_hered.derives P (predicates_hered.imp A B)) end.
    repeat intro; simpl in *.
    assert ((approx (S (level a')) (Ψ b rho)) a') as []; auto.
    rewrite <- H; [split; eauto|].
    eapply dist_le; eauto.
    apply necR_level in H1; lia.
  - intros; intro rho.
    unseal_derives; repeat intro.
    specialize (H x); auto.
  - intros; intro rho.
    unseal_derives; repeat intro.
    apply H.
  - intros; intro rho.
    unseal_derives; repeat intro; simpl in *.
    rewrite discrete_iff; apply H0.
  - intros; intro rho.
    apply (sbi_mixin_later_eq_1 _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
  - intros; intro rho.
    apply (sbi_mixin_later_eq_2 _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
  - intros; apply later_derives; auto.
  - apply now_later.
  - intros. rewrite seplog.later_allp; auto.
  - intros. eapply derives_trans; [eapply (seplog.later_exp'')|].
    apply orp_left; [apply orp_right2 | apply orp_right1]; auto.
    apply later_derives, FF_left.
  - intros; rewrite later_sepcon; auto.
  - intros; rewrite later_sepcon; auto.
  - intros; intro rho; unfold lift; simpl.
    apply (sbi_mixin_later_persistently_1 _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
  - intros; intro rho; unfold lift; simpl.
    apply (sbi_mixin_later_persistently_2 _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
  - intros; intro rho; unfold lift; simpl.
    apply (sbi_mixin_later_false_em _ _ _ _ _ _ _ _ _ _ mpred_sbi_mixin).
Qed.

Canonical Structure env_mpredI : bi :=
  {| bi_ofe_mixin := env_mpred_ofe_mixin; bi_bi_mixin := env_mpred_bi_mixin |}.
Canonical Structure env_mpredSI : sbi :=
  {| sbi_ofe_mixin := env_mpred_ofe_mixin;
     sbi_bi_mixin := env_mpred_bi_mixin; sbi_sbi_mixin := env_mpred_sbi_mixin |}.*)

(* Return from IPM to VST entailment. *)
Ltac iVST := iStopProof; repeat change (bi_car mpredI) with mpred; match goal with |-bi_entails ?P ?Q => change (P |-- Q) end;
  repeat match goal with |-context[bi_sep ?P ?Q] => change (bi_sep P Q) with (P * Q)%logic end.

Global Close Scope logic_upd. (* hide non-Iris update notation *)
Global Open Scope Z.
Global Open Scope logic.
Global Open Scope bi_scope.
