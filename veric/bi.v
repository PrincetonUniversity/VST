From iris.bi Require Import interface.

(* Conflicting notation:
  !!   PMap.get (level 1) vs lookup (level 20)
  Fixed for now by changing compcert.lib.Maps.
*)

Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.own.
Require Import VST.veric.seplog.

Instance mpred_equiv : Equiv (pred rmap) := eq.
Instance mpred_dist : Dist (pred rmap) := fun n P Q => approx n P = approx n Q.

Definition persistently (P : pred rmap) := andp P cored.

Lemma approx_imp : forall n P Q, compcert_rmaps.RML.R.approx n (predicates_hered.imp P Q) =
  compcert_rmaps.RML.R.approx n (predicates_hered.imp (compcert_rmaps.RML.R.approx n P)
    (compcert_rmaps.RML.R.approx n Q)).
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? Ha' HP.
  - destruct HP; split; auto.
  - apply Himp; auto; split; auto.
    pose proof (ageable.necR_level _ _ Ha'); omega.
Qed.

Lemma wand_nonexpansive_l: forall P Q n,
  approx n (P -* Q) = approx n (approx n P  -* Q).
Proof.
  repeat intro.
  apply pred_ext; intros ? [? Hshift]; split; auto; intros ??????.
  - destruct H2; eauto.
  - eapply Hshift; eauto; split; auto.
    apply necR_level in H0; apply join_level in H1 as []; omega.
Qed.

Lemma wand_nonexpansive_r: forall P Q n,
  approx n (P -* Q) = approx n (P  -* approx n Q).
Proof.
  repeat intro.
  apply pred_ext; intros ? [? Hshift]; split; auto; intros ??????.
  - split; eauto.
    apply necR_level in H0; apply join_level in H1 as []; omega.
  - eapply Hshift; eauto.
Qed.

Lemma wand_nonexpansive: forall P Q n,
  approx n (P -* Q) = approx n (approx n P  -* approx n Q).
Proof.
  intros; rewrite wand_nonexpansive_l wand_nonexpansive_r; reflexivity.
Qed.

Lemma VC_bi_mixin :
  BiMixin
    (@derives rmap _) predicates_sl.emp prop andp orp
    imp (@allp rmap _) (@exp rmap _) sepcon wand persistently.
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
    apply pred_ext.
    + intros ? [? HP]; split; auto.
      intro z; specialize (HP z).
      assert (approx n (P z) a) as HP' by (split; auto).
      rewrite H in HP'; apply HP'.
    + intros ? [? HP]; split; auto.
      intro z; specialize (HP z).
      assert (approx n (Q z) a) as HP' by (split; auto).
      rewrite <- H in HP'; apply HP'.
  - intros ?? P Q ?; hnf in *.
    rewrite !approx_exp; f_equal; extensionality.
    apply H.
  - intros ???????; hnf in *.
    rewrite !approx_sepcon; congruence.
  - intros ? P Q ????; hnf in *.
    rewrite wand_nonexpansive (wand_nonexpansive Q); congruence.
  - intros ????; hnf in *.
    unfold persistently; rewrite !approx_andp; congruence.
  - repeat intro; auto.
  - repeat intro; apply H; hnf; auto.
  - repeat intro; apply H.
  - intros; apply andp_left1, derives_refl.
  - intros; apply andp_left2, derives_refl.
  - intros; apply andp_right; auto.
  - intros; apply orp_right1, derives_refl.
  - intros; apply orp_right2, derives_refl.
  - apply orp_left.
  - apply imp_andp_adjoint.
  - apply imp_andp_adjoint.
  - intros; apply allp_right; auto.
  - intros; eapply allp_left; eauto.
  - intros; eapply exp_right; eauto.
  - intros; apply exp_left; auto.
  - apply sepcon_derives.
  - intros; rewrite emp_sepcon; auto.
  - intros; rewrite emp_sepcon; auto.
  - intros; rewrite sepcon_comm; auto.
  - intros; rewrite sepcon_assoc; auto.
  - intros; rewrite <- wand_sepcon_adjoint; auto.
  - intros; rewrite wand_sepcon_adjoint; auto.
  - intros; apply andp_derives; auto.
  - intros; unfold persistently.
    rewrite andp_assoc andp_dup; auto.
  - apply andp_right; auto.
    apply emp_cored.
  - admit.
  - intros ??? [x ?]; exists x; split; auto.
    apply allp_left.
SearchAbout prop.
    SearchAbout approx wand.
Locate approx_sepcon.
apply wand_nonexpansive.
    rewrite !approx_sepcon; congruence.
    apply H.
    apply pred_ext.
    + intros ? [? HP]; split; auto.
      intro z; specialize (HP z).
      assert (approx n (P z) a) as HP' by (split; auto).
      rewrite H in HP'; apply HP'.
    + intros ? [? HP]; split; auto.
      intro z; specialize (HP z).
      assert (approx n (Q z) a) as HP' by (split; auto).
      rewrite <- H in HP'; apply HP'.
