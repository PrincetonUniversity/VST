Require Import VST.msl.log_normalize.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Import RML. Import R.
Local Open Scope pred.

(* Ghost state construction drawn from "Iris from the ground up", Jung et al. *)
Program Definition ghost_is {RA: Ghost} (g: G) (pp: preds): pred rmap :=
  fun m => ghost_of m = GHOST RA g (preds_fmap (approx (level m)) (approx (level m)) pp).
Next Obligation.
  repeat intro.
  erewrite (age1_ghost_of _ _ H) by (symmetry; apply ghost_of_approx).
  rewrite H0; simpl.
  pose proof (age_level _ _ H).
  rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by omega; auto.
Qed.

Definition Own {RA: Ghost} (g: G) pp: pred rmap := allp noat && ghost_is g pp.

Lemma Own_op: forall {RA: Ghost} (a b c: G) pp, join a b c ->
  Own c pp = Own a pp * Own b pp.
Proof.
  intros; apply pred_ext.
  - intros w [Hno Hg]; simpl in *.
    destruct (make_rmap (resource_at w) (GHOST _ a (preds_fmap (approx (level w)) (approx (level w)) pp)) (rmap_valid w) (level w))
      as (wa & Hla & Hra & Hga).
    { extensionality; apply resource_at_approx. }
    { apply ghost_same_level.
      eexists.
      rewrite Hg; constructor; eauto. }
    destruct (make_rmap (resource_at w) (GHOST _ b (preds_fmap (approx (level w)) (approx (level w)) pp)) (rmap_valid w) (level w))
      as (wb & Hlb & Hrb & Hgb).
    { extensionality; apply resource_at_approx. }
    { apply ghost_same_level.
      eexists.
      apply join_comm; rewrite Hg; constructor; eauto. }
    exists wa, wb; rewrite Hla, Hlb, Hra, Hrb; split; auto.
    apply resource_at_join2; auto.
    + intro; rewrite Hra, Hrb.
      apply identity_unit'; auto.
    + rewrite Hg, Hga, Hgb; constructor; auto.
  - intros w (w1 & w2 & J & [Hnoa Hga] & [Hnob Hgb]); simpl in *.
    split.
    + intro l; apply (resource_at_join _ _ _ l) in J.
      rewrite <- (Hnoa _ _ _ J); auto.
    + destruct (join_level _ _ _ J) as [<- _].
      apply ghost_of_join in J.
      rewrite Hga, Hgb in J; inv J.
      repeat inj_pair_tac.
      pose proof (join_eq H H1); subst; auto.
Qed.

Program Definition bupd (P: pred rmap): pred rmap :=
  fun m => forall c, joins (ghost_of m) c -> exists b, joins b c /\ exists m',
    level m' = level m /\ resource_at m' = resource_at m /\ ghost_of m' = b /\ P m'.
Next Obligation.
Proof.
  repeat intro.
  erewrite (age1_ghost_of _ _ H) in H1 by (symmetry; apply ghost_of_approx).
  destruct (ghost_of a) eqn: Hga; simpl in *.
  destruct H1 as [d H1]; inv H1.
  inj_pair_tac.
  destruct (H0 (GHOST _ b pds)) as (b' & J' & Hrb).
  { eexists; constructor; eauto. }
  destruct b', J' as [? J']; inv J'.
  repeat inj_pair_tac.
  exists (GHOST _ g0 (preds_fmap (approx (level a')) (approx (level a')) pds)); split.
  - eexists; constructor; eauto.
  - destruct Hrb as (m' & Hl' & Hr' & Hg' & HP).
    pose proof (age_level _ _ H).
    destruct (levelS_age m' (level a')) as (m'' & Hage' & Hl'').
    { congruence. }
    exists m''; repeat split; auto.
    + extensionality l.
      erewrite (age1_resource_at _ _ H l) by (symmetry; apply resource_at_approx).
      erewrite (age1_resource_at _ _ Hage' l) by (symmetry; apply resource_at_approx).
      congruence.
    + erewrite (age1_ghost_of _ _ Hage') by (symmetry; apply ghost_of_approx).
      rewrite Hg', Hl''; auto.
    + eapply (proj2_sig P); eauto.
Qed.

Definition fp_update {A} {J: Join A} (a b : A) := forall c, joins a c -> joins b c.

Lemma Own_update: forall {RA: Ghost} a b pp, fp_update a b ->
  Own a pp |-- bupd (Own b pp).
Proof.
  repeat intro.
  destruct H0 as [Hno Hg]; simpl in *.
  rewrite Hg in H1.
  destruct H1 as [? J]; inv J.
  inj_pair_tac.
  destruct (H b0).
  { eexists; eauto. }
  exists (GHOST _ b (preds_fmap (approx (level a0)) (approx (level a0)) pp)); split.
  { eexists; constructor; eauto. }
  destruct (make_rmap (resource_at a0)
    (GHOST _ b (preds_fmap (approx (level a0)) (approx (level a0)) pp)) (rmap_valid a0) (level a0))
    as (m' & Hl & Hr & ?).
  { extensionality; apply resource_at_approx. }
  { simpl.
    rewrite preds_fmap_fmap, approx_oo_approx; auto. }
  exists m'; repeat split; auto.
  - intro; rewrite Hr; auto.
  - rewrite Hl; auto.
Qed.

Definition gname := nat.

(* A map of RAs is an RA, but a map of Ghosts is not a Ghost: in particular, it's not a Disj_alg,
   since a map containing only cores is not a universal unit.
Instance Global_Ghost {I} {RAs: I -> Ghost}: Ghost :=
  { G := forall i, nat -> option (@G (RAs i)) }.*)



Definition own {I} {RAs: I -> Ghost} {RA: Ghost} {inG: {i | RAs i = RA}}
  (n: gname) (a: G) pp :=
  @Own () (fun j => if eq_dec j (proj1_sig inG) then fun m => if eq_dec m n then Some a else None
                 else fun _ => None) pp.

