Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.msl.age_to.
Require Import VST.veric.aging_lemmas.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_new.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.coqlib4.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.sync_preds_defs.

Set Bullet Behavior "Strict Subproofs".

Lemma resource_decay_LK {b phi phi'} :
  resource_decay b phi phi' ->
  forall  loc rsh sh n i pp,
  phi @ loc = YES rsh sh (LK n i) pp ->
  phi' @ loc = YES rsh sh (LK n i) (preds_fmap (approx (level phi')) (approx (level phi')) pp).
Proof.
  intros [L R]; intros. rename H into E.
  specialize (R loc).
  rewrite E in *.
  destruct R as [N [R|[R|[R|R]]]].
  - rewrite <- R.
    reflexivity.
  - destruct R as [sh' [Psh [v [v' [R H]]]]]. simpl in R. congruence.
  - destruct R as [v [v' R]]. specialize (N ltac:(auto)). congruence.
  - destruct R as [v [pp' [R H]]]. congruence.
Qed.

Lemma resource_decay_LK_inv {b phi phi'} :
  resource_decay b phi phi' ->
  forall { loc rsh sh n i pp'}, 
  phi' @ loc = YES rsh sh (LK n i) pp' ->
  exists pp,
    pp' = preds_fmap (approx (level phi')) (approx (level phi')) pp /\
    phi @ loc = YES rsh sh (LK n i) pp.
Proof.
  intros [L R]; intros; rename H into E.
  specialize (R loc).
  rewrite E in *.
  destruct R as [N [R|[R|[R|R]]]].
  - destruct (phi @ loc); simpl in R; try discriminate.
    eexists.
    injection R. intros; subst.
    split; try reflexivity.
    f_equal; apply proof_irr. 
  - destruct R as [sh' [Psh [v [v' [R H]]]]]; congruence.
  - destruct R as [v [v' R]]; congruence.
  - destruct R as [v [pp [R H]]]; congruence.
Qed.

Lemma resource_decay_identity {b phi phi' loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  identity (phi @ loc) ->
  identity (phi' @ loc).
Proof.
  intros [lev RD] LT ID; specialize (RD loc).
  destruct RD as [N [RD|[RD|[RD|RD]]]].
  destruct (phi @ loc) as [t | t p k p0 | k p]; simpl in RD; try rewrite <- RD.
  - auto.
  - apply YES_not_identity in ID. tauto.
  - apply PURE_identity.
  - destruct RD as (sh & Psh & v1 & v2 & A & B).
    destruct (phi @ loc); simpl in A; simpl in B; try discriminate.
    apply YES_not_identity in ID. tauto.
  - destruct RD. auto with *.
  - destruct RD as (? & ? & ? & ->).
    apply NO_identity.
Qed.

Lemma resource_decay_LK_at {b phi phi' R sh loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (LK_at R sh loc) phi ->
  (LK_at (approx (level phi) R) sh loc) phi'.
Proof.
  intros RD LT LKAT loc'.
  specialize (LKAT loc').
  destruct (adr_range_dec loc LKSIZE loc') as [range|notrange]; swap 1 2.
  - rewrite jam_false in *; auto.
  - rewrite jam_true in *; auto.
      destruct LKAT as [p E]; simpl in E.
      apply (resource_decay_LK RD) in E.
      eexists.
      hnf.
      rewrite E.
      reflexivity.
Qed.

Lemma resource_decay_lkat' {b phi phi' R loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (lkat R loc) phi ->
  (lkat (approx (level phi) R) loc) phi'.
Proof.
  intros RD LT LKAT loc' r.
  specialize (LKAT loc' r).
  destruct LKAT as (sh & rsh & E); exists sh, rsh.
  apply (resource_decay_LK RD) in E. rewrite E; reflexivity.
Qed.

Lemma resource_decay_lkat'' {b phi phi' R loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (lkat R loc) phi ->
  (lkat R loc) phi'.
Proof.
  intros RD LT LKAT loc' r.
  eapply resource_decay_lkat' in LKAT; eauto.
  specialize (LKAT loc' r).
  destruct LKAT as (sh & rsh & E); exists sh, rsh.
  rewrite E.
  replace (pack_res_inv _) with (pack_res_inv (approx (level phi') R)); auto.
  unfold pack_res_inv; f_equal.
  extensionality.
  change (approx _ (approx _ _)) with ((approx (level phi') oo approx (level phi)) R).
  rewrite approx_oo_approx'; auto.
  apply RD.
Qed.

Lemma resource_decay_lkat {b phi phi' R loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (lkat R loc) phi ->
  (lkat (approx (level phi') R) loc) phi'.
Proof.
  intros RD LT LKAT loc' r.
  specialize (LKAT loc' r).
  destruct LKAT as (sh & rsh & E); exists sh, rsh.
 apply (resource_decay_LK RD) in E. rewrite E. f_equal.
    unfold preds_fmap in *.
    unfold pack_res_inv in *.
    f_equal.
    unfold fmap.
    simpl.
    extensionality Ts.
    destruct RD as (Hlev, _).
    pose proof approx_oo_approx' (level phi') (level phi) as RR'.
    pose proof approx_oo_approx (level phi') as RR.
    autospec RR'.
    unfold "oo" in *.
    rewrite (equal_f RR' R).
    rewrite (equal_f RR R).
    reflexivity.
Qed.

Lemma resource_decay_LK_at' {b phi phi' R sh loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (LK_at R sh loc) phi ->
  (LK_at (approx (level phi') R) sh loc) phi'.
Proof.
  intros RD LT LKAT loc'.
  specialize (LKAT loc').
  destruct (adr_range_dec loc LKSIZE loc') as [range|notrange]; swap 1 2.
  - rewrite jam_false in *; auto.
  - rewrite jam_true in *; auto.
      destruct LKAT as [p E]; simpl in E.
      apply (resource_decay_LK RD) in E.
      eexists.
      hnf.
      rewrite E.
      f_equal.
      simpl.
      f_equal.
      extensionality.
      change (approx (level phi') (approx (level phi) R)) with
       ((approx (level phi') oo approx (level phi)) R).
      rewrite approx_oo_approx' by apply RD.
      unfold "oo".
      change (approx (level phi')   (approx (level phi')  R))
      with  ((approx (level phi') oo approx (level phi')) R).
      rewrite approx_oo_approx.
      reflexivity.
Qed.

Lemma resource_decay_PURE {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc sh P,
    phi @ loc = PURE sh P ->
    phi' @ loc = PURE sh (preds_fmap (approx (level phi')) (approx (level phi')) P).
Proof.
  intros [L RD] loc sh P PAT.
  specialize (RD loc).
  destruct RD as [N [RD|[RD|[RD|RD]]]].
  - rewrite PAT in RD; simpl in RD. rewrite RD; auto.
  - rewrite PAT in RD; simpl in RD. destruct RD as (?&?&?&?&?&?). congruence.
  - rewrite PAT in N. pose proof (N (proj1 RD)). congruence.
  - rewrite PAT in RD; simpl in RD. destruct RD as (?&?&?&?). congruence.
Qed.

Lemma resource_decay_PURE_inv {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc sh P',
    phi' @ loc = PURE sh P' ->
    exists P,
      phi @ loc = PURE sh P /\
      P' = preds_fmap (approx (level phi')) (approx (level phi')) P.
Proof.
  intros [L RD] loc sh P PAT.
  specialize (RD loc).
  destruct RD as [N [RD|[RD|[RD|RD]]]].
  all: rewrite PAT in *; destruct (phi @ loc); simpl in *.
  all: inversion RD; subst; eauto.
  all: repeat match goal with H : ex _ |- _ => destruct H end.
  all: repeat match goal with H : and _ _ |- _ => destruct H end.
  all: discriminate.
Qed.

Lemma resource_decay_func_at' {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc fs,
    seplog.func_at' fs loc phi ->
    seplog.func_at' fs loc phi'.
Proof.
  intros RD loc [f cc A P Q] [pp E]; simpl.
  rewrite (resource_decay_PURE RD _ _ _ E).
  eexists. reflexivity.
Qed.

Lemma resource_decay_func_at'_inv {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc fs,
    seplog.func_at' fs loc phi' ->
    seplog.func_at' fs loc phi.
Proof.
  intros RD loc [f cc A P Q] [pp E]; simpl.
  destruct (resource_decay_PURE_inv RD _ _ _ E) as [pp' [Ephi E']].
  pose proof resource_at_approx phi loc as H.
  rewrite Ephi in H at 1. rewrite <-H.
  eexists. reflexivity.
Qed.

Lemma resource_decay_same_locks {b phi phi'} :
  resource_decay b phi phi' -> same_locks phi phi'.
Proof.
  intros R loc n i. unfold resource_is_lock. split; intro.
 -
  pose proof (resource_decay_LK R loc).
  destruct (phi @ loc); try contradiction; destruct k; try contradiction; destruct H; subst.
  rewrite (H0 sh r n0 i0 p (eq_refl _)). auto.
 -
  pose proof (@resource_decay_LK_inv _ _ _ R loc).
  destruct (phi' @ loc); try contradiction; destruct k; try contradiction; destruct H; subst.
  destruct (H0 sh r n0 i0 p (eq_refl _)) as [pp' [? ?]]. rewrite H1. auto.
Qed.
