Require Import VST.msl.log_normalize.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Import RML. Import R.
Local Open Scope pred.

(* Ghost state construction drawn from "Iris from the ground up", Jung et al. *)
Program Definition ghost_is (g : ghost): pred rmap :=
  fun m => ghost_of m = ghost_fmap (approx (level m)) (approx (level m)) g.
Next Obligation.
  repeat intro.
  erewrite (age1_ghost_of _ _ H) by (symmetry; apply ghost_of_approx).
  rewrite H0; simpl.
  pose proof (age_level _ _ H).
  rewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx by omega; auto.
Qed.

Definition Own g: pred rmap := allp noat && ghost_is g.

Lemma Own_op: forall {RA: Ghost} (a b c: ghost), join a b c ->
  Own c = Own a * Own b.
Proof.
  intros; apply pred_ext.
  - intros w [Hno Hg]; simpl in *.
    destruct (make_rmap (resource_at w) (ghost_fmap (approx (level w)) (approx (level w)) a)
      (rmap_valid w) (level w)) as (wa & Hla & Hra & Hga).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    destruct (make_rmap (resource_at w) (ghost_fmap (approx (level w)) (approx (level w)) b)
      (rmap_valid w) (level w)) as (wb & Hlb & Hrb & Hgb).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    exists wa, wb; rewrite Hla, Hlb, Hra, Hrb; split; auto.
    apply resource_at_join2; auto.
    + intro; rewrite Hra, Hrb.
      apply identity_unit'; auto.
    + rewrite Hg, Hga, Hgb.
      apply ghost_fmap_join; auto.
  - intros w (w1 & w2 & J & [Hnoa Hga] & [Hnob Hgb]); simpl in *.
    split.
    + intro l; apply (resource_at_join _ _ _ l) in J.
      rewrite <- (Hnoa _ _ _ J); auto.
    + eapply join_eq.
      * apply ghost_of_join; eauto.
      * rewrite Hga, Hgb.
        destruct (join_level _ _ _ J) as [-> ->].
        apply ghost_fmap_join; auto.
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

Definition fp_update (a b : ghost) :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
               joins (ghost_fmap (approx n) (approx n) b) c.

Lemma Own_update: forall a b, fp_update a b ->
  Own a |-- bupd (Own b).
Proof.
  repeat intro.
  destruct H0 as [Hno Hg]; simpl in *.
  rewrite Hg in H1.
  destruct H1 as [? J].
  destruct (H (level a0) c).
  { eexists; eauto. }
  exists (ghost_fmap (approx (level a0)) (approx (level a0)) b); split.
  { eexists; eauto. }
  destruct (make_rmap (resource_at a0)
    (ghost_fmap (approx (level a0)) (approx (level a0)) b) (rmap_valid a0) (level a0))
    as (m' & Hl & Hr & ?).
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
  exists m'; repeat split; auto.
  - intro; rewrite Hr; auto.
  - rewrite Hl; auto.
Qed.

Definition fp_update_ND a B :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
    exists b, B b /\ joins (ghost_fmap (approx n) (approx n) b) c.

Lemma Own_update_ND: forall {RA: Ghost} a B, fp_update_ND a B ->
  Own a |-- bupd (EX b : _, !!(B b) && Own b).
Proof.
  repeat intro.
  destruct H0 as [Hno Hg]; simpl in *.
  rewrite Hg in H1.
  destruct H1 as [? J].
  destruct (H (level a0) c) as (g' & ? & ?).
  { eexists; eauto. }
  exists (ghost_fmap (approx (level a0)) (approx (level a0)) g'); split; auto.
  destruct (make_rmap (resource_at a0)
    (ghost_fmap (approx (level a0)) (approx (level a0)) g') (rmap_valid a0) (level a0))
    as (m' & Hl & Hr & ?).
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
  exists m'; repeat split; auto.
  exists g'; repeat split; auto.
  - intro; rewrite Hr; auto.
  - rewrite Hl; auto.
Qed.

Definition gname := nat.

(* Note that finite maps are not a Disj_alg, since a map containing only cores joins with itself
   but isn't a universal unit. *)
Instance Global_Ghost {I} {RAs: I -> Ghost}: Ghost :=
  { G := forall i, nat -> option (@G (RAs i)) }.

Definition RA_of g := match g with GHOST RA _ _ => RA end.

Definition Global_preds {I} (pds: I -> gname -> preds) :=
  SomeP (PiType (ConstType I) (fun i => PiType (ConstType gname) (fun n =>
    match pds i n with SomeP A _ => A end)))
        (fun ts i n => match pds i n with SomeP A P => P ts end).
  
  
  ArrowType (ConstType I) (ArrowType (ConstType gname) (PiType ())))
    (fun ts i n => match pds i n with SomeP A P => P ts end).

Definition own {I} `{EqDec I} {RAs: I -> Ghost} (n: gname) (a: ghost) {inG: {i | RAs i = RA_of a}} :=
  match a with GHOST _ g (SomeP A pp) =>
  EX A' : _, Own (GHOST Global_Ghost (fun j => if eq_dec j (proj1_sig inG) then fun m =>
                                       if eq_dec m n then Some g else None else fun _ => None)
                         (SomeP (ArrowType (ConstType I) (ArrowType (ConstType nat) Mpred))
                                (fun _ => )) end.
                 Print preds.

Lemma ghost_alloc: forall {I} `{EqDec I} {RAs: I -> Ghost} {RA: Ghost} {inG: {i | RAs i = RA}}
  (a: G) pp, (exists b, joins a b) ->
  TT |-- bupd (EX g: gname, @own _ _ _ _ inG g a pp).
Proof.

Lemma ghost_op: forall {I} `{EqDec I} {RAs: I -> Ghost} {RA: Ghost} {inG: {i | RAs i = RA}}
  (a b c: G) pp, join a b c ->
  own g c = own g a * own g b.
Proof.

Lemma ghost_valid: forall {I} `{EqDec I} {RAs: I -> Ghost} {RA: Ghost} {inG: {i | RAs i = RA}}
  (a: G) pp, (exists b, joins a b) ->
  TT |-- bupd (EX g: gname, @own _ _ _ _ inG g a pp).
Proof.

Lemma ghost_update: forall {I} `{EqDec I} {RAs: I -> Ghost} {RA: Ghost} {inG: {i | RAs i = RA}}
  (a: G) pp, (exists b, joins a b) ->
  TT |-- bupd (EX g: gname, @own _ _ _ _ inG g a pp).
Proof.

