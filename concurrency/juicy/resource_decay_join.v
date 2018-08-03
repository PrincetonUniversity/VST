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
Require Import VST.veric.coqlib4.
Require Import VST.veric.age_to_resource_at.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.sync_preds_defs.

Set Bullet Behavior "Strict Subproofs".

(* @andrew those lemmas already somewhere? *)

Lemma NO_ext: forall sh1 sh2 p1 p2, sh1=sh2 -> NO sh1 p1 = NO sh2 p2.
Proof.
intros.
subst. f_equal. apply proof_irr. 
Qed.

Lemma rmap_bound_join {b phi1 phi2 phi3} :
  sepalg.join phi1 phi2 phi3 ->
  rmap_bound b phi3 <-> (rmap_bound b phi1 /\ rmap_bound b phi2).
Proof.
  intros j; split.
  - intros B; split.
    + intros l p; specialize (B l p).
      apply resource_at_join with (loc := l) in j.
      rewrite B in j.
      inv j. apply NO_ext.
      clear - RJ. apply split_identity in RJ. apply identity_share_bot in RJ.  auto. apply bot_identity.
    + intros l p; specialize (B l p).
      apply resource_at_join with (loc := l) in j.
      rewrite B in j.
      inv j. apply NO_ext.
      clear - RJ.
      apply join_comm in RJ.
      apply split_identity in RJ. apply identity_share_bot in RJ.  auto. apply bot_identity.
  - intros [B1 B2] l p.
    specialize (B1 l p).
    specialize (B2 l p).
    apply resource_at_join with (loc := l) in j.
    rewrite B1, B2 in j.
    inv j. apply NO_ext.
    clear - RJ. apply join_unit1_e in RJ. auto. apply bot_identity.
Qed.

Import shares.

Lemma resource_decay_aux_spec b phi1 phi2 :
  resource_decay b phi1 phi2 -> resource_decay_aux b phi1 phi2.
Proof.
  intros [lev rd]; split; [ apply lev | clear lev]; intros loc; specialize (rd loc).
  assert (D: {(fst loc >= b)%positive} + {(fst loc < b)%positive}) by (pose proof zlt; zify; eauto).
  split. apply rd. destruct rd as [nn rd].
  remember (phi1 @ loc) as r1.
  remember (phi2 @ loc) as r2.
  remember (level phi2) as n.
  clear phi1 phi2 Heqr1 Heqr2 Heqn.
  destruct r1 as [ sh1 nsh1 | sh1 sh1' k1 pp1 | k1 pp1 ];
    destruct r2 as [ sh2 nsh2 | sh2 sh2' k2 pp2 | k2 pp2 ];
    simpl in *.

  - sumsimpl. sumsimpl. sumsimpl. breakhyps.

  - sumsimpl. sumsimpl. breakhyps.
     split; auto.
     assert (exists v : memval,
        YES sh2 sh2' k2 pp2 =
        YES Share.top shares.readable_share_top (VAL v) NoneP)
         by (breakhyps; eauto).
     clear rd.      
    destruct k2; try solve [exfalso; destruct H as [m H]; inv H].
    exists m. destruct H as [v ?]. inv H. apply YES_ext; auto.
    exfalso; breakhyps.

  - sumsimpl.
    exfalso. breakhyps.

  - sumsimpl.
    destruct (eq_dec sh1 Share.top). subst sh1.
    destruct (eq_dec sh2 Share.bot). subst sh2.
    destruct k1.
    exists m. exists pp1. split. apply YES_ext; auto. apply NO_ext; auto.
    all: exfalso; breakhyps.

  - sumsimpl.
    destruct D.
    + autospec nn. congruence.
    + sumsimpl.
      destruct (writable_share_dec sh1);
      destruct (writable_share_dec sh2).
      destruct (eq_dec k1 k2); try subst k2.
      left. breakhyps. inv H. inv H0. rewrite H4.  apply YES_ext; auto.
      destruct k1, k2; try solve [exfalso; breakhyps].
      right. exists sh1, sh1',  m, m0.
      breakhyps. inv H; inv H0. rewrite H4. split3; auto; apply YES_ext; auto.

      left. breakhyps. inv H. inv H0. contradiction.

      destruct (eq_dec k1 k2); try subst k2.
      left. breakhyps. inv H. inv H0. rewrite H4.  apply YES_ext; auto.
      destruct k1, k2; try solve [exfalso; breakhyps].
      right. exists sh1, sh1',  m, m0.
      breakhyps. inv H; inv H0. rewrite H4. split3; auto; apply YES_ext; auto.

     left. breakhyps. inv H.  inv H0. contradiction.

  - sumsimpl. exfalso; breakhyps.

  - sumsimpl. exfalso; breakhyps.

  - sumsimpl. sumsimpl. breakhyps.
    destruct k2; split; eauto; try solve [exfalso; breakhyps].
    exists m; breakhyps. inv H0. apply YES_ext; auto.
    exfalso; breakhyps.

  - sumsimpl. sumsimpl. sumsimpl. breakhyps.
Qed.

Lemma resource_decay_aux_spec_inv b phi1 phi2 :
  resource_decay_aux b phi1 phi2 -> resource_decay b phi1 phi2.
Proof.
  intros [lev rd]; split; [ apply lev | clear lev]; intros loc; specialize (rd loc).
  breakhyps; intuition eauto.
  right; left. exists x, H1. exists x1, x2. rewrite H, H0.  split; apply YES_ext; auto.
Qed.

Lemma resource_fmap_approx_idempotent n r :
  resource_fmap (approx n) (approx n) (resource_fmap (approx n) (approx n) r) = resource_fmap (approx n) (approx n) r.
Proof.
  destruct r; simpl; f_equal.
  - rewrite preds_fmap_fmap.
    rewrite approx_oo_approx.
    reflexivity.
  - rewrite preds_fmap_fmap.
    rewrite approx_oo_approx.
    reflexivity.
Qed.

Inductive res_join' : resource -> resource -> resource -> Type :=
    res_join'_NO1 : forall (sh1 sh2 sh3 : Share.t) nsh1 nsh2 nsh3,
                   sepalg.join sh1 sh2 sh3 ->
                   res_join' (NO sh1 nsh1) (NO sh2 nsh2) (NO sh3 nsh3)
  | res_join'_NO2 : forall (sh1 sh2 sh3 : Share.t) rsh1 nsh2 rsh3
                     (k : AV.kind) (p : preds),
                   sepalg.join sh1 sh2 sh3 ->
                   res_join' (YES sh1 rsh1 k p) (NO sh2 nsh2) (YES sh3 rsh3 k p)
  | res_join'_NO3 : forall (sh1 sh2 sh3 : Share.t) nsh1 rsh2 rsh3
                     (k : AV.kind) (p : preds),
                   sepalg.join sh1 sh2 sh3 ->
                   res_join' (NO sh1 nsh1) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
  | res_join'_YES : forall (sh1 sh2 sh3 : Share.t) rsh1 rsh2 rsh3
                     (k : AV.kind) (p : preds),
                   sepalg.join sh1 sh2 sh3 ->
                   res_join' (YES sh1 rsh1 k p) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
  | res_join'_PURE : forall (k : AV.kind) (p : preds),
                    res_join' (PURE k p) (PURE k p) (PURE k p).

Lemma res_join'_spec r1 r2 r3 : res_join r1 r2 r3 -> res_join' r1 r2 r3.
Proof.
  intros J.
  destruct r1 as [sh1 | sh1 sh1' k1 pp1 | k1 pp1],
           r2 as [sh2 | sh2 sh2' k2 pp2 | k2 pp2],
           r3 as [sh3 | sh3 sh3' k3 pp3 | k3 pp3].
  all: try solve [ exfalso; inversion J ].
  all: try (assert (k1 = k3) by (inv J; auto); subst).
  all: try (assert (k2 = k3) by (inv J; auto); subst).
  all: try (assert (pp1 = pp3) by (inv J; auto); subst).
  all: try (assert (pp2 = pp3) by (inv J; auto); subst).
  all: try (assert (sh1' = sh3') by (inv J; auto); subst).
  all: try (assert (sh2' = sh3') by (inv J; auto); subst).
  all: constructor; inv J; auto.
Qed.

Lemma res_join'_spec_inv r1 r2 r3 : res_join' r1 r2 r3 -> res_join r1 r2 r3.
Proof.
  inversion 1; constructor; assumption.
Qed.

Lemma res_option_age_to n phi loc : res_option ((age_to n phi) @ loc) = res_option (phi @ loc).
Proof.
  rewrite age_to_resource_at.
  destruct (phi @ loc) as [t0 | t0 p [m | z  | f c] p0 | k p]; simpl; auto.
Qed.

Lemma resource_decay_at_LK {nextb n r1 r2 b sh n' i} :
  resource_decay_at nextb n r1 r2 b ->
  res_option r1 = Some (sh, LK n' i) <->
  res_option r2 = Some (sh, LK n' i).
Proof.
  destruct r1 as [t1 p1 | t1 p1 [m1 | z1 | f1 c1] pp1 | k1 p1];
    destruct r2 as [t2 p2 | t2 p2 [m2 | z2 | f2 c2] pp2 | k2 p2]; simpl;
      unfold resource_decay_at; intros rd; split; intros E;
  try congruence; breakhyps.
  autospec H; congruence.
  simpl in H0.
  rewrite <- E.
  assert (z1=z2) by congruence. assert (i1=i0) by congruence. subst. f_equal. f_equal.
  unfold readable_part. apply exist_ext.
  inv H0; auto.
  simpl in H0.
  rewrite <- E.
  assert (z1=z2) by congruence. subst. f_equal. f_equal.
  unfold readable_part. apply exist_ext.
  inv H0; auto.
  inv E.  inv H0. auto.
Qed.

Lemma resource_decay_join b phi1 phi1' phi2 phi3 :
  rmap_bound b phi2 ->
  resource_decay b phi1 phi1' ->
  ghost_of phi1' = own.ghost_approx phi1' (ghost_of phi1) ->
  sepalg.join phi1 phi2 phi3 ->
  exists phi3',
    sepalg.join phi1' (age_to (level phi1') phi2) phi3' /\
    resource_decay b phi3 phi3' /\ ghost_of phi3' = own.ghost_approx phi3' (ghost_of phi3).
Proof.
  intros bound rd; apply resource_decay_aux_spec in rd; revert rd.
  intros [lev rd] Hg J.
  assert (lev12 : level phi1 = level phi2).
  { apply join_level in J; intuition congruence. }

  set (phi2' := age_to (level phi1') phi2).
  unfold resource_decay in *.

  assert (DESCR : forall loc,
             { r3 |
               sepalg.join (phi1' @ loc) (phi2' @ loc) r3 /\
               resource_decay_at b (level phi1') (phi3 @ loc) r3 (fst loc) /\
               resource_fmap (approx (level phi1')) (approx (level phi1')) r3 = r3
         }).
  {
    intros loc.
    specialize (rd loc).
    assert (D: {(fst loc >= b)%positive} + {(fst loc < b)%positive}) by (pose proof zlt; zify; eauto).
    apply resource_at_join with (loc := loc) in J.

    unfold phi2'; clear phi2'; rewrite age_to_resource_at.
    autospec bound.

    destruct rd as [nn [[[E1 | (sh & rsh & v & v' & E1 & E1' & E1'')] | (pos & v & E1') ] | (v & pp & E1 & E1')]].

    - exists ( resource_fmap (approx (level phi1')) (approx (level phi1')) (phi3 @ loc)).
      rewrite <-E1.
      split;[|split;[split|]].
      + inversion J; simpl; constructor; auto.
      + intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
        inv J. apply NO_ext. eapply join_bot_bot_eq; auto.
      + left. auto.
      + apply resource_fmap_approx_idempotent.

    -  rewrite E1'.
      apply res_join'_spec in J.
      inversion J; rewr (phi1 @ loc) in E1; simpl in *.
      all:try congruence.
      + injection E1; intros; subst.
        exists (YES sh3 rsh3 (VAL v') NoneP).
        split;[|split;[split|]].
        * constructor; assumption.
        * intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
          congruence.
        * right. left. simpl. exists sh3, rsh3, v, v'. split3; auto; try congruence.
          clear - H2 E1''. eapply join_writable1; eauto.
        * simpl. f_equal.
      + injection E1; intros; subst.
        rewr (phi1 @ loc) in J.
        apply res_join'_spec_inv in J.
        apply YES_join_full in J.
        exfalso. breakhyps. auto. 

    - autospec nn.
      autospec bound.
      rewrite nn in *.
      rewrite bound in *.
      apply res_join'_spec in J.
      inv J; simpl.
      exists (phi1' @ loc).
      rewrite E1'.
      split;[|split;[split|]].
      + constructor. eauto.
      + intros _. apply NO_ext.
        apply join_bot_bot_eq. auto.
      + right. right. left. eauto.
      + simpl. unfold NoneP in *. simpl. do 2 f_equal.

    - rewrite E1 in J.
      exists (NO _ bot_unreadable).
      rewrite E1'.
      inv J.
      + simpl.
        split;[|split;[split|]].
        * constructor. clear - RJ. apply join_top_l in RJ. rewrite RJ. apply join_bot.
        * intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
          congruence.
        * right. right. right. exists v, pp. split; f_equal.
          revert RJ; clear.
          intro. apply YES_ext. eapply join_top; eauto.
        * reflexivity.
      + exfalso.
        clear - RJ rsh2. apply join_top_l in RJ. subst. contradiction bot_unreadable; auto.
  }

  destruct (make_rmap (fun loc => proj1_sig (DESCR loc)) (own.ghost_approx phi1' (ghost_of phi3)))
    with (n := level phi1') as (phi3' & lev3 & at3 & Hg3).
  {
    (* the right level of approximation *)
    unfold "oo".
    extensionality loc; simpl.
    destruct (DESCR loc) as (?&?&rd3&?); simpl; auto.
  }
  {
    rewrite !ghost_fmap_fmap, approx_oo_approx; auto.
  }

  exists phi3'.
  split;[|split; [split|]].
  - apply resource_at_join2; auto.
    + rewrite lev3.
      unfold phi2'.
      apply level_age_to.
      eauto with *.
    + intros loc.
      rewrite at3.
      destruct (DESCR loc) as (?&?&?); simpl; auto.
    + subst phi2'; rewrite Hg, age_to_ghost_of, Hg3.
      apply ghost_fmap_join, ghost_of_join; auto.
  - rewrite lev3.
    apply join_level in J.
    auto with *.
  - intros loc.
    rewrite at3.
    destruct (DESCR loc) as (?&?&rd3); simpl; auto.
    destruct rd3 as [[NN rd3] _].
    split; auto.
    destruct rd3 as [R|[R|[R|R]]].
    + left. exact_eq R; do 3 f_equal; auto.
    + right; left. destruct R as [sh [psh [v [v' [H [H0 H1]]]]]].
       exists sh, H1, v, v'.
       split. replace (level phi3') with (level phi1'); rewrite H. apply YES_ext; auto.
       rewrite H0; apply YES_ext; auto.
    + right; right; left. auto.
    + auto.
  - congruence.
Qed.
