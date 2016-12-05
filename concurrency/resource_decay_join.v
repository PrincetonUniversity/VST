Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import msl.age_to.
Require Import veric.aging_lemmas.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import veric.coqlib4.
Require Import veric.age_to_resource_at.
Require Import concurrency.permjoin.
Require Import concurrency.sync_preds_defs.

Set Bullet Behavior "Strict Subproofs".

(* @andrew those lemmas already somewhere? *)

Lemma rmap_bound_join {b phi1 phi2 phi3} :
  sepalg.join phi1 phi2 phi3 ->
  rmap_bound b phi3 <-> (rmap_bound b phi1 /\ rmap_bound b phi2).
Proof.
  intros j; split.
  - intros B; split.
    + intros l p; specialize (B l p).
      apply resource_at_join with (loc := l) in j.
      rewrite B in j.
      inv j. f_equal. apply (join_to_bot_l RJ).
    + intros l p; specialize (B l p).
      apply resource_at_join with (loc := l) in j.
      rewrite B in j.
      inv j. f_equal. apply (join_to_bot_r RJ).
  - intros [B1 B2] l p.
    specialize (B1 l p).
    specialize (B2 l p).
    apply resource_at_join with (loc := l) in j.
    rewrite B1, B2 in j.
    inv j. f_equal. apply join_bot_bot_eq; auto.
Qed.

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
  destruct r1 as [ sh1 | sh1 sh1' k1 pp1 | k1 pp1 ];
    destruct r2 as [ sh2 | sh2 sh2' k2 pp2 | k2 pp2 ];
    simpl in *.
  
  - sumsimpl. sumsimpl. sumsimpl. breakhyps.
  
  - sumsimpl.
    sumsimpl.
    breakhyps.
    destruct k2; split; eauto.
    now (exists m; breakhyps).
    all: exfalso; breakhyps.
  
  - sumsimpl.
    exfalso. breakhyps.
  
  - sumsimpl.
    destruct (eq_dec sh1 Share.top).
    destruct (eq_dec sh1' pfullshare).
    destruct k1.
    destruct (eq_dec sh2 Share.bot).
    now subst; eauto.
    all: exfalso; breakhyps.
  
  - sumsimpl.
    destruct D.
    + autospec nn. congruence.
    + sumsimpl.
      destruct (eq_dec sh1' pfullshare); subst.
      destruct (eq_dec sh2' pfullshare); subst.
      destruct (eq_dec k1 k2); try subst k2.
      now left; f_equal; breakhyps.
      destruct k1, k2.
      right. exists sh1, m, m0. split; auto; f_equal; breakhyps.
      all: try solve [exfalso; breakhyps].
      sumsimpl. breakhyps.
  
  - sumsimpl. exfalso; breakhyps.
  
  - sumsimpl. exfalso; breakhyps.
  
  - sumsimpl. sumsimpl. breakhyps.
    destruct k2; split; eauto.
    now (exists m; breakhyps).
    all: exfalso; breakhyps.
  
  - sumsimpl. sumsimpl. sumsimpl. breakhyps.
Qed.

Lemma resource_decay_aux_spec_inv b phi1 phi2 :
  resource_decay_aux b phi1 phi2 -> resource_decay b phi1 phi2.
Proof.
  intros [lev rd]; split; [ apply lev | clear lev]; intros loc; specialize (rd loc).
  breakhyps; intuition eauto.
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
    res_join'_NO1 : forall rsh1 rsh2 rsh3 : Share.t,
                   sepalg.join rsh1 rsh2 rsh3 ->
                   res_join' (NO rsh1) (NO rsh2) (NO rsh3)
  | res_join'_NO2 : forall (rsh1 rsh2 rsh3 : Share.t) (sh : pshare) 
                     (k : AV.kind) (p : preds),
                   sepalg.join rsh1 rsh2 rsh3 ->
                   res_join' (YES rsh1 sh k p) (NO rsh2) (YES rsh3 sh k p)
  | res_join'_NO3 : forall (rsh1 rsh2 rsh3 : Share.t) (sh : pshare) 
                     (k : AV.kind) (p : preds),
                   sepalg.join rsh1 rsh2 rsh3 ->
                   res_join' (NO rsh1) (YES rsh2 sh k p) (YES rsh3 sh k p)
  | res_join'_YES : forall (rsh1 rsh2 rsh3 : Share.t) (sh1 sh2 sh3 : pshare)
                     (k : AV.kind) (p : preds),
                   sepalg.join rsh1 rsh2 rsh3 ->
                   sepalg.join sh1 sh2 sh3 ->
                   res_join' (YES rsh1 sh1 k p) (YES rsh2 sh2 k p) (YES rsh3 sh3 k p)
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
  destruct (phi @ loc) as [t0 | t0 p [m | z | z | f c] p0 | k p]; simpl; auto.
Qed.

Lemma resource_decay_at_LK {nextb n r1 r2 b sh i} :
  resource_decay_at nextb n r1 r2 b ->
  res_option r1 = Some (sh, LK i) <->
  res_option r2 = Some (sh, LK i).
Proof.
  destruct r1 as [t1 | t1 p1 [m1 | z1 | z1 | f1 c1] pp1 | k1 p1];
    destruct r2 as [t2 | t2 p2 [m2 | z2 | z2 | f2 c2] pp2 | k2 p2]; simpl;
      unfold resource_decay_at; intros rd; split; intros E.
  all: try congruence.
  all: breakhyps.
  autospec H; congruence.
  all: simpl in *; congruence.
Qed.

Lemma resource_decay_at_CT {nextb n r1 r2 b sh i} :
  resource_decay_at nextb n r1 r2 b ->
  res_option r1 = Some (sh, CT i) <->
  res_option r2 = Some (sh, CT i).
Proof.
  destruct r1 as [t1 | t1 p1 [m1 | z1 | z1 | f1 c1] pp1 | k1 p1];
    destruct r2 as [t2 | t2 p2 [m2 | z2 | z2 | f2 c2] pp2 | k2 p2]; simpl;
      unfold resource_decay_at; intros rd; split; intros E.
  all: try congruence.
  all: breakhyps.
  autospec H; congruence.
  all: simpl in *; congruence.
Qed.

Lemma resource_decay_join b phi1 phi1' phi2 phi3 :
  rmap_bound b phi2 ->
  resource_decay b phi1 phi1' ->
  sepalg.join phi1 phi2 phi3 ->
  exists phi3',
    sepalg.join phi1' (age_to (level phi1') phi2) phi3' /\
    resource_decay b phi3 phi3'.
Proof.
  Unset Printing Implicit.
  intros bound rd; apply resource_decay_aux_spec in rd; revert rd.
  intros [lev rd] J.
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
    
    destruct rd as [nn [[[E1 | (rsh & v & v' & E1 & E1')] | (pos & v & E1') ] | (v & pp & E1 & E1')]].
    
    - exists ( resource_fmap (approx (level phi1')) (approx (level phi1')) (phi3 @ loc)).
      rewrite <-E1.
      split;[|split;[split|]].
      + inversion J; simpl; constructor; auto.
      + intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
        inv J. f_equal. eapply join_bot_bot_eq; auto.
      + left. auto.
      + apply resource_fmap_approx_idempotent.
    
    - rewrite E1'.
      apply res_join'_spec in J.
      inversion J; rewr (phi1 @ loc) in E1; simpl in *.
      all:try congruence.
      + injection E1; intros; subst.
        exists (YES rsh3 pfullshare (VAL v') NoneP).
        split;[|split;[split|]].
        * constructor; assumption.
        * intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
          congruence.
        * right. left. simpl. exists rsh3, v, v'. split; congruence.
        * simpl. f_equal.
      + injection E1; intros; subst.
        rewr (phi1 @ loc) in J.
        apply res_join'_spec_inv in J.
        apply YES_join_full in J.
        exfalso. breakhyps.
    
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
      + intros _. f_equal.
        apply join_bot_bot_eq. auto.
      + right. right. left. eauto.
      + simpl. unfold NoneP in *. simpl. do 2 f_equal.
    - rewrite E1 in J.
      exists (NO Share.bot).
      rewrite E1'.
      inv J.
      + simpl.
        split;[|split;[split|]].
        * constructor.
          cut (rsh2 = Share.bot).
          now intros ->; auto with *.
          revert RJ; clear.
          apply join_top_l.
        * intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
          congruence.
        * right. right. right. exists v, pp. split; f_equal.
          revert RJ; clear.
          apply join_top.
        * reflexivity.
      + exfalso.
        eapply join_pfullshare.
        eauto.
  }
  
  destruct (make_rmap (fun loc => proj1_sig (DESCR loc))) with (n := level phi1') as (phi3' & lev3 & at3).
  {
    (* validity *)
    intros b' ofs.
    pose proof phi_valid phi3 b' ofs as V3.
    change compcert_rmaps.R.res_option with res_option.
    unfold "oo" in *; simpl in *.
    destruct (DESCR (b', ofs)) as (r & j & rd' & Er); simpl; auto; clear Er.
    destruct (res_option r) as [[sh [m | z | z | f c]] | ] eqn:Err; auto.
    - apply (resource_decay_at_LK rd') in Err.
      rewrite Err in V3.
      intros i Hi; specialize (V3 i Hi).
      destruct (DESCR (b', Z.add ofs i)) as (r' & j' & rd'' & Er); simpl; auto; clear Er.
      apply (resource_decay_at_CT rd'').
      auto.
    - apply (resource_decay_at_CT rd') in Err.
      rewrite Err in V3.
      destruct V3 as (n & lz & E).
      exists n; split; auto.
      destruct (DESCR (b', Z.sub ofs z)) as (r' & j' & rd'' & Er); simpl; auto; clear Er.
      apply (resource_decay_at_LK rd'').
      auto.
  }
  {
    (* the right level of approximation *)
    unfold "oo".
    extensionality loc; simpl.
    destruct (DESCR loc) as (?&?&rd3&?); simpl; auto.
  }
  
  exists phi3'.
  split;[|split].
  - apply resource_at_join2; auto.
    + rewrite lev3.
      unfold phi2'.
      apply level_age_to.
      eauto with *.
    + intros loc.
      rewrite at3.
      destruct (DESCR loc) as (?&?&?); simpl; auto.
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
    + right; left. exact_eq R;
      do 7 (f_equal; try extensionality);
      auto.
    + right; right; left. auto.
    + auto.
Qed.
