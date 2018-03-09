Require Import VST.msl.log_normalize.
Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Import RML. Import R.
Local Open Scope pred.

Notation ghost_approx m := (ghost_fmap (approx (level m)) (approx (level m))).

(* Ghost state construction drawn from "Iris from the ground up", Jung et al. *)
Program Definition ghost_is (g : ghost): pred rmap :=
  fun m => ghost_of m = ghost_approx m g.
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
    destruct (make_rmap (resource_at w) (ghost_approx w a) (rmap_valid w) (level w))
      as (wa & Hla & Hra & Hga).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    destruct (make_rmap (resource_at w) (ghost_approx w b) (rmap_valid w) (level w))
      as (wb & Hlb & Hrb & Hgb).
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

Lemma preds_join_i: forall {I} a b, (forall i n x y, a i n = Some x -> b i n = Some y -> x = y) ->
  preds_join I a b (fun i n => match a i n with Some x => Some x | _ => b i n end).
Proof.
  intros.
  intros i n; specialize (H i n).
  destruct (a i n); [|constructor].
  destruct (b i n); constructor.
  specialize (H _ _ eq_refl eq_refl); subst; auto.
Qed.

Lemma ghost_joins_approx: forall n a c,
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  exists c', joins (ghost_fmap (approx (S n)) (approx (S n)) a) (ghost_fmap (approx (S n)) (approx (S n)) c') /\
    forall b, joins b (ghost_fmap (approx (S n)) (approx (S n)) c') ->
      joins (ghost_fmap (approx n) (approx n) b) (ghost_fmap (approx n) (approx n) c).
Proof.
  intros.
  destruct a as [?? ga pdsa], c as [?? gc pdsc], H as [? H]; inv H; repeat inj_pair_tac.
  assert (forall i n pp, match pdsa i n, pdsc i n with Some x, Some _ => Some x | _, _ => pdsc i n end = Some pp ->
    exists a, finmap_get (gc i) n = Some a) as dom'.
  { intros; destruct (pdsa i n0) eqn: Hi; eauto.
    destruct (pdsc i n0) eqn: Hi'; inv H; eauto. }
  eexists (GHOST _ _ gc _ dom'); split.
  - eexists; constructor; eauto.
    apply preds_join_i; intros.
    destruct (pdsa i n0); inv H.
    destruct (pdsc i n0); inv H0; auto.
  - intros [?? gb pdsb] [? J]; inv J; repeat inj_pair_tac.
    eexists; constructor; eauto.
    apply preds_join_i; intros.
    specialize (H10 i n0); specialize (H11 i n0); simpl in *.
    destruct (pdsb i n0); inv H.
    destruct (pdsc i n0); inv H0.
    destruct (pdsa i n0); inv H10; inv H11.
    + inv H2; inv H4.
      rewrite <- H, preds_fmap_fmap, approx_oo_approx', approx'_oo_approx; auto.
    + inv H3.
      rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx; auto.
  Unshelve.
  simpl; intros.
  specialize (H9 i); apply finmap_get_join with (i0 := n0) in H9.
  destruct (finmap_get (c0 i) n0); eauto.
  destruct (pdsa i n0) eqn: Hi; inv H.
  destruct (dom _ _ _ Hi) as [? Hget]; rewrite Hget in H9.
  destruct (finmap_get (gc i) n0); inv H9.
  destruct (pdsc i n0) eqn: Hi'; inv H1.
  destruct (dom0 _ _ _ Hi') as [? Hget]; rewrite Hget in H9.
  destruct (finmap_get (ga i) n0); inv H9.
  simpl; intros.
  specialize (H8 i); apply finmap_get_join with (i0 := n0) in H8.
  destruct (finmap_get (c1 i) n0); eauto.
  destruct (pdsb i n0) eqn: Hi; inv H.
  destruct (dom1 _ _ _ Hi) as [? Hget]; rewrite Hget in H8.
  destruct (finmap_get (gc i) n0); inv H8.
  destruct (pdsc i n0) eqn: Hi'; inv H1.
  destruct (dom0 _ _ _ Hi') as [? Hget]; rewrite Hget in H8.
  destruct (finmap_get (gb i) n0); inv H8.
Qed.

Program Definition bupd (P: pred rmap): pred rmap :=
  fun m => forall c, joins (ghost_of m) (ghost_approx m c) ->
    exists b, joins b (ghost_approx m c) /\
    exists m', level m' = level m /\ resource_at m' = resource_at m /\ ghost_of m' = b /\ P m'.
Next Obligation.
Proof.
  repeat intro.
  rewrite (age1_ghost_of _ _ H) in H1.
  rewrite <- ghost_of_approx in H0.
  destruct (ghost_joins_approx _ _ _ H1) as (c0 & J0 & Hc0).
  rewrite <- (age_level _ _ H) in *.
  specialize (H0 _ J0); destruct H0 as (b & J & Hrb).
  pose proof (age_level _ _ H).
  exists (ghost_approx a' b); split; auto.
  destruct Hrb as (m' & Hl' & Hr' & Hg' & HP).
  destruct (levelS_age m' (level a')) as (m'' & Hage' & Hl'').
  { congruence. }
  exists m''; repeat split; auto.
  + extensionality l.
    erewrite (age1_resource_at _ _ H l) by (symmetry; apply resource_at_approx).
    erewrite (age1_resource_at _ _ Hage' l) by (symmetry; apply resource_at_approx).
    congruence.
  + rewrite (age1_ghost_of _ _ Hage').
    rewrite Hg', <- Hl''; auto.
  + eapply (proj2_sig P); eauto.
Qed.

Lemma bupd_intro: forall P, P |-- bupd P.
Proof.
  repeat intro; eauto 7.
Qed.

Lemma bupd_mono: forall P Q, P |-- Q -> bupd P |-- bupd Q.
Proof.
  repeat intro.
  simpl in *.
  destruct (H0 _ H1) as (b & ? & m' & ? & ? & ? & ?).
  exists b; split; auto.
  exists m'; repeat split; auto.
Qed.

Lemma bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q).
Proof.
  repeat intro.
  destruct H as (w1 & w2 & J & HP & HQ).
  destruct (join_level _ _ _ J) as [Hl1 Hl2].
  pose proof (ghost_of_join _ _ _ J) as Jg.
  destruct H0 as [? J'].
  destruct (join_assoc Jg J') as (c' & J1 & J2).
  erewrite <- (ghost_same_level_gen (level a) (ghost_of w2) c c') in J2, J1
    by (rewrite <- Hl2 at 1 2; rewrite ghost_of_approx; auto).
  destruct (HP c') as (? & [? J1'] & w1' & ? & Hr' & ? & HP'); subst.
  { rewrite Hl1; eauto. }
  rewrite Hl1 in J1'; destruct (join_assoc (join_comm J1) (join_comm J1')) as (w' & ? & ?).
  exists w'; split; [eexists; apply join_comm; eauto|].
  destruct (make_rmap _ w' (rmap_valid a) (level a)) as (m' & ? & Hr'' & ?); subst.
  { extensionality l; apply resource_at_approx. }
  { eapply ghost_same_level_gen.
    rewrite <- (ghost_of_approx w2), <- (ghost_of_approx w1'), H, Hl1, Hl2 in H0.
    apply join_comm; eauto. }
  exists m'; repeat split; auto.
  exists w1', w2; repeat split; auto.
  apply resource_at_join2; auto; try omega.
  intro; rewrite Hr', Hr''.
  apply resource_at_join; auto.
Qed.

Lemma bupd_frame_l: forall P Q, P * bupd Q |-- bupd (P * Q).
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply bupd_frame_r.
Qed.

Lemma bupd_trans: forall P, bupd (bupd P) |-- bupd P.
Proof.
  repeat intro.
  destruct (H _ H0) as (b & J & a' & Hl & Hr & ? & Ha'); subst.
  rewrite <- Hl in J; destruct (Ha' _ J) as (b' & ? & Hm').
  rewrite <- Hl, <- Hr; eauto.
Qed.

Definition ghost_fp_update_ND a B :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
    exists b, B b /\ joins (ghost_fmap (approx n) (approx n) b) c.

Lemma Own_update_ND: forall a B, ghost_fp_update_ND a B ->
  Own a |-- bupd (EX b : _, !!(B b) && Own b).
Proof.
  repeat intro.
  destruct H0 as [Hno Hg]; simpl in *.
  rewrite Hg in H1.
  destruct H1 as [? J].
  destruct (H (level a0) (ghost_approx a0 c)) as (g' & ? & ?).
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

Definition ghost_fp_update (a b : ghost) :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
               joins (ghost_fmap (approx n) (approx n) b) c.

Instance ghost_fp_update_preorder: RelationClasses.PreOrder ghost_fp_update.
Proof.
  split; repeat intro; auto.
Qed.

Lemma ghost_fp_update_approx: forall a b n, ghost_fp_update a b ->
  ghost_fp_update (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) b).
Proof.
  intros; intros m c J.
  rewrite ghost_fmap_fmap in *.
  replace (approx m oo approx n) with (approx (min m n)) in *.
  replace (approx n oo approx m) with (approx (min m n)) in *.
  auto.
  { destruct (Min.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx'_oo_approx | rewrite approx_oo_approx']; auto; omega. }
  { destruct (Min.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx_oo_approx' | rewrite approx'_oo_approx]; auto; omega. }
Qed.

Lemma Own_update: forall a b, ghost_fp_update a b ->
  Own a |-- bupd (Own b).
Proof.
  intros; eapply derives_trans.
  - apply (Own_update_ND a (Ensembles.Singleton _ b)).
    repeat intro.
    exists b; split; auto; constructor.
  - apply bupd_mono.
    apply exp_left; intro.
    apply prop_andp_left; intro X; inv X; auto.
Qed.

Lemma Own_unit: emp |-- EX a : _, !!(identity a) && Own a.
Proof.
  intros w ?; simpl in *.
  exists (ghost_of w); split; [|split].
  - apply ghost_of_identity; auto.
  - intro; apply resource_at_identity; auto.
  - rewrite ghost_of_approx; auto.
Qed.

Definition gname := {I : Type & I * nat}%type.

Definition singleton {A} k (x : A) : finmap A := repeat None k ++ Some x :: nil.

Lemma singleton_get: forall {A} k (x : A) j,
  finmap_get (singleton k x) j = if eq_dec j k then Some x else None.
Proof.
  intros; unfold finmap_get, singleton.
  destruct (eq_dec j k).
  - subst; rewrite app_nth2; rewrite repeat_length; [|omega].
    rewrite minus_diag; auto.
  - destruct (lt_dec j k).
    + rewrite app_nth1 by (rewrite repeat_length; auto).
      apply nth_repeat.
    + rewrite app_nth2; rewrite repeat_length; [|omega].
      destruct (j - k)%nat eqn: Hd; [omega|].
      simpl; apply nth_nil.
Qed.

Program Definition single_ghost {I} {_ : EqDec I} {RAs} {RA} n {H: RAs (fst n) = RA} (a: @G RA) pp :=
  GHOST I RAs (fun j => if eq_dec j (fst n) then
                                singleton (snd n) _ else nil)
         (fun j m => if eq_dec j (fst n) then if eq_dec m (snd n) then Some pp else None else None) _.
Next Obligation.
Proof.
  intros; subst; auto.
Defined.
Next Obligation.
Proof.
  simpl; intros.
  destruct (eq_dec _ _); [|discriminate].
  destruct (eq_dec _ _); inv H1.
  rewrite singleton_get, if_true; eauto.
Qed.

Definition own {RA: Ghost} (n: gname) (a: G) (pp: preds) :=
  match n with existT A n =>
    EX _ : EqDec A, EX RAs : _, EX H : RAs (fst n) = RA, Own (single_ghost(H := H) n a pp) end.

(*Lemma fmap_alloc: forall f a,
  fp_update_ND f (fun g => exists i, finmap_get f i = None /\ g = finmap_set f i a).*)

(* Because the type of the ghost state is existentially quantified in the rmap, inG has to be a
   state predicate instead of a pure assertion. *)
Program Definition inG (RA: Ghost): pred rmap :=
  (fun m => match ghost_of m with GHOST A RAs g _ _ =>
    exists A_eq : EqDec A, exists inG : {i | RAs i = RA}, True end) && emp.
Next Obligation.
  repeat intro.
  subst filtered_var program_branch_0; simpl in *.
  rewrite (age1_ghost_of _ _ H).
  destruct (ghost_of a) eqn: Ha; auto.
Qed.

Lemma skipn_all: forall {A} (n : nat) (l : list A), (length l <= n)%nat -> skipn n l = nil.
Proof.
  induction n; destruct l; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Opaque skipn.

Lemma join_fresh: forall {A} {J: Join A} (m : finmap A) v,
  join (singleton (fresh m) v) m (finmap_set m (fresh m) v).
Proof.
  intros; unfold singleton, finmap_set, fresh; simpl.
  rewrite firstn_all, minus_diag, skipn_all by omega; simpl.
  induction m; simpl; constructor; auto.
  constructor.
Qed.

Lemma ghost_alloc: forall {RA: Ghost} a pp,
  (exists b, joins a b) ->
  inG RA |-- bupd (EX g: gname, own g a pp).
Proof.
  repeat intro; simpl in *.
  destruct H1; inv H1.
  rewrite <- H2 in H0.
  destruct H0 as [(? & [i e] & _) Hemp].
  eexists (ghost_approx (level a0) (GHOST _ RA0 (fun j => match eq_dec j i with
    | left H => singleton (fresh (b j)) ((fun _ _ => _) e H) | _ => nil end)
    (fun j n => if eq_dec j i then if eq_dec n (fresh (b j)) then Some pp
                 else None else None) _)).
  set (g' := ghost_approx _ _).
  split.
  - eexists; constructor.
    + instantiate (1 := fun j => if eq_dec j i then _ else _).
      hnf; intro j.
      destruct (eq_dec _ _); [|constructor].
      apply join_fresh.
    + instantiate (1 := fun j n => if eq_dec j i then if eq_dec n (fresh (b j)) then _ else _ else _).
      intros j n.
      destruct (eq_dec _ _); [|constructor].
      destruct (eq_dec _ _); [|constructor].
      assert (pdsb j n = None) as ->; [|constructor].
      destruct (pdsb j n) eqn: Hj; auto.
      destruct (domb _ _ _ Hj) as [? Hget]; subst j n.
      rewrite fresh_spec in Hget; discriminate.
  - destruct (make_rmap (resource_at a0) g' (rmap_valid a0) (level a0)) as (m' & Hl & Hr & Hg).
    { extensionality; apply resource_at_approx. }
    { subst g'; rewrite ghost_fmap_fmap, !approx_oo_approx; auto. }
    exists m'; repeat split; auto.
    exists (existT _ A (i, fresh (b i))).
    exists _, _, e; split; simpl.
    + intro; rewrite Hr; apply resource_at_identity; auto.
    + rewrite Hl, Hg; subst g'; apply ghost_ext.
      * extensionality j.
        destruct (eq_dec _ _); auto.
        rewrite e0; auto.
      * extensionality j n.
        destruct (eq_dec _ _); subst; auto.
  Unshelve.
  simpl; intros.
  destruct (eq_dec _ _); [|discriminate].
  rewrite singleton_get.
  destruct (eq_dec _ _); inv H0; eauto.
  simpl; intros.
  destruct (eq_dec _ _); [|eauto].
  rewrite finmap_get_set.
  destruct (eq_dec _ _); eauto.
Qed.

Lemma singleton_join: forall {A} {J: Join A} a b c k,
  join (singleton k a) (singleton k b) (singleton k c) <-> join a b c.
Proof.
  unfold singleton; induction k; simpl.
  - split.
    + inversion 1; subst.
      inv H3; auto.
    + repeat constructor; auto.
  - rewrite <- IHk.
    split; [inversion 1 | repeat constructor]; auto.
Qed.

Lemma single_ghost_join: forall I (I_eq : EqDec I) (RAs: I -> Ghost) RA n
  (H : RAs (fst n) = RA) a b c pp, join a b c ->
  join (single_ghost(H := H) n a pp) (single_ghost(H := H) n b pp) (single_ghost(H := H) n c pp).
Proof.
  intros; constructor.
  - intros i.
    destruct (eq_dec _ _); [|constructor].
    apply singleton_join; subst; auto.
  - intros ??; destruct (eq_dec _ _); [|constructor].
    destruct (eq_dec _ _); constructor; auto.
Qed.

Lemma ghost_op: forall {RA: Ghost} g (a1 a2 a3: G) pp,
  join a1 a2 a3 ->
  own g a3 pp = own g a1 pp * own g a2 pp.
Proof.
  intros; apply pred_ext.
  - destruct g.
    repeat (apply exp_left; intro).
    erewrite Own_op by (apply single_ghost_join, H).
    apply sepcon_derives; repeat eapply exp_right; eauto.
  - destruct g.
    intros ? (w1 & w2 & J & (? & ? & ? & ? & Hg1) & (? & ? & ? & ? & Hg2)).
    pose proof (ghost_of_join _ _ _ J) as Jg.
    rewrite Hg1, Hg2 in Jg; inversion Jg.
    repeat inj_pair_tac.
    do 3 eexists.
    erewrite Own_op by (apply single_ghost_join, H).
    exists w1, w2; repeat split; auto.
    + simpl in *.
      rewrite Hg1; apply ghost_ext.
      * extensionality j.
        destruct (eq_dec _ _), (eq_dec _ _); try contradiction; auto.
        replace e with e0 by apply proof_irr; auto.
      * extensionality i n.
        destruct (eq_dec i _), (eq_dec i _); try contradiction; auto.
    + simpl in *.
      rewrite Hg2; apply ghost_ext; auto.
      replace x5 with x2 by apply proof_irr; auto.
Qed.

Lemma singleton_join_inv: forall {A} {J: Join A} k a b c,
  join (singleton k a) (singleton k b) c -> exists c', join a b c' /\ c = singleton k c'.
Proof.
  unfold singleton; induction k; inversion 1; subst.
  - assert (m3 = nil) by (inv H6; auto).
    inv H5; eauto.
  - assert (a3 = None) by (inv H5; auto); subst.
    edestruct IHk as (? & ? & ?); eauto; subst; eauto.
Qed.

Lemma ghost_conflict: forall {RA: Ghost} g (a1 a2: G) pp,
  own g a1 pp * own g a2 pp |-- !!joins a1 a2.
Proof.
  intros.
  destruct g as [? [i]]; intros w (? & ? & J & (? & ? & ? & ? & Hg1) & (? & ? & e1 & ? & Hg2)); simpl.
  apply ghost_of_join in J.
  rewrite Hg1, Hg2 in J; inv J.
  repeat inj_pair_tac.
  specialize (H3 i); simpl in *.
  destruct (eq_dec i i); [|contradiction].
  destruct (eq_dec i i); [|contradiction].
  apply singleton_join_inv in H3 as (? & J & ?); clear - J.
  rewrite (UIP_refl _ _ e), (UIP_refl _ _ e0), (UIP_refl _ _ e1) in J; eauto.
Qed.

Lemma singleton_join_some: forall {A} {J: Join A} k (a b c: A) m
  (Hget: finmap_get m k = Some b) (Hjoin: join a b c),
  join (singleton k a) m (finmap_set m k c).
Proof.
  unfold finmap_get; induction k; intros.
  - destruct m; [rewrite nth_nil in Hget; discriminate|].
    simpl in *; subst; repeat constructor; auto.
  - destruct m; [discriminate|].
    repeat constructor; eapply IHk; eauto.
Qed.

Lemma singleton_join_none: forall {A} {J: Join A} k (a: A) m (Hget: finmap_get m k = None),
  join (singleton k a) m (finmap_set m k a).
Proof.
  unfold finmap_get; induction k; intros.
  - destruct m; simpl in *; subst; repeat constructor.
  - destruct m; repeat constructor; eapply IHk; eauto.
Qed.

Lemma ghost_update_ND: forall {RA: Ghost} g (a: G) B pp,
  fp_update_ND a B -> own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp).
Proof.
  intros.
  destruct g as [? [i n]].
  repeat (apply exp_left; intro).
  eapply derives_trans.
  - apply Own_update_ND with
      (B := fun g => exists b, B b /\ g = @single_ghost _ _ _ _ (i, n) x2 b pp).
    intros ?? [? J].
    inv J; repeat inj_pair_tac.
    pose proof (H6 i) as J.
    apply finmap_get_join with (i0 := n) in J.
    destruct (eq_dec i i); [|contradiction].
    rewrite singleton_get, if_true in J by auto.
    destruct (finmap_get (b0 i) n) eqn: Hb.
    + destruct (finmap_get (c1 i) n); [|contradiction].
      rewrite (UIP_refl _ _ e) in J.
      lapply (H g); eauto.
      intros (b & ? & [g' J']); simpl in *.
      pose proof (singleton_join_some _ _ _ _ _ Hb J').
      do 2 eexists; eauto.
      eexists; constructor; eauto; simpl.
      instantiate (1 := fun j => match eq_dec j i with
        left H => finmap_set (b0 j) n (eq_rect_r (fun j => @G (x1 j)) g' H) | _ => b0 j end).
      intro j; destruct (eq_dec j i); [|constructor].
      subst; auto.
    + lapply (H (core a)); [|eexists; apply join_comm, core_unit].
      intros (b & ? & _).
      do 2 eexists; eauto.
      eexists; constructor; eauto; simpl.
      instantiate (1 := fun j => match eq_dec j i with
        left H => _ | _ => b0 j end).
      intro j; destruct (eq_dec j i); [|constructor].
      apply singleton_join_none; subst; auto.
  - apply bupd_mono.
    apply exp_left; intro; apply prop_andp_left; intros (? & ? & ?); subst.
    eapply exp_right, andp_right; [repeat intro; simpl; eauto|].
    repeat eapply exp_right; auto.
  Unshelve.
  intros j m ??; specialize (H7 j m); simpl in *.
  destruct (eq_dec _ _); [|eapply domb; inv H7; rewrite H2 in *; eauto].
  rewrite finmap_get_set; destruct (eq_dec _ _); eauto.
  eapply domb; inv H7; rewrite H2 in *; eauto.
  intros j m ??; specialize (H7 j m); simpl in *.
  destruct (eq_dec _ _); [|eapply domb; inv H7; rewrite H1 in *; eauto].
  rewrite finmap_get_set; destruct (eq_dec _ _); eauto.
  eapply domb; inv H7; rewrite H1 in *; eauto.
Qed.

Lemma ghost_update: forall {RA: Ghost} g (a b: G) pp,
  fp_update a b -> own g a pp |-- bupd (own g b pp).
Proof.
  intros; eapply derives_trans.
  - apply (ghost_update_ND g a (Ensembles.Singleton _ b)).
    intros ? J; destruct (H _ J).
    do 2 eexists; [constructor | eauto].
  - apply bupd_mono.
    apply exp_left; intro; apply prop_andp_left; intro X; inv X; auto.
Qed.
