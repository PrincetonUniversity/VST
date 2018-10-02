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

(* Ownership construction based on "Iris from the ground up", Jung et al. *)
Program Definition ghost_is g: pred rmap :=
  fun m => ghost_of m = ghost_approx m g.
Next Obligation.
  intros ???? Hg.
  rewrite (age1_ghost_of _ _ H), Hg.
  pose proof (age_level _ _ H).
  rewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx by omega; eauto.
Qed.

Definition Own g: pred rmap := allp noat && ghost_is g.

Lemma Own_op: forall a b c, join a b c -> Own c = Own a * Own b.
Proof.
  intros; apply pred_ext.
  - intros w (Hno & Hg).
    destruct (make_rmap (resource_at w) (ghost_approx w a) (level w))
      as (wa & Hla & Hra & Hga).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    destruct (make_rmap (resource_at w) (ghost_approx w b) (level w))
      as (wb & Hlb & Hrb & Hgb).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    exists wa, wb; split.
    + apply resource_at_join2; auto.
      * intro; rewrite Hra, Hrb.
        apply identity_unit', Hno.
      * rewrite Hg, Hga, Hgb.
        apply ghost_fmap_join; auto.
    + simpl; rewrite Hla, Hlb, Hra, Hrb, Hga, Hgb; simpl; eauto 6.
  - intros w (w1 & w2 & J & (Hnoa & Hga) & (Hnob & Hgb)).
    split.
    + intro l; apply (resource_at_join _ _ _ l) in J.
      simpl in *; rewrite <- (Hnoa _ _ _ J); auto.
    + destruct (join_level _ _ _ J) as [Hl1 Hl2].
      apply ghost_of_join in J.
      rewrite Hga, Hgb in J.
      eapply join_eq; eauto.
      rewrite Hl1, Hl2; apply ghost_fmap_join; auto.
Qed.

Fixpoint make_join (a c : ghost) : ghost :=
  match a, c with
  | nil, _ => c
  | _, nil => nil
  | None :: a', x :: c' => x :: make_join a' c'
  | _ :: a', None :: c' => None :: make_join a' c'
  | Some (ga, pa) :: a', Some (gc, _) :: c' => Some (gc, pa) :: make_join a' c'
  end.

Lemma make_join_nil : forall a, make_join a nil = nil.
Proof.
  destruct a; auto.
  destruct o as [[]|]; auto.
Qed.

Lemma make_join_nil_cons : forall o a c, make_join (o :: a) (None :: c) = None :: make_join a c.
Proof.
  destruct o as [[]|]; auto.
Qed.

Lemma ghost_joins_approx: forall n a c,
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  let c' := make_join a c in
  joins (ghost_fmap (approx (S n)) (approx (S n)) a) (ghost_fmap (approx (S n)) (approx (S n)) c') /\
    forall b, joins b (ghost_fmap (approx (S n)) (approx (S n)) c') ->
      joins (ghost_fmap (approx n) (approx n) b) (ghost_fmap (approx n) (approx n) c).
Proof.
  intros ???; revert a; induction c; intros; subst c'; simpl.
  - rewrite make_join_nil; split.
    + eexists; constructor.
    + eexists; constructor.
  - destruct H; inv H.
    + destruct a0; inv H1.
      split.
      { eexists; constructor. }
      intros ? []; eexists.
      apply ghost_fmap_join with (f := approx n)(g := approx n) in H.
      rewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx in H by auto; eauto.
    + destruct a0; inv H0.
      destruct (IHc a0) as (H & Hc'); eauto.
      inv H3.
      * destruct o; inv H1.
        split.
        { destruct H; eexists; constructor; eauto; constructor. }
        intros ? [? J]; inv J; [eexists; constructor|].
        destruct (Hc' m1); eauto.
        eexists; constructor; eauto.
        instantiate (1 := option_map (fun '(a, b) => (a, preds_fmap (approx n) (approx n) b)) a3).
        inv H3.
        -- destruct a as [[]|]; [simpl | constructor].
           rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor; auto.
        -- destruct a; inv H4; constructor.
        -- destruct a as [[]|]; inv H1; constructor.
           destruct a2, a5; inv H4; constructor; auto; simpl in *.
           inv H2.
           rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor; auto.
      * destruct a; inv H2.
        rewrite make_join_nil_cons.
        split.
        { destruct H; eexists; constructor; eauto; constructor. }
        intros ? [? J]; inv J; [eexists; constructor|].
        destruct (Hc' m1); eauto.
        eexists; constructor; eauto; constructor.
      * destruct o as [[]|], a as [[]|]; inv H0; inv H1.
        split.
        { destruct H.
          destruct a4; inv H2; simpl in *.
          inv H1.
          eexists (Some (_, _) :: _); constructor; eauto; constructor.
          constructor; simpl; eauto; constructor; eauto. }
        intros ? [? J]; inv J; [eexists; constructor|].
        destruct (Hc' m1); eauto.
        eexists; constructor; eauto.
        instantiate (1 := option_map (fun '(a, b) => (a, preds_fmap (approx n) (approx n) b)) a3).
        inv H4.
        -- destruct a4; inv H2; simpl in *.
           inv H3.
           rewrite <- H2, preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor.
        -- constructor.
           destruct a2, a4, a6; inv H2; inv H6; constructor; auto; simpl in *.
           inv H3; inv H4.
           rewrite <- H6, preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor; auto.
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
  destruct (ghost_joins_approx _ _ _ H1) as (J0 & Hc0).
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
  destruct (make_rmap (resource_at a) w' (level a)) as (m' & ? & Hr'' & ?); subst.
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

Lemma bupd_prop : forall P, bupd (!! P) = !! P.
Proof.
  intros ?; apply pred_ext.
  - intros ??; simpl in *.
    destruct (H (core (ghost_of a))) as (? & ? & ? & ? & ? & ? & ?); auto.
    eexists.
    rewrite ghost_core; simpl; erewrite <- ghost_core.
    apply join_comm, core_unit.
  - intros ??.
    do 2 eexists; eauto.
Qed.

Lemma subp_bupd: forall (G : pred nat) (P P' : pred rmap), G |-- P >=> P' ->
    G |-- (bupd P >=> bupd P')%pred.
Proof.
  repeat intro.
  specialize (H3 _ H4) as (? & ? & ? & ? & ? & ? & HP).
  do 2 eexists; eauto; do 2 eexists; eauto; repeat (split; auto).
  pose proof (necR_level _ _ H2).
  apply (H _ H0 x0 ltac:(omega) _ (necR_refl _)); auto.
Qed.

Lemma eqp_bupd: forall (G : pred nat) (P P' : pred rmap), G |-- P <=> P' ->
    G |-- (bupd P <=> bupd P').
Proof.
  intros.
  rewrite fash_and in *.
  apply andp_right; apply subp_bupd; eapply derives_trans; try apply H;
    [apply andp_left1 | apply andp_left2]; apply derives_refl.
Qed.

Definition ghost_fp_update_ND a B :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
    exists b, B b /\ joins (ghost_fmap (approx n) (approx n) b) c.

Lemma Own_update_ND: forall a B, ghost_fp_update_ND a B ->
  Own a |-- bupd (EX b : _, !!(B b) && Own b).
Proof.
  repeat intro.
  destruct H0 as (Hno & Hg).
  rewrite Hg in H1.
  destruct H1 as [? J].
  destruct (H (level a0) (ghost_approx a0 c)) as (g' & ? & J').
  { eexists; eauto. }
  exists (ghost_fmap (approx (level a0)) (approx (level a0)) g'); split; auto.
  destruct (make_rmap (resource_at a0)
    (ghost_fmap (approx (level a0)) (approx (level a0)) g') (level a0))
    as (m' & Hl & Hr & Hg').
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
  exists m'; repeat split; auto.
  exists g'; repeat split; auto.
  - simpl in *; intro; rewrite Hr; auto.
  - simpl; rewrite Hg', Hl; simpl; eauto.
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
  - eapply (Own_update_ND _ (eq _)).
    repeat intro.
    eexists; split; [constructor|].
    apply H; eauto.
  - apply bupd_mono.
    repeat (apply exp_left; intro).
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

Lemma Own_dealloc: forall a, Own a |-- bupd emp.
Proof.
  intros ? w [] ??.
  exists (core ((ghost_approx w) c)); split; [eexists; apply core_unit|].
  destruct (make_rmap (resource_at w) (core (ghost_approx w c)) (level w)) as (w' & ? & Hr & Hg).
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_core; auto. }
  exists w'; repeat split; auto.
  apply all_resource_at_identity.
  - rewrite Hr; auto.
  - rewrite Hg; apply core_identity.
Qed.

Definition singleton {A} k (x : A) : list (option A) := repeat None k ++ Some x :: nil.

Definition gname := nat.

Definition own {RA: Ghost} (n: gname) (a: G) (pp: preds) :=
  EX v : _, Own (singleton n (existT _ RA (exist _ a v), pp)).

Definition list_set {A} (m : list (option A)) k v : list (option A) :=
  firstn k m ++ repeat None (k - length m) ++ Some v :: skipn (S k) m.

Lemma singleton_join_gen: forall k a c (m: ghost)
  (Hjoin: join (Some a) (nth k m None) (Some c)),
  join (singleton k a) m (list_set m k c).
Proof.
  induction k; intros.
  - destruct m; simpl in *; subst; inv Hjoin; constructor; constructor; auto.
  - destruct m; simpl in *.
    + inv Hjoin; constructor.
    + constructor; [constructor | apply IHk; auto].
Qed.

Lemma map_repeat : forall {A B} (f : A -> B) x n, map f (repeat x n) = repeat (f x) n.
Proof.
  induction n; auto; simpl.
  rewrite IHn; auto.
Qed.

Lemma ghost_fmap_singleton: forall f g k v, ghost_fmap f g (singleton k v) =
  singleton k (match v with (a, b) => (a, preds_fmap f g b) end).
Proof.
  intros; unfold ghost_fmap, singleton.
  rewrite map_app, map_repeat; auto.
Qed.

Lemma ghost_fmap_singleton_inv : forall f g a k v,
  ghost_fmap f g a = singleton k v ->
  exists v', a = singleton k v' /\ v = let (a, b) := v' in (a, preds_fmap f g b).
Proof.
  unfold singleton; induction a; simpl; intros.
  - destruct k; discriminate.
  - destruct a as [[]|]; simpl in *.
    + destruct k; inv H.
      destruct a0; inv H2.
      simpl; eauto.
    + destruct k; inv H.
      edestruct IHa as (? & ? & ?); eauto; subst.
      simpl; eauto.
Qed.

Lemma ghost_alloc: forall {RA: Ghost} a pp, ghost.valid a ->
  emp |-- bupd (EX g: gname, own g a pp).
Proof.
  intros.
  eapply derives_trans; [apply Own_unit|].
  apply exp_left; intro g0.
  apply prop_andp_left; intro Hg0.
  eapply derives_trans.
  - apply Own_update_ND with (B := fun b => exists g, b = singleton g (existT _ RA (exist _ _ H), pp)).
    intros ? c [? J]; exists (singleton (length c) (existT _ RA (exist _ _ H), pp)).
    split; eauto.
    rewrite (identity_core Hg0), ghost_core in J; inv J; [|eexists; constructor].
    rewrite ghost_fmap_singleton; eexists; apply singleton_join_gen.
    rewrite nth_overflow by auto; constructor.
  - apply bupd_mono, exp_left; intro g'.
    apply prop_andp_left; intros [g]; subst.
    apply exp_right with g.
    eapply exp_right; eauto.
Qed.

Lemma singleton_join: forall a b c k,
  join (singleton k a) (singleton k b) (singleton k c) <-> join a b c.
Proof.
  unfold singleton; induction k; simpl.
  - split.
    + inversion 1; subst.
      inv H3; auto.
    + intro; do 2 constructor; auto.
  - rewrite <- IHk.
    split; [inversion 1 | repeat constructor]; auto.
Qed.

Lemma singleton_join_inv: forall k a b c,
  join (singleton k a) (singleton k b) c -> exists c', join a b c' /\ c = singleton k c'.
Proof.
  unfold singleton; induction k; inversion 1; subst.
  - assert (m3 = nil) by (inv H6; auto).
    inv H5; eauto.
  - assert (a3 = None) by (inv H5; auto); subst.
    edestruct IHk as (? & ? & ?); eauto; subst; eauto.
Qed.

Lemma ghost_valid_2: forall {RA: Ghost} g a1 a2 pp,
  own g a1 pp * own g a2 pp |-- !!ghost.valid_2 a1 a2.
Proof.
  intros.
  intros w (? & ? & J%ghost_of_join & (? & ? & Hg1) & (? & ? & Hg2)).
  rewrite Hg1, Hg2, !ghost_fmap_singleton in J.
  apply singleton_join_inv in J as ([] & J & ?).
  inv J; simpl in *.
  inv H2; repeat inj_pair_tac.
  eexists; eauto.
Qed.

Lemma ghost_op: forall {RA: Ghost} g (a1 a2 a3: G) pp, join a1 a2 a3 ->
  own g a3 pp = own g a1 pp * own g a2 pp.
Proof.
  intros; apply pred_ext.
  - apply exp_left; intro.
    erewrite Own_op; [apply sepcon_derives; eapply exp_right; eauto|].
    apply singleton_join; constructor; constructor; auto.
  - eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
    apply prop_andp_left; intros (? & J & ?).
    eapply join_eq in H; eauto; subst.
    unfold own; rewrite exp_sepcon1; apply exp_left; intro.
    rewrite exp_sepcon2; apply exp_left; intro.
    erewrite <- Own_op; [eapply exp_right; eauto|].
    apply singleton_join; constructor; constructor; auto.
  Unshelve.
  eapply join_valid; eauto.
  eapply join_valid; eauto.
  auto.
Qed.

Lemma ghost_valid: forall {RA: Ghost} g a pp,
  own g a pp |-- !!ghost.valid a.
Proof.
  intros.
  rewrite <- (normalize.andp_TT (!!_)).
  erewrite ghost_op by apply core_unit.
  eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
  apply prop_andp_left; intros (? & J & ?); apply prop_andp_right; auto.
  apply core_identity in J; subst; auto.
Qed.

Lemma singleton_join_inv_gen: forall k a (b c: ghost),
  join (singleton k a) b c ->
  join (Some a) (nth k b None) (nth k c None) /\
    exists c', nth k c None = Some c' /\ c = list_set b k c'.
Proof.
  unfold singleton; induction k; inversion 1; subst; auto.
  - split; simpl; eauto; constructor.
  - split; auto.
    unfold list_set; simpl.
    rewrite <- (ghost_core m2) in H5.
    apply (core_identity m2) in H5; subst.
    inv H2; eauto.
  - rewrite app_nth2; rewrite repeat_length; auto.
    rewrite minus_diag; split; [constructor | simpl; eauto].
  - assert (a2 = a3) by (inv H2; auto).
    destruct (IHk _ _ _ H5) as (? & ? & ? & ?); subst; eauto.
Qed.

Lemma ghost_update_ND: forall {RA: Ghost} g (a: G) B pp,
  fp_update_ND a B -> own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp).
Proof.
  intros.
  apply exp_left; intro Hva.
  eapply derives_trans.
  - apply Own_update_ND with
      (B := fun b => exists b' Hvb, B b' /\ b = singleton g (existT _ RA (exist _ b' Hvb), pp)).
    intros ?? [? J].
    rewrite ghost_fmap_singleton in J.
    destruct (singleton_join_inv_gen _ _ _ _ J) as [Jg _].
    inv Jg.
    + destruct (H (core a)) as (b & ? & Hv).
      { eexists; split; [apply join_comm, core_unit | auto]. }
      assert (ghost.valid b) as Hvb.
      { destruct Hv as (? & ? & ?); eapply join_valid; eauto. }
      exists (singleton g (existT _ RA (exist _ _ Hvb), pp)); split; eauto.
      rewrite ghost_fmap_singleton.
      eexists; apply singleton_join_gen.
      rewrite <- H2; constructor.
    + destruct a2, a3; inv H3; simpl in *.
      inv H0; inj_pair_tac.
      destruct (H b0) as (b & ? & Hv).
      { eexists; eauto. }
      destruct Hv as (? & ? & ?).
      assert (ghost.valid b) as Hvb by (eapply join_valid; eauto).
      exists (singleton g (existT _ RA (exist _ _ Hvb), pp)); split; eauto.
      rewrite ghost_fmap_singleton.
      eexists; apply singleton_join_gen.
      instantiate (1 := (_, _)).
      rewrite <- H1; constructor; constructor; [constructor|]; eauto.
  - apply bupd_mono, exp_left; intro.
    apply prop_andp_left; intros (b & ? & ? & ?); subst.
    apply exp_right with b, prop_andp_right; auto.
    eapply exp_right; auto.
  Unshelve.
  auto.
Qed.

Lemma ghost_update: forall {RA: Ghost} g (a b: G) pp,
  fp_update a b -> own g a pp |-- bupd (own g b pp).
Proof.
  intros; eapply derives_trans.
  - apply (ghost_update_ND g a (eq b)).
    intros ? J; destruct (H _ J).
    do 2 eexists; [constructor | eauto].
  - apply bupd_mono.
    apply exp_left; intro; apply prop_andp_left; intro X; inv X; auto.
Qed.

Lemma ghost_dealloc: forall {RA: Ghost} g a pp,
  own g a pp |-- bupd emp.
Proof.
  intros; unfold own.
  apply exp_left; intro; apply Own_dealloc.
Qed.

Lemma list_set_same : forall {A} n l (a : A), nth n l None = Some a ->
  list_set l n a = l.
Proof.
  unfold list_set; induction n; destruct l; simpl; try discriminate; intros; subst; auto.
  f_equal; eauto.
Qed.

(* The addition of ghost state means that there are rmaps that have only
   cores for ghost state, but are not cores themselves (since they have ghost
   state at all). An rmap of this sort is not emp, but is its own unit. *)

Definition cored: pred rmap := ALL P : pred rmap, ALL Q : pred rmap,
  P && Q --> P * Q.

Program Definition is_w w: pred rmap := fun w' => necR w w'.
Next Obligation.
Proof.
  repeat intro.
  eapply necR_trans; eauto.
  constructor; auto.
Qed.

Lemma cored_unit: forall w, cored w = join w w w.
Proof.
  intro; apply prop_ext; split; unfold cored; intro.
  - edestruct (H (is_w w) (is_w w)) as (? & ? & J & Hw1 & Hw2).
    { apply necR_refl. }
    { split; apply necR_refl. }
    simpl in *.
    destruct (join_level _ _ _ J).
    eapply necR_linear' in Hw1; try apply necR_refl; auto.
    eapply necR_linear' in Hw2; try apply necR_refl; auto.
    subst; auto.
  - intros P Q ?? [HP HQ].
    exists a', a'; repeat split; auto.
    eapply nec_join in H as (? & ? & ? & Hw1 & Hw2); eauto.
    destruct (join_level _ _ _ H).
    eapply necR_linear' in Hw1; try apply H0; [|omega].
    eapply necR_linear' in Hw2; try apply H0; [|omega].
    subst; auto.
Qed.

Lemma cored_dup: forall P, P && cored |-- (P && cored) * (P && cored).
Proof.
  intros.
  rewrite <- (andp_dup cored) at 1.
  rewrite <- andp_assoc.
  intros; unfold cored at 2.
  eapply modus_ponens.
  + apply andp_left1, derives_refl.
  + eapply andp_left2, allp_left, allp_left.
    rewrite andp_dup; apply derives_refl.
Qed.

Lemma cored_core: forall w, cored (core w).
Proof.
  intro; rewrite cored_unit.
  apply identity_unit', core_identity.
Qed.

Lemma cored_duplicable: cored = cored * cored.
Proof.
  apply pred_ext.
  - rewrite <- andp_dup at 1.
    eapply derives_trans; [apply cored_dup|].
    apply sepcon_derives; apply andp_left1; auto.
  - intros ? (? & ? & J & J1 & J2).
    rewrite cored_unit in *.
    destruct (join_assoc J1 J) as (? & J' & J1').
    eapply join_eq in J'; [|apply J]; subst.
    destruct (join_assoc J2 (join_comm J)) as (? & J' & J2').
    eapply join_eq in J'; [|apply join_comm, J]; subst.
    destruct (join_assoc (join_comm J1') (join_comm J2')) as (? & J' & ?).
    eapply join_eq in J'; [|apply J]; subst; auto.
Qed.

Lemma cored_emp: cored |-- bupd emp.
Proof.
  intro; rewrite cored_unit; intros J ??.
  exists nil; split; [eexists; constructor|].
  destruct (make_rmap (resource_at a) nil (level a)) as (m' & ? & Hr & Hg); auto.
  { intros; extensionality; apply resource_at_approx. }
  exists m'; repeat split; auto.
  apply all_resource_at_identity.
  - intro; rewrite Hr.
    apply (resource_at_join _ _ _ l) in J.
    inv J.
    + apply join_self, identity_share_bot in RJ; subst.
      apply NO_identity.
    + apply join_self, identity_share_bot in RJ; subst.
      contradiction shares.bot_unreadable.
    + apply PURE_identity.
  - rewrite Hg, <- (ghost_core nil); apply core_identity.
Qed.

Lemma join_singleton_inv: forall k a b RA c v pp,
  join a b (singleton k (existT _ RA (exist _ (core c) v), pp)) ->
  a = singleton k (existT _ RA (exist _ (core c) v), pp) \/ b = singleton k (existT _ RA (exist _ (core c) v), pp).
Proof.
  induction k; unfold singleton; intros; simpl in *.
  - inv H; auto.
    assert (m1 = nil /\ m2 = nil) as [] by (inv H5; auto); subst.
    inv H4; auto.
    destruct a0, a3; inv H2; simpl in *.
    inv H0; inv H.
    inj_pair_tac.
    pose proof (core_unit a0) as J.
    erewrite join_core, core_idem in J by eauto.
    unfold unit_for in J.
    eapply join_positivity in J; eauto; subst.
    left; repeat f_equal; apply proof_irr.
  - inv H; auto.
    edestruct IHk as [|]; eauto; [left | right]; f_equal; auto; inv H4; auto.
Qed.

Lemma own_cored: forall {RA: Ghost} g a pp, join a a a -> own g a pp |-- cored.
Proof.
  intros; intros ? (? & ? & Hg).
  rewrite cored_unit; simpl in *.
  apply resource_at_join2; auto.
  - intro; apply identity_unit'.
    eapply necR_resource_at_identity; eauto.
  - rewrite Hg, ghost_fmap_singleton.
    apply singleton_join; repeat constructor; auto.
Qed.

Require Import VST.veric.tycontext.
Require Import VST.veric.Clight_seplog.
 
Lemma own_super_non_expansive: forall {RA: Ghost} n g a pp,
  approx n (own g a pp) = approx n (own g a (preds_fmap (approx n) (approx n) pp)).
Proof.
  intros; unfold own.
  rewrite !approx_exp; f_equal; extensionality v.
  unfold Own.
  rewrite !approx_andp; f_equal.
  apply pred_ext; intros ? [? Hg]; split; auto; simpl in *.
  - rewrite <- ghost_of_approx, Hg.
    rewrite !ghost_fmap_singleton, !preds_fmap_fmap.
    rewrite approx_oo_approx, approx_oo_approx', approx'_oo_approx by omega; auto.
  - rewrite ghost_fmap_singleton in *.
    rewrite preds_fmap_fmap in Hg.
    rewrite approx_oo_approx', approx'_oo_approx in Hg by omega; auto.
Qed.
