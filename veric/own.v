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
  fun m => join_sub (ghost_approx m g) (ghost_of m).
Next Obligation.
  split; intros ??? J.
  - rewrite (age1_ghost_of _ _ H).
    destruct J as [? J].
    eapply ghost_fmap_join in J.
    assert (level a >= level a')%nat as Hl by (apply age_level in H; lia).
    erewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx in J by apply Hl.
    eexists; eauto.
  - apply rmap_order in H as (? & _ & J').
    eapply join_sub_trans; eauto.
    rewrite <- H; auto.
Qed.

Definition Own g: pred rmap := allp noat && ghost_is g.

Lemma Own_op: forall a b c, join a b c -> Own c = Own a * Own b.
Proof.
  intros; apply pred_ext.
  - intros w (Hno & [? J]).
    eapply ghost_fmap_join in H.
    destruct (join_assoc H J) as (b' & J1 & J2).
    eapply ghost_fmap_join in J1; rewrite ghost_fmap_fmap, 2approx_oo_approx in J1.
    eapply ghost_fmap_join in J2; rewrite ghost_fmap_fmap, 2approx_oo_approx, ghost_of_approx in J2.
    destruct (make_rmap (resource_at w) (ghost_approx w a) (level w))
      as (wa & Hla & Hra & Hga).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    destruct (make_rmap (resource_at w) (ghost_approx w b') (level w))
      as (wb & Hlb & Hrb & Hgb).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    exists wa, wb; split.
    + apply resource_at_join2; auto.
      * intro; rewrite Hra, Hrb.
        apply identity_unit', Hno.
      * rewrite Hga, Hgb; auto.
    + simpl; rewrite Hla, Hlb, Hra, Hrb, Hga, Hgb; simpl.
      repeat split; auto.
      * apply join_sub_refl.
      * eexists; eauto.
  - intros w (w1 & w2 & J & (Hnoa & Hga) & (Hnob & Hgb)).
    split.
    + intro l; apply (resource_at_join _ _ _ l) in J.
      simpl in *; rewrite <- (Hnoa _ _ _ J); auto.
    + destruct (join_level _ _ _ J) as [Hl1 Hl2].
      apply ghost_of_join in J.
      destruct Hga as [? Ja], Hgb as [? Jb].
      destruct (join_assoc (join_comm Ja) J) as (? & Ja' & J').
      destruct (join_assoc (join_comm Jb) (join_comm Ja')) as (? & Jc & J'').
      rewrite Hl1, Hl2 in Jc.
      eapply ghost_fmap_join, join_eq in H; [|apply join_comm, Jc]; subst.
      destruct (join_assoc (join_comm J'') (join_comm J')) as (? & ? & ?).
      eexists; eauto.
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
  split; repeat intro.
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
  + eapply pred_hereditary; eauto.
  + apply rmap_order in H as (Hl & Hr & [? J]).
    destruct H1 as [d J'].
    destruct (join_assoc J J') as (c' & ? & Jc').
    eapply ghost_fmap_join in Jc'; rewrite ghost_of_approx in Jc'.
    destruct (H0 c') as (? & Jm' & m' & ? & ? & ? & ?); eauto; subst.
    do 2 eexists; [|exists m'; repeat split; eauto; congruence].
    eapply join_sub_joins'; eauto.
    { apply join_sub_refl. }
    eapply ghost_fmap_join in H; rewrite ghost_fmap_fmap, 2approx_oo_approx in H.
    rewrite Hl; eexists; eauto.
Qed.

Lemma bupd_intro: forall P, P |-- bupd P.
Proof.
  repeat intro; eauto 7.
Qed.

Lemma bupd_mono: forall P Q, (P |-- Q) -> bupd P |-- bupd Q.
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
  apply resource_at_join2; auto; try lia.
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

Lemma joins_approx_core : forall a, joins (ghost_of a) (ghost_approx a (core (ghost_of a))).
Proof.
  intros; eexists.
  rewrite <- ghost_of_approx at 1; apply ghost_fmap_join.
  apply join_comm, core_unit.
Qed.

Lemma bupd_prop : forall P, bupd (!! P) = !! P.
Proof.
  intros ?; apply pred_ext.
  - intros ??; simpl in *.
    destruct (H _ (joins_approx_core _)) as (? & ? & ? & ? & ? & ? & ?); auto.
  - intros ??.
    do 2 eexists; eauto.
Qed.

Lemma corable_resource_at : forall P, corable P ->
  forall a b, level a = level b -> resource_at a = resource_at b -> P a -> P b.
Proof.
  intros.
  apply (H (id_core a)); [eapply H; eauto|].
  - right; left; eexists; apply id_core_unit.
  - left. exists b.
    apply resource_at_join2; auto.
    + rewrite id_core_level; auto.
    + intros; rewrite id_core_resource.
      rewrite <- core_resource_at, H1; apply core_unit.
    + rewrite id_core_ghost; constructor.
Qed.

Lemma bupd_andp_corable : forall P Q, corable P -> bupd (P && Q) = P && bupd Q.
Proof.
  intros; apply pred_ext.
  - intros ??; simpl in *.
    split.
    + destruct (H0 _ (joins_approx_core _)) as (? & ? & ? & ? & ? & ? & ? & ?); auto.
      eapply corable_resource_at; eauto.
    + intros ? J; destruct (H0 _ J) as (? & ? & m & ? & ? & ? & ? & ?).
      do 2 eexists; eauto.
  - intros ? [? HQ] ? J.
    destruct (HQ _ J) as (? & ? & m & ? & ? & ? & ?).
    do 2 eexists; eauto.
    do 2 eexists; eauto.
    repeat split; auto.
    eapply corable_resource_at, H0; auto.
Qed.

Lemma bupd_andp_prop : forall P Q, bupd (!! P && Q) = !! P && bupd Q.
Proof.
  intros; apply bupd_andp_corable, corable_prop.
Qed.

Lemma subp_bupd: forall (G : pred nat) (P P' : pred rmap), (G |-- P >=> P') ->
    G |-- (bupd P >=> bupd P')%pred.
Proof.
  repeat intro.
  specialize (H4 _ H5) as (? & ? & ? & ? & ? & ? & HP).
  do 2 eexists; eauto; do 2 eexists; eauto; repeat (split; auto).
  eapply H; try apply ext_refl; try apply necR_refl; eauto.
  apply necR_level in H2; apply ext_level in H3; lia.
Qed.

Lemma eqp_bupd: forall (G : pred nat) (P P' : pred rmap), (G |-- P <=> P') ->
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
  unfold ghost_fp_update_ND; repeat intro.
  destruct H0 as (Hno & J).
  eapply join_sub_joins_trans in H1; eauto; [|apply J].
  apply H in H1 as (g' & ? & J').
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
    apply join_sub_refl.
Qed.

Definition ghost_fp_update (a b : ghost) :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
               joins (ghost_fmap (approx n) (approx n) b) c.

#[export] Instance ghost_fp_update_preorder: RelationClasses.PreOrder ghost_fp_update.
Proof.
  split; repeat intro; auto.
Qed.

Lemma ghost_fp_update_approx: forall a b n, ghost_fp_update a b ->
  ghost_fp_update (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) b).
Proof.
  intros; intros m c J.
  rewrite ghost_fmap_fmap in *.
  replace (approx m oo approx n) with (approx (Nat.min m n)) in *.
  replace (approx n oo approx m) with (approx (Nat.min m n)) in *.
  auto.
  { destruct (Nat.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx'_oo_approx | rewrite approx_oo_approx']; auto; lia. }
  { destruct (Nat.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx_oo_approx' | rewrite approx'_oo_approx]; auto; lia. }
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
  intros w Hemp.
  assert (forall l, identity (w @ l)).
  { rewrite emp_no in Hemp; auto. }
  destruct Hemp as (e & ? & Hext).
  exists (ghost_of e); split; [|split; auto].
  - apply ghost_of_identity; auto.
  - apply rmap_order in Hext as (? & ? & []).
    eexists.
    rewrite <- (ghost_of_approx w).
    apply ghost_fmap_join; eauto.
Qed.

Lemma Own_dealloc: forall a, Own a |-- emp.
Proof.
  rewrite emp_no.
  intros; apply andp_left1; auto.
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

Import ListNotations.
Fixpoint uptoN (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => uptoN n' ++ [n']
  end.

Lemma In_uptoN : forall m n, (m < n)%nat -> In m (uptoN n).
Proof.
  induction n; intros; [lia | simpl].
  rewrite in_app; destruct (lt_dec m n); auto.
  right; simpl; lia.
Qed.

Lemma ghost_alloc_strong: forall {RA: Ghost} P a pp, pred_infinite P -> ghost.valid a ->
  emp |-- bupd (EX g, !!(P g) && own g a pp).
Proof.
  intros.
  eapply derives_trans; [apply Own_unit|].
  apply exp_left; intro g0.
  apply prop_andp_left; intro Hg0.
  eapply derives_trans.
  - apply Own_update_ND with (B := fun b => exists g, P g /\ b = singleton g (existT _ RA (exist _ _ H0), pp)).
    intros ? c [? J].
    destruct (H (uptoN (length c))) as (g & ? & ?).
    exists (singleton g (existT _ RA (exist _ _ H0), pp)).
    split; eauto.
    apply ghost_identity in Hg0; subst.
    assert (x = c) by (inv J; auto); subst.
    rewrite ghost_fmap_singleton; eexists; apply singleton_join_gen.
    rewrite nth_overflow; [constructor|].
    destruct (lt_dec g (length c)); [|lia].
    apply In_uptoN in l; contradiction.
  - apply bupd_mono, exp_left; intro g'.
    apply prop_andp_left; intros (g & ? & ?); subst.
    apply exp_right with g.
    apply prop_andp_right; auto.
    eapply exp_right; eauto.
Qed.

Lemma list_max : forall x (l : list nat), In x l -> (x <= fold_right max O l)%nat.
Proof.
  induction l; [contradiction | simpl; intros].
  destruct H.
  - subst.
    apply Nat.le_max_l.
  - etransitivity; [apply IHl; auto|].
    apply Nat.le_max_r.
Qed.

Lemma fresh_nat: forall (l : list nat), exists n, ~In n l.
Proof.
  intros; exists (S (fold_right max O l)).
  intros X%list_max; lia.
Qed.

Lemma ghost_alloc: forall {RA: Ghost} a pp, ghost.valid a ->
  emp |-- bupd (EX g, own g a pp).
Proof.
  intros.
  eapply derives_trans; [apply (ghost_alloc_strong (fun _ => True)); eauto|].
  { intros ?.
    destruct (fresh_nat l); eauto. }
  apply bupd_mono.
  apply exp_left; intros g.
  apply exp_right with g.
  apply andp_left2; auto.
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
  intros w (? & ? & J%ghost_of_join & (? & ? & [? J1]) & (? & ? & [? J2])).
  destruct (join_assoc (join_comm J1) J) as (? & J1' & ?).
  destruct (join_assoc (join_comm J2) (join_comm J1')) as (? & J' & ?).
  rewrite !ghost_fmap_singleton in J'.
  apply singleton_join_inv in J' as ([] & J' & ?).
  inv J'; simpl in *.
  inv H4; repeat inj_pair_tac.
  eexists; eauto.
Qed.

Lemma ghost_op: forall {RA: Ghost} g (a1 a2 a3: G) pp, join a1 a2 a3 ->
  own g a3 pp = own g a1 pp * own g a2 pp.
Proof.
  intros; apply pred_ext.
  - apply exp_left; intro.
    erewrite Own_op; [apply sepcon_derives; eapply exp_right; eauto|].
    instantiate (1 := join_valid _ _ _ (join_comm H) x).
    instantiate (1 := join_valid _ _ _ H x).
    apply singleton_join; constructor; constructor; auto.
  - eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
    apply prop_andp_left; intros (? & J & ?).
    eapply join_eq in H; eauto; subst.
    unfold own; rewrite exp_sepcon1; apply exp_left; intro.
    rewrite exp_sepcon2; apply exp_left; intro.
    erewrite <- Own_op; [eapply exp_right; eauto|].
    instantiate (1 := H0).
    apply singleton_join; constructor; constructor; auto.
Qed.

Lemma ghost_valid: forall {RA: Ghost} g a pp,
  own g a pp |-- !!ghost.valid a.
Proof.
  intros.
  rewrite <- (normalize.andp_TT (!!_)).
  erewrite ghost_op by apply core_unit.
  eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
  apply prop_andp_left; intros (? & J & ?); apply prop_andp_right; auto.
  assert (x = a) as <-; auto.
  eapply join_eq, core_unit; assumption.
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
    assert (m2 = m3) by (inv H5; auto).
    inv H2; eauto.
  - rewrite app_nth2; rewrite repeat_length; auto.
    rewrite Nat.sub_diag; split; [constructor | simpl; eauto].
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
      Unshelve. auto.
  - apply bupd_mono, exp_left; intro.
    apply prop_andp_left; intros (b & ? & ? & ?); subst.
    apply exp_right with b, prop_andp_right; auto.
    eapply exp_right; auto.
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
  own g a pp |-- emp.
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

Lemma map_firstn : forall {A B} (f : A -> B) (l : list A) n,
  map f (firstn n l) = firstn n (map f l).
Proof.
  induction l; destruct n; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma map_skipn : forall {A B} (f : A -> B) (l : list A) n,
  map f (skipn n l) = skipn n (map f l).
Proof.
  induction l; destruct n; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma list_set_set : forall {A} n l (a b : A), (n <= length l)%nat ->
  list_set (list_set l n a) n b = list_set l n b.
Proof.
  intros; unfold list_set.
  rewrite (proj2 (Nat.sub_0_le _ _) H).
  rewrite !app_length, !skipn_app, firstn_app, firstn_length, min_l, Nat.sub_diag, app_nil_r, repeat_length by auto.
  rewrite firstn_firstn, min_l by auto; f_equal.
  unfold length; setoid_rewrite skipn_length; f_equal.
  - f_equal. lia.
  - rewrite skipn_all2, skipn_nil, Nat.sub_0_r; [|rewrite firstn_length; lia].
    rewrite (Nat.add_sub 1); auto.
Qed.

Lemma nth_list_set : forall {A} n l (a : A) d, nth n (list_set l n a) d = Some a.
Proof.
  intros; unfold list_set.
  rewrite 2app_nth2; rewrite ?repeat_length, ?firstn_length; try lia.
  match goal with |- nth ?n _ _ = _ => replace n with O by lia end; auto.
Qed.

Lemma own_core : forall {RA: Ghost} g (a : G) pp,
  a = core a -> forall w, own g a pp w -> own g a pp (core w).
Proof.
  unfold own, Own, ghost_is; intros; simpl in *.
  destruct H0 as (Hv & _ & ? & J).
  exists Hv; split; auto.
  - intros ?; apply resource_at_core_identity.
  - rewrite ghost_of_core.
    rewrite ghost_fmap_singleton in J.
    apply singleton_join_inv_gen in J as (J & ((?, (?, ?)), ?) & Hg & Hw).
    rewrite Hg in J.
    rewrite Hw, ghost_core_eq.
    unfold list_set; rewrite !map_app, map_firstn, map_repeat.
    unfold map at 2; setoid_rewrite map_skipn.
    rewrite ghost_fmap_singleton; simpl Datatypes.option_map.
    erewrite <- map_length.
    rewrite level_core.
    inv J.
    + inj_pair_tac.
      eexists; apply singleton_join_gen.
      setoid_rewrite (map_nth _ _ None). rewrite <- H2.
      match goal with |- join ?a _ ?c => assert (a = c) as ->; [|constructor] end.
      do 3 f_equal. apply exist_ext; auto.
    + destruct a2, H3 as [J ?].
      inv J.
      repeat inj_pair_tac.
      apply join_core_sub in H5 as [].
      setoid_rewrite <- list_set_set.
      eexists; apply singleton_join_gen.
      rewrite nth_list_set.
      instantiate (1 := (_, _)).
      constructor. split; simpl in *; [|split; auto].
      constructor. rewrite H; eauto.
      Unshelve.
      * inv H0; auto.
      * rewrite map_length.
        destruct (le_dec (length x) g); [|lia].
        rewrite nth_overflow in H1 by auto; discriminate.
      * apply join_comm, join_valid in H2; auto.
        apply core_valid; auto.
Qed.
