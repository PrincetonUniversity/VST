(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Local Open Scope nat_scope.

Require Import VST.msl.ageable.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_sl.
Require Import VST.msl.knot_full_variant.

Module Type KNOT_FULL_BASIC_INPUT.
  Import MixVariantFunctor.
  Parameter F: functor.

  Parameter Rel : forall A, relation (F A).

  Parameter Rel_fmap : forall A B (f1: A->B) (f2:B->A) x y,
    Rel A x y ->
    Rel B (fmap F f1 f2 x) (fmap F f1 f2 y).
  Axiom Rel_refl : forall A x, Rel A x x.
  Axiom Rel_trans : forall A x y z,
    Rel A x y -> Rel A y z -> Rel A x z.

End KNOT_FULL_BASIC_INPUT.

Module Type KNOT_FULL_SA_INPUT.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
  Import MixVariantFunctor.
  Import KI.

  Parameter Join_F: forall A, Join (F A). #[global] Existing Instance Join_F.
  Parameter paf_F : pafunctor F Join_F.
  Parameter Perm_F: forall A, Perm_alg (F A).
  Parameter Sep_F: forall A, Sep_alg (F A).

  Axiom Rel_join_commut : forall {A} {x y z z' : F A}, join x y z ->
    Rel A z z' -> exists x', Rel A x x' /\ join x' y z'.
  Axiom join_Rel_commut : forall {A} {x x' y' z' : F A}, Rel A x x' ->
    join x' y' z' -> exists z, join x y' z /\ Rel A z z'.
  Axiom id_exists : forall {A} (x : F A), exists e,
    identity e /\ unit_for e x.

End KNOT_FULL_SA_INPUT.

Module Type KNOT_BASIC.
  Declare Module KI:KNOT_FULL_BASIC_INPUT.
  Import MixVariantFunctor.
  Import KI.
  Parameter knot: Type.
  Parameter ageable_knot : ageable knot.
  #[global] Existing Instance ageable_knot.

  Parameter predicate: Type.
  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).
  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.

  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

  Parameter ext_knot : Ext_ord knot.
  #[export] Existing Instance ext_knot.

  Axiom knot_order : forall k1 k2 : knot, ext_order k1 k2 <->
    level k1 = level k2 /\ Rel predicate (snd (unsquash k1)) (snd (unsquash k2)).

End KNOT_BASIC.

Module Type KNOT_BASIC_LEMMAS.

  Declare Module K: KNOT_BASIC.
  Import MixVariantFunctor.
  Import K.KI.
  Import K.

  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.

  Axiom unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap F (approx n) (approx n) Fp.
  Arguments unsquash_approx [k n Fp] _.

  Axiom approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).

  Axiom approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.

End KNOT_BASIC_LEMMAS.

Module Type KNOT_ASSM.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
  Declare Module KSAI: KNOT_FULL_SA_INPUT with Module KI := KI.
  Declare Module K: KNOT_BASIC with Module KI := KI.
  Import MixVariantFunctor.
  Import KI.
  Import KSAI.
  Import K.

  Axiom approx_core : forall n (f : F predicate),
    core(Sep_alg := Sep_F predicate) (fmap F (approx n) (approx n) f) = fmap F (approx n) (approx n) (core(Sep_alg := Sep_F predicate) f).

End KNOT_ASSM.


Module Type KNOT_FULL_SA.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
  Declare Module KSAI: KNOT_FULL_SA_INPUT with Module KI := KI.
  Declare Module K: KNOT_BASIC with Module KI := KI.
  Declare Module KL: KNOT_BASIC_LEMMAS with Module K := K.
  Declare Module KA: KNOT_ASSM with Module KI := KI with Module KSAI := KSAI with Module K := K.

  Import KI.
  Import KSAI.
  Import K.
  Import KL.
  Import KA.

  Parameter Join_knot: Join knot.  #[global] Existing Instance Join_knot.
  Parameter Perm_knot : Perm_alg knot.  #[global] Existing Instance Perm_knot.
  Parameter Sep_knot : Sep_alg knot.  #[global] Existing Instance Sep_knot.
  #[global] Instance Join_nat_F: Join (nat * F predicate) :=
       Join_prod nat  (Join_equiv nat) (F predicate) _.
  #[global] Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
    @Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F _).
  #[global] Instance Sep_nat_F : Sep_alg (nat * F predicate) :=
    @Sep_prod nat _ _ _ _ (Perm_F predicate) (fsep_sep (Sep_equiv _)) (Sep_F predicate).

  Axiom join_unsquash : forall x1 x2 x3 : knot,
    join x1 x2 x3 = join (unsquash x1) (unsquash x2) (unsquash x3).
  Axiom core_unsquash : forall x, core x = squash (core (unsquash x)).

  Axiom asa_knot : Age_alg knot.

  Axiom ea_knot : Ext_alg knot.

End KNOT_FULL_SA.

Module KnotFullSa
  (KSAI': KNOT_FULL_SA_INPUT)
  (K': KNOT_BASIC with Module KI:=KSAI'.KI)
  (KL': KNOT_BASIC_LEMMAS with Module K:=K')
  (KA': KNOT_ASSM with Module KI := KSAI'.KI with Module KSAI := KSAI' with Module K := K'):
  KNOT_FULL_SA with Module KI := KSAI'.KI
               with Module KSAI := KSAI'
               with Module K:=K'
               with Module KL := KL'
               with Module KA := KA'.

  Module KI := KSAI'.KI.
  Module KSAI := KSAI'.
  Module K := K'.
  Module KL := KL'.
  Module KA := KA'.

  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import KI.
  Import KSAI.
  Import K.
  Import KL.
  Import KA.

  #[global] Instance Join_nat_F: Join (nat * F predicate) :=
       Join_prod nat  (Join_equiv nat) (F predicate) _.
  #[global] Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
      @Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F _).
  #[global] Instance Sep_nat_F : Sep_alg (nat * F predicate) :=
    @Sep_prod nat _ _ _ _ (Perm_F predicate) (fsep_sep (Sep_equiv _)) (Sep_F predicate).

  Lemma unsquash_squash_join_hom : join_hom (unsquash oo squash).
  Proof.
    unfold compose.
    intros [x1 x2] [y1 y2] [z1 z2] ?.
    do 3 rewrite (unsquash_squash).
    firstorder.
    simpl in *.
    subst y1.
    subst z1.
    apply (paf_join_hom paf_F); auto.
  Qed.

  #[global] Instance Join_knot : Join knot :=
           Join_preimage knot (nat * F predicate) Join_nat_F unsquash.

  Lemma join_unsquash : forall x1 x2 x3,
    join x1 x2 x3 =
    join (unsquash x1) (unsquash x2) (unsquash x3).
  Proof.
    intuition.
  Qed.

  #[global] Instance Perm_knot : Perm_alg knot :=
    Perm_preimage _ _ _ _ unsquash squash squash_unsquash unsquash_squash_join_hom.

  Lemma core_unsquash_squash : forall b, core (unsquash (squash b)) = unsquash (squash (core b)).
  Proof.
    intros (?, ?); simpl; rewrite !unsquash_squash; simpl.
    pose proof approx_core n _f.
    setoid_rewrite approx_core. reflexivity.
  Qed.

  #[global] Instance Sep_knot: Sep_alg knot :=
    Sep_preimage _ _ _ _ unsquash squash squash_unsquash unsquash_squash_join_hom core_unsquash_squash.

  Lemma core_unsquash : forall x, core x = squash (core (unsquash x)).
  Proof.
    auto.
  Qed.

  Lemma age_join1 :
    forall x y z x' : K'.knot,
      join x y z ->
      age x x' ->
      exists y' : K'.knot,
        exists z' : K'.knot, join x' y' z' /\ age y y' /\ age z z'.
  Proof.
    intros.
    unfold age in *; simpl in *.
    rewrite knot_age1 in H0.
    repeat rewrite knot_age1.
    do 3 red in H.
    destruct (unsquash x) as [n f].
    destruct (unsquash y) as [n0 f0].
    destruct (unsquash z) as [n1 f1].
    destruct n; try discriminate.
    inv H0.
    simpl in H; destruct H.
    simpl in H; destruct H.
    subst n0 n1.
    exists (squash (n,f0)).
    exists (squash (n,f1)).
    simpl in H0.
    split; intuition. do 3  red.
    repeat rewrite unsquash_squash.
    split; auto. simpl snd.
    apply (paf_join_hom paf_F); auto.
  Qed.

  Lemma age_join2 :
    forall x y z z' : K'.knot,
      join x y z ->
      age z z' ->
      exists x' : K'.knot,
        exists y' : K'.knot, join x' y' z' /\ age x x' /\ age y y'.
  Proof.
    intros.
    unfold age in *; simpl in *.
    rewrite knot_age1 in H0.
    repeat rewrite knot_age1.
    do 3 red in H.
    destruct (unsquash x) as [n f].
    destruct (unsquash y) as [n0 f0].
    destruct (unsquash z) as [n1 f1].
    destruct n1; try discriminate.
    inv H0.
    destruct H; simpl in *.
    destruct H; subst.
    exists (squash (n1,f)).
    exists (squash (n1,f0)).
    split; intuition. do 3  red.
    repeat rewrite unsquash_squash.
    split; auto. simpl snd.
    apply (paf_join_hom paf_F); auto.
  Qed.

  Lemma unage_join1 : forall x x' y' z', join x' y' z' -> age x x' ->
    exists y, exists z, join x y z /\ age y y' /\ age z z'.
  Proof.
    intros.
    unfold join, Join_knot, Join_preimage, age in *; simpl in *.
    revert H0; rewrite knot_age1;
    destruct (unsquash x) as [n f] eqn:?H; intros.
    destruct n; inv H1.
    hnf in H. rewrite unsquash_squash in H. simpl in H.
    revert H.
    destruct (unsquash y') as [n1 f1] eqn:?H.
    destruct (unsquash z') as [n0 f0] eqn:?H; intros.
    destruct H2; simpl in *.
    destruct H2; subst.
    rename n0 into n.
    destruct (paf_preserves_unmap_right paf_F (approx n) (approx n) f f1 f0)
      as [q [w [? [? ?]]]].
    rewrite <- (unsquash_approx H); auto.
    exists (squash (S n,q)).
    exists (squash (S n,w)). split. hnf.
    repeat rewrite unsquash_squash.
    split; simpl; auto.
    generalize (paf_join_hom paf_F (approx (S n)) (approx (S n)) _ _ _ H2).
    rewrite <- (unsquash_approx H0); auto.

    split; hnf.
    rewrite knot_age1.
    rewrite unsquash_squash. f_equal.
    replace y' with (squash (n, fmap F (approx (S n)) (approx (S n)) q)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H.
    apply injective_projections; simpl; auto.
    rewrite (unsquash_approx H).
    rewrite <- H4.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n);
    [replace (approx (S n) oo approx n) with (approx n) |]; auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx2 1 n).
    trivial.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.

    rewrite knot_age1.
    rewrite unsquash_squash. f_equal.
    replace z' with  (squash (n,fmap F (approx (S n)) (approx (S n)) w)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H1.
    apply injective_projections; simpl; auto.
    rewrite <- H5.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n);
    [replace (approx (S n) oo approx n) with (approx n) |]; auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx2 1 n).
    trivial.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.
  Qed.

  Lemma unage_join2 :
    forall z x' y' z', join x' y' z' -> age z z' ->
      exists x, exists y, join x y z /\ age x x' /\ age y y'.
  Proof.
    intros.
    rewrite join_unsquash in H.
    revert H H0.
    unfold join, Join_knot, Join_preimage, age in *; simpl in *.
    repeat rewrite knot_age1.

    destruct (unsquash z) as [n f] eqn:?H;
    destruct (unsquash z') as [n0 f0] eqn:?H;
    destruct (unsquash y') as [n1 f1] eqn:?H;
    destruct (unsquash x') as [n2 f2] eqn:?H; intros.
    destruct n;  inv H4.
    destruct H3. hnf in H3. simpl in *. destruct H3; subst.
    rewrite unsquash_squash in H0.
    inv H0.
    rename n0 into n.

    destruct (paf_preserves_unmap_left paf_F
      (approx n) (approx n) f2 f1 f)
      as [wx [wy [? [? ?]]]]; auto.
    rewrite <- (unsquash_approx H1); auto.
    exists (squash (S n, wx)).
    exists (squash (S n, wy)).
    split. unfold join, Join_nat_F, Join_prod; simpl.
    (* unfold Join_knot; simpl. unfold Join_preimage; simpl. *)
    repeat rewrite unsquash_squash.  simpl.  split; auto.

    rewrite (unsquash_approx H).
    apply (paf_join_hom paf_F); auto.
    split; rewrite knot_age1; rewrite unsquash_squash; f_equal; hnf.
    apply unsquash_inj.
    rewrite unsquash_squash, H2.
    apply injective_projections; simpl; auto.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n);
    [replace (approx (S n) oo approx n) with (approx n) |]; auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx2 1 n).
    trivial.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.

    apply unsquash_inj.
    rewrite unsquash_squash, H1.
    apply injective_projections; simpl; auto.
    rewrite fmap_app.
    rewrite (unsquash_approx H1), <- H5; auto.
    replace (approx n oo approx (S n)) with (approx n);
    [replace (approx (S n) oo approx n) with (approx n) |]; auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx2 1 n).
    trivial.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.
  Qed.

  Lemma age_core :
    forall x y, age x y -> age (core x) (core y).
  Proof.
    intros x y.
    unfold age; rewrite !knot_age1; simpl.
    destruct (unsquash x) eqn: Hx; simpl.
    destruct n; [discriminate|].
    intros X; inv X; simpl.
    rewrite !unsquash_squash; simpl.
    rewrite approx_core.
    f_equal; apply unsquash_inj.
    rewrite !unsquash_squash, !fmap_app.
    change (S n) with (1 + n).
    rewrite <- (approx_approx1 1 n), <- (approx_approx2 1 n).
    setoid_rewrite <- (approx_approx1 0 n).
    reflexivity.
  Qed.

  #[export] Instance asa_knot : @Age_alg knot _ K.ageable_knot _.
  Proof.
    constructor.
    exact age_join1.
    exact age_join2.
    exact unage_join1.
    exact unage_join2.
    exact age_core.
  Qed.

  #[export] Existing Instance Perm_F.
  #[export] Existing Instance Sep_F.

  #[export] Instance ea_knot : Ext_alg knot.
  Proof.
    constructor.
    - intros. rewrite knot_order in H0.
      destruct H0.
      destruct (join_level _ _ _ H) as [Hl Hly].
      destruct H as [? J].
      eapply Rel_join_commut in H1 as (x' & ? & ?); eauto.
      exists (squash (level z, x')).
      rewrite knot_order; split.
      + split. setoid_rewrite knot_level at 2; rewrite unsquash_squash; auto.
        rewrite unsquash_squash; simpl.
        destruct (unsquash x) eqn: Hx.
        rewrite (unsquash_approx Hx).
        rewrite <- Hl, knot_level, Hx.
        apply Rel_fmap; auto.
      + split; rewrite unsquash_squash; simpl. rewrite <- !knot_level; hnf; split; congruence.
        destruct (unsquash y) eqn: Hy, (unsquash z') eqn: Hz'.
        rewrite (unsquash_approx Hy), (unsquash_approx Hz').
        symmetry in H0; rewrite knot_level, Hz' in H0.
        rewrite knot_level, Hy in Hly.
        simpl in *; subst. apply paf_join_hom; auto.
        apply paf_F.
    - intros.
      rewrite knot_order in H.
      destruct H.
      destruct (join_level _ _ _ H0) as [Hl Hly].
      destruct H0 as [? J].
      eapply join_Rel_commut in H1 as (z & ? & ?); eauto.
      exists (squash (level x, z)).
      rewrite knot_order, unsquash_squash; simpl. split.
      + split; rewrite unsquash_squash; simpl. rewrite <- !knot_level; hnf; split; congruence.
        rewrite knot_level in H |- *.
        destruct (unsquash x) eqn: Hx, (unsquash y') eqn: Hy'.
        rewrite (unsquash_approx Hx), (unsquash_approx Hy').
        rewrite knot_level, Hy' in Hly; simpl in *.
        rewrite Hly, <- Hl, <- H.
        apply paf_F; auto.
      + split. rewrite knot_level, unsquash_squash; simpl; congruence.
        destruct (unsquash z') eqn: Hz'.
        rewrite (unsquash_approx Hz').
        symmetry in Hl; rewrite knot_level, Hz' in Hl.
        simpl in Hl; subst. rewrite H.
        apply Rel_fmap; auto.
    - intros. destruct (unsquash x) eqn: Hx.
      destruct (id_exists _f) as (_f0 & ? & ?).
      exists (squash (n, _f0)); split.
      + intros ?? J.
        apply unsquash_inj.
        destruct J as [Jl J].
        rewrite unsquash_squash in *; simpl in *.
        destruct (unsquash a) eqn: Ha, (unsquash b) eqn: Hb; simpl in *.
        destruct Jl; subst.
        rewrite (unsquash_approx Ha) in J.
        apply (paf_preserves_unmap_right paf_F) in J as (? & ? & J & ? & ?).
        rewrite <- (unsquash_approx Ha) in *; subst.
        apply H in J; subst; auto.
      + split; rewrite unsquash_squash, Hx; simpl. split; auto.
        rewrite (unsquash_approx Hx).
        apply (paf_join_hom paf_F); auto.
  Qed.

End KnotFullSa.
