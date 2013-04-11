(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Open Local Scope nat_scope.

Require Import msl.ageable.
Require Import msl.functors.
Require Import msl.sepalg.
Require Import msl.sepalg_functors.
Require Import msl.sepalg_generators.
Require Import msl.predicates_hered.
Require Import msl.knot_hered.
Require Import msl.knot_lemmas.
Require Import msl.age_sepalg.

Module Type TY_FUNCTOR_SA_PROP.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.

  Parameter Join_F: forall A, Join (F A). Existing Instance Join_F.
(*   Parameter Perm_F: forall A, Perm_alg (F A). EXisting Instance Perm_F. *)
  Parameter paf_F : pafunctor f_F.        Existing Instance paf_F.
  Parameter Perm_F: Perm_paf f_F Join_F.
  Parameter Sep_F: Sep_paf f_F Join_F.
  Parameter Canc_F: Canc_paf f_F Join_F.
  Parameter Disj_F: Disj_paf f_F Join_F.
End TY_FUNCTOR_SA_PROP.

Module Type KNOT_HERED_SA.
  Declare Module TFSA:TY_FUNCTOR_SA_PROP.
  Declare Module K:KNOT_HERED with Module TF:=TFSA.TF.

  Import TFSA.TF.
  Import TFSA.
  Import K.

  Parameter Join_knot: Join knot.  Existing Instance Join_knot.
  Parameter Perm_knot : Perm_alg knot.  Existing Instance Perm_knot.
  Parameter Sep_knot : (forall A, Sep_alg (F A)) -> Sep_alg knot.  Existing Instance Sep_knot.
  Parameter Canc_knot : (forall A, Canc_alg (F A)) -> Canc_alg knot.  Existing Instance Canc_knot.
  Parameter Disj_knot : (forall A, Disj_alg (F A)) -> Disj_alg knot.  Existing Instance Disj_knot.

  Instance Join_nat_F: Join (nat * F predicate) := 
       Join_prod nat  (Join_equiv nat) (F predicate) _.

 Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
    @Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F predicate _ (Perm_equiv _)).
 Instance Sep_nat_F (Sep_F: forall A, Sep_alg (F A)): Sep_alg (nat * F predicate) :=
    @Sep_prod nat _ _ _ (Sep_equiv _) (Sep_F predicate).
 Instance Canc_nat_F (Canc_F: forall A, Canc_alg (F A)): Canc_alg (nat * F predicate) :=
    @Canc_prod nat _ _ _ (Canc_equiv _) (Canc_F predicate).
 Instance Disj_nat_F (Disj_F: forall A, Disj_alg (F A)): Disj_alg (nat * F predicate) :=
    @Disj_prod nat _ _ _ (Disj_equiv _) (Disj_F predicate).

  Axiom join_unsquash : forall x1 x2 x3 : knot,
    join x1 x2 x3 = join (unsquash x1) (unsquash x2) (unsquash x3).

  Axiom asa_knot : Age_alg knot.

End KNOT_HERED_SA.

Module KnotHeredSa (TFSA':TY_FUNCTOR_SA_PROP) (K':KNOT_HERED with Module TF:=TFSA'.TF)
  : KNOT_HERED_SA with Module TFSA:=TFSA' with Module K:=K'.

  Module TFSA:=TFSA'.
  Module K:=K'.

  Module KL := KnotHered_Lemmas(K).

  Import TFSA.TF.
  Import TFSA.
  Import K.
  Import KL.

  Instance Join_nat_F: Join (nat * F predicate) := 
       Join_prod nat  (Join_equiv nat) (F predicate) _.

 Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
    @Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F predicate _ (Perm_equiv _)).
 Instance Sep_nat_F (Sep_F: forall A, Sep_alg (F A)): Sep_alg (nat * F predicate) :=
    @Sep_prod nat _ _ _ (Sep_equiv _) (Sep_F predicate).
 Instance Canc_nat_F (Canc_F: forall A, Canc_alg (F A)): Canc_alg (nat * F predicate) :=
    @Canc_prod nat _ _ _ (Canc_equiv _) (Canc_F predicate).
 Instance Disj_nat_F (Disj_F: forall A, Disj_alg (F A)): Disj_alg (nat * F predicate) :=
    @Disj_prod nat _ _ _ (Disj_equiv _) (Disj_F predicate).

  Lemma unsquash_squash_join_hom : join_hom (unsquash oo squash).
  Proof.
    unfold compose.
    intros [x1 x2] [y1 y2] [z1 z2] ?.
    do 3 rewrite (unsquash_squash).
    firstorder.
    simpl in *.
    subst y1.
    subst z1.
    apply paf_join_hom. auto.
  Qed.

  Instance Join_knot : Join knot := 
           Join_preimage knot (nat * F predicate) Join_nat_F unsquash.

  Instance Perm_knot : Perm_alg knot := 
    Perm_preimage _ _ _ _ unsquash squash squash_unsquash unsquash_squash_join_hom.

  Instance Sep_knot(Sep_F: forall A, Sep_alg (F A)) : Sep_alg knot := 
    Sep_preimage _ _ _  unsquash squash squash_unsquash unsquash_squash_join_hom.

  Lemma join_unsquash : forall x1 x2 x3,
    join x1 x2 x3 =
    join (unsquash x1) (unsquash x2) (unsquash x3).
  Proof.
    intuition.
  Qed.

  Instance Canc_knot(Canc_F: forall A, Canc_alg (F A)) : Canc_alg knot.
  Proof. repeat intro. 
            do 3 red in H, H0.
            apply unsquash_inj.
            apply (join_canc H H0).
  Qed.

  Instance Disj_knot(Disj_F: forall A, Disj_alg (F A)) : Disj_alg knot.
  Proof.
   repeat intro.
   do 3 red in H.
   apply join_self in H.
   apply unsquash_inj; auto.
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
    destruct (unsquash x).
    destruct (unsquash y).
    destruct (unsquash z).
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
    apply paf_join_hom; auto.
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
    destruct (unsquash x).
    destruct (unsquash y).
    destruct (unsquash z).
    destruct n1; try discriminate.
    inv H0.
    destruct H; simpl in *.
    destruct H; subst.
    exists (squash (n1,f)).
    exists (squash (n1,f0)).
    split; intuition. do 3  red.
    repeat rewrite unsquash_squash.
    split; auto. simpl snd.
    apply paf_join_hom; auto.
  Qed.

  Lemma unage_join1 : forall x x' y' z', join x' y' z' -> age x x' ->
    exists y, exists z, join x y z /\ age y y' /\ age z z'.
  Proof.
    intros.
    unfold join, Join_knot, Join_preimage, age in *; simpl in *.
    revert H0; rewrite knot_age1; case_eq (unsquash x); intros.
    destruct n; inv H1.
    hnf in H. rewrite unsquash_squash in H. simpl in H.
    revert H.
    case_eq (unsquash y');
    case_eq (unsquash z'); intros.
    destruct H2; simpl in *.
    destruct H2; subst.
    rename n0 into n.
    destruct (paf_preserves_unmap_right (approx n) f f1 f0)
      as [q [w [? [? ?]]]].
    rewrite <- (unsquash_approx H1); auto.
    exists (squash (S n,q)).
    exists (squash (S n,w)). split. hnf.
    repeat rewrite unsquash_squash.
    split; simpl; auto.
    generalize (paf_join_hom (approx (S n)) _ _ _ H2).
    rewrite <- (unsquash_approx H0); auto.

    split; hnf.
    rewrite knot_age1.
    rewrite unsquash_squash. f_equal.
    replace y' with (squash (n,fmap (approx (S n)) q)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H1.
    apply injective_projections; simpl; auto.
    rewrite (unsquash_approx H1).
    rewrite <- H4.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n); auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.

    rewrite knot_age1.
    rewrite unsquash_squash. f_equal.
    replace z' with  (squash (n,fmap (approx (S n)) w)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H.
    apply injective_projections; simpl; auto.
    rewrite <- H5.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n); auto.
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

    case_eq (unsquash x');
    case_eq (unsquash y');
    case_eq (unsquash z');
    case_eq (unsquash z); intros.
    destruct n;  inv H4.
    destruct H3. hnf in H3. simpl in *. destruct H3; subst.
    rewrite unsquash_squash in H0.
    inv H0.
    rename n0 into n.

    destruct (paf_preserves_unmap_left
      (approx n) f2 f1 f)
      as [wx [wy [? [? ?]]]]; auto.
    rewrite <- (unsquash_approx H1); auto.
    exists (squash (S n, wx)).
    exists (squash (S n, wy)).
    split. unfold join, Join_nat_F, Join_prod; simpl.
    (* unfold Join_knot; simpl. unfold Join_preimage; simpl. *)
    repeat rewrite unsquash_squash.  simpl.  split; auto. 

    rewrite (unsquash_approx H).
    apply paf_join_hom; auto.
    split; rewrite knot_age1; rewrite unsquash_squash; f_equal; hnf.
    apply unsquash_inj.
    rewrite unsquash_squash, H2.
    apply injective_projections; simpl; auto.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n); auto.
    extensionality x.
    unfold compose.
    change (approx n (approx (S n) x)) with ((approx n oo approx (1 + n)) x).
    rewrite <- (approx_approx1 1 n).
    trivial.
    apply unsquash_inj.
    rewrite unsquash_squash, H1.
    apply injective_projections; simpl; auto.
    rewrite fmap_app.
    replace (approx n oo approx (S n)) with (approx n); auto.
    rewrite H5.
    rewrite <- (unsquash_approx H1); auto.
    extensionality x.
    unfold compose.
    change (approx n (approx (S n) x)) with ((approx n oo approx (1 + n)) x).
    rewrite <- (approx_approx1 1 n).
    trivial.
  Qed.

  Theorem asa_knot : @Age_alg knot _ K.ag_knot.
  Proof.
    constructor.
    exact age_join1.
    exact age_join2.
    exact unage_join1.
    exact unage_join2.
  Qed.

End KnotHeredSa.
