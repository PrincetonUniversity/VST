(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.
Require Import msl.sepalg_functors.
Require Import msl.ageable.
Require Import msl.age_sepalg.
Require Import msl.knot.
Require Import msl.knot_lemmas.
Require Import msl.functors.
Require Import msl.sepalg_functors.



Module Type TY_FUNCTOR_SA.
  Declare Module TF:TY_FUNCTOR.
  Import TF.

  Parameter Join_T : Join T.  Existing Instance Join_T.
  Parameter pa_T : Perm_alg T.  Existing Instance pa_T.
(*   Parameter sa_T : Sep_alg T.  EXisting Instance sa_T. *)

  Axiom T_bot_identity : identity T_bot.
  Axiom T_bot_unit : unit_for T_bot T_bot.

  Instance pa_TF (A : Type) : Perm_alg (A -> T) := Perm_fun _ _ _ pa_T.
  Instance sa_TF (sa_T: Sep_alg T) (A : Type): Sep_alg (A -> T) := Sep_fun _ _ _ sa_T.
  Instance ca_TF (ca_T: Canc_alg T) (A : Type): Canc_alg (A -> T) := Canc_fun _ _ _ ca_T.
  Instance da_TF (da_T: Disj_alg T) (A : Type): Disj_alg (A -> T) := Disj_fun _ _ _ da_T.

  Parameter J_F: forall A, Join (F (A -> T)).
  Existing Instance J_F.
  Parameter Perm_F: forall A, Perm_alg  (F (A -> T)).
  Implicit Arguments Perm_F.   Existing Instance Perm_F.
  Parameter Sep_F: forall A, Sep_alg  (F (A -> T)).
  Implicit Arguments Sep_F.
  Existing Instance Sep_F.
  Parameter Canc_F: forall A, Canc_alg  (F (A -> T)).
  Implicit Arguments Canc_F.
  Existing Instance Canc_F.
  Parameter Disj_F: forall A, Disj_alg  (F (A -> T)).
  Implicit Arguments Disj_F.
  Existing Instance Disj_F.

  Axiom fmap_hom : forall A B (f: (A -> T) -> (B -> T)),
    @join_hom  _ (Join_fun A T _) _ (Join_fun B T _) f ->
    @join_hom _  (J_F A) _ (J_F B) (fmap f).
  Implicit Arguments fmap_hom.

  Axiom F_preserves_unmaps_left : forall A B (f : (A -> T) -> (B -> T)) 
    (Hhom : @join_hom  _ (Join_fun A T _) _ (Join_fun B T _) f ),
    unmap_left (Join_fun A T Join_T) (Join_fun B T Join_T) f ->
    unmap_left (J_F A) (J_F B) (fmap f).
  Implicit Arguments F_preserves_unmaps_left.

  Axiom F_preserves_unmaps_right : forall A B (f : (A -> T) -> (B -> T)) 
    (Hhom : @join_hom  _ (Join_fun A T _) _ (Join_fun B T _) f ),
    unmap_right (Join_fun A T Join_T) (Join_fun B T Join_T) f ->
    unmap_right (J_F A) (J_F B) (fmap f).
  Implicit Arguments F_preserves_unmaps_right.
End TY_FUNCTOR_SA.

Module Type KNOT_SA.
  Declare Module TFSA:TY_FUNCTOR_SA.
  Declare Module K:KNOT with Module TF:=TFSA.TF.

  Import TFSA.TF.
  Import TFSA.
  Import K.

  Parameter Join_knot: Join knot.  Existing Instance Join_knot.
  Parameter Perm_knot : Perm_alg knot.  Existing Instance Perm_knot.
  Parameter Sep_knot: forall (sa_T: Sep_alg T), Sep_alg knot. Existing Instance Sep_knot.
  Parameter Canc_knot: forall (sa_T: Canc_alg T), Canc_alg knot. Existing Instance Canc_knot.
  Parameter Disj_knot: forall (sa_T: Disj_alg T), Disj_alg knot. Existing Instance Disj_knot.

  Instance Join_nat_F: Join (nat * F predicate) := 
       Join_prod nat  (Join_equiv nat) (F predicate) _.

  Instance Perm_nat_F : Perm_alg (nat * F predicate) := 
   @Perm_prod _ _ (F (knot * TF.other -> T)) (J_F (knot * TF.other)) (Perm_equiv nat) _.

  Instance Sep_nat_F (sa_T: Sep_alg T) : Sep_alg (nat * F predicate) := 
   @Sep_prod _ _ (F (knot * TF.other -> T)) (J_F (knot * TF.other)) (Sep_equiv nat) _.
  Instance Canc_nat_F (sa_T: Canc_alg T) : Canc_alg (nat * F predicate) := 
   @Canc_prod _ _ (F (knot * TF.other -> T)) (J_F (knot * TF.other)) (Canc_equiv nat) _.
  Instance Disj_nat_F (sa_T: Disj_alg T) : Disj_alg (nat * F predicate) := 
   @Disj_prod _ _ (F (knot * TF.other -> T)) (J_F (knot * TF.other)) (Disj_equiv nat) _.

  Axiom join_unsquash : forall x1 x2 x3 : knot,
    join x1 x2 x3 = join (unsquash x1) (unsquash x2) (unsquash x3).

  Axiom asa_knot : Sep_alg T -> @Age_alg knot _ K.ag_knot.

End KNOT_SA.

Module KnotSa (TFSA':TY_FUNCTOR_SA) (K':KNOT with Module TF:=TFSA'.TF)
  : KNOT_SA with Module TFSA:=TFSA' with Module K:=K'.

  Module TFSA:=TFSA'.
  Module K:=K'.
  Module KL := Knot_Lemmas(K).

  Import TFSA.TF.
  Import TFSA.
  Import K.
  Import KL.

  Instance Join_pred : Join predicate := Join_fun (knot * other) T Join_T.
  Instance pred_pa : Perm_alg predicate := pa_TF (knot * other).
  Instance pred_sa (sa_T: Sep_alg T): Sep_alg predicate := sa_TF _ _.
  Instance pred_ca (ca_T: Canc_alg T): Canc_alg predicate := ca_TF _ _.
  Instance pred_da (da_T: Disj_alg T): Disj_alg predicate := da_TF _ _.

  Lemma approx_join_hom : forall n, join_hom (approx n).
  Proof.
    unfold join_hom.
    intros.
    hnf in *.
    intro x0.
    spec H x0.
    unfold K'.approx.
    destruct (le_gt_dec n (level x0)).
    generalize (T_bot_identity); intro.
    apply T_bot_unit.
    trivial.
  Qed.
  Lemma F_approx_join_hom : forall n,
    join_hom (JA := J_F (knot * other)) (JB := J_F (knot * other)) (fmap (approx n)).
  Proof.
    intros; apply fmap_hom; apply approx_join_hom.
  Qed.
  
  Instance Join_nat_F: Join (nat * F predicate) := 
         Join_prod nat (Join_equiv nat) (F (knot * other -> T))  (J_F (knot * other)).
  Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
         Perm_prod (Perm_equiv nat) (Perm_F (knot * other)).
  Instance Sep_nat_F (sa_T: Sep_alg T) : Sep_alg (nat * F predicate) :=
         Sep_prod (Sep_equiv nat) (Sep_F (knot * other)).
  Instance Canc_nat_F (ca_T: Canc_alg T) : Canc_alg (nat * F predicate) :=
         Canc_prod _ _ _ _.
  Instance Disj_nat_F (sa_T: Disj_alg T) : Disj_alg (nat * F predicate) :=
         Disj_prod _ _ _ _.

  Lemma unsquash_squash_join_hom : join_hom (unsquash oo squash).
  Proof.
    unfold compose.
    intros [x1 x2] [y1 y2] [z1 z2] ?.
    do 3 rewrite (unsquash_squash).
    firstorder.
    simpl in *.
    subst y1.
    subst z1.
    apply F_approx_join_hom.
    trivial.
  Qed.

  Instance Join_knot : Join knot :=  
         Join_preimage knot (nat * F predicate) Join_nat_F unsquash.

  Instance Perm_knot : Perm_alg knot := 
    Perm_preimage _ _ _  _ unsquash squash squash_unsquash unsquash_squash_join_hom.

  Lemma join_unsquash : forall x1 x2 x3,
    join x1 x2 x3 =
    join (unsquash x1) (unsquash x2) (unsquash x3).
  Proof.
    intuition.
  Qed.

  Instance Sep_knot (sa_T: Sep_alg T): Sep_alg knot := 
    Sep_preimage _ _ _  unsquash squash squash_unsquash unsquash_squash_join_hom.
  Instance Canc_knot (sa_T: Canc_alg T): Canc_alg knot.
  Proof.
     repeat intro.
     do 3 red in H,H0. 
     apply unsquash_inj. apply (join_canc H H0).
  Qed.
  Instance Disj_knot (da_T: Disj_alg T): Disj_alg knot.
  Proof.
     repeat intro.
     do 3 red in H. 
     apply unsquash_inj. apply (join_self H).
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
    apply F_approx_join_hom; auto.
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
    apply F_approx_join_hom; auto.
  Qed.

  Lemma pred_unmap_left_approx (sa_T: Sep_alg T):
    forall n, unmap_left _ Join_pred (approx n).
  Proof.
    red; intros.
    assert (x' = approx n x').
      extensionality k.
      spec H k.
      unfold approx in *.
      revert H.
      elim (le_gt_dec n (level k)); intros; trivial.
      apply T_bot_identity.
      apply join_comm.
      trivial.

    exists (fun w => if le_gt_dec n (level w) then projT1 (join_ex_units (z w)) else x' w).
    exists (fun w => if le_gt_dec n (level w) then z w else y w).
    split.
    intro w.
    spec H w.
    revert H.
    rewrite H0.
    unfold approx.
    elim (le_gt_dec n (level w)); intros; trivial.
    destruct (join_ex_units (z w)).
    simpl. apply u.

    split.
    extensionality w.
    spec H w.
    revert H.
    unfold approx.
    elim (le_gt_dec n (level w)); intros; trivial.
    apply join_unit2_e in H; auto.
    apply T_bot_identity.
    
    unfold approx.
    extensionality w.
    elim (le_gt_dec n (level w)); intros; trivial.
  Qed.

  Lemma pred_unmap_right_approx (sa_T: Sep_alg T):
    forall n, unmap_right _ Join_pred (approx n).
  Proof.
    red; intros.
    exists (fun w => if le_gt_dec n (level w) then (projT1 (join_ex_units (x w))) else y w).
    exists (fun w => if le_gt_dec n (level w) then x w else z' w).
    split.
    intro w.
    spec H w.
    revert H.
    unfold approx.
    elim (le_gt_dec n (level w)); intros; trivial.
    destruct (join_ex_units (x w)).
    simpl. apply join_comm; apply u.
    
    split.
    unfold approx.
    extensionality w.
    elim (le_gt_dec n (level w)); intros; trivial.
    
    pattern z' at 2.
    assert (z' = approx n z').
      extensionality k.
      spec H k.
      unfold approx in *.
      revert H.
      elim (le_gt_dec n (level k)); intros; trivial.
      symmetry.
      apply (T_bot_identity _ _ H).
    rewrite H0.
    unfold approx.
    extensionality w.
    elim (le_gt_dec n (level w)); intros; trivial.
  Qed.

  Lemma unage_join1 (sa_T: Sep_alg T) : forall x x' y' z', join x' y' z' -> age x x' ->
    exists y, exists z, join x y z /\ age y y' /\ age z z'.
  Proof.
(*    destruct F_preserves_unmaps as [_ fmap_commute1]. *)
    intros.
    unfold age in *; simpl in *.
    rewrite knot_age1 in H0. do 3 red in H.
    case_eq (unsquash x); intros.
    rewrite H1 in H0.
    destruct n; try discriminate.
    inv H0.
    revert H.
    case_eq (unsquash y');
    case_eq (unsquash z'); intros.
    rewrite unsquash_squash in H2.
    destruct H2; simpl in *.
    destruct H2; subst.
    rename n0 into n.
(* new technique *)
    destruct (@F_preserves_unmaps_right  _ _ _ (approx_join_hom n) (pred_unmap_right_approx _ _) f f1 f0) as [q [w [? [? ?]]]].
    change (prod K'.knot TF.other -> TF.T) with predicate.
(* end new technique *)
    rewrite <- (unsquash_approx H0); auto.
    exists (squash (S n,q)).
    exists (squash (S n,w)). 

    split.
    do 3 red. rewrite H1.     repeat rewrite unsquash_squash.
    split; simpl; auto.
    generalize (F_approx_join_hom (S n) _ _ _ H2).
    rewrite <- (unsquash_approx H1); auto.

    split.
    rewrite knot_age1.
    rewrite unsquash_squash.
    replace y' with (squash (n,fmap (approx (S n)) q)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H0.
    apply injective_projections; simpl; auto.
    rewrite (unsquash_approx H0).
(* new technique *)
    change (prod K'.knot TF.other -> TF.T) with predicate in H4.
(* end new technique *)
    rewrite <- H4.
    change ((fmap (approx n) oo fmap (approx (S n))) q = fmap (approx n) q).
    rewrite fmap_comp.
    replace (approx n oo approx (S n)) with (approx n); auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.

    rewrite knot_age1.
    rewrite unsquash_squash.
    replace z' with  (squash (n,fmap (approx (S n)) w)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H.
    apply injective_projections; simpl; auto.
    rewrite <- H5.
    change ((fmap (approx n) oo fmap (approx (S n))) w = fmap (approx n) w).
    rewrite fmap_comp.
    replace (approx n oo approx (S n)) with (approx n); auto.
    extensionality a.
    replace (S n) with (1 + n)%nat by trivial.
    rewrite <- (approx_approx1 1 n).
    trivial.
  Qed.

  Lemma unage_join2 (sa_T: Sep_alg T):
    forall z x' y' z', join x' y' z' -> age z z' ->
      exists x, exists y, join x y z /\ age x x' /\ age y y'.
  Proof.
    intros.
    rewrite join_unsquash in H.
    revert H H0.
    unfold age in *; simpl in *.
    repeat rewrite knot_age1.
    case_eq (unsquash x');
    case_eq (unsquash y');
    case_eq (unsquash z');
    case_eq (unsquash z); intros.
    destruct n; try discriminate.
    inv H4.
    rewrite unsquash_squash in H0.
    inv H0.
    destruct H3; simpl in *.
    destruct H0; subst.
    rename n0 into n.
    destruct (@F_preserves_unmaps_left _ _ _ (approx_join_hom n) (pred_unmap_left_approx _ _) f2 f1 f)
      as [wx [wy [? [? ?]]]]; auto.
    change (prod K'.knot TF.other -> TF.T) with predicate.
    unfold join, Join_knot, Join_preimage; simpl.
    rewrite <- (unsquash_approx H1); auto.
    unfold join, Join_knot, Join_preimage; simpl.
    exists (squash (S n, wx)).
    exists (squash (S n, wy)).
    repeat rewrite unsquash_squash.
    rewrite H.
 
    split.
    split; simpl; auto.    
    rewrite (unsquash_approx H).
    apply F_approx_join_hom; auto.
    split; rewrite knot_age1; rewrite unsquash_squash.
    replace x' with (squash (n,(fmap (approx (S n)) wx))); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H2.
    apply injective_projections; simpl; auto.
    change ((fmap (approx n) oo fmap (approx (S n))) wx = f2).
    rewrite fmap_comp.
    replace (approx n oo approx (S n)) with (approx n); auto.
    extensionality x.
    unfold compose.
    change (approx n (approx (S n) x)) with ((approx n oo approx (1 + n)) x).
    rewrite <- (approx_approx1 1 n).
    trivial.
    replace y' with (squash (n,(fmap (approx (S n)) wy))); auto.
    apply unsquash_inj.
    rewrite unsquash_squash, H1.
    apply injective_projections; simpl; auto.
    change ((fmap (approx n) oo fmap (approx (S n))) wy = f1).
    rewrite fmap_comp.
    replace (approx n oo approx (S n)) with (approx n); auto.
    change (prod K'.knot TF.other -> TF.T) with predicate in H5.
    rewrite H5.
    rewrite <- (unsquash_approx H1); auto.
    extensionality x.
    unfold compose.
    change (approx n (approx (S n) x)) with ((approx n oo approx (1 + n)) x).
    rewrite <- (approx_approx1 1 n).
    trivial.
  Qed.

  Theorem asa_knot(sa_T: Sep_alg T) : @Age_alg knot _ K.ag_knot.
  Proof.
    constructor.
    exact age_join1.
    exact age_join2.
    exact (unage_join1 _).
    exact (unage_join2 _).
  Qed.

End KnotSa.
