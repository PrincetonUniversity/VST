(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.

Class Age_alg (A:Type) {JOIN: Join A}{as_age : ageable A} :=
mkAge {
  age1_join : forall x {y z x'}, join x y z -> age x x' ->
    exists y':A, exists z':A, join x' y' z' /\ age y y' /\ age z z'
; age1_join2 : forall x {y z z'}, join x y z -> age z z' ->
    exists x':A, exists y':A, join x' y' z' /\ age x x' /\ age y y'
; unage_join : forall x {x' y' z'}, join x' y' z' -> age x x' ->
    exists y:A, exists z:A, join x y z /\ age y y' /\ age z z'
; unage_join2 : forall z {x' y' z'}, join x' y' z' -> age z z' ->
    exists x:A, exists y:A, join x y z /\ age x x' /\ age y y'
}.

Lemma age1_None_joins {A}{JA: Join A}{PA: Perm_alg A}{agA: ageable A}{XA: Age_alg A}: forall phi1 phi2, joins phi1 phi2 -> age1 phi1 = None -> age1 phi2 = None.
Proof.
  intros.
  destruct H.
  case_eq (age1 phi2); intros; auto.
  destruct (age1_join _ (join_com H) H1)  as [phi1' [x' [? [? ?]]]].
  unfold age in *; rewrite H0 in H3; inv H3.
Qed.

Lemma age1_joins_eq {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{XA: Age_alg A}: forall phi1 phi2,
        joins phi1 phi2 -> 
        forall phi1', age1 phi1 = Some phi1' -> 
        forall phi2', age1 phi2 = Some phi2' ->
        joins phi1' phi2'.
Proof.
  intros.
  destruct H.
  destruct (age1_join _ H H0) as [phi7 [x' [? [? ?]]]].
  unfold age in *; rewrite H1 in H3; inv H3.
  exists x'; auto.
Qed.

Section BIJECTION.
  Variables A B : Type.
  Variable JA: Join A.
  Variable PA: Perm_alg A.
  Variable ag: ageable A.
  Variable bijAB: bijection A B.
  Variable asa : Age_alg A.

  Existing Instance PA.

  Instance agB : ageable B := (ag_bij _ _ ag bijAB).

(*  Instance PA_B:  @Perm_alg B (Join_bij _ _ _ bijAB ) := @Perm_bij A JA PA B bijAB. *)

  Theorem asa_bijection : @Age_alg B (Join_bij _ _ _ bijAB) agB.
  Proof.
    constructor; unfold age, Join_bij; simpl;     destruct bijAB as [f g fg gf]; simpl  in *; intros.

    (* commute1 *)
    revert H0; case_eq (age1 (g x)); intros; try discriminate.
    inv H1.
    rename a into gx'.  red in H.
    destruct (age1_join _ H H0) as  [gy' [gz' [? [? ?]]]].
    exists (f gy'); exists (f gz').
    split. red.
    repeat rewrite gf. auto.
    rewrite H2; rewrite H3.
    auto.

    (* commute2 *)
    revert H0; case_eq (age1 (g z)); intros; try discriminate.
    inv H1.
    rename a into gz'. red in H.
    destruct (age1_join2 _ H H0) as  [gx' [gy' [? [? ?]]]].
    exists (f gx'); exists (f gy').
    split. red; repeat rewrite gf; auto.
    rewrite H2; rewrite H3.
    auto.
    
    (* commute3 *)
    revert H0; case_eq (age1 (g x)); intros; try discriminate.
    inv H1.
    rename a into gx'. red in H.
    rewrite gf in *.
    destruct (unage_join _ H H0) as  [gy' [gz' [? [? ?]]]].
    exists (f gy'); exists (f gz').
    split. red; repeat rewrite gf; auto.
    repeat rewrite gf. rewrite H2; rewrite H3.
    repeat rewrite fg; split; auto.
    
    (* commute4 *)
    revert H0; case_eq (age1 (g z)); intros; try discriminate.
    inv H1.
    rename a into gz'. red in H.
    rewrite gf in *.
    destruct (unage_join2 _ H H0) as  [gx' [gy' [? [? ?]]]].
    exists (f gx'); exists (f gy').
    split. red.    repeat rewrite gf; auto.
    repeat rewrite gf.
    rewrite H2; rewrite H3.
    repeat rewrite fg; split; auto.
  Qed.
End BIJECTION.

Section PROD.
  Variable A : Type.
  Variable J_A: Join A.
  Variable saA : Perm_alg A.
  Variable agA : ageable A.
  Variable B: Type.
  Variable J_B: Join B.
  Variable saB : Perm_alg B.
  Variable asa : Age_alg A.

  Theorem asa_prod : @Age_alg (prod A B) _ (ag_prod A B agA).
  Proof.
    constructor; unfold age; simpl; unfold Join_prod.

    (* commute1 *)
    intros [xa xb] [ya yb] [za zb] [xa' xb'] [? ?].
    simpl in *.
    case_eq (age1 xa); intros; inv H2.
    destruct (age1_join _ H H1) as [ya' [za' [? [? ?]]]].
    exists (ya',yb); exists (za',zb); 
      rewrite H3; rewrite H4; repeat split; auto.

    (* commute2 *)
    intros [xa xb] [ya yb] [za zb] [za' zb'] [? ?].
    simpl in *.
    case_eq (age1 za); intros; inv H2.
    destruct (age1_join2 _ H H1) as [xa' [ya' [? [? ?]]]].
    exists (xa',xb); exists (ya',yb); 
      rewrite H3; rewrite H4; repeat split; auto.

    (* commute3 *)
    intros [xa xb] [xa' xb'] [ya' yb'] [za' zb'] [? ?].
    simpl in *.
    case_eq (age1 xa); intros; inv H2.
    destruct (unage_join _ H H1) as [ya [za [? [? ?]]]].
    exists (ya,yb'); exists (za,zb'); simpl.
    rewrite H3; rewrite H4; repeat split; auto.

    (* commute4 *)
    intros [za zb] [xa' xb'] [ya' yb'] [za' zb'] [? ?].
    simpl in *.
    case_eq (age1 za); intros; inv H2.
    destruct (unage_join2 _ H H1) as [xa [ya [? [? ?]]]].
    exists (xa,xb'); exists (ya,yb'); simpl.
    rewrite H3; rewrite H4; repeat split; auto.
  Qed.
End PROD.

Section PROD'.
  Variable A : Type.
  Variable J_A: Join A.
  Variable saA : Perm_alg A.
  Variable B: Type.
  Variable J_B: Join B.
  Variable saB : Perm_alg B.
  Variable agB : ageable B.
  Variable asb : Age_alg B.


  Theorem asa_prod' : @Age_alg (prod A B) _ (ag_prod' A B agB).
  Proof.
    constructor; unfold age; simpl; unfold Join_prod.

    (* commute1 *)
    intros [xa xb] [ya yb] [za zb] [xa' xb'] [? ?].
    simpl in *.
    case_eq (age1 xb); intros; inv H2.
    destruct (age1_join _ H0 H1) as [yb' [zb' [? [? ?]]]].
    exists (ya,yb'); exists (za,zb'); 
      rewrite H3; rewrite H4; repeat split; auto.

    (* commute2 *)
    intros [xa xb] [ya yb] [za zb] [za' zb'] [? ?].
    simpl in *.
    case_eq (age1 zb); intros; inv H2.
    destruct (age1_join2 _ H0 H1) as [xb' [yb' [? [? ?]]]].
    exists (xa,xb'); exists (ya,yb'); 
      rewrite H3; rewrite H4; repeat split; auto.

    (* commute3 *)
    intros [xa xb] [xa' xb'] [ya' yb'] [za' zb'] [? ?].
    simpl in *.
    case_eq (age1 xb); intros; inv H2.
    destruct (unage_join _ H0 H1) as [yb [zb [? [? ?]]]].
    exists (ya',yb); exists (za',zb); simpl.
    rewrite H3; rewrite H4; repeat split; auto.

    (* commute4 *)
    intros [za zb] [xa' xb'] [ya' yb'] [za' zb'] [? ?].
    simpl in *.
    case_eq (age1 zb); intros; inv H2.
    destruct (unage_join2 _ H0 H1) as [xb [yb [? [? ?]]]].
    exists (xa',xb); exists (ya',yb); simpl.
    rewrite H3; rewrite H4; repeat split; auto.
  Qed.
End PROD'.


Lemma joins_fashionR {A}  {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{XA: Age_alg A} : forall x y,
  joins x y -> fashionR x y.
Proof.
  pose proof I.  
  intros.
  unfold fashionR.
  destruct H0 as [z ?].
  revert y z H0; induction x using age_induction; intros.
  case_eq (age1 x); intros.
  destruct (age1_join _ H1 H2) as [p [q [? [? ?]]]].
  assert (level a = level p).
  apply H0 with q; auto.
  replace (level x) with (S (level a)).
  replace (level y) with (S (level p)).
  f_equal; auto.
  symmetry; apply age_level; auto.
  symmetry; apply age_level; auto.
  case_eq (age1 y); intros.
  apply join_com in H1.
  destruct (age1_join _ H1 H3) as [p [q [? [? ?]]]].
  hnf in H5; rewrite H5 in H2; discriminate.
  rewrite age1_level0 in H2.
  rewrite age1_level0 in H3.
  congruence.
Qed.

Lemma comparable_fashionR {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} {agA: ageable A} {XA: Age_alg A} : forall x y,
  comparable x y -> fashionR x y.
Proof.
  intros.
  apply comparable_common_unit in H.
  destruct H as [u [H1 H2]].
  hnf; transitivity (level u).
  apply joins_fashionR; eauto.
  symmetry.
  apply joins_fashionR; eauto.
Qed.

Lemma age_identity {A} `{asaA: Age_alg A}: forall phi phi', age phi phi'->
    identity phi -> identity phi'.
Proof.
intros.
unfold identity in *.
intros.
destruct (unage_join _ H1 H) as [y [? [? [? ?]]]].
spec H0 y x H2.
subst.
unfold age in *. congruence.
Qed.

Lemma age_comparable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} {agA: ageable A}{asaA: Age_alg A}:
    forall phi1 phi2 phi1' phi2', age phi1 phi1' -> age phi2 phi2' ->
      comparable phi1 phi2 -> comparable phi1' phi2'.
Proof.
  intros.
  destruct (comparable_common_unit H1) as [e [? ?]].
  destruct (age1_join _ (join_com H2) H) as [a [b [? [? ?]]]].
  destruct (age1_join _ (join_com H3) H0) as [c [d [? [? ?]]]].
  assert (c=a) by (unfold age in *; congruence); subst c.
  assert (b=phi1') by (unfold age in *; congruence). subst b.
  assert (d=phi2') by (unfold age in *; congruence). subst d.
  apply common_unit_comparable.
  exists a.
  split; apply join_com; auto.
Qed.

Lemma asa_flat {A} {JOIN: Join A}  :  @Age_alg A JOIN (@ag_flat _).
Proof.
  constructor; intros; inv H0.
Qed.

  Lemma asa_nat : @Age_alg nat (Join_equiv nat) ag_nat.
  Proof.
    constructor.
    repeat intro. hnf in H; subst; auto.
    intros.
    destruct H; subst.
    exists x'. exists x'.
    intuition. 
    intros.
    destruct H; subst.
    exists z'; exists z'; intuition.
    intros. destruct H; subst.
    exists x; exists x. intuition.
    intros. destruct H; subst.
    exists z; exists z; intuition.
  Qed.

Lemma nec_join2 {A} `{asaA : Age_alg A}: forall {x y z z' : A},
       join x y z ->
       necR z z' ->
       exists x',
         exists y',
           join x' y' z' /\ necR x x' /\ necR y y'.
Proof.
intros.
revert x y H; induction H0; intros.
edestruct (age1_join2) as [x' [y' [? [? ?]]]]; eauto.
exists x'; exists y'; split; auto.
split; constructor 1; auto.
exists x0; exists y; split; auto.
destruct (IHclos_refl_trans1 _ _ H) as [x' [y' [? [? ?]]]].
destruct (IHclos_refl_trans2 _ _ H0) as [x'' [y'' [? [? ?]]]].
exists x''; exists y''.
split; auto.
split; econstructor 3; eauto.
Qed.

Lemma nec_join {A} `{asaA : Age_alg A}: forall {x y z x' : A},
       join x y z ->
       necR x x' ->
       exists y' ,
         exists z' ,
           join x' y' z' /\ necR y y' /\ necR z z'.
Proof.
intros.
revert y z H; induction H0; intros.
edestruct age1_join as [y' [z' [? [? ?]]]]; eauto.
exists y'; exists z'; split; auto.
split; constructor 1; auto.
exists y; exists z; split; auto.
destruct (IHclos_refl_trans1 _ _ H) as [y' [z' [? [? ?]]]].
destruct (IHclos_refl_trans2 _ _ H0) as [y'' [z'' [? [? ?]]]].
exists y''; exists z''.
split; auto.
split; econstructor 3; eauto.
Qed.

Lemma nec_join4 {A} `{asaA : Age_alg A}: forall z x' y' z' : A,
       join x' y' z' ->
       necR z z' ->
       exists x,
         exists y,
           join x y z /\ necR x x' /\ necR y y'.
Proof.
intros.
revert x' y' H.
induction H0; intros.
destruct (unage_join2 _ H0 H) as  [x0 [y0 [? [? ?]]]].
exists x0; exists y0; split; auto.
split; constructor 1; auto.
exists x'; exists y'; split; auto.

rename x into z1.
rename y into z2.
destruct (IHclos_refl_trans2 _ _ H) as [x'' [y'' [? [? ?]]]].
destruct (IHclos_refl_trans1 _ _ H0) as [x0 [y0 [? [? ?]]]].
exists x0; exists y0.
split; auto.
split; econstructor 3; eauto.
Qed.


Lemma join_level {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{AgeA: Age_alg A}:
  forall x y z, join x y z -> level x = level z /\ level y = level z.
Proof.
  intros.
  assert (exists n, n = level x) by (eexists; reflexivity).
  destruct H0 as [n  ?].
  revert x y z H0 H; induction n; intros.
  case_eq (level y); intros.
  case_eq (level z); intros.
  split; congruence.
  destruct (levelS_age1 _ _ H2).
  destruct (age1_join2 _ H H3) as [u [v [? [? ?]]]].
  apply age_level in H5. congruence.
  destruct (levelS_age1 _ _ H1).
  destruct (age1_join _ (join_com H) H2) as [u [v [? [? ?]]]].
  apply age_level in H4. congruence.
  symmetry in H0.
  destruct (levelS_age1 _ _ H0) as [x' ?].
  destruct (age1_join _ H H1) as [y' [z' [? [? ?]]]].
  specialize (IHn x' y' z').
  apply age_level in H1. apply age_level in H3. apply age_level in H4.
  destruct IHn; auto. congruence.
  split; congruence.
Qed.

 Lemma level_core {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
     forall m:A, level (core m) = level m.
 Proof. intros.
  generalize (core_unit m); unfold unit_for; intro.
  apply join_level in H. intuition.
 Qed.
