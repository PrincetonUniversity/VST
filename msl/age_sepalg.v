(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)
Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.

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
  destruct (age1_join _ (join_comm H) H1)  as [phi1' [x' [? [? ?]]]].
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
  apply join_comm in H1.
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
specialize ( H0 y x H2).
subst.
unfold age in *. congruence.
Qed.

Lemma age_comparable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} {agA: ageable A}{asaA: Age_alg A}:
    forall phi1 phi2 phi1' phi2', age phi1 phi1' -> age phi2 phi2' ->
      comparable phi1 phi2 -> comparable phi1' phi2'.
Proof.
  intros.
  destruct (comparable_common_unit H1) as [e [? ?]].
  destruct (age1_join _ (join_comm H2) H) as [a [b [? [? ?]]]].
  destruct (age1_join _ (join_comm H3) H0) as [c [d [? [? ?]]]].
  assert (c=a) by (unfold age in *; congruence); subst c.
  assert (b=phi1') by (unfold age in *; congruence). subst b.
  assert (d=phi2') by (unfold age in *; congruence). subst d.
  apply common_unit_comparable.
  exists a.
  split; apply join_comm; auto.
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

Lemma nec_identity {A} `{asaA: Age_alg A}: forall phi phi', necR phi phi'->
    identity phi -> identity phi'.
Proof.
  induction 1; auto.
  apply age_identity; auto.
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
  destruct (age1_join _ (join_comm H) H2) as [u [v [? [? ?]]]].
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

Lemma age_core_eq {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall x y x' y', age x x' -> age y y' -> core x = core y -> core x' = core y'.
Proof.
 intros.
 generalize (core_unit x); unfold unit_for; intro. apply join_comm in H2.
 generalize (core_unit y); unfold unit_for; intro. apply join_comm in H3.
 destruct (age1_join _ H2 H) as [u [v [? [? ?]]]].
 destruct (age1_join _ H3 H0) as [i [j [? [? ?]]]].
 unfold age in *. rewrite H in H6. inv H6. rewrite H0 in H9; inv H9.
 rewrite H1 in *. rewrite H5 in H8; inv H8.
 apply join_core2 in H4. apply join_core2 in H7.
  congruence.
Qed.

Lemma age_twin {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall phi1 phi2 n phi1',
  level phi1 = level phi2 ->
  ageN n phi1 = Some phi1' ->
  exists phi2', ageN n phi2 = Some phi2' /\ level phi1' = level phi2'.
Proof.
intros until n; revert n phi1 phi2.
induction n; intros.
exists phi2.
split; trivial.
inversion H0.
subst phi1'.
trivial.
unfold ageN in H0.
simpl in H0.
revert H0; case_eq (age1 phi1); intros; try discriminate.
rename a into phi.
assert (exists ophi2, age phi2 ophi2 /\ level phi = level ophi2).
generalize (age_level _ _ H0); intro.
rewrite H in H2; apply levelS_age1 in H2. destruct H2 as [y ?].
exists y; split; auto.
apply age_level in H0; apply age_level in H2; omega.
destruct H2 as [ophi2 [? ?]].
specialize (IHn _ _ _ H3 H1).
destruct IHn as [phi2' [? ?]].
exists phi2'.
split; trivial.
unfold ageN.
simpl.
rewrite H2.
trivial.
Qed.

Lemma age1_join_eq {A}  {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A} : forall phi1 phi2 phi3,
        join phi1 phi2 phi3 ->
        forall phi1', age1 phi1 = Some phi1' ->
        forall phi2', age1 phi2 = Some phi2' ->
        forall phi3', age1 phi3 = Some phi3' ->
        join phi1' phi2' phi3'.
Proof.
intros until phi3.
intros H phi1' H0 phi2' H1 phi3' H2.
destruct (age1_join _ H H0) as [phi4 [x' [? [? ?]]]].
unfold age in *.
rewrite H4 in H1.
inversion H1.
rewrite <- H7.
rewrite H5 in H2.
inversion H2.
rewrite <- H8.
auto.
Qed.

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, lt i n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Lemma age_core {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall x y : A, age x y -> age (core x) (core y).
Proof.
 intros. unfold age in *.
 pose proof (core_unit x).
 unfold unit_for in H0.
 destruct (age1_join2 _ H0 H) as [a [b [? [? ?]]]].
 unfold age in H3. rewrite H3 in H; inv H.
 pose proof (core_unit y).
 assert (a = core y); [|subst; auto].
 eapply same_identity; eauto.
 - eapply age_identity; eauto.
   apply core_identity.
 - apply core_identity.
Qed.

Lemma necR_core {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall x y : A, necR x y -> necR (core x) (core y).
Proof.
 induction 1.
 constructor 1; apply age_core; auto.
 constructor 2.
 constructor 3 with (core y); auto.
Qed.

Definition relation_mul {A: Type} (R0 R1: relation A) (x y: A) := exists z, R0 x z /\ R1 z y.

Fixpoint relation_power {A: Type} (n: nat) (R: relation A) :=
  match n with
  | O => eq
  | S n0 => relation_mul R (relation_power n0 R)
  end.

Fixpoint partial_fun_power {A: Type} (n: nat) (f: A -> option A) (x: A) :=
  match n with
  | O => Some x
  | S n0 => match f x with
            | Some fx => partial_fun_power n0 f fx
            | None => None
            end
  end.

Lemma laterR_power_age: forall {A:Type} {agA:ageable A} (x y: A),
  laterR x y <-> (exists n, relation_power (S n) age x y).
Proof.
  intros.
  remember (level x) eqn:?H.
  revert x y H; induction n; intros.
  + split; intros.
    - apply laterR_level in H0.
      omega.
    - destruct H0 as [n ?H].
      destruct H0 as [z [? ?]].
      apply age_level in H0; omega.
  + split; intros.
    - destruct (age1 x) as [a' |] eqn:?H; [| apply age1_level0 in H1; omega].
      assert (age x a') by auto; clear H1.
      pose proof age_later_nec _ _ _ H2 H0.
      destruct (nec_refl_or_later _ _ H1).
      * exists 0.
        simpl.
        exists y.
        subst; auto.
      * simpl.
        pose proof age_level _ _ H2.
        rewrite <- H in H4; inversion H4; clear H4.
        destruct (IHn a' y H6) as [? _].
        destruct (H4 H3) as [n0 ?H].
        exists (S n0).
        simpl.
        exists a'.
        auto.
    - destruct H0 as [n0 [z [?H ?H]]].
      pose proof age_level _ _ H0.
      rewrite <- H in H2; inversion H2; clear H2.
      destruct (IHn z y H4) as [_ ?H].
      destruct n0.
      * simpl in H1; subst.
        apply t_step; auto.
      * spec H2; [exists n0; auto |].
        eapply t_trans; eauto.
        apply t_step; auto.
Qed.

Lemma necR_power_age: forall {A:Type} {agA:ageable A} (x y: A),
  necR x y <-> (exists n, relation_power n age x y).
Proof.
  intros.
  split; intros.
  + destruct (nec_refl_or_later _ _ H).
    - subst.
      exists 0.
      simpl.
      auto.
    - destruct (laterR_power_age x y) as [? _].
      destruct (H1 H0) as [n0 ?H].
      exists (S n0); auto.
  + destruct H as [n ?H].
    destruct n.
    - simpl in H; subst.
      auto.
    - destruct (laterR_power_age x y) as [_ ?].
      spec H0; [exists n; auto |].
      apply laterR_necR; auto.
Qed.

Lemma power_age_age1: forall {A:Type} {agA:ageable A} n x y,
  relation_power n age x y <-> partial_fun_power n age1 x = Some y.
Proof.
  intros.
  revert x; induction n; intros.
  + simpl.
    split; intros; [subst| inversion H]; reflexivity.
  + simpl.
    split; intros.
    - destruct H as [z [?H ?H]].
      rewrite H.
      apply IHn; auto.
    - destruct (age1 x) as [z |] eqn:?H; [| inversion H].
      exists z.
      split; [auto |].
      apply IHn; auto.
Qed.

Lemma power_age1_level_small: forall {A:Type} {agA:ageable A} n x,
  partial_fun_power n age1 x = None <-> level x < n.
Proof.
  intros.
  revert x; induction n; intros.
  + simpl; split; intros.
    - inversion H.
    - omega.
  + simpl; split; intros.
    - destruct (age1 x) eqn:?H.
      * apply age_level in H0.
        apply IHn in H.
        omega.
      * apply age1_level0 in H0.
        omega.
    - destruct (age1 x) eqn:?H.
      * apply IHn.
        apply age_level in H0.
        omega.
      * reflexivity.
Qed.

Lemma power_age_core: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (x y: A) n,
  relation_power n age x y -> relation_power n age (core x) (core y).
Proof.
  intros.
  revert x y H; induction n; intros.
  + simpl in H |- *.
    subst; reflexivity.
  + simpl in H |- *.
    destruct H as [z [?H ?H]].
    exists (core z).
    split.
    - apply age_core; auto.
    - apply IHn; auto.
Qed.

Lemma power_age_core_eq: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (x x' y y': A) n,
  relation_power n age x x' -> relation_power n age y y' -> core x = core y -> core x' = core y'.
Proof.
  intros.
  revert x y H H0 H1; induction n; intros.
  + simpl in H, H0 |- *.
    subst; auto.
  + simpl in H, H0 |- *.
    destruct H as [x'' [?H ?H]].
    destruct H0 as [y'' [?H ?H]].
    pose proof age_core_eq _ _ _ _ H H0 H1.
    specialize (IHn x'' y'' H2 H3 H4).
    auto.
Qed.

Lemma levelS_age {A: Type} {agA: ageable A} : forall (x:A) n,
  S n = level x ->
  exists y, age x y /\ n = level y.
Proof.
  intros.
  apply eq_sym in H.
  remember H as H0; clear HeqH0.
  apply levelS_age1 in H0.
  destruct H0 as [y ?].
  exists y.
  assert (age x y).
  unfold age.
  exact H0.
  split.
  exact H1.
  apply age_level in H1.
  rewrite H in H1.
  inversion H1.
  reflexivity.
Qed.

Lemma clos_refl_trans_addone: forall (A : Type) (R : relation A) (x y z: A), R x y -> clos_refl_trans A R y z -> clos_refl_trans A R x z.
Proof.
  intros.
  apply (rt_step A R x y) in H.
  apply rt_trans with y.
  exact H.
  exact H0.
Qed.

Lemma necR_same_level: forall {A:Type} {agA:ageable A} (x y x': A), necR x x' -> level x = level y -> exists y', (necR y y' /\ level x' = level y').
Proof.
  intros A agA x y.
  remember (level x) as n.
  generalize Heqn; clear Heqn.
  generalize x y; clear x y.
  induction n.
  (* basic step *)
  + intros.
    apply necR_level in H.
    rewrite <- Heqn in H.
    destruct (level x') eqn:HH; [|omega].
    exists y.
    split.
       unfold necR; auto.
       exact H0.
  + intros.
    apply nec_refl_or_later in H.
    destruct H.
    - exists y.
      split.
         unfold necR; auto.
         rewrite <- H0. rewrite -> Heqn. rewrite H. reflexivity.
    - apply levelS_age in H0; destruct H0 as [y'' [? ?]].
      apply levelS_age in Heqn; destruct Heqn as [x'' [? ?]].
      remember (IHn x'' y'' H3 x') as HH; clear HeqHH.
      assert(necR x'' x').
        apply (age_later_nec x); [exact H2 | exact H].
      apply HH in H4; clear HH; [|exact H1].
      destruct H4 as [y' [? ?]].
      exists y'.
      split; [| exact H5].
      unfold necR.
      apply clos_refl_trans_addone with y''; [exact H0| exact H4].
Qed.

Lemma laterR_same_level: forall {A:Type} {agA:ageable A} (x y x': A), laterR x x' -> level x = level y -> exists y', (laterR y y' /\ level x' = level y').
Proof.
  intros.
  assert (HH: laterR x x'). exact H.
  apply laterR_necR in H.
  assert (exists y' : A, necR y y' /\ level x' = level y').
     apply (necR_same_level x y).
     exact H.
     exact H0.
  destruct H1 as [y' [? ?]].
  exists y'.
  split; [|exact H2].
  apply nec_refl_or_later in H1.
  destruct H1.
  + apply laterR_level in HH.
    subst.
    rewrite <- H0 in H2.
    omega.
  + exact H1.
Qed.

Lemma power_age_parallel: forall {A:Type} {agA:ageable A} (x x' y: A) n,
  level x = level y ->
  relation_power n age x x' ->
  exists y', relation_power n age y y'.
Proof.
  intros.
  destruct (partial_fun_power n age1 y) eqn:?H.
  + exists a.
    apply power_age_age1; auto.
  + apply power_age_age1 in H0.
    apply power_age1_level_small in H1.
    rewrite <- H in H1.
    apply power_age1_level_small in H1.
    rewrite H0 in H1.
    inversion H1.
Qed.

Lemma power_age_parallel': forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (x x' y: A) n,
  core x = core y ->
  relation_power n age x x' ->
  exists y', relation_power n age y y' /\ core x' = core y'.
Proof.
  intros.
  assert (level x = level y).
  1:{
    pose proof level_core y.
    pose proof level_core x.
    rewrite H in H2.
    congruence.
  }
  destruct (power_age_parallel x x' y n H1 H0) as [y' ?H].
  exists y'.
  split; [auto |].
  eapply power_age_core_eq; eauto.
Qed.

