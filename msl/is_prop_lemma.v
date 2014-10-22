Require Import msl.base.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.age_sepalg.
Require Import msl.predicates_hered.
Require Import msl.predicates_sl.

Definition is_prop {A:Type} {agA:ageable A} (P: pred A): Prop := forall x y:A, (level x = level y) -> P x -> P y.

Lemma prop_is_prop: forall {A:Type} {agA:ageable A} (P: Prop), is_prop (predicates_hered.prop P).
Proof.
  unfold is_prop.
  intros.
  unfold prop in *.
  simpl in *.
  exact H0.
Qed.

Lemma is_prop_andp: forall {A:Type} {agA:ageable A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P && Q).
Proof.
  unfold is_prop.
  intros.
  unfold andp in *.
  simpl in *.
  destruct H2 as [HH1 HH2]; apply (H _ y H1) in HH1; apply (H0 _ y H1) in HH2.
  split; [exact HH1 | exact HH2].  
Qed.

Lemma is_prop_orp: forall {A:Type} {agA:ageable A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P || Q).
Proof.
  unfold is_prop.
  intros.
  unfold orp in *.
  simpl in *.
  destruct H2 as [HH1 | HH2].
     apply (H _ y H1) in HH1. auto.
     apply (H0 _ y H1) in HH2. auto.
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

Lemma is_prop_imp: forall {A:Type} {agA:ageable A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P --> Q).
Proof.
  unfold is_prop.
  intros.
  unfold imp in *.
  simpl in *.
  intros.
  apply (necR_same_level y x a') in H3; [| apply eq_sym; exact H1].
  destruct H3 as [a'' [? ?]].
  apply H2 in H3.
  apply (H0 a'' a'); [apply eq_sym; exact H5 | exact H3].
  apply (H a' a''); [assumption | assumption].
Qed.

Lemma is_prop_sepcon: forall {A:Type} {agA:ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P * Q).
Proof.
  intros.
  unfold is_prop in *.
  unfold sepcon in *.
  simpl in *.
  intros.
  destruct H2 as [x1 [x2 [? [? ?]]]].
  exists (core y), y.
  assert (join (core y) y y); [apply core_unit|].
  split; [exact H5|].
  apply join_level in H5.
  apply join_level in H2.
  destruct H5.
  destruct H2.
  split.
    apply H with x1; [omega | exact H3].
    apply H0 with x2; [omega | exact H4].
Qed.

Lemma is_prop_wand: forall {A:Type} {agA:ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (wand P Q).
Proof.
  intros.
  pose proof I.
  unfold is_prop in *.
  unfold wand in *.
  simpl in *.
  intros.
  apply necR_same_level with y x x' in H4; [| apply eq_sym; exact H2].
  destruct H4 as [y' [? ?]].
  remember H5 as H8; clear HeqH8.
  apply join_level in H5.
  destruct H5.
  assert (join y' (core y') y').
    apply join_comm.
    apply core_unit.
  apply (H3 y' (core y') y') in H4; [| exact H10|].
  + rewrite -> H7 in H5.
    apply H0 with y'; [exact H5 | exact H4].
  + apply join_level in H10.
    destruct H10.
    apply H with y0; [omega|exact H6].
Qed.

Lemma is_prop_ewand: forall {A:Type} {agA:ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (ewand P Q).
Proof.
  intros.
  pose proof I.
  unfold is_prop in *.
  unfold ewand in *.
  simpl in *.
  intros.
  destruct H3 as [x1 [x2 [? [? ?]]]].
  exists (core y), y.
  assert (join (core y) y y); [apply core_unit|].
  split; [exact H6|].
  apply join_level in H6.
  apply join_level in H3.
  destruct H6.
  destruct H3.
  split.
    apply H with x1; [omega | exact H4].
    apply H0 with x2; [omega | exact H5].
Qed.

Lemma is_prop_later: forall {A:Type} {agA:ageable A} P, is_prop P -> is_prop (|> P).
Proof.
  unfold is_prop.
  intros.
  unfold box in *.
  simpl in *.
  intros.
  remember (laterR_same_level y x a') as HH; clear HeqHH.
  apply HH in H2; [|apply eq_sym; exact H0]; clear HH.
  destruct H2 as [a'' [? ?]].  
  apply H with a''.
  apply eq_sym; exact H3.
  apply H1; exact H2.
Qed.

Lemma is_prop_exp: forall {A:Type} {agA:ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {B: Type} (P: B -> pred A), (forall x, is_prop (P x)) -> is_prop (EX x:B, P x).
  intros.
  unfold is_prop in *.
  unfold exp in *.
  simpl in *.
  intros.
  destruct H1 as [b ?].
  exists b.
  apply (H b x y H0 H1).
Qed.

Lemma is_prop_allp: forall {A:Type} {agA:ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {B: Type} (P: B -> pred A), (forall x, is_prop (P x)) -> is_prop (ALL x:B, P x).
  intros.
  unfold is_prop in *.
  unfold allp in *.
  simpl in *.
  intros.
  apply (H b x y H0 (H1 b)).
Qed.

Lemma is_prop_andp_sepcon: forall {A:Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} (P Q R: pred A), is_prop P -> ((P && Q) * R = P && (Q * R))%pred.
Proof.
  intros.
  unfold is_prop in H.
  apply pred_ext; unfold derives; intros;
  unfold sepcon in *; unfold andp in *;
  simpl in *.
  + destruct H0 as [y [z [? [[? ?] ?]]]].
    split.
    - apply join_level in H0.
      destruct H0.
      apply H with y; [exact H0|exact H1].
    - exists y, z.
      auto.
  + destruct H0 as [H0 [y [z [? [? ?]]]]].
    exists y, z.
    repeat (split; auto).
    apply join_level in H1.
    destruct H1.
    apply H with a; [apply eq_sym|]; auto.
Qed.

Lemma is_prop_sepcon_is_prop: forall {A:Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} (P Q R: pred A), is_prop P -> (P * Q = (P && Q) * TT)%pred.
Proof.
  intros.
  unfold is_prop in H.
  apply pred_ext; unfold derives; intros;
  unfold sepcon in *; unfold andp in *;
  unfold prop in *; simpl in *.
  + destruct H0 as [y [z [? [? ?]]]].
    exists z, y.
    split; [apply join_comm; exact H0|repeat (split; auto)].
    apply join_level in H0.
    assert(level y = level z); [omega|].
    apply H with y; [exact H3 | exact H1].
  + destruct H0 as [y [z [? [[? ?] HH]]]]; clear HH.
    exists z, y.
    split; [apply join_comm; exact H0|repeat (split; auto)].
    apply join_level in H0.
    assert(level y = level z); [omega|].
    apply H with y; [exact H3 | exact H1].
Qed.

Lemma is_prop_andp_eq: forall {A:Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {CaA: Canc_alg A} (P Q R: pred A), is_prop P -> (P && Q = (P && emp) * Q)%pred.
(* In fact, this can be proved by is_prop_andp_sepcon *)
Proof.
  intros.
  unfold is_prop in H.
  apply pred_ext; unfold derives; intros;
  unfold sepcon in *; unfold andp in *;
  unfold emp in *; simpl in *.
  + destruct H0.
    exists (core a), a.
    assert(join (core a) a a); [apply core_unit|].
    repeat (split; auto).
    - apply join_level in H2; destruct H2.
      apply H with a;[apply eq_sym; exact H2|exact H0].
    - apply unit_identity with a.
      unfold unit_for; exact H2.
  + destruct H0 as [y [z [? [[? ?] ?]]]].
    unfold identity in H2.
    remember (H2 z a  H0) as HH; clear HeqHH; clear H2.
    subst.
    split; [| exact H3].
    apply join_level in H0; destruct H0.
    apply H with y; assumption.
Qed.

Lemma right_is_prop: forall {A:Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {CaA: Canc_alg A} (P Q R: pred A), (is_prop P) -> (Q |-- P) -> (sepcon Q R |-- P)%pred.
Proof.
  intros.
  unfold is_prop in H.
  unfold derives in *; unfold sepcon in *; intros.
  simpl in *.
  destruct H1 as [b [c [? [? _]]]].
  apply join_level in H1.
  destruct H1 as [? _].
  exact (H b a H1 (H0 b H2)).
Qed.

Lemma later_prop_andp_sepcon: forall {A: Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A}(P: Prop) (Q R: pred A), 
(((|> !! P) && Q) * R = (|> !! P) && (Q * R))%pred.
Proof.
  intros.
  assert (@is_prop A agA (|> !! P)).
  apply is_prop_later.
  apply prop_is_prop.
  apply (is_prop_andp_sepcon (|>!!P) Q R).
  exact H.
Qed.

