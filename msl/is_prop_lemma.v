Require Import msl.base.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.age_sepalg.
Require Import msl.predicates_hered.
Require Import msl.predicates_sl.

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

Lemma power_age_core: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} {CaA: Canc_alg A} (x y: A) n,
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

Definition is_prop {A:Type} {agA:ageable A} {JA: Join A} {SaA: Sep_alg A} (P: pred A): Prop :=
  forall x y:A, core x = core y -> P x -> P y.

Lemma prop_is_prop: forall {A:Type} {agA:ageable A} {JA: Join A} {SaA: Sep_alg A} (P: Prop), is_prop (predicates_hered.prop P).
Proof.
  unfold is_prop.
  intros.
  unfold prop in *.
  simpl in *.
  tauto.
Qed.

Lemma is_prop_andp: forall {A:Type} {agA:ageable A} {JA: Join A} {SaA: Sep_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P && Q).
Proof.
  unfold is_prop.
  intros.
  unfold andp in *.
  simpl in *.
  specialize (H x y H1).
  specialize (H0 x y H1).
  tauto.
Qed.

Lemma is_prop_orp: forall {A:Type} {agA:ageable A} {JA: Join A} {SaA: Sep_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P || Q).
Proof.
  unfold is_prop.
  intros.
  unfold orp in *.
  simpl in *.
  specialize (H x y H1).
  specialize (H0 x y H1).
  tauto.
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
  Focus 1. {
    pose proof level_core y.
    pose proof level_core x.
    rewrite H in H2.
    congruence.
  } Unfocus.
  destruct (power_age_parallel x x' y n H1 H0) as [y' ?H].
  exists y'.
  split; [auto |].
  eapply power_age_core_eq; eauto.
Qed.

Lemma is_prop_imp: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P --> Q).
Proof.
  unfold is_prop.
  intros.
  unfold imp in *.
  simpl in *.
  intros.
  rename a' into y'.
  pose proof H3.
  apply necR_power_age in H5.
  destruct H5 as [n ?H].
  destruct (power_age_parallel' _ y' _ n (eq_sym H1) H5) as [x' [?H ?H]].
  apply (H0 _ _ (eq_sym H7)).
  apply H2.
  + apply necR_power_age; exists n; auto.
  + apply (H _ _ H7); auto.
Qed.

Lemma is_prop_sepcon: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (P * Q).
Proof.
  unfold is_prop.
  unfold sepcon.
  intros.
  simpl in H2 |- *.
  destruct H2 as [x' [x'' [? [? ?]]]].
  pose proof join_core H2.
  pose proof join_core (join_comm H2).
  exists (core y), y.
  repeat split.
  + apply core_unit.
  + apply H with x'; auto.
    rewrite core_idem.
    congruence.
  + apply H0 with x''; auto.
    congruence.
Qed.

Lemma is_prop_wand: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (wand P Q).
Proof.
  intros.
  unfold is_prop in *.
  unfold wand in *.
  simpl in *.
  intros.
  rename x' into y'.
  rename y0 into w'.
  rename z into z'.
  apply necR_power_age in H3.
  destruct H3 as [n ?H].
  pose proof power_age_parallel' _ y' _ n (eq_sym H1) H3.
  destruct H6 as [x' [?H ?H]].
  pose proof join_core H4.
  pose proof join_core (join_comm H4).
  apply H0 with x'; [congruence |].
  apply (H2  x' (core x') x').
  + apply necR_power_age.
    exists n; auto.
  + apply join_comm, core_unit.
  + apply H with w'; auto.
    rewrite core_idem.
    congruence.
Qed.

Lemma is_prop_ewand: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (P Q: pred A), is_prop P -> is_prop Q -> is_prop (ewand P Q).
Proof.
  intros.
  unfold is_prop in *.
  unfold ewand in *.
  simpl in *.
  intros.
  destruct H2 as [x1 [x2 [? [? ?]]]].
  pose proof join_core H2.
  pose proof join_core (join_comm H2).
  exists (core y), y.
  split; [apply core_unit |].
  split.
  + apply H with x1; auto.
    rewrite core_idem.
    congruence.
  + apply H0 with x2; auto.
    congruence.
Qed.

Lemma is_prop_later: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} P, is_prop P -> is_prop (|> P).
Proof.
  unfold is_prop.
  intros.
  unfold box in *.
  simpl in *.
  intros.
  apply laterR_power_age in H2.
  destruct H2 as [n ?H].
  rename a' into y'.
  destruct (power_age_parallel' _ y' _ _ (eq_sym H0) H2) as [x' [? ?]].
  apply H with x'; auto.
  apply H1.
  apply laterR_power_age.
  exists n; auto.
Qed.

Lemma is_prop_exp: forall {A:Type} {agA:ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {B: Type} (P: B -> pred A), (forall x, is_prop (P x)) -> is_prop (EX x:B, P x).
Proof.
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
Proof.
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
    - pose proof join_core H0.
      pose proof join_core (join_comm H0).
      apply H with y; auto.
    - exists y, z.
      auto.
  + destruct H0 as [H0 [y [z [? [? ?]]]]].
    exists y, z.
    repeat (split; auto).
    pose proof join_core H1.
    pose proof join_core (join_comm H1).
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
    pose proof join_core H0.
    pose proof join_core (join_comm H0).
    apply H with y; auto.
    congruence.
  + destruct H0 as [y [z [? [[? ?] HH]]]]; clear HH.
    exists z, y.
    split; [apply join_comm; exact H0|repeat (split; auto)].
    pose proof join_core H0.
    pose proof join_core (join_comm H0).
    apply H with y; auto.
    congruence.
Qed.

Lemma is_prop_andp_eq: forall {A:Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {CaA: Canc_alg A} (P Q R: pred A), is_prop P -> (P && Q = (P && emp) * Q)%pred.
Proof.
  intros.
  unfold is_prop in H.
  apply pred_ext; unfold derives; intros;
  unfold sepcon in *; unfold andp in *;
  unfold emp in *; simpl in *.
  + destruct H0.
    exists (core a), a.
    repeat (split; auto).
    - apply core_unit.
    - apply H with a; auto.
      rewrite core_idem.
      reflexivity.
    - apply unit_identity with a.
      apply core_unit.
  + destruct H0 as [y [z [? [[? ?] ?]]]].
    unfold identity in H2.
    remember (H2 z a  H0) as HH; clear HeqHH; clear H2.
    subst.
    split; [| exact H3].
    apply H with y; auto.
    eapply join_core, H0.
Qed.

Lemma right_is_prop: forall {A:Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A} {CaA: Canc_alg A} (P Q R: pred A), (is_prop P) -> (Q |-- P) -> (sepcon Q R |-- P)%pred.
Proof.
  intros.
  unfold is_prop in H.
  unfold derives in *; unfold sepcon in *; intros.
  simpl in *.
  destruct H1 as [b [c [? [? _]]]].
  pose proof join_core H1.
  pose proof join_core (join_comm H1).
  apply H with b; auto.
Qed.

Lemma later_prop_andp_sepcon: forall {A: Type} {agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SaA: Sep_alg A}{XA: Age_alg A}(P: Prop) (Q R: pred A), 
(((|> !! P) && Q) * R = (|> !! P) && (Q * R))%pred.
Proof.
  intros.
  assert (@is_prop A agA _ _ (|> !! P))%pred.
  apply is_prop_later.
  apply prop_is_prop.
  apply (is_prop_andp_sepcon (|>!!P) Q R).
  exact H.
Qed.

