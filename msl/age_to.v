(* The definitions and other results of age_by and age_to should be
moved here from msl/ageable.v.  Alternatively, this can be moved to
msl/ageable.v (or this file to msl/) eventually, but we keep it here
for now to reduce compilation time. *)

Require Import VST.msl.ageable.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.sepalg.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.sepalg_generators.
Require Import Lia.

(* Apply [age1] n times (meaningful when [n <= level x] *)

Definition age1' {A} `{agA : ageable A} : A -> A :=
  fun x => match age1 x with Some y => y | None => x end.

Definition age_by n {A} `{agA : ageable A} : A -> A := Nat.iter n age1'.

Lemma level_age1' {A} `{agA : ageable A} x : level (age1' x) = level x - 1.
Proof.
  unfold age1'. destruct (age1 x) eqn:E.
  - apply age_level in E. lia.
  - apply age1_level0 in E. lia.
Qed.

Lemma level_age_by n {A} `{agA : ageable A} x : level (age_by n x) = level x - n.
Proof.
  revert x; induction n; intros x; simpl.
  - lia.
  - simpl. rewrite level_age1'. rewrite IHn. lia.
Qed.

Lemma age_age_by n {A} `{agA : ageable A} (x y : A) : age x y -> age_by (S n) x = age_by n y.
Proof.
  intros E.
  induction n.
  - simpl.
    unfold age1' in *.
    rewrite E. auto.
  - change (age1' (age_by (S n) x) = age_by (S n) y).
    rewrite IHn.
    reflexivity.
Qed.

(* Age [x] to the level [k] (meaningul when [k <= level x] *)
Definition age_to k {A} `{agA : ageable A} (x : A) : A := age_by (level x - k) x.

Lemma level_age_to k {A} `{agA : ageable A} x : k <= level x -> level (age_to k x) = k.
Proof.
  intros L. unfold age_to.
  rewrite level_age_by; lia.
Qed.

(* Proof techniques for age_to *)
Lemma age_to_lt k {A} `{agA : ageable A} (x : A) : k < level x -> exists y, age x y /\ age_to k x = age_to k y.
Proof.
  intros L.
  destruct (age1 x) as [y|] eqn:Ex; swap 1 2.
  - rewrite age1_level0 in Ex. lia.
  - exists y; split; auto.
    unfold age_to.
    pose proof age_level _ _ Ex as E.
    replace (level x - k) with (S (level y - k)) by lia.
    generalize (level y - k).
    clear E L.
    intros.
    apply age_age_by, Ex.
Qed.

Lemma age_to_ge k {A} `{agA : ageable A} (x : A) : k >= level x -> age_to k x = x.
Proof.
  intros E. unfold age_to.
  replace (level x - k) with 0 by lia.
  reflexivity.
Qed.

Lemma age_to_eq k {A} `{agA : ageable A} (x : A) : k = level x -> age_to k x = x.
Proof.
  intros ->; apply age_to_ge, Le.le_refl.
Qed.

Lemma age_age_to n {A} `{agA : ageable A} x y : level x = S n -> age x y -> age_to n x = y.
Proof.
  intros E Y.
  assert (L : (n < level x)%nat) by lia.
  unfold age_to. rewrite E. replace (S n - n) with 1 by lia.
  simpl. unfold age1'. rewrite Y. reflexivity.
Qed.

Lemma age_by_ind {A} `{agA : ageable A} (P : A -> Prop) :
  (forall x y, age x y -> P x -> P y) ->
  forall x n, P x -> P (age_by n x).
Proof.
  intros IH x n.
  unfold age_by.
  induction n; intros Px.
  - auto.
  - simpl. unfold age1' at 1.
    destruct (age1 (Nat.iter n age1' x)) as [y|] eqn:Ey; auto.
    eapply IH; eauto.
Qed.

Lemma age_to_ind {A} `{agA : ageable A} (P : A -> Prop) :
  (forall x y, age x y -> P x -> P y) ->
  forall x n, P x -> P (age_to n x).
Proof.
  intros IH x n.
  apply age_by_ind, IH.
Qed.

Lemma age_to_ind_refined n {A} `{agA : ageable A} (P : A -> Prop) :
  (forall x y, age x y -> n <= level y -> P x -> P y) ->
  forall x, P x -> P (age_to n x).
Proof.
  intros IH x Px.
  assert (dec : n >= level x \/ n <= level x) by lia.
  destruct dec as [Ge|Le].
  - rewrite age_to_ge; auto.
  - eapply (age_to_ind (fun x => n <= level x -> P x)); auto.
    + intros x0 y H H0 H1.
      eapply IH; eauto.
      apply age_level in H.
      apply H0.
      lia.
    + rewrite level_age_to; auto.
Qed.

Lemma iter_iter n m {A} f (x : A) : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof.
  induction n; auto; simpl. rewrite IHn; auto.
Qed.

Lemma age_by_age_by n m  {A} `{agA : ageable A} (x : A) : age_by n (age_by m x) = age_by (n + m) x.
Proof.
  apply iter_iter.
Qed.

Lemma age_by_ind_opp {A} `{agA : ageable A} (P : A -> Prop) :
  (forall x y, age x y -> P y -> P x) ->
  forall x n, P (age_by n x) -> P x.
Proof.
  intros IH x n.
  unfold age_by.
  induction n; intros Px.
  - auto.
  - simpl in Px. unfold age1' at 1 in Px.
    destruct (age1 (Nat.iter n age1' x)) as [y|] eqn:Ey; auto.
    eapply IH in Ey; eauto.
Qed.

Lemma age_to_ind_opp {A} `{agA : ageable A} (P : A -> Prop) :
  (forall x y, age x y -> P y -> P x) ->
  forall x n, P (age_to n x) -> P x.
Proof.
  intros IH x n.
  apply age_by_ind_opp, IH.
Qed.

Lemma rewrite_age_to {A} `{agA : ageable A} (P : A -> Prop) :
  (forall x y, age x y -> P x <-> P y) ->
  forall x n, P x <-> P (age_to n x).
Proof.
  intros IH x n; split.
  - apply age_to_ind. intros; rewrite <-IH; eauto.
  - apply age_to_ind_opp. intros; rewrite IH; eauto.
Qed.

Lemma level_age_to_le k {A} `{agA : ageable A} x : level (age_to k x) <= level x.
Proof.
  destruct (Compare_dec.le_lt_dec k (level x)) as [l|l]. rewrite level_age_to; auto.
  rewrite age_to_ge; lia.
Qed.

Lemma level_age_to_le' k {A} `{agA : ageable A} x : level (age_to k x) <= k.
Proof.
  destruct (Compare_dec.le_lt_dec k (level x)) as [l|l]. rewrite level_age_to; auto.
  rewrite age_to_ge; lia.
Qed.

Lemma age_by_necR {A} `{agA : ageable A} n x : necR x (age_by n x).
Proof.
  generalize (necR_refl x).
  generalize x at 1 3; intros u.
  apply age_by_ind; clear x.
  intros x y a N.
  constructor 3 with x; auto.
  constructor; auto.
Qed.

Lemma age_to_necR {A} `{agA : ageable A} n x : necR x (age_to n x).
Proof.
  apply age_by_necR.
Qed.

Lemma necR_age_by {A} `{agA : ageable A} x x' : necR x x' -> x' = age_by (level x - level x') x.
Proof.
  intros N; induction N.
  - rewrite (age_level _ _ H).
    replace (S _ - _) with 1. 2:lia.
    simpl. unfold age1'. rewrite H; auto.
  - replace (_ - _) with 0. 2:lia. reflexivity.
  - rewrite IHN2, IHN1.
    rewrite age_by_age_by.
    repeat rewrite level_age_by.
    f_equal.
    apply necR_level in N1.
    apply necR_level in N2.
    replace (_ x - (_ x - _ y)) with (level y) by lia.
    replace (_ y - _ z + (_ x - _ y)) with (level x - level z) by lia.
    lia.
Qed.

Lemma necR_age_to {A} `{agA : ageable A} x x' : necR x x' -> x' = age_to (level x') x.
Proof.
  apply necR_age_by.
Qed.

Lemma necR_age_by_iff {A} `{agA : ageable A} x x' : necR x x' <-> x' = age_by (level x - level x') x.
Proof.
  split. apply necR_age_by. intros ->. apply age_by_necR.
Qed.

Lemma necR_age_to_iff {A} `{agA : ageable A} x x' : necR x x' <-> x' = age_to (level x') x.
Proof.
  apply necR_age_by_iff.
Qed.

Lemma age_to_pred {A} `{agA : ageable A} (P : pred A) x n :
  app_pred P x ->
  app_pred P (age_to n x).
Proof.
  apply age_to_ind. clear x n.
  destruct P as [x h]. apply h.
Qed.

Lemma age_by_pred {A} `{agA : ageable A} (P : pred A) x n :
  app_pred P x ->
  app_pred P (age_by n x).
Proof.
  apply age_by_ind. clear x n.
  destruct P as [x h]. apply h.
Qed.

Lemma pred_age1' {A} `{agA : ageable A} (R : pred A) x : app_pred R x -> app_pred R (age1' x).
Proof.
  unfold age1'. destruct (age1 x) as [phi' | ] eqn:Ephi'; auto.
  destruct R as [R h]. apply h. apply Ephi'.
Qed.

Lemma age_by_age_by_pred {A} `{agA : ageable A} (P : pred A) x n1 n2 :
  le n1 n2 ->
  app_pred P (age_by n1 x) ->
  app_pred P (age_by n2 x).
Proof.
  intros l. replace n2 with ((n2 - n1) + n1) by lia.
  rewrite <-age_by_age_by.
  apply age_by_pred.
Qed.

Fixpoint composeOptN' {A} (f : A -> option A) n x :=
  match n with
  | 0 => Some x
  | S n =>
    match composeOptN' f n x with
    | Some y => f y
    | None => None
    end
  end.

Lemma composeOptN_assoc_aux_None {A} (f : A -> option A) n x :
  f x = None ->
  match composeOptN f n x with
  | Some x => f x
  | None => None
  end = None.
Proof.
  revert x; induction n; intros x E; simpl; auto.
  destruct (f x); congruence.
Qed.

Lemma composeOptN_assoc_aux_Some {A} (f : A -> option A) n x y :
  f x = Some y ->
  match composeOptN f n x with
  | Some x => f x
  | None => None
  end = composeOptN f n y.
Proof.
  revert x y; induction n; intros x y Ey; simpl. auto.
  rewrite Ey.
  destruct (f y) as [z|] eqn:Ez.
  - eauto.
  - apply composeOptN_assoc_aux_None, Ez.
Qed.

Lemma composeOptN_assoc {A} (f : A -> option A) n x :
  composeOptN f n x = composeOptN' f n x.
Proof.
  revert x; induction n; intros x; simpl. auto.
  destruct (f x) as [y|] eqn:Ey; rewrite <-IHn.
  - erewrite composeOptN_assoc_aux_Some; eauto.
  - rewrite composeOptN_assoc_aux_None; eauto.
Qed.

Lemma age_by_ageN {A} `{agA : ageable A} n (x : A) :
  n <= level x ->
  ageN n x = Some (age_by n x).
Proof.
  revert x; induction n; intros x l. reflexivity.
  unfold ageN.
  rewrite composeOptN_assoc; simpl; rewrite <-composeOptN_assoc.
  change (composeOptN age1 n x) with (ageN n x).
  rewrite IHn. 2:lia.
  unfold age1' in *.
  destruct (age1 (age_by n x)) as [y|] eqn:Ey. auto.
  exfalso. rewrite age1_level0 in Ey.
  rewrite level_age_by in Ey. lia.
Qed.

Lemma age_to_ageN {A} `{agA : ageable A} n (x : A) :
  ageN (level x - n) x = Some (age_to n x).
Proof.
  apply age_by_ageN. lia.
Qed.

Lemma age_by_1 {A} {_ : ageable A} x : 0 < level x -> age x (age_by 1 x).
Proof.
  intros l.
  unfold age_by, age1'; simpl.
  destruct (age1 x) eqn:E; eauto.
  apply age1_level0 in E.
  lia.
Qed.

Lemma age_to_1 {A} {_ : ageable A} n x : level x = S n -> age x (age_to n x).
Proof.
  unfold age_to; intros E; rewrite E.
  replace (S n - n) with 1 by lia.
  apply age_by_1. lia.
Qed.

Lemma age_to_identy {A} `{asaA: Age_alg A}: forall k phi,
    identity phi -> identity (age_to k phi).
Proof.
  intros k phi. unfold age_to. generalize (level phi - k); intros n; revert phi.
  induction n; intros phi id; simpl; auto. unfold age1'.
  destruct (age1 (age_by n phi)) eqn:E; auto.
  eapply age_identity. apply E. auto.
Qed.

Lemma age_to_join_eq {A}  {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A} :
  forall k x1 x2 x3,
    join x1 x2 x3 ->
    k <= level x3 ->
    join (age_to k x1) (age_to k x2) (age_to k x3).
Proof.
  intros k x1 x2 x3 J.
  remember (level x3) as l3 eqn:e3; symmetry in e3.
  pose proof join_level _ _ _ J as [e1 e2]; rewrite e3 in e1, e2.
  revert l3 x1 x2 x3 e1 e2 e3 J.
  intros n; induction n as [ n IHn ] using strong_nat_ind. intros x1 x2 x3 e1 e2 e3 J L.
  destruct (Compare_dec.le_lt_eq_dec _ _ L) as [Lt | ->]; swap 1 2.
  now do 3 (rewrite age_to_eq at 1; auto).
  assert (l1 : k < level x1) by lia.
  assert (l2 : k < level x2) by lia.
  assert (l3 : k < level x3) by lia.
  destruct (age_to_lt _ x1 l1) as [x1' [E1 ->]].
  destruct (age_to_lt _ x2 l2) as [x2' [E2 ->]].
  destruct (age_to_lt _ x3 l3) as [x3' [E3 ->]].
  pose proof @age1_join_eq A _ _ _ _ _ _ _ J _ E1 _ E2 _ E3.
  pose proof @af_level2 A level age1 (@age_facts _ agA) _ _ E1.
  pose proof @af_level2 A level age1 (@age_facts _ agA) _ _ E2.
  pose proof @af_level2 A level age1 (@age_facts _ agA) _ _ E3.
  apply IHn with (level x1'); lia || auto.
Qed.
