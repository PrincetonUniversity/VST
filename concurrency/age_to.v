(* The definitions and other results of age_by and age_to should be
moved here from msl/ageable.v.  Alternatively, this can be moved to
msl/ageable.v (or this file to msl/) eventually, but we keep it here
for now to reduce compilation time. *)

Require Import msl.ageable.
Require Import Coq.omega.Omega.

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

Require Import msl.predicates_hered.

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

Lemma age_by_age_by_pred {A} `{agA : ageable A} (P : pred A) x n1 n2 :
  le n1 n2 ->
  app_pred P (age_by n1 x) ->
  app_pred P (age_by n2 x).
Proof.
  intros l. replace n2 with ((n2 - n1) + n1) by auto with *.
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
  rewrite IHn. 2:omega.
  unfold age1' in *.
  destruct (age1 (age_by n x)) as [y|] eqn:Ey. auto.
  exfalso. rewrite age1_level0 in Ey.
  rewrite level_age_by in Ey. omega.
Qed.

Lemma age_to_ageN {A} `{agA : ageable A} n (x : A) :
  ageN (level x - n) x = Some (age_to n x).
Proof.
  apply age_by_ageN. auto with *.
Qed.

Lemma age_by_1 {A} {_ : ageable A} x : 0 < level x -> age x (age_by 1 x).
Proof.
  intros l.
  unfold age_by, age1'; simpl.
  destruct (age1 x) eqn:E; eauto.
  apply age1_level0 in E.
  omega.
Qed.

Lemma age_to_1 {A} {_ : ageable A} n x : level x = S n -> age x (age_to n x).
Proof.
  unfold age_to; intros E; rewrite E.
  replace (S n - n) with 1 by auto with *.
  apply age_by_1. auto with *.
Qed.
