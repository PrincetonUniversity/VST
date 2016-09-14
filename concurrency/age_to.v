(* The definitions and other results of age_by and age_to should be
moved here from msl/ageable.v.  Alternatively, this can be moved to
msl/ageable.v (or this file to msl/) eventually, but we keep it here
for now to reduce compilation time. *)

Require Import msl.ageable.

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
