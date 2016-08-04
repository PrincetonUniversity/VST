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
