Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.

Local Open Scope logic.

Fixpoint power_later (n:nat) P :=
    match n with
    | 0%nat => P
    | S n' => later (power_later n' P)
    end
.

Lemma power_now_later: forall n P, P |-- power_later n P.
Proof.
   induction n.
   (* Base step *)
   intros. unfold power_later.
   apply derives_refl.
   (* Induction step *)
   intros. simpl.
   apply derives_trans with (power_later n P).
   apply IHn. apply now_later.
Qed.

Lemma power_later_andp: forall (n:nat) (P Q : mpred), power_later n (P && Q) = (power_later n P) && (power_later n Q).
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. apply later_andp.
Qed.

Lemma power_later_exp': forall (n:nat) T (any:T) F,
     power_later n (EX x:T, F x) = EX x:T, (power_later n (F x)).
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> (IHn T any). apply (later_exp' T any).
Qed.

Lemma power_later_sepcon: forall n P Q, power_later n (P * Q) = (power_later n P) * (power_later n Q).
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. apply later_sepcon.
Qed.

Lemma power_later_connect: forall n P, power_later n (|> P) = power_later (n + 1) P.
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. reflexivity.
Qed.

Lemma power_later_connect': forall n P, |> (power_later n P) = power_later (n + 1) P.
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. reflexivity.
Qed.

Lemma power_later_derives: forall n:nat, forall P Q:mpred,
   P |-- Q -> (power_later n P) |-- (power_later n Q).
Proof.
   induction n; intros; simpl.
   assumption.
   apply later_derives. apply IHn. assumption.
Qed.

Lemma power_later_TT: forall n, TT = power_later n TT.
Proof.
   intros.
   apply pred_ext.
   apply power_now_later.
   normalize.
Qed.

Lemma corable_power_later: forall n P, corable P -> corable (power_later n P).
Proof.
  intros.
  induction n; simpl.
  + exact H.
  + exact (corable_later _ IHn).
Qed.

Ltac power_normalize :=
    repeat (
      try rewrite -> power_later_andp;
      try rewrite -> power_later_sepcon;
      try rewrite <- power_later_TT)
.

Lemma power_later_erase: forall n P Q R, P * Q |-- R -> power_later n P * Q |-- power_later n R.
Proof.
  intros.
  apply derives_trans with (power_later n (P * Q)).
  power_normalize.
  cancel.
  apply power_now_later.
  apply power_later_derives.
  assumption.
Qed.

Lemma power_prop_andp_sepcon:
  forall (n:nat) P Q R, ((power_later n (!! P)) && Q) * R = (power_later n (!! P)) && (Q * R).
Proof.
  intros.
  apply (corable_andp_sepcon1 (power_later n (!! P))).
  apply corable_power_later.
  exact (corable_prop P).
Qed.