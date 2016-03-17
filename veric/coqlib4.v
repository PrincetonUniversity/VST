Require Import compcert.lib.Coqlib.
Require Import Integers.
Require Import EqNat.
Require Import msl.Coqlib2.
Require Import Relations.
Require Export msl.eq_dec.
Lemma power_nat_divide: forall n m, two_power_nat n <= two_power_nat m -> Z.divide (two_power_nat n) (two_power_nat m).
Proof.
  intros.
  repeat rewrite two_power_nat_two_p in *.
  unfold Zdivide.
  exists (two_p (Z.of_nat m - Z.of_nat n)).
  assert ((Z.of_nat m) = (Z.of_nat m - Z.of_nat n) + Z.of_nat n) by omega.
  rewrite H0 at 1.
  assert (Z.of_nat m >= 0) by omega.
  assert (Z.of_nat n >= 0) by omega.
  assert (Z.of_nat n <= Z.of_nat m).
    destruct (Z_le_gt_dec (Z.of_nat n) (Z.of_nat m)).
    exact l.
    assert (Z.of_nat m < Z.of_nat n) by omega.
    assert (two_p (Z.of_nat m) < two_p (Z.of_nat n)) by (apply two_p_monotone_strict; omega).
    omega.  
  apply (two_p_is_exp (Z.of_nat m - Z.of_nat n) (Z.of_nat n)); omega.
Qed.

Lemma power_nat_divide': forall n m: Z,
  (exists N, n = two_power_nat N) ->
  (exists M, m = two_power_nat M) ->
  n >= m ->
  (m | n).
Proof.
  intros.
  destruct H, H0.
  subst.
  apply power_nat_divide.
  omega.
Qed.

Lemma nat_of_Z_eq: forall i, nat_of_Z (Z_of_nat i) = i.
Proof.
intros.
apply inj_eq_rev.
rewrite nat_of_Z_eq; auto.
omega.
Qed.

Lemma nth_error_length:
  forall {A} i (l: list A), nth_error l i = None <-> (i >= length l)%nat.
Proof.
induction i; destruct l; simpl; intuition.
inv H.
inv H.
rewrite IHi in H. omega.
rewrite IHi. omega.
Qed.

Lemma prop_unext: forall P Q: Prop, P=Q -> (P<->Q).
Proof. intros. subst; split; auto. Qed.

Lemma list_norepet_In_In: forall {K X} a x y (l:list (K*X)),
  list_norepet (map (@fst K X) l) -> In (a, x) l -> In (a, y) l -> x = y.
Proof.
  induction l; intros N Ix Iy.
   - inv Ix.
   - simpl in N; inv N.
     destruct Ix.
     + subst.
       simpl in Iy; destruct Iy as [|Iy]; [congruence|].
       exfalso; apply (in_map (@fst K X)) in Iy; tauto.
     + simpl in Iy; destruct Iy as [|Iy].
       subst. exfalso; apply (in_map (@fst K X)) in H; tauto.
       apply IHl; auto.
Qed.

Inductive sublist {A} : list A -> list A -> Prop :=
| sublist_nil : sublist nil nil
| sublist_cons a l1 l2 : sublist l1 l2 -> sublist (a :: l1) (a :: l2)
| sublist_drop a l1 l2 : sublist l1 l2 -> sublist l1 (a :: l2).

Lemma sublist_In {A} (a : A) l1 l2 : sublist l1 l2 -> In a l1 -> In a l2.
Proof.
  intros S; induction S; intros I.
  - inversion I.
  - simpl in I; destruct I.
    subst; left; auto.
    right; auto.
  - right; auto.
Qed.

Lemma sublist_norepet {A} (l1 l2 : list A) : sublist l1 l2 -> list_norepet l2 -> list_norepet l1.
Proof.
  intros S; induction S; intros N; auto.
  - inversion N; subst; constructor; auto.
    pose proof sublist_In a l1 l2; auto.
  - inversion N; auto.
Qed.

Require Import Coq.Sets.Ensembles.

Definition Ensemble_join {A} (X Y Z: Ensemble A): Prop :=
  (forall a, Z a <-> X a \/ Y a) /\ (forall a, X a -> Y a -> False).
