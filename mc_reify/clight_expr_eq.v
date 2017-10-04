Require Import Clight.
Require Import Ctypes.
Require Import VST.veric.expr.
Require Import Integers.
Require Import Floats.
Require Import Zbool.
Require Import Coq.Numbers.BinNums.
Require Import Cop.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.List.

Definition beq_int (i1 i2 : Integers.int) : bool :=
Zbool.Zeq_bool (Int.intval i1) (Int.intval i2).


Lemma beq_int_true : forall a b, beq_int a b = true -> a = b.
Proof.
intros.
destruct a, b.
unfold beq_int in *.
simpl in H.
apply Zbool.Zeq_bool_eq in H. subst.
replace intrange with intrange0.
auto.
apply Axioms.proof_irr.
Qed.

Hint Resolve beq_int_true : expr_beq.

Lemma beq_int_refl : forall i, beq_int i i = true.
Proof.
intros.
unfold beq_int. apply Zeq_is_eq_bool. auto.
Qed.

Hint Resolve beq_int_refl : expr_beq.
Hint Rewrite beq_int_refl : expr_beq.


Definition beq_long (i1 i2 : int64) : bool :=
Zeq_bool (Int64.intval i1) (Int64.intval i2).

Lemma beq_long_true : forall a b, beq_long a b = true -> a = b.
Proof.
intros.
destruct a, b.
unfold beq_long in *.
simpl in H.
apply Zeq_bool_eq in H. subst.
replace intrange with intrange0.
auto.
apply Axioms.proof_irr.
Qed.

Lemma beq_long_refl : forall i, beq_long i i = true.
Proof.
intros.
unfold beq_long. apply Zeq_is_eq_bool. auto.
Qed.

Hint Resolve beq_long_refl : expr_beq.
Hint Rewrite beq_long_refl : expr_beq.
Hint Resolve beq_long_true : expr_beq.

Definition beq_float_dec a b:= if Float.eq_dec a b then true else false.

Lemma beq_float_dec_true a b : beq_float_dec a b = true -> a = b.
intros.  unfold beq_float_dec in *. destruct (Float.eq_dec a b); congruence.
Qed. (*If things are slow, this may be the culprit *)

Lemma beq_float_refl : forall a, beq_float_dec a a = true.
Proof.
intros. unfold beq_float_dec.
consider (Float.eq_dec a a); auto.
Qed.

Hint Resolve beq_float_refl : expr_beq.
Hint Rewrite beq_float_refl : expr_beq.
Hint Resolve beq_float_dec_true : expr_beq.

Definition beq_float32_dec a b:= if Float32.eq_dec a b then true else false.

Lemma beq_float32_dec_true a b : beq_float32_dec a b = true -> a = b.
intros.  unfold beq_float32_dec in *. destruct (Float32.eq_dec a b); congruence.
Qed. (*If things are slow, this may be the culprit *)

Lemma beq_float32_refl : forall a, beq_float32_dec a a = true.
Proof.
intros. unfold beq_float32_dec.
consider (Float32.eq_dec a a); auto.
Qed.

Hint Resolve beq_float32_refl : expr_beq.
Hint Rewrite beq_float32_refl : expr_beq.


Hint Resolve beq_float32_dec_true : expr_beq.

Definition unary_op_beq a b :=
match a, b with
  | Onotbool, Onotbool
  | Onotint, Onotint
  | Oneg, Oneg
  | Oabsfloat, Oabsfloat => true
  | _, _ => false
end.

Lemma unary_op_beq_sound : forall a b, unary_op_beq a b = true -> a = b .
destruct a, b; simpl in *; try congruence; auto.
Qed.

Lemma unary_op_beq_refl : forall a, unary_op_beq a a = true.
destruct a; auto.
Qed.

Hint Resolve unary_op_beq_refl : expr_beq.
Hint Rewrite unary_op_beq_refl : expr_beq.
Hint Resolve unary_op_beq_sound: expr_beq.

Definition binary_op_beq a b :=
match a, b with
    Oadd, Oadd
  | Osub, Osub
  | Omul, Omul
  | Odiv, Odiv
  | Omod, Omod
  | Oand, Oand
  | Oor, Oor
  | Oxor, Oxor
  | Oshl, Oshl
  | Oshr, Oshr
  | Oeq, Oeq
  | One, One
  | Olt, Olt
  | Ogt, Ogt
  | Ole, Ole
  | Oge, Oge => true
  | _, _ => false
end.

Lemma binary_op_beq_sound : forall a b, binary_op_beq a b = true -> a = b .
destruct a, b; simpl in *; try congruence; auto.
Qed.

Lemma binary_op_beq_refl : forall a, binary_op_beq a a = true.
destruct a; auto.
Qed.

Hint Resolve binary_op_beq_refl : expr_beq.
Hint Rewrite binary_op_beq_refl : expr_beq.
Hint Resolve binary_op_beq_sound : expr_beq.

Fixpoint expr_beq a b :=
match a, b with
| Econst_int i1 ty1, Econst_int i2 ty2 => andb (beq_int i1 i2) (eqb_type ty1 ty2)
| Econst_float f1 ty1, Econst_float f2 ty2 => andb (beq_float_dec f1 f2) (eqb_type ty1 ty2)
| Econst_single f1 ty1, Econst_single f2 ty2 => andb (beq_float32_dec f1 f2) (eqb_type ty1 ty2)
| Econst_long l1 ty1, Econst_long l2 ty2 => andb (beq_long l1 l2) (eqb_type ty1 ty2)
| Evar id1 ty1, Evar id2 ty2
| Etempvar id1 ty1, Etempvar id2 ty2 => andb (BinPos.Pos.eqb id1 id2) (eqb_type ty1 ty2)
| Ederef e1 ty1, Ederef e2 ty2
| Eaddrof e1 ty1, Eaddrof e2 ty2
| Ecast e1 ty1, Ecast e2 ty2 => (andb (expr_beq e1 e2) (eqb_type ty1 ty2))
| Eunop op1 e1 ty1, Eunop op2 e2 ty2 => (andb (andb (unary_op_beq op1 op2) (expr_beq e1 e2)) (eqb_type ty1 ty2))
| Ebinop op1 e11 e21 ty1, Ebinop op2 e12 e22 ty2 => (andb (andb (andb (binary_op_beq op1 op2) (expr_beq e11 e12)) (eqb_type ty1 ty2)) (expr_beq e21 e22))
| Efield e1 id1 ty1, Efield e2 id2 ty2 => andb (andb (expr_beq e1 e2) (BinPos.Pos.eqb id1 id2)) (eqb_type ty1 ty2)
| _, _ => false
end.

Hint Rewrite Bool.andb_true_iff : expr_beq.
Hint Resolve eqb_type_true : expr_beq.
Hint Resolve BinPos.Peqb_true_eq : expr_beq.
Hint Rewrite BinPos.Pos.eqb_refl : expr_beq.
Hint Resolve BinPos.Pos.eqb_refl : expr_beq.
Hint Resolve eqb_type_refl : expr_beq.
Hint Rewrite eqb_type_refl : expr_beq.

Ltac solve_expr_beq_sound :=
try solve [simpl in *; try congruence]; try reflexivity;
simpl in *; autorewrite with expr_beq in *;
repeat match goal with
| [ H : _ /\ _  |- _] => destruct H
end;
try match goal with
| [ H : List.list_eqb ?r ?a ?b = _ |- _] => consider ( List.list_eqb r a b); intros
end;
try f_equal;
auto with expr_beq.

Lemma expr_beq_refl : forall a, expr_beq a a = true.
Proof.
induction a; simpl; repeat (rewrite Bool.andb_true_iff; split); auto with expr_beq.
Qed.

Hint Resolve expr_beq_refl : expr_beq.

Lemma expr_beq_spec : forall a b, expr_beq a b = true <-> a = b.
split; revert b. induction a; intros; match goal with [ |-  _ = ?b] => destruct b end; solve_expr_beq_sound.
intros. induction a, b; inversion H; subst; auto with expr_beq.
Qed.

Lemma expr_beq_sound : forall a b, expr_beq a b = true -> a = b.
Proof.
apply expr_beq_spec.
Qed.

