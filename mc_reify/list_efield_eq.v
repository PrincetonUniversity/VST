Require Import Clight.
Require Import Ctypes.
Require Import VST.veric.expr.
Require Import VST.floyd.efield_lemmas.
Require Import mc_reify.clight_expr_eq.
Require Import compcert.common.AST.
Require Import ExtLib.Core.RelDec.

Definition efield_beq a b :=
  match a, b with
  | eStructField x, eStructField y => eqb_ident x y
  | eUnionField x, eUnionField y => eqb_ident x y
  | eArraySubsc x, eArraySubsc y => expr_beq x y
  | _, _ => false
  end.

Lemma efield_beq_spec: forall a b, efield_beq a b = true <-> a = b.
Proof.
  intros.
  destruct a, b; split; intros; try solve [inversion H]; simpl in H.
  + apply expr_beq_spec in H.
    subst.
    reflexivity.
  + inversion H.
    subst.
    simpl.
    apply expr_beq_spec.
    reflexivity.
  + apply eqb_ident_spec in H.
    subst.
    reflexivity.
  + inversion H.
    subst.
    simpl.
    apply eqb_ident_spec.
    reflexivity.
  + apply eqb_ident_spec in H.
    subst.
    reflexivity.
  + inversion H.
    subst.
    simpl.
    apply eqb_ident_spec.
    reflexivity.
Qed.

Instance RelDec_efield_beq: RelDec (@eq efield) := { rel_dec := efield_beq }.

Instance RelDec_Correct_efield_beq : RelDec_Correct RelDec_efield_beq.
Proof.
  constructor.
  unfold rel_dec; simpl.
  exact efield_beq_spec.
Qed.

Instance RelDec_list_efield_beq: RelDec (@eq (list efield)) := List.RelDec_eq_list RelDec_efield_beq.
Instance RelDec_Correct_list_efield_beq: RelDec_Correct RelDec_list_efield_beq :=
  List.RelDec_Correct_eq_list RelDec_Correct_efield_beq.
