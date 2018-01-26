Require Import Clight.
Require Import Ctypes.
Require Import VST.veric.expr.
Require Import mc_reify.clight_expr_eq.
Require Import compcert.common.AST.
Require Import ExtLib.Core.RelDec.

Instance RelDec_ctype_beq: RelDec (@eq type) := { rel_dec := eqb_type }.

Instance RelDec_Correct_ctype_beq : RelDec_Correct RelDec_ctype_beq.
Proof.
  constructor.
  unfold rel_dec; simpl.
  exact eqb_type_spec.
Qed.

Instance RelDec_list_ctype_beq: RelDec (@eq (list type)) := List.RelDec_eq_list RelDec_ctype_beq.
Instance RelDec_Correct_list_ctype_beq: RelDec_Correct RelDec_list_ctype_beq :=
  List.RelDec_Correct_eq_list RelDec_Correct_ctype_beq.
