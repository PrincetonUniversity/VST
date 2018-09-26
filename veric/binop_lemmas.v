Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.binop_lemmas5.
Require Import VST.veric.binop_lemmas6.
Import Cop.

Lemma typecheck_binop_sound:
forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  destruct op;
  first
    [ eapply typecheck_Oadd_sound; eauto
    | eapply typecheck_Osub_sound; eauto
    | eapply typecheck_Omul_sound; eauto
    | eapply typecheck_Odiv_sound; eauto
    | eapply typecheck_Omod_sound; eauto
    | eapply typecheck_Oshift_sound; solve [eauto]
    | eapply typecheck_Obin_sound; solve [eauto]
    | eapply typecheck_Otest_eq_sound; solve [eauto]
    | eapply typecheck_Otest_order_sound; solve [eauto]].
Qed.

