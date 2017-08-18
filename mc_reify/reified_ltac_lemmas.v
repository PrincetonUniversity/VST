Require Import VST.floyd.proofauto.
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Lemma mpred_prop_right: forall (P: mpred) (Q: Prop), Q -> P |-- !! Q.
Proof.
  intros.
  apply prop_right.
  auto.
Qed.

Lemma mpred_now_later: forall (P: mpred), P |-- |> P.
Proof.
  apply now_later.
Qed.

Lemma mpred_derives_refl: forall (P: mpred), P |-- P.
Proof.
  apply derives_refl.
Qed.

Lemma mpred_semax_post' : forall (R' : environ -> mpred) (Espec : OracleKind)
         (Delta : tycontext) (R P : environ -> mpred)
         (c : statement),
       (forall rho, R' rho |-- R rho) ->
       semax Delta P c (normal_ret_assert R') ->
       semax Delta P c (normal_ret_assert R).
Proof.
  intros.
  apply semax_post' with (R' := R'); eauto.
Qed.

Require Export mc_reify.reify.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
Require Import mc_reify.typ_eq.
Require Import mc_reify.rtac_base.

Definition reify_prop_right: my_lemma.
reify_lemma reify_vst mpred_prop_right.
Defined.

(* Print reify_prop_right. *)

Definition reify_now_later : my_lemma.
reify_lemma reify_vst mpred_now_later.
Defined.

(* Print reify_now_later. *)

Definition reify_derives_refl : my_lemma.
reify_lemma reify_vst mpred_derives_refl.
Defined.

(* Print reify_derives_refl. *)

Definition reify_semax_post' : my_lemma.
reify_lemma reify_vst mpred_semax_post'.
Defined.

(* Print reify_semax_post'. *)

Definition writable_Tsh_lemma: my_lemma.
reify_lemma reify_vst writable_share_top.
Defined.

(* Print writable_Tsh_lemma. *)

Definition writable_Ews_lemma: my_lemma.
reify_lemma reify_vst writable_Ews.
Defined.

(* Print writable_Ews_lemma. *)

Section tbled.

Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Let ExprVar_expr := @ExprVariables.ExprVar_expr typ func.
Existing Instance ExprVar_expr.

Existing Instance MA.

Existing Instance rtac_base.MentionsAnyOk.

Lemma APPLY_sound_prop_right: rtac_sound (EAPPLY typ func reify_prop_right).
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    apply prop_right; auto.
Qed.

Lemma APPLY_sound_now_later: rtac_sound (EAPPLY typ func reify_now_later).
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    apply now_later; auto.
Qed.

Lemma APPLY_sound_derives_refl: rtac_sound (EAPPLY typ func reify_derives_refl).
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    apply derives_refl; auto.
Qed.

Lemma APPLY_sound_semax_post': rtac_sound (EAPPLY typ func reify_semax_post').
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    unfold ILogicFunc.typ2_cast_quant in *. simpl in *.
    apply mpred_semax_post' with (R' := x4); auto.
Qed.

Lemma APPLY_sound_writable_Tsh: rtac_sound (APPLY typ func writable_Tsh_lemma).
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    apply writable_share_top.
Qed.

Lemma APPLY_sound_writable_Ews: rtac_sound (APPLY typ func writable_Ews_lemma).
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    apply writable_Ews.
Qed.

End tbled.
