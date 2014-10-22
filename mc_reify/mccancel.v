Require Import MirrorCore.STac.STac.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.ExprUnify_simul.
(*Require Import MirrorCharge.OrderedCanceller.*)
(*Require Import MirrorCharge.BILNormalize.*)
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.BILogic.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
(*Require Import MirrorCharge.Java.Cancelation2.*)
Require Export MirrorCore.RTac.RTac.
Require Export MirrorCore.RTac.Core.
Require Export MirrorCore.STac.STac.
Require Import MirrorCore.Lambda.Red.
Require Import floyd.proofauto.
Require Export types.
Require Export funcs.
Require Export reify.
Require Export bool_funcs.
Require Import MirrorCore.Lambda.Expr.
Require Import func_eq.

Definition typeof_func_opt t := Some (typeof_func t).

Global Instance RSym_Func' : SymI.RSym func' := {
   typeof_sym := typeof_func_opt;
   symD := funcD;
   sym_eqb := fun a b => (Some (func_beq a b)) 
}.

Global Instance RSymOk_Func' : SymI.RSymOk RSym_Func'.
constructor.
Admitted. (*guess we need complete equality??*)


Instance ILogicOps_mpred : ILogicOps mpred := {
lentails := derives;
ltrue := TT;
lfalse := FF;
land := andp;
lor := orp;
limpl := imp;
lforall := @allp mpred _;
lexists := @exp mpred _
}.

Instance ILogic_mpred : ILogic mpred.
Proof.
split; intros.
+ split.
  * intro x; apply derives_refl.
  * intros x y z Hxy Hyz; apply derives_trans with y; assumption.
+ apply prop_right. apply I.
+ apply prop_left. intro H; destruct H.
+ apply allp_left with x; assumption.
+ apply allp_right; apply H.
+ apply exp_left; apply H.
+ apply exp_right with x; apply H.
+ apply andp_left1; apply H.
+ apply andp_left2; apply H.
+ apply orp_right1; apply H.
+ apply orp_right2; apply H.
+ apply andp_right; [apply H | apply H0].
+ apply orp_left; [apply H | apply H0].
+ apply imp_andp_adjoint. apply H.
+ apply imp_andp_adjoint. apply H.
Qed.

Instance BILOperators_mpred : BILOperators mpred := {
  empSP := emp;
  sepSP := sepcon;
  wandSP := wand
}.

Instance BILogic_mpred : BILogic mpred.
Proof.
split; intros.
+ apply _.
+ unfold sepSP; simpl; rewrite sepcon_comm; apply derives_refl.
+ unfold sepSP; simpl; rewrite sepcon_assoc; apply derives_refl.
+ apply wand_sepcon_adjoint.
+ apply sepcon_derives; [apply H | apply derives_refl].
+ unfold sepSP; simpl; rewrite sepcon_emp; reflexivity.
Qed.


Definition ilops : @logic_ops _ RType_typ :=
fun t =>
  match t
          return option (ILogic.ILogicOps (typD t))
  with
  | tympred => Some _
  | typrop => Some _
  | _ => None  
end.

Definition bilops : @bilogic_ops _ RType_typ :=
fun t =>
  match t
          return option (BILogic.BILOperators (typD t))
  with
  | tympred => Some _
  | _ => None  
end.

Definition fs : @SymEnv.functions typ _ := SymEnv.from_list nil.
Instance RSym_env : RSym SymEnv.func := SymEnv.RSym_func fs.
Instance RSym_ilfunc : RSym (@ilfunc typ) := 
	RSym_ilfunc _ _ ilops.
Instance RSym_bilfunc : RSym (@bilfunc typ) := 
	RSym_bilfunc _ bilops.

Existing Instance SymSum.RSym_sum.
Existing Instance SymSum.RSymOk_sum.
Instance Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
Instance Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := ExprOk_expr.

Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
  FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ func).
Instance SO : SubstI.SubstOk SS := 
  @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _ _.

Definition test_lemma :=
  @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
          (fun tus tvs e => exprD' tus tvs typrop e)
          typrop
          (fun x => x) nil nil.

(*Definition skip_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_vst 
@SeparationLogicSoundness.SoundSeparationLogic.CSL.semax_skip.
Defined.

Definition forward_setx_closed_now_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_vst forward_setx_closed_now.
Defined.*)
(*
Goal forall (Espec : OracleKind) (Delta : tycontext) (Q : list (environ -> Prop))
   (R : list (environ -> mpred)) (id : ident) (e : Clight.expr)
   (PQR : ret_assert),
 List.Forall (closed_wrt_vars (eq id)) Q ->
 List.Forall (closed_wrt_vars (eq id)) R ->
 closed_wrt_vars (eq id) (eval_expr e) ->
 (PROP  ()  (LOCALx (tc_environ Delta :: Q) (SEPx R)))%logic
 |-- local (tc_expr Delta e) ->
 (PROP  ()  (LOCALx (tc_environ Delta :: Q) (SEPx R)))%logic
 |-- local (tc_temp_id id (typeof e) Delta e) ->
 normal_ret_assert
   (PROP  ()  (LOCALx (`eq (eval_id id) (eval_expr e) :: Q) (SEPx R)))%logic
 |-- PQR -> semax Delta (PROP  ()  (LOCALx Q (SEPx R)))%logic (Sset id e) PQR.
intros until PQR.
Check @closed_wrt_vars.
Print closed_wrt_vars.
Check forward_setx_wow.
reify_vst (closed_wrt_vars (eq id) (eval_expr e)).
reify_vst (List.Forall (closed_wrt_vars (eq id)) Q).
reify_vst (List.Forall (closed_wrt_vars (eq id)) Q ->
 List.Forall (closed_wrt_vars (eq id)) R ->
 closed_wrt_vars (eq id) (eval_expr e) ->
 (PROP  ()  (LOCALx (tc_environ Delta :: Q) (SEPx R)))%logic
 |-- local (tc_expr Delta e) ->
 (PROP  ()  (LOCALx (tc_environ Delta :: Q) (SEPx R)))%logic
 |-- local (tc_temp_id id (typeof e) Delta e) ->
 normal_ret_assert
   (PROP  ()  (LOCALx (`eq (eval_id id) (eval_expr e) :: Q) (SEPx R)))%logic
 |-- PQR -> semax Delta (PROP  ()  (LOCALx Q (SEPx R)))%logic (Sset id e) PQR).
Check forward_setx_closed_now.
Print forward_setx_closed_now_lemma.
Locate forward_setx_closed_now.
*)
(*
Definition stac_cancel := @stac_cancel typ func subst tympred _ _ _ _ _ _ _ _.

Definition fintro e : option (OpenAs typ (expr typ func)) :=
match e with
| App (Inj f) P =>
match ilogicS f with
  | Some (ilf_forall t tyProp) => Some (AsAl t (fun x => beta (App P x)))
  | Some (ilf_exists t tyProp) => Some (AsAl t (fun x => beta (App P x)))
  | _ => None
end
| App (App (Inj f) P) Q =>
match ilogicS f with
  | Some (ilf_impl tyProp) => Some (AsHy typ P Q)
  | _ => None
end
| _ => None
end.

Let INTRO := @INTRO typ (expr typ func) subst (@Var typ func) (@UVar typ func) fintro.
Local Open Scope logic.
Definition testSym : expr typ func.
do_reify (forall (P Q: mpred), P * Q |-- Q * P).
Defined.

Time Eval vm_compute in 
(THEN (REPEAT 10 INTRO) 
(STAC_no_hyps (@ExprSubst.instantiate typ func) stac_cancel)) 
CTop (SubstI.empty (expr := expr typ func)) testSym.

Definition cancel exp := (THEN (REPEAT 10 INTRO) 
(STAC_no_hyps (@ExprSubst.instantiate typ func) stac_cancel)) 
CTop (SubstI.empty (expr := expr typ func)) exp.

*)