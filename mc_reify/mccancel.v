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