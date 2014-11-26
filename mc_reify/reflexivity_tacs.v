Require Import func_defs.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import update_tycon.


Locate SubstUpdate_ctx_subst .

Existing Instance SubstUpdate_ctx_subst.
Locate subst.
Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.


Definition REFLEXIVITYTAC : rtac typ (expr typ func) :=
fun tus tvs n m c s e => 
match e with 
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 s l r ty
(*@exprUnify subst typ func _ _ _ SS SU 10 
                   tus tvs 0 s l r ty *) with
    | Some s => RTac.Core.Solved s 
    | None =>  RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Definition REFLEXIVITY := REFLEXIVITYTAC.

Definition REFLEXIVITY_BOOL tbl : rtac typ (expr typ func) := 
   fun tus tvs lus lvs c s e =>(
match e with
| (App (App (Inj (inr (Other (feq tybool)))) l) r) =>
  match reflect tbl nil nil l tybool, reflect tbl nil nil r tybool with
  | Some v1, Some v2 => if @RelDec.rel_dec _ eq _ v1 v2 then Solved s else Fail
  | _, _ => Fail
  end
| _ => Fail
end).

