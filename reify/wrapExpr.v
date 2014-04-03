Require Import sep.
Require Import MirrorShard.Expr.
Require Import floyd.proofauto.

Definition assumptions := list Expr.expr.
Definition derives_r := prod Sep.sexpr Sep.sexpr .
Definition goal := prod assumptions derives_r.

Definition force_Opt {T} p (d:T) :=
match p with
| Some p' => p'
| None => d
end.

Fixpoint assumptionsD types functions meta_env var_env assumptions (g : Prop):=
match assumptions with 
| cons h t => force_Opt (@Expr.exprD types functions meta_env var_env h tvProp) False -> assumptionsD types functions meta_env var_env t g
| nil => g
end.

Definition derivesD types functions preds meta_env var_env (der : derives_r) :=
let (l,r) := der in
@Sep.sexprD types functions preds meta_env var_env l
|--
@Sep.sexprD types functions preds meta_env var_env r. 


Definition goalD types functions preds meta_env var_env (goal : goal) :=
let (assumptions, derives) := goal in
match assumptions with 
| nil => derivesD types functions preds meta_env var_env derives
| _ => 
assumptionsD types functions meta_env var_env assumptions
(derivesD types functions preds meta_env var_env derives)
end.
