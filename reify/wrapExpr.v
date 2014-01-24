Require Import sep.
Require Import MirrorShard.Expr.
Require Import floyd.proofauto.

Definition assumptions types := list (Expr.expr types).
Definition derives_r types := prod (Sep.sexpr types) (Sep.sexpr types).
Definition goal types := prod (assumptions types) (derives_r types).

Definition force_Opt {T} p (d:T) :=
match p with
| Some p' => p'
| None => d
end.

Fixpoint assumptionsD types functions meta_env var_env assumptions (g : Prop):=
match assumptions with 
| cons h t => force_Opt (@Expr.exprD types functions meta_env var_env h tvProp) True -> assumptionsD types functions meta_env var_env t g
| nil => g
end.

Definition derivesD types functions preds meta_env var_env (der : derives_r types) :=
let (l,r) := der in
@Sep.sexprD types functions preds meta_env var_env l
|--
@Sep.sexprD types functions preds meta_env var_env r. 


Fixpoint goalD types functions preds meta_env var_env (goal : goal types) :=
let (assumptions, derives) := goal in
match assumptions with 
| nil => derivesD types functions preds meta_env var_env derives
| _ => 
assumptionsD types functions meta_env var_env assumptions
(derivesD types functions preds meta_env var_env derives)
end.
