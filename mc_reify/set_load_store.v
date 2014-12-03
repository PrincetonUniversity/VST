Require Import floyd.proofauto. 
Require Import mc_reify.funcs.
Require Import mc_reify.types.
Require Import mc_reify.bool_funcs.
Require Import MirrorCore.Lambda.ExprCore.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Definition my_set {T} := @PTree.set T.

Lemma semax_set_localD id e (t: PTree.t (type * bool)) (v : PTree.t type) 
      (r : type) (gt : PTree.t type):
forall vl ls vs Espec R gs P,
tc_expr_b_norho (mk_tycontext t v r gt gs) e= true ->
tc_temp_id_b_norho id (typeof e) (mk_tycontext t v r gt gs) e = true ->
msubst_eval_expr ls vs e = Some vl ->
(assertD nil (localD (my_set id vl ls) vs) R) = P -> 
@semax Espec (mk_tycontext t v r gt gs) (assertD nil (localD ls vs) R)
      (Sset id e)
(normal_ret_assert P).
Proof.
