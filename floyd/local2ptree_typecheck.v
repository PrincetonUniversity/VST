Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.local2ptree_denote.
Require Import floyd.local2ptree_eval.

Local Open Scope logic.

Definition msubst_simpl_tc_assert (T1: PTree.t val): tc_assert -> tc_assert :=
  fix msubst_simpl_tc_assert (tc: tc_assert): tc_assert :=
  match tc with
  | tc_andp' tc1 tc2 => tc_andp (msubst_simpl_tc_assert tc1) (msubst_simpl_tc_assert tc2)
  | tc_orp' tc1 tc2 => tc_orp (msubst_simpl_tc_assert tc1) (msubst_simpl_tc_assert tc2)
  | tc_initialized i _ => match T1 ! i with Some _ => tc_TT | None => tc_FF miscellaneous_typecheck_error end
  | _ => tc
  end.

Fixpoint msubst_denote_tc_assert {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (tc: tc_assert): mpred :=
  match tc with
  | tc_FF msg => !! (typecheck_error msg)
  | tc_TT => TT
  | tc_andp' b c => (msubst_denote_tc_assert T1 T2 b) && (msubst_denote_tc_assert T1 T2 c)
  | tc_orp' b c => (msubst_denote_tc_assert T1 T2 b) || (msubst_denote_tc_assert T1 T2 c)
  | tc_nonzero' e => denote_tc_nonzero (force_val (msubst_eval_expr T1 T2 e))
  | tc_isptr e => denote_tc_isptr (force_val (msubst_eval_expr T1 T2 e))
  | tc_test_eq' e1 e2 => denote_tc_test_eq (force_val (msubst_eval_expr T1 T2 e1)) (force_val (msubst_eval_expr T1 T2 e2))
  | tc_test_order' e1 e2 => denote_tc_test_order (force_val (msubst_eval_expr T1 T2 e1)) (force_val (msubst_eval_expr T1 T2 e2))
  | tc_ilt' e i => denote_tc_igt i (force_val (msubst_eval_expr T1 T2 e))
  | tc_Zle e z => denote_tc_Zge z (force_val (msubst_eval_expr T1 T2 e))
  | tc_Zge e z => denote_tc_Zle z (force_val (msubst_eval_expr T1 T2 e))
  | tc_samebase e1 e2 => denote_tc_samebase (force_val (msubst_eval_expr T1 T2 e1)) (force_val (msubst_eval_expr T1 T2 e2))
  | tc_nodivover' v1 v2 => denote_tc_nodivover (force_val (msubst_eval_expr T1 T2 v1)) (force_val (msubst_eval_expr T1 T2 v2))
  | tc_initialized id ty => FF
  | tc_iszero' e => denote_tc_iszero (force_val (msubst_eval_expr T1 T2 e))
  end.

Definition msubst_tc_lvalue {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc) (e: expr) :=
  msubst_denote_tc_assert T1 T2 (msubst_simpl_tc_assert T1 (typecheck_lvalue Delta e)).

Definition msubst_tc_expr {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc) (e: expr) :=
  msubst_denote_tc_assert T1 T2 (msubst_simpl_tc_assert T1 (typecheck_expr Delta e)).
