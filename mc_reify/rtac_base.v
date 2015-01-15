Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Import mc_reify.typ_eq.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.func_defs.

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).

Definition THEN' (r1 r2 : rtac typ (expr typ func)) := THEN r1 (runOnGoals r2).

Definition THEN (r1 r2 : rtac typ (expr typ func)) := 
  THEN' r1 (THEN' (INSTANTIATE typ func) r2).
