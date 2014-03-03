Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import sep.
Require Import reify_derives.
Require Import functions.
Import Expr.

Module SL := SepLemma VericSepLogic Sep.
Module HintModule := ReifyHints.Make VericSepLogic Sep SL. 

Axiom PQ : forall n, VericSepLogic_Kernel.himp (P n) (Q n).

(*Make a tuple here *)
Definition left_hints := PQ.

Ltac id_this x := assert (exists n, x=n).


(*Uncomment this if you are adding new lemmas and need to see some reified things*)
(*Goal False.
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints types functions preds 
ltac:(fun funcs preds hints => id_this (funcs, preds, hints)). 
Admitted.*)

(*Copied and pasted from above goal.
NOTE: Be sure that you add any predicates/functions
that were added here in functions.v (so if you see anything other than functions and preds
as the first two items of the tuple printed in the above goal, you need to add something
to the appropriate list in functions.v
NOTE2: you might need to change to a form of record notation where you can give the
implicit argument. Do this if you are having type errors
*)
Definition left_lemmas: list (Lemma.lemma types.our_types (SL.sepConcl types.our_types))  := 
{|   Lemma.Foralls := tvType 11 :: nil;
     Lemma.Hyps := nil;
     Lemma.Concl := (Sep.Func 1%nat (Var 0%nat :: nil),
                    Sep.Func 2%nat (Var 0%nat :: nil)) |} :: nil.


Axiom QP : forall n,  VericSepLogic_Kernel.himp (Q n) (P n).

Definition right_hints := QP.

(*Make sure you have already updated any funcs and preds that might have been added by doing
the left rules *)

(*Uncomment this if you are adding new lemmas and need to see some reified things*)
(*Goal False.
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints => id_this (funcs, preds, hints)). *)
Admitted.

(*Copied from above goal*)
Definition right_lemmas : list (Lemma.lemma types.our_types (SL.sepConcl types.our_types)) :=
{|
     Lemma.Foralls := tvType 11 :: nil;
     Lemma.Hyps := nil;
     Lemma.Concl := (Sep.Func 2%nat (Var 0%nat :: nil),
                    Sep.Func 1%nat (Var 0%nat :: nil)) |} :: nil.
