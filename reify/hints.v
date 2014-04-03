Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import sep.
Require Import reify_derives.
Require Import functions.
Require Import progs.list_dt.
Require Import lseg_lemmas.
Import Expr.

Module SL := SepLemma VericSepLogic Sep.
Module HintModule := ReifyHints.Make VericSepLogic Sep SL. 


(* Begin hints *)

(* right-hints *)

(* from verif_reverse *)
Lemma eq_ptr_emp_lseg : forall T ll a b sh LS,
        (*(ptr_eq a b -> *)(VericSepLogic_Kernel.himp VericSepLogic_Kernel.emp (@lseg T ll LS sh nil a b)).
Admitted.
(*intros.
entailer!.
Qed. *)
(*assert (dreq := (derives_refl'' _ _ (lseg_nil_eq LS0 sh a b))).
eapply derives_trans.
Focus 2.
apply dreq.
eapply andp_right.
apply prop_right. assumption.
auto.
Qed. *)
(* End hints *)

Axiom PQ : forall n, VericSepLogic_Kernel.himp (P n) (Q n).
Axiom QP : forall n,  VericSepLogic_Kernel.himp (Q n) (P n).
Check PQ. Check VericSepLogic_Kernel.himp.

(*Make a tuple here *)
Check null_field_at_false.

Check (null_field_at_false Tvoid).


(* We think the issue is in prepare_reify; it's not dealing with TT
   correctly, somehow. *)
Local Open Scope logic.
Check null_field_at_false.

Lemma field_at_trivial' : forall sh T id y, field_at sh T id y nullval |-- FF && emp.
Proof.
intros.
pose_env.
reify_derives.
Admitted.


Definition left_hints := PQ.

(* need to make the following types
   - listspec _ _ for each _ _
   - list (elemtype _) *)

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
(*Definition left_lemmas: list (Lemma.lemma types.our_types (SL.sepConcl types.our_types)).*)


Definition left_lemmas: list (Lemma.lemma SL.sepConcl).
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints types functions preds 
ltac:(fun funcs preds hints => apply hints). 
Defined.
 
(* Axiom QP : forall n,  VericSepLogic_Kernel.himp (Q n) (P n). *)

Definition right_hints := QP. (*(QP, eq_ptr_emp_lseg).*)

(*Make sure you have already updated any funcs and preds that might have been added by doing
the left rules *)

(*Uncomment this if you are adding new lemmas and need to see some reified things*)
(*Goal False.
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints => id_this (funcs, preds, hints)). *)
(* Admitted. *)

(*Copied from above goal*)
(*Definition right_lemmas : list (Lemma.lemma types.our_types (SL.sepConcl types.our_types)).*)
Definition right_lemmas : list (Lemma.lemma SL.sepConcl).
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints =>  apply hints). 
Defined.
