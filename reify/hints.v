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

Local Open Scope logic.

Lemma null_field_at_false' : forall T sh id y,
  field_at sh T id y nullval |-- FF && emp.
Proof.
intros; entailer.
Qed.

Definition left_hints := (QP, PQ, null_field_at_false).

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


(* For testing changes to reify_hints *)
(*
  Ltac reify_hints2 unfoldTac pcType stateType isConst Ps types funcs preds k :=
    match (vm_compute in Ps) with
      | tt => k funcs preds (@nil (Lemma.lemma types (@SL.sepConcl types))) || fail 2
      | (?P1, ?P2) =>
        reify_hints2 unfoldTac pcType stateType isConst P1 types funcs preds ltac:(fun funcs preds P1 =>
          reify_hints2 unfoldTac pcType stateType isConst P2 types funcs preds ltac:(fun funcs preds P2 =>
            k funcs preds (P1 ++ P2)))
        || fail 2
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
        HintModule.reify_hint pcType stateType isConst (fun _ : ReifyExpr.VarType unit => T) types funcs preds (@nil tvar) ltac:(fun funcs preds P =>
          k funcs preds (P :: nil))
    end. *)

(* TODO - need to find a way to force it to evaluate left_hints
   down to an actual tuple. Right now it's matching against the
   syntax "left_hints" - and, of course, failing *)
Definition left_lemmas: list (Lemma.lemma SL.sepConcl).
Unset Ltac Debug.
pose_env.
(* ensure hints are processed as tuple *)
let left_hints := eval hnf in left_hints in
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

