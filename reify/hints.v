Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import sep.
Require Import reify_derives.
Require Import functions.
Require Import types.
Require Import progs.list_dt.
Require Import lseg_lemmas.
Require Import instantiate_lemmas.
Require Import reverse_defs.
Import Expr.

Module SL := SepLemma VericSepLogic Sep.
Module HintModule := ReifyHints.Make VericSepLogic Sep SL. 


(* from verif_reverse *)
Lemma eq_ptr_emp_lseg : forall T ll a b sh LS,
        (*(ptr_eq a b -> *)(VericSepLogic_Kernel.himp VericSepLogic_Kernel.emp (@lseg T ll LS sh nil a b)).
Admitted.
(*intros.
entailer!.p
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

Definition left_hints_base := (PQ, @null_field_at_false, @field_at_conflict').
(*Definition left_hints_base := PQ.*)

(* NP Well-Formedness lemmas that require a listspec *)
Definition left_lseg_hints := (@lseg_null_null, @next_lseg_equal, @lseg_conflict).
(*Definition left_lseg_hints := @next_lseg_equal.*)

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

(* For testing changes to reify_hints *)
(*
nn  Ltac reify_hints2 unfoldTac pcType stateType isConst Ps types funcs preds k :=
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
(*
Definition left_lemmas_old: list (Lemma.lemma SL.sepConcl).
Unset Ltac Debug.
pose_env. *)
(* ensure hints are processed as tuple *)
(* let left_hints := eval hnf in left_hints in
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints types functions preds *)
(*ltac:(fun funcs preds hints => id_this (funcs, preds, hints)).*)
(*ltac:(fun funcs preds hints => apply hints).
Defined.*)

Record hint_rec := mkHintRec { T : Type; hints : T}.

Definition left_hint_rec: hint_rec.
refine ({| T := _; hints := _ |}).
let left_hints_base := eval hnf in left_hints_base in
let left_lseg_hints := eval hnf in left_lseg_hints in
let list_specs := LS in
combine_hints_with_lseg_lemmas left_hints_base left_lseg_hints list_specs ltac:(fun tup => apply tup).
Defined.

Definition left_hints := left_hint_rec.(hints).

(*
Definition left_hints': Type.
let left_hints_base := eval hnf in left_hints_base in
let left_lseg_hints := eval hnf in left_lseg_hints in
let list_specs := eval hnf in list_specs in
let rhints_T := reify_hints_with_lseg_lemmas ltac:(fun x => x) tt tt is_const left_hints_base left_lseg_hints list_specs types functions preds ltac:(fun tup => apply tup) in
apply rhints_T.
*)



Definition left_lemmas: list (Lemma.lemma SL.sepConcl).
pose_env.
Eval simpl in (length functions).
let left_hints := eval hnf in left_hints in
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints types functions preds ltac:(fun funcs preds hints => apply hints).
Defined.

Print left_lemmas.

(* Axiom QP : forall n,  VericSepLogic_Kernel.himp (Q n) (P n). *)

Definition right_hints_base := QP.


(* Navarro Perez Unfolding Lemmas that require a listspec *)
(*Definition right_lseg_hints := (@first_field_at_lseg, @next_field_at_lseg, @lseg_nil_append, @lseg_next_append, @three_lseg_append).*)

(* U4 and U5 won't be usable by mirror-shard; they have conjunction on both sides *)
(*Definition right_lseg_hints := (@first_field_at_lseg, @next_field_at_lseg, @lseg_nil_append).*)

Definition right_lseg_hints := @first_field_at_lseg.

Definition right_hints_rec : hint_rec.
refine ({| T := _; hints := _ |}).
let right_hints_base := eval hnf in right_hints_base in
let right_lseg_hints := eval hnf in right_lseg_hints in
let list_specs := LS in
combine_hints_with_lseg_lemmas right_hints_base right_lseg_hints list_specs ltac:(fun tup => apply tup).
Defined.

Definition right_hints := right_hints_rec.(hints).

(*Make sure you have already updated any funcs and preds that might have been added by doing
the left rules *)

(* This works... But for some reason reifying hints with lseg doesn't! *)
Goal forall a b c d,
lseg LS a b c d |-- emp.
Proof.
intros.
pose_env.
reify_derives.
Abort.

(*Uncomment this if you are adding new lemmas and need to see some reified things*)
(*Goal False.
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints => id_this (funcs, preds, hints)). *)
(* Admitted. *)
(* need to fold up sample_ls or some shit *)
Definition right_lemmas : list (Lemma.lemma SL.sepConcl).
pose_env.
Unset Ltac Debug.
let right_hints := eval hnf in right_hints in
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints => apply hints).
Defined.

Print right_lemmas.