Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import sep.
Require Import reify_derives.
Require Import functions.
Require Import progs.list_dt.
Require Import lseg_lemmas.
Import Expr.

(* routines for partially applying lseg lemmas
   (type and ident/listlink)
   to get rid of dependent types *)

(* W1 has no dependency *)

(* partially apply, then reify *)

(* Partially apply this lemma to each pair (type, list-link)
   Then reify each partial application.
   This is to remove the dependency so we can reify it properly
   Takes a list and returns a tuple; this is to keep typing sane *)
Module SL := SepLemma VericSepLogic Sep.
Module HintModule := ReifyHints.Make VericSepLogic Sep SL. 
Import ListNotations.

(* OK maybe we should just give user a way to reify their own lemmas
   Writing a function like the one we have *)
Require Import progs.reverse.
Instance sample_ls: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.


(* By convention listspec is the third argument (after type and ll/id) *)
Definition list_seg_lemmas := (@lseg_null_null, @next_lseg_equal).
Definition list_specs := (sample_ls, sample_ls).

(* Wrapper aound reify_hints that adds in the lemmas provided, partially applied to the   given arguments 
   k is the continuation for this function; k' is the continuation for the call to
   reify_hints *)
(* idea - see pair, reify LHS, then move on to other arguments
   we should do this using continuations, just as in reify_hints *)

(* Helper; applies a single lemma to its arguments; tuples; calls k *)
Ltac partial_apply_lseg_lemma lemma args k :=
  match args with
    | tt => k tt
    | (?A1, ?A2) => partial_apply_lseg_lemma lemma A1 ltac:(fun new => 
                      partial_apply_lseg_lemma lemma A2 ltac:(fun newer => k (new, newer)))
    | _ => k (lemma _ _ args)
end.

Goal False.
Unset Ltac Debug.
partial_apply_lseg_lemma @lseg_null_null (sample_ls, sample_ls) ltac:(fun apps => id_this apps).
Abort.

(* what data needs to carry over? just ps? *)
Ltac reify_hints_with_lseg_lemmas unfoldTac pcType stateType isConst
     Ps partial_lemmas lemma_args types funcs preds k :=
  match partial_lemmas with
    | tt => k Ps
    | (?L1, ?L2) => reify_hints_with_lseg_lemmas unfoldTac pcType stateType isConst
                      Ps L1 lemma_args types funcs preds ltac:(fun newPs =>
                         reify_hints_with_lseg_lemmas unfoldTac pcType stateType isConst
                           (newPs, Ps) L2 lemma_args types funcs preds ltac:(fun newrPs =>
                                              k (newrPs, newPs, Ps))) (*change k?*)
    | _ => partial_apply_lseg_lemma partial_lemmas lemma_args k (* maybe fun with k applied to arg, tupling? *)
(*(fun new_lemmas =>
             reify_hints_with_lseg_lemmas unfoldTac pcType stateType isConst
             (new_lemmas, Ps) types funcs preds k) *)
  end.

(* Module containing PQ and QP, testing parameters *)
Axiom PQ : forall n, VericSepLogic_Kernel.himp (P n) (Q n).
Axiom QP : forall n,  VericSepLogic_Kernel.himp (Q n) (P n).

(* todo make it work with multiple hints *)
Definition left_hints := (PQ, QP).
Definition right_hints := QP.

Module TestModule.

Goal False.
Unset Ltac Debug.
pose_env.
let left_hints := eval hnf in left_hints in
let list_seg_lemmas := eval hnf in list_seg_lemmas in
let list_specs := eval hnf in list_specs in
let left_hints' := reify_hints_with_lseg_lemmas ltac:(fun x => x) tt tt is_const left_hints list_seg_lemmas list_specs types functions preds ltac:(fun tup => tup) in
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints' types functions preds ltac:(fun funcs preds hints => id_this hints)
.

  (*HintModule.reify_hints unfoldTac pcType stateType isConst Ps types funcs preds k'*)


(* (* A later optimization might be to implement "dummy variables"
      and substitution to avoid re-reification *)
Definition dummy_lemmas: list (Lemma.lemma SL.sepConcl).
pose_env.
Unset Ltac Debug.
let lemmas := eval hnf in lemmas in
HintModule.reify_hints ltac:(fun x => x) tt tt is_const lemmas types functions preds 
ltac:(fun funcs preds hints => apply hints).
*)