Require Import floyd.proofauto.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import reverse_defs.
Require Import mirror_cancel.
Require Import ExtLib.Tactics.
Require Import hints.
Require Import preproc.

Local Open Scope logic.


(* trying to test if my reified hints are usable by Mirror *)
Goal forall T sh id y, field_at sh T id y nullval |-- !!False && emp.
Proof.
Unset Ltac Debug.
intros.
rcancel.
Qed.

Goal forall (a b c d: nat), a = b -> b = c -> c = d ->
                            functions.P a |-- functions.P d.
Proof.
intros.
rcancel.
Qed.

(* need to deal with singleton? *)
(* we may need also to add hnf somewhere in mirror_cancel_default. *)
(* mirror_cancel_default. *)

Goal forall (A B : Prop),(!!(A /\ B) && emp |-- !!( B) && emp).
Proof.
intros.
rcancel.
Qed.


Goal forall n, functions.P n |-- functions.Q n.
intros.
rcancel.
Qed.


Parameter X : Z -> mpred.


Goal  X (1 + 3) |-- X (2 + 2).
intros.
rcancel.
Qed.

Goal  emp |-- emp.
Proof.
rcancel.
Qed.

Goal forall a,  a |-- a.
Proof.
intros.
rcancel.
Qed.

Goal forall a b, a * b |-- b * a.
intros.
rcancel.
Qed.

Definition P2 (v :val) := emp.



Goal forall contents sh rho,
(eval_id _t rho) = (eval_id _p rho) ->
lseg LS sh (map Vint contents) (eval_id _t rho) nullval * emp |--
lseg LS sh (map Vint contents) (eval_id _p rho) nullval * emp.
intros.
rcancel.
Qed.

Goal forall a ,
 !!True && a
   |-- !!True &&
       (a * !!True).
Proof.
intros.
rcancel.
Qed.


Goal
 forall (i : int) (cts : list int) (t0 y : val) (sh : share)
     (contents : list int) (t : name _t) (p_ : name _p) 
     (s : name _s) (h : name _h) (a b c d : mpred) (e: Prop),
     (!!True * emp)
   |-- a (*!!True &&
       (d * !!True)*).
Proof.
intros.
pose_env.
prepare_reify.
match goal with
| [ |- _ ?X _ |-- _] => let t := type of X in idtac X ":" t
end.
pose (TT' := TT). fold TT'.
reify_derives.
Abort.

Lemma prove_TT' : forall P, P |-- TT'.
intros.
entailer!.
Qed.

Ltac cleanup_cancel :=
intros;
try match goal with
 | |-  _ /\ _ => split; cleanup_cancel
 | |- _ = _ => reflexivity
 | |- _ |-- TT' => apply prove_TT'
 | |- emp |-- emp => exact derives_emp
 | |- True => exact I
end.

Ltac get_types_name :=
match goal with 
| [ H := _ : (list Expr.type) |- _] => H
end.

Ltac get_funcs_name t := 
match goal with
| [ X := _ : list (Expr.signature t) |- _ ] => X
 end.

Ltac get_predicates_name t :=
match goal with
[ X := _ : list (Sep.predicate t) |- _] => X end.

Ltac get_uenv_name t := 
match goal with 
| [ X := _ : Expr.env t |- _ ] => X
| [ X := _ : list (sigT (Expr.tvarD t)) |- _ ] => X
end.

Ltac our_cbv :=
let types' := get_types in
let types := get_types_name in
let funcs := get_funcs_name types' in
let preds := get_predicates_name types' in 
let uenv := get_uenv_name types' in
cbv [
exprD functionTypeD applyD
forallEach AllProvable_impl AllProvable_gen AllProvable_and projT1 projT2 Provable lookupAs
nth_error equiv_dec length fold_right tvarD Impl_ EqDec_tvar eq_nat_dec
CancelModule.INS.existsSubst
SUBST.Subst_equations_to SUBST.Subst_lookup SUBST.subst_lookup
FM.find FM.Raw.find FM.this
Basics.impl Impl Exc
Sep.sexprD Sep.SDenotation Sep.SDomain Denotation Domain Range 
SH.sheapD SH.pures SepHeap.FM.fold SepHeap.FM.Raw.fold SH.starred SepHeap.FM.this
SH.other SH.impures
NatMap.Ordered_nat.compare  NatMap.Ordered_nat.eq nat_compare EqDec_tvar tvar_rec tvar_rect Range
VericSepLogic.himp  VericSepLogic.inj VericSepLogic.star VericSepLogic_Kernel.emp VericSepLogic.hprop
sumbool_rec sumbool_rect nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym f_equal
funcs preds types uenv abbreviate value
functions.True_signature functions.eval_id_signature functions.Vint_signature
functions.int_sub_signature functions.int_add_signature functions.reverse_t_struct_list_signature
 functions.field_at_psig functions.all_types_r functions.reverse__tail_signature
functions.nullval_signature functions.map_Vint_signature
types.val_tv types.ident_tv  types.environ_tv types.int_tv types.our_types types.share_tv
types.c_type_tv types.val_type types.list_val_type types.no_eqb_type types.list_val_tv
types.list_int_tv
Env.repr Env.listToRepr].

Lemma load_entail1 : 
 forall (i : int) (cts : list int) (t0 y : val) (sh : share)
     (contents : list int) (t : name _t) (p_ : name _p) 
     (s : name _s) (h : name _h),
   exists a, exists b,
   PROP  ()
   LOCAL  (tc_environ Delta; `(eq t0) (eval_id _t);
   `(eq (Vint (Int.sub (sum_int contents) (sum_int (i :: cts)))))
     (eval_id _s))
   SEP 
   (`(field_at sh t_struct_list _head (Vint i))
      (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(field_at sh t_struct_list _tail y)
     (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(lseg LS sh (map Vint cts)) `y `nullval; TT)
   |-- local (tc_expr Delta (Etempvar _t (tptr t_struct_list))) &&
       (`(field_at a t_struct_list _head b)
          (eval_expr (Etempvar _t (tptr t_struct_list))) * TT).
Proof.
intros. 
eexists. eexists. 
go_lower0.
pose_env.
(*Time entailer!.*)
prepare_reify.
pose (TT'' := TT); fold TT''.
Time reify_derives.
Time
(let types := get_types in 
let funcs := get_funcs types in
(* ensure hints/lemmas are processed as tuples correctly *)
(* TODO figure out if there are issue with processing singletons *)
let left_hints := eval hnf in left_hints in
let right_hints := eval hnf in right_hints in
eapply (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _ (vst_prover types funcs user_comp) left_lemmas right_lemmas); 
[ reflexivity
| HintModule.prove left_hints
| HintModule.prove right_hints
| apply vstProver_correct
| simpl (Sep.typeof_preds); simpl (typeof_env); e_vm_compute_left
| our_cbv; cleanup_cancel]).

cleanup_cancel. 

simpl.
sumbool_rect not_eq_sym
split; [ split; [ reflexivity | split; [reflexivity | auto] ] | ];
apply prove_TT'.
Time
prepare_reify;
pose (TT'' := TT); fold TT'';
reify_derives;
let types := get_types in 
let funcs := get_funcs types in
(* ensure hints/lemmas are processed as tuples correctly *)
(* TODO figure out if there are issue with processing singletons *)
let left_hints := eval hnf in left_hints in
let right_hints := eval hnf in right_hints in
eapply (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _ (vst_prover types funcs user_comp) left_lemmas right_lemmas); 
[ reflexivity
| HintModule.prove left_hints
| HintModule.prove right_hints
| apply vstProver_correct
| 
| repeat (split; try assumption; try apply I; try apply derives_emp)];
simpl (Sep.typeof_preds); simpl (typeof_env);
[e_vm_compute_left |
split; [ split; [ reflexivity | split; [reflexivity | auto] ] | ];
apply prove_TT'].
Qed.


Lemma while_entail1 :
  name _t ->
  name _p ->
  name _s ->
  name _h ->
  forall (sh : share) (contents : list int),
   PROP  ()
   LOCAL 
   (tc_environ
      Delta;
   `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list))
);
   `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
   SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
   |-- PROP  ()
       LOCAL 
       (`(eq (Vint (Int.sub (sum_int contents) (sum_int contents))))
          (eval_id _s))
       SEP  (TT; `(lseg LS sh (map Vint contents)) (eval_id _t) `nullval).
Proof.
intros.
go_lower0.
unfold LS.
pose (TT := !!True). fold TT.
pose_env.
prepare_reify.
reify_derives.

SearchAbout andp.
Locate Ltac reify_expression.
lift_and_goal.
mirror_cancel_default.
unfold Provable in *. simpl in *. admit. (*Provable pure fact we can't deal with yet *)
simpl in *. (*ugly thing that shouldn't be left*) apply prop_right; auto.
Qed.

Lemma while_entail2 :
  name _t ->
  name _p ->
  name _s ->
  name _h ->
  forall (sh : share) (contents : list int),
  PROP  ()
  LOCAL  (tc_environ Delta;
         `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list)));
         `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
  SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
          |-- EX  cts : list int,
  PROP  ()
  LOCAL 
        (`(eq (Vint (Int.sub (sum_int contents) (sum_int cts)))) (eval_id _s))
  SEP  (TT; `(lseg LS sh (map Vint cts)) (eval_id _t) `nullval).
Proof.
intros.
go_lower0.
pose_env.
prepare_reify. pose (TT := !!True). fold TT.
prepare_reify. prepare_reify.
reify_derives.
Admitted.