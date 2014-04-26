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

Goal forall (a b c d: nat), a = b -> b = c -> c = d -> functions.P a |-- functions.P d.
Proof.
intros.
rcancel.
Qed.

Lemma goal_lift_and' :
forall t f preds uenv a l r newl newr n,
nth_error f 5 = Some (functions.and_signature t) ->
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
lift_ands l = newl -> lift_ands r = newr ->
n = nil ->
(goalD (functions.all_types_r t) f preds uenv n (a, (l,r)) <-> 
goalD (functions.all_types_r t) f preds uenv nil (a, (newl, newr))).
intros. rewrite <- H1. rewrite <- H2. rewrite H3. apply goal_lift_and; auto.
Qed.


Ltac lift_and_goal :=
erewrite goal_lift_and';
[ | auto | auto | e_vm_compute_left |  e_vm_compute_left | auto ]. 



(* need to deal with singleton? *)
(* we may need also to add hnf somewhere in mirror_cancel_default. *)
(* mirror_cancel_default. *)

Goal forall (A B : Prop),(!!(A /\ B) && emp |-- !!( B) && emp).
Proof.
intros.
rcancel.
Qed.
(*Print Ltac rcancel.
pose_env.
reify_derives.
Unset Ltac Debug.
Print left_hints.
Print Ltac mirror_cancel_default.
  let types := get_types in
  let funcs := get_funcs types in
  let left_hints := eval hnf in left_hints in
  let right_hints := eval hnf in right_hints in
  eapply
   (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _
      (vst_prover types funcs user_comp) left_lemmas right_lemmas);
   [ reflexivity
   | HintModule.prove left_hints 
   | HintModule.prove right_hints
   | apply vstProver_correct
   | first
   [ e_vm_compute_left | fail "Canceler failed" ]
   | repeat (split; try assumption; try apply I; try apply derives_emp) ].

   (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _
      (vst_prover types funcs user_comp) left_lemmas right_lemmas).
reflexivity.
mirror_cancel_default.
rcancel.
rcancel.
reify_derives.
lift_and_goal.
mirror_cancel_default. 
Qed.*)

Goal forall n, functions.P n |-- functions.Q n.
intros.
rcancel.
Qed.

Import functions.

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
reify_derives.
Admitted.