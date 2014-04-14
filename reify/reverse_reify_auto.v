Require Import floyd.proofauto.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import reverse_defs.
Require Import mirror_cancel.
Require Import ExtLib.Tactics.
Require Import hints.
Require Import preproc.

Local Open Scope logic.

Unset Ltac Debug.


(* trying to test if my reified hints are usable by Mirror *)
Goal forall T sh id y, field_at sh T id y nullval |-- !!False && emp.
Proof.
intros.
pose_env.
reify_derives.
mirror_cancel_default.
Qed.

Goal forall (a b c d: nat), a = b -> b = c -> c = d -> functions.P a |-- functions.P d.
Proof.
intros.
pose_env.
reify_derives.
mirror_cancel_default.
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
pose_env.
reify_derives.
lift_and_goal.
mirror_cancel_default. 
Qed.

Goal forall n, functions.P n |-- functions.Q n.
intros.
pose_env.
reify_derives.
mirror_cancel_default.
Qed.

Import functions.

Parameter X : Z -> mpred.


Goal  X (1 + 3) |-- X (2 + 2).
intros.
pose_env.
reify_derives. 
mirror_cancel_default.
Qed.

Goal  emp |-- emp.
Proof.
pose_env.
reify_derives.
mirror_cancel_default.
Qed.

Goal forall a,  a |-- a.
Proof.
intros.
pose_env.
reify_derives.
mirror_cancel_default.
Qed.

Goal forall a b, a * b |-- b * a.
intros.
pose_env.
prepare_reify.
reify_derives.
mirror_cancel_default.
Qed.

(* Below this point, stuff breaks.
   Some of it is mirror_cancel failing for reasons I don't understand.
   Some of it is that the code below hasn't been updated to pass in
     functions that describe which funcs are computable.
   *)

Goal forall (a b c d: nat), a = b -> b = c -> c = d -> functions.P a |-- functions.P d.
Proof.
intros.
pose_env.
reify_derives.
try mirror_cancel_default.
Qed. 

Definition P2 (v :val) := emp.

Goal forall contents sh rho,
(eval_id _t rho) = (eval_id _p rho) ->
lseg LS sh (map Vint contents) (eval_id _t rho) nullval * emp |--
lseg LS sh (map Vint contents) (eval_id _p rho) nullval * emp.
intros.
pose_env.
reify_derives.
mirror_cancel_default.
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
pose_env.
(
autorewrite with gather_prop.
reify_derives.
Check vst_prover.
let types := get_types in 
eapply (ApplyCancelSep_with_eq_goal 10 10 _ _ _ _ _ (vst_prover types) nil nil _ _ _ ). 
apply eq_refl.
 constructor.
 constructor.
 apply vstProver_correct.
match goal with 
| [ |- ?X = _ ] => assert (exists e, package_cancel X = Some e)
end.
eexists.
match goal with
[ |- ?X = Some ?n] =>  
let p := fresh p in pose (p:=X); fold p; vm_compute in p; unfold p; reflexivity
end.
mirror_cancel_default. 
simpl; unfold Provable; simpl.
Check UNF.hintSideD.
Print SL.sepLemma.


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