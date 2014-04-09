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

Ltac pose_compute x :=
let comp := fresh "comp" in 
pose (comp := x); fold comp; vm_compute in comp; unfold comp; clear comp.

Ltac ecompute_left :=
match goal with
| |- ?X = _ => pose_compute X; exact eq_refl
end.

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
[ | auto | auto | ecompute_left | ecompute_left | auto ]. 


(* trying to test if my reified hints are usable by Mirror *)
Goal forall T sh id y, field_at sh T id y nullval |-- !!False && emp.
Proof.
intros.
pose_env.
reify_derives.
Check lseg_lemmas.null_field_at_false.
mirror_cancel_default.
simpl.
Eval compute in functions.False_f.
Unset Ltac Debug.
Admitted.
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
mirror_cancel_default.
simpl.
Admitted.

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
apply derives_extract_prop. intros.
apply derives_extract_prop. intros.
destruct H5. destruct H6.
pose_env.
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

Locate Ltac prepare.
Fixpoint remove



Fixpoint unflatten_conjuncts {types} l : Expr.expr types :=
match l with
| nil => @Const types tvProp True
| h::nil => h
| h::t => Func 5%nat (h::(unflatten_conjuncts t)::nil)
end . 


Lemma provable_flatten_unflatten :  forall uenv nil e f,
@Provable funcs.all_types.all_types (funcs.functions++f) uenv nil e <->
Provable (funcs.functions ++f) uenv nil (unflatten_conjuncts (flatten_conjuncts e)).
intros.
split. induction e; intros;
auto.
unfold flatten_conjuncts.
do 6 (destruct f0; auto).
simpl. 
destruct l; auto.
simpl. induction l; auto.
simpl.
Admitted.

Fixpoint clean_up_pure' {types} (pl : Expr.exprs types) :=
match pl with 
| Func 48%nat nil :: t => clean_up_pure' t
| h :: t => h :: clean_up_pure' t
| _ => nil
end.

Definition clean_up_pure {types} (p : Expr.expr types) :=
unflatten_conjuncts (clean_up_pure' (flatten_conjuncts p)). 
match goal with
[ |- context [Provable ?funcs ?uenv nil ?r] ] => 
assert (Provable funcs uenv nil (clean_up_pure r))
end.
unfold Provable, clean_up_pure. simpl.
assert (
 Provable funcs uenv nil
     (clean_up_pure (Func 5%nat
        (Func 48%nat nil
         :: Func 5%nat
              (Equal (tvType 4)
                 (Func 9%nat
                    (Func 8%nat
                       (Func 53%nat (Func 50%nat nil :: nil)
                        :: Func 53%nat (Func 50%nat nil :: nil) :: nil)
                     :: nil))
                 (Func 47%nat (Const _s :: Func 51%nat nil :: nil))
               :: Func 48%nat nil :: nil) :: nil)))).

Func 5%nat (a :: b :: nil) => Func 5%nat ((clean_up_pure a)::(clean_up_pure b)::nil)
| Const 

unfold Provable in *.
unfold VericSepLogic.himp.
Admitted.

Lemma try_ex :
  emp |-- EX x : nat, P x.
Proof.
pose_env.
prepare_reify.
reify_derives.
Admitted.

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