Require Import veric.base.
Require Import veric.expr.
(*A boolean denote_tc_assert *)

Definition denote_tc_iszero_b v :=
         match v with Vint i => (Int.eq i Int.zero) 
                            | Vlong i =>  (Int.eq (Int.repr (Int64.unsigned i)) Int.zero)
                            | _ => false 
         end.

Definition denote_tc_nonzero_b v := 
         match v with Vint i => if negb (Int.eq i Int.zero) then true else false
                                               | _ => false end.

Definition denote_tc_igt_b i v :=
     match v with | Vint i1 => (Int.ltu i1 i)
                     | _ => false
                  end.

Definition denote_tc_Zge_b z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => (Zge_bool z n)
                                    | None => false
                                   end
                     | _ => false 
                  end.

Definition denote_tc_Zle_b z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => (Zle_bool z n)
                                    | None => false
                                   end
                     | _ => false 
                  end.

Definition denote_tc_samebase_b v1 v2 :=
                         match v1, v2 with
                           | Vptr b1 _, Vptr b2 _ => (peq b1 b2)
                           | _, _ => false 
                         end.

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover_b v1 v2 :=
match v1, v2 with
                           | Vint n1, Vint n2 => (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                           | _ , _ => false
                          end.

Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Export veric.lift.
Require Export veric.Cop2.


Definition denote_tc_initialized_b id ty rho := 
match Map.get (te_of rho) id with 
| Some v => typecheck_val v ty
| None => false
end.

Definition isptr_b v := 
   match v with | Vptr _ _ => true | _ => false end.

Fixpoint denote_tc_assert_b (a: tc_assert) : environ -> bool :=
  match a with
  | tc_FF _ => `false
  | tc_noproof => `false
  | tc_TT => `true
  | tc_andp' b c => `andb (denote_tc_assert_b b) (denote_tc_assert_b c)
  | tc_orp' b c => `orb (denote_tc_assert_b b) (denote_tc_assert_b c)
  | tc_nonzero e => `denote_tc_nonzero_b (eval_expr e)
  | tc_isptr e => `isptr_b (eval_expr e)
  | tc_ilt e i => `(denote_tc_igt_b i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge_b z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle_b z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase_b (eval_expr e1) (eval_expr e2)
  | tc_nodivover v1 v2 => `denote_tc_nodivover_b (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized_b id ty
  | tc_iszero' e => `denote_tc_iszero_b (eval_expr e)
 end.

Lemma false_true : False <-> false=true.
intuition.
Qed.

Lemma true_false : False <-> true=false.
intuition.
Qed.

Lemma true_true : True <-> true = true.
intuition.
Qed.

Lemma false_false : True <-> false = false.
intuition.
Qed. 

Hint Rewrite <- false_true : bool.
Hint Rewrite <- true_false : bool.
Hint Rewrite <- false_false : bool.
Hint Rewrite <- true_true : bool.
Hint Rewrite andb_true_iff : bool.
Hint Rewrite orb_true_iff : bool.
Hint Rewrite andb_false_iff : bool.
Hint Rewrite orb_false_iff : bool.
Hint Rewrite andb_false_r : bool.
Hint Rewrite andb_true_r : bool.
Hint Rewrite orb_false_r : bool.
Hint Rewrite orb_true_r : bool.

Ltac bool_r:=
try unfold is_true; autorewrite with bool; try symmetry; autorewrite with bool; auto.

Ltac bool_n H := 
try unfold is_true in H; autorewrite with bool in H; try symmetry in H; autorewrite with bool in H; auto.

Ltac bool_s :=
try unfold is_true in *; autorewrite with bool in *; try symmetry in *; autorewrite with bool in *; auto.


Tactic Notation "bool_r" "in" ident(H) :=
bool_n H.

Tactic Notation "bool_r" "in" "*" :=
bool_s.

Definition denote_te_assert_b_eq : forall a rho, 
denote_tc_assert a rho <-> is_true (denote_tc_assert_b a rho).
Proof. intros. split; intros.
induction a; simpl in *; super_unfold_lift; bool_r in *; intuition;
simpl in *;
try destruct (eval_expr e); simpl in *;
try match goal with 
| [ H : if ?e then True else False |- _ ] => destruct e; simpl; inv H
| [ H : match ?e with | _ => _  end |- _ ] => destruct e; simpl in *; inv H
end; auto; try congruence;
unfold denote_tc_initialized, denote_tc_initialized_b in *;
destruct H. destruct H. rewrite H. auto.

induction a; simpl in *; super_unfold_lift; bool_r in *; intuition; try congruence;
simpl in *;
try destruct (eval_expr e); simpl in *; try congruence;
try match goal with 
| [ H : (if ?e then true else false) = true |- _ ] => destruct e; simpl; inv H
| [ H : (match ?e with | _ => _ end) = true |- _ ] => destruct e; simpl in *; inv H
end; auto; try congruence.
unfold denote_tc_initialized, denote_tc_initialized_b in *.
destruct (Map.get (te_of rho) e). exists v. auto.
congruence.
Qed.