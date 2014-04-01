Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.expr.

Fixpoint denote_tc_assert_b (a: tc_assert) :  bool :=
  match a with
  | tc_TT => true
  | tc_andp' b c => andb (denote_tc_assert_b b) (denote_tc_assert_b c)
  | tc_orp' b c => orb (denote_tc_assert_b b) (denote_tc_assert_b c)
  | _ => false
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
is_true (denote_tc_assert_b a) -> denote_tc_assert a rho.
Proof. intros. induction a; inv H; simpl; unfold_lift; simpl; auto;
bool_r in *; intuition.
Qed.
