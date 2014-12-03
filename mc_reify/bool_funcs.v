Require Import veric.expr.
Require Import veric.SeparationLogic.
Require Import floyd.local2ptree.
Require Import floyd.client_lemmas.
Require Import floyd.loadstore_field_at.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Fixpoint denote_tc_assert_b_norho a:=
match a with 
| tc_TT => true
| tc_andp' a b => andb (denote_tc_assert_b_norho a) (denote_tc_assert_b_norho b)
| tc_orp' a b => orb (denote_tc_assert_b_norho a) (denote_tc_assert_b_norho b)
| _ => false
end.

Definition tc_expr_b_norho Delta e :=
denote_tc_assert_b_norho (typecheck_expr Delta e).

Definition tc_temp_id_b_norho id t Delta e:=
denote_tc_assert_b_norho (typecheck_temp_id id t Delta e).

Lemma tc_expr_b_sound : 
forall e Delta rho,
tc_expr_b_norho Delta e = true ->
tc_expr Delta e rho .
Proof.
intros.
unfold tc_expr, tc_expr_b_norho in *. 
induction (typecheck_expr Delta e); simpl in *; unfold_lift; simpl; auto; try congruence. 
rewrite andb_true_iff in *. intuition.
rewrite orb_true_iff in *. intuition.
Qed.

Lemma tc_temp_id_b_sound : 
forall id t Delta e rho,
tc_temp_id_b_norho id t Delta e= true ->
tc_temp_id id t Delta e rho .
Proof.
intros. 
unfold tc_temp_id, tc_temp_id_b_norho in *.
induction (typecheck_temp_id id t Delta e); simpl in *; unfold_lift; simpl; auto; try congruence.
rewrite andb_true_iff in *. intuition.
rewrite orb_true_iff in *. intuition.
Qed.

Fixpoint tc_efield_b_norho Delta efs :=
  match efs with
  | nil => true
  | eArraySubsc ei :: efs' =>
      (tc_expr_b_norho Delta ei && tc_efield_b_norho Delta efs')%bool
  | eStructField _ :: efs' => tc_efield_b_norho Delta efs'
  | eUnionField _ :: efs' => tc_efield_b_norho Delta efs'
  end.

Lemma tc_efield_b_sound: forall efs Delta rho,
  tc_efield_b_norho Delta efs = true -> tc_efield Delta efs rho.
Proof.
  intros.
  induction efs.
  + simpl; auto.
  + destruct a; simpl in H |- *.
    - apply andb_true_iff in H.
      destruct H.
      apply tc_expr_b_sound with (rho := rho) in H.
      tauto.
    - tauto.
    - tauto.
Qed.

Definition localD (temps : PTree.t val) (locals : PTree.t (type * val)) :=
LocalD temps locals nil.

Definition assertD (P : list Prop) (Q : list (environ -> Prop)) (sep : list mpred) := 
PROPx P (LOCALx Q (SEPx (map (liftx) sep))).
