Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.local2ptree_denote.
Require Import floyd.local2ptree_eval.

Local Open Scope logic.

Definition msubst_simpl_tc_assert (T1: PTree.t val): tc_assert -> tc_assert :=
  fix msubst_simpl_tc_assert (tc: tc_assert): tc_assert :=
  match tc with
  | tc_andp' tc1 tc2 => tc_andp (msubst_simpl_tc_assert tc1) (msubst_simpl_tc_assert tc2)
  | tc_orp' tc1 tc2 => tc_orp (msubst_simpl_tc_assert tc1) (msubst_simpl_tc_assert tc2)
  | tc_initialized i _ => match T1 ! i with Some _ => tc_TT | None => tc_FF miscellaneous_typecheck_error end
  | _ => tc
  end.

Fixpoint msubst_denote_tc_assert {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (tc: tc_assert): mpred :=
  match tc with
  | tc_FF msg => !! (typecheck_error msg)
  | tc_TT => TT
  | tc_andp' b c => (msubst_denote_tc_assert T1 T2 b) && (msubst_denote_tc_assert T1 T2 c)
  | tc_orp' b c => (msubst_denote_tc_assert T1 T2 b) || (msubst_denote_tc_assert T1 T2 c)
  | tc_nonzero' e => denote_tc_nonzero (force_val (msubst_eval_expr T1 T2 e))
  | tc_isptr e => denote_tc_isptr (force_val (msubst_eval_expr T1 T2 e))
  | tc_test_eq' e1 e2 => denote_tc_test_eq (force_val (msubst_eval_expr T1 T2 e1)) (force_val (msubst_eval_expr T1 T2 e2))
  | tc_test_order' e1 e2 => denote_tc_test_order (force_val (msubst_eval_expr T1 T2 e1)) (force_val (msubst_eval_expr T1 T2 e2))
  | tc_ilt' e i => denote_tc_igt i (force_val (msubst_eval_expr T1 T2 e))
  | tc_Zle e z => denote_tc_Zge z (force_val (msubst_eval_expr T1 T2 e))
  | tc_Zge e z => denote_tc_Zle z (force_val (msubst_eval_expr T1 T2 e))
  | tc_samebase e1 e2 => denote_tc_samebase (force_val (msubst_eval_expr T1 T2 e1)) (force_val (msubst_eval_expr T1 T2 e2))
  | tc_nodivover' v1 v2 => denote_tc_nodivover (force_val (msubst_eval_expr T1 T2 v1)) (force_val (msubst_eval_expr T1 T2 v2))
  | tc_initialized id ty => FF
  | tc_iszero' e => denote_tc_iszero (force_val (msubst_eval_expr T1 T2 e))
  end.

Definition msubst_tc_lvalue {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc) (e: expr) :=
  msubst_denote_tc_assert T1 T2 (msubst_simpl_tc_assert T1 (typecheck_lvalue Delta e)).

Definition msubst_tc_expr {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc) (e: expr) :=
  msubst_denote_tc_assert T1 T2 (msubst_simpl_tc_assert T1 (typecheck_expr Delta e)).


(* Soundness proof *)

(* We cannot prove the following lemma because we need the property that
whenever a tc_initialized is called, a temp_type exists in Delta

Lemma msubst_simpl_tc_assert_sound: forall {cs: compspecs} Delta P T1 T2 Q R tc,
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    denote_tc_assert (msubst_simpl_tc_assert T1 tc) ->
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    denote_tc_assert tc.*)

Lemma msubst_denote_tc_assert_sound: forall {cs: compspecs} Delta P T1 T2 Q R tc,
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    `(msubst_denote_tc_assert T1 T2 tc) ->
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    denote_tc_assert tc.
Proof.
  intros.
  rewrite (add_andp _ _ H); clear H.
  induction tc.
  + apply andp_left2; auto.
  + apply andp_left2; auto.
  + change (denote_tc_assert (tc_andp' tc1 tc2)) with (denote_tc_assert tc1 && denote_tc_assert tc2).
    change (`(msubst_denote_tc_assert T1 T2 (tc_andp' tc1 tc2)))
      with (`(msubst_denote_tc_assert T1 T2 tc1) && `(msubst_denote_tc_assert T1 T2 tc2)).
    apply andp_right.
    - eapply derives_trans; [| apply IHtc1].
      solve_andp.
    - eapply derives_trans; [| apply IHtc2].
      solve_andp.
  + change (denote_tc_assert (tc_orp' tc1 tc2)) with (denote_tc_assert tc1 || denote_tc_assert tc2).
    change (`(msubst_denote_tc_assert T1 T2 (tc_orp' tc1 tc2)))
      with (`(msubst_denote_tc_assert T1 T2 tc1) || `(msubst_denote_tc_assert T1 T2 tc2)).
    rewrite (andp_comm (_ && _)).
    apply imp_andp_adjoint.
    apply orp_left; apply imp_andp_adjoint; rewrite <- (andp_comm (_ && _)).
    - eapply derives_trans; [exact IHtc1 | apply orp_right1; auto].
    - eapply derives_trans; [exact IHtc2 | apply orp_right2; auto].
  + simpl msubst_denote_tc_assert; simpl denote_tc_assert.
    apply imp_andp_adjoint.
    destruct (msubst_eval_expr T1 T2 e) eqn:?H.
    - eapply derives_trans; [apply andp_left2; eapply msubst_eval_expr_eq; eauto |].
      apply imp_andp_adjoint.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
    - apply andp_left1, imp_andp_adjoint, andp_left2.
      simpl denote_tc_nonzero.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
  + simpl msubst_denote_tc_assert; simpl denote_tc_assert.
    apply imp_andp_adjoint.
    destruct (msubst_eval_expr T1 T2 e) eqn:?H.
    - eapply derives_trans; [apply andp_left2; eapply msubst_eval_expr_eq; eauto |].
      apply imp_andp_adjoint.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
    - apply andp_left1, imp_andp_adjoint, andp_left2.
      simpl denote_tc_iszero.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
  + simpl msubst_denote_tc_assert; simpl denote_tc_assert.
    apply imp_andp_adjoint.
    destruct (msubst_eval_expr T1 T2 e) eqn:?H.
    - eapply derives_trans; [apply andp_left2; eapply msubst_eval_expr_eq; eauto |].
      apply imp_andp_adjoint.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
    - apply andp_left1, imp_andp_adjoint, andp_left2.
      unfold denote_tc_isptr.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
  + simpl msubst_denote_tc_assert; simpl denote_tc_assert.
    apply imp_andp_adjoint.
    destruct (msubst_eval_expr T1 T2 e) eqn:?H.
    - eapply derives_trans; [apply andp_left2; eapply msubst_eval_expr_eq; eauto |].
      apply imp_andp_adjoint.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
    - apply andp_left1, imp_andp_adjoint, andp_left2.
      simpl denote_tc_nonzero.
      unfold local, lift1; unfold_lift.
      intros rho.
      simpl.
      normalize.
    SearchAbout msubst_eval_expr.

Lemma msubst_simpl_tc_andp: forall {cs: compspecs} P T1 tc1 tc2,
  P |-- denote_tc_assert (msubst_simpl_tc_assert T1 tc1) && denote_tc_assert (msubst_simpl_tc_assert T1 tc2) ->
  P |-- denote_tc_assert (msubst_simpl_tc_assert T1 (tc_andp' tc1 tc2)).
Proof. 
  intros.
  eapply derives_trans; [exact H | clear H].
  simpl msubst_simpl_tc_assert.
  rewrite denote_tc_assert_andp.
  change (denote_tc_assert (tc_andp' tc1 tc2)) with (denote_tc_assert tc1 && denote_tc_assert tc2).
  auto.
Qed.
SearchAbout tc_andp.
Lemma msubst_simpl_tc_andp_sound: forall {cs: compspecs} T1 tc1 tc2,
  msubst_simpl_tc_assert T1 (tc_andp tc1 tc2) =
  tc_andp (msubst_simpl_tc_assert T1 tc1) (msubst_simpl_tc_assert T1 tc2).
Proof.
  intros.
  destruct tc1, tc2; auto.
  + simpl.
    destruct (tc_andp (msubst_simpl_tc_assert T1 tc1_1) (msubst_simpl_tc_assert T1 tc1_2)); auto.
                         msubst_denote_tc_assert T1 T2 (msubst_simpl_tc_assert T1 tc1) &&
  msubst_denote_tc_assert T1 T2 (msubst_simpl_tc_assert T1 tc2).

Lemma msubst_simpl_tc_orp: forall {cs: compspecs} P T1 tc1 tc2,
  P |-- denote_tc_assert (msubst_simpl_tc_assert T1 tc1) || denote_tc_assert (msubst_simpl_tc_assert T1 tc2) ->
  P |-- denote_tc_assert (msubst_simpl_tc_assert T1 (tc_orp' tc1 tc2)).
Proof. 
  intros.
  eapply derives_trans; [exact H | clear H].
  simpl msubst_simpl_tc_assert.
  rewrite denote_tc_assert_orp.
  change (denote_tc_assert (tc_orp' tc1 tc2)) with (denote_tc_assert tc1 || denote_tc_assert tc2).
  auto.
Qed.

Lemma msubst_tc_lvalue_sound: forall {cs: compspecs} Delta P T1 T2 Q R e,
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    `(msubst_tc_lvalue Delta T1 T2 e) ->
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    tc_lvalue Delta e
 with msubst_tc_expr_sound: forall {cs: compspecs} Delta P T1 T2 Q R e,
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    `(msubst_tc_expr Delta T1 T2 e) ->
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    tc_expr Delta e.
Proof.
  + intros.
    rewrite (add_andp _ _ H); clear H.
    induction e; try solve [apply andp_left2; auto];
    unfold tc_lvalue, msubst_tc_lvalue;
    simpl denote_tc_assert; simpl msubst_denote_tc_assert.
    - destruct (get_var_type Delta i); try solve [apply andp_left2; auto].
      destruct (eqb_type t t0); try solve [apply andp_left2; auto].
    - unfold tc_lvalue, msubst_tc_lvalue.
      simpl denote_tc_assert; simpl msubst_denote_tc_assert.
      destruct (get_var_type Delta i); try solve [apply andp_left2; auto].
      destruct (eqb_type t t0); try solve [apply andp_left2; auto].
  + simpl msubst_simpl_tc_assert.
    rewrite denote_tc_assert_andp.
    change (denote_tc_assert (tc_andp' tc1 tc2)) with (denote_tc_assert tc1 && denote_tc_assert tc2).
    apply andp_right.
    - eapply derives_trans; [| exact IHtc1].
      solve_andp.
    - eapply derives_trans; [| exact IHtc2].
      solve_andp.
  + simpl msubst_simpl_tc_assert.
    rewrite denote_tc_assert_orp.
    change (denote_tc_assert (tc_orp' tc1 tc2)) with (denote_tc_assert tc1 || denote_tc_assert tc2).
    rewrite (andp_comm (_ && _)).
    apply imp_andp_adjoint.
    apply orp_left; apply imp_andp_adjoint; rewrite <- (andp_comm (_ && _)).
    - eapply derives_trans; [exact IHtc1 | apply orp_right1; auto].
    - eapply derives_trans; [exact IHtc2 | apply orp_right2; auto].
  + simpl denote_tc_assert.
    unfold denote_tc_initialized.
    destruct (T1 ! e) eqn:?H.
    - intros rho.
      unfold PROPx, LOCALx.
      simpl.
      unfold local, lift1; unfold_lift.
      apply andp_left1.
      rewrite <- !andp_assoc.
      apply andp_left1.
      rewrite andp_comm, <- andp_assoc.
      apply andp_left1.
      rewrite <- prop_and.
      apply prop_derives.
      intros [? ?].
      apply msubst_eval_eq_aux in H0.
      destruct H0 as [? _].
      specialize (H0 _ _ H).
      unfold eval_id in H0.
      destruct H1 as [? _].
      specialize (H1 e t).
      unfold force_val in H0.
    SearchAbout LocalD (_ ! _).
