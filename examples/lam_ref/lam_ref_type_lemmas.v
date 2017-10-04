(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

Require Import msl.msl_standard.

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.
Require Import lam_ref_mach_lemmas.
Require Import lam_ref_type_prelim.
Require Import lam_ref_type_defs.
Require Import lam_ref_type_safety.

Lemma exp_to_val_to_exp : forall v H,
  exp_to_val (val_to_exp v) H = v.
Proof.
  unfold val_to_exp, exp_to_val.
  intros.
  destruct v as [v Hv]; simpl in *.
  destruct v; simpl in *;
    (replace Hv with H by (apply proof_irr); auto).
Qed.

Lemma forces2exprType: forall w v tau,
  forces w v (%tau) ->
  forall v', expr_type (val_to_exp v) tau (w,v').
Proof.
  intros.
  rewrite expr_type_eqn.
  repeat intro.
  split.
  repeat intro.
  simpl in H4.
  assert (stopped b (val_to_exp v)).
  apply values_stopped.
  unfold val_to_exp.
  destruct v; simpl; auto.
  elim H6; eauto.
  repeat intro.
  simpl in H4.
  exists (projT2 v).
  rewrite exp_to_val_to_exp.
  destruct a'.
  destruct H0.
  subst.
  rewrite <- (box_refl_trans extendM) in H; auto.
  assert (forces m v (%tau)).
  apply H.
  split; auto.
  assert (forces (fst a'1) v (%tau)).
  apply pred_nec_hereditary with (m,v).
  rewrite value_knot_necR; split; auto.
  assert (necR (m,v0) a'1).
  apply rt_trans with a'0; auto.
  destruct a'1.
  rewrite value_knot_necR in H6.
  intuition.
  auto.
  apply H6.
Qed.

Lemma exprType_value : forall w e tau m v
  (H:isValue e),
  forces w v (mtype_valid m) ->
  expr_type e tau (w,v) ->
  forces w (exp_to_val e H) (%tau).
Proof.
  intros.
  rewrite expr_type_eqn in H1.
  spec H1 (w,v).
  detach H1.
  spec H1 m.
  spec H1 (w,v) (rt_refl _ age (w,v)) H0.
  destruct H1.
  spec H2 (w,v) (rt_refl _ age (w,v)).
  detach H2.
  destruct H2.
  replace H with x by (apply proof_irr).
  auto.
  simpl; auto.
  apply values_stopped; auto.
  apply R_extends_refl.
Qed.

Lemma expr_type_search_rule : forall (G Q tau sigma:pred world) (f:expr -> expr),
  forall e a,
         closed (f e) ->
         expr_type e tau a ->
         (Q) a ->
         (|>G) a ->
  forall
  (HQ: boxy extendM Q)
  (HG: boxy extendM G)
  (Hstep : forall m m' x y, step (m,x) (m',y) -> step (m,f x) (m',f y))
  (Hredex:
     forall k v e m (H:isValue e),
         closed (f e) ->
         (|>G) (k,v) ->
         Q (k,v) ->
         mtype_valid m (k,v) ->
         (%tau) (k,exp_to_val e H) ->
         expr_type (f e) sigma (k,v))
  (Hsearch:
     forall e a,
         closed (f e) ->
         G a ->
         Q a ->
         expr_type e tau a ->
         expr_type (f e) sigma a),

  expr_type (f e) sigma a.
Proof.
  intros G Q tau sigma f e a Hcl H H0 H1; intros.
  rewrite expr_type_eqn; repeat intro.
  destruct (stopped_dec e b).
  destruct s as [[m' e'] Hst].
  split; repeat intro.
  simpl in H6.
  destruct a'2 as [k v].
  generalize (Hstep _ _ _ _ Hst); intros.
  assert (m' = b0 /\ f e' = b1).
  eapply step_deterministic; eauto.
  destruct H9; subst b0 b1.
  clear H8.
  rewrite expr_type_eqn in H.
  spec H a' H2.
  spec H b a'0 H3 H4.
  destruct H.
  spec H m' e' a'1 H5.
  detach H.
  spec H (k,v) H7.
  destruct H as [w [? ?]].
  exists w; split; auto.
  destruct H9.
  split; auto.
  apply Hsearch; auto.
  change (f e') with (snd (m',f e')).
  eapply closed_step; eauto.
  rewrite <- HG in H1.
  rewrite <- later_commute in H1.
  spec H1 a' H2.
  spec H1 (k,v).
  detach H1.
  rewrite <- HG in H1.
  apply H1; auto.
  simpl; apply Rft_Rt_trans with a'1; auto.
  apply rt_trans with a'0; auto.
  rewrite <- HQ in H0.
  spec H0 a' H2.
  eapply pred_nec_hereditary in H0.
  2: instantiate (1:=(k,v)).
  rewrite <- HQ in H0.
  apply H0; auto.
  apply rt_trans with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  simpl; auto.
  simpl in H6.
  elim H6.
  exists m'; exists (f e').
  apply Hstep; auto.

  rewrite expr_type_eqn in H.
  spec H a' H2.
  spec H b a'0 H3 H4.
  destruct H.
  spec H5 a'0 (rt_refl _ age a'0).
  spec H5.
  simpl; auto.
  destruct H5.
  destruct a'0 as [k v].
  assert (expr_type (f e) sigma (k,v)).
  spec Hredex k v e b x.
  apply Hredex; auto.
  rewrite <- HG in H1.
  rewrite <- later_commute in H1.
  spec H1 a' H2.
  apply pred_nec_hereditary with a'; auto.
  rewrite <- HQ in H0.
  spec H0 a' H2.
  apply pred_nec_hereditary with a'; auto.
  rewrite expr_type_eqn in H6.
  spec H6 (k,v).
  detach H6.
  eapply H6; eauto.
  apply R_extends_refl.
Qed.

Lemma subst_env_valid_closed :  forall env G e a,
  closed' (length G) e ->
  etype_valid env G a ->
  closed (subst_env env e).
Proof.
  intros.
  unfold closed, subst_env.
  change 0 with (0 + 0).
  apply closed_subst_env.
  replace (length env + 0) with (length G); auto.
  revert H0; clear.
  revert env a; induction G; destruct env; simpl; intuition.
  rewrite IHG with env a0; auto.
Qed.

Lemma etype_valid_lookup: forall G x tau w env v,
  nth_error G x = Some tau ->
  etype_valid env G (w,v) ->
  exists v,
    nth_error env x = Some v /\ forces w v (%tau).
Proof.
  induction G; intros.
  destruct x; inversion H.
  destruct x.
  simpl in H.
  inversion H; clear H.
  subst a.
  destruct env.
  inversion H0.
  simpl in H0.
  destruct H0.
  exists v0.
  simpl.
  auto.
  destruct env.
  inversion H0.
  simpl in H0.
  destruct H0.
  simpl in H.
  apply (IHG _ _ _ _ _ H H1).
Qed.

Lemma etype_valid_val : forall G env m v v',
  etype_valid env G (m,v) ->
  etype_valid env G (m,v').
Proof.
  induction G; destruct env; simpl; intuition.
  eapply IHG; eauto.
Qed.

Lemma expr_type_val' : forall tau,
  TT |-- ALL v:value, ALL e:expr, %(expr_type e tau --> with_val v (expr_type e tau)).
Proof.
  intros; apply goedel_loeb.
  hnf; intros.
  intro v.
  destruct H; destruct a.
  clear H.
  rename H0 into H.
  repeat intro.
  destruct a'; simpl.
  destruct H0; subst.
  destruct a'0.
  rewrite value_knot_necR in H1; destruct H1; subst.
  rewrite expr_type_eqn.
  rewrite expr_type_eqn in H2.
  repeat intro.
  destruct a'.
  destruct H3; subst.
  simpl in H3.
  destruct a'0.
  rewrite value_knot_necR in H4; destruct H4; subst.
  spec H2 (m2,v0).
  detach H2.
  spec H2 b0 (m3,v0).
  detach H2.
  spec H2 H5.
  split; destruct H2.
  repeat intro.
  spec H2 b1 b2.
  destruct a'.
  rewrite value_knot_necR in H7; destruct H7; subst.
  destruct a'0.
  simpl in H9.
  rewrite value_knot_laterR in H9; destruct H9; subst.
  spec H2 (m4,v0).
  detach H2.
  detach H2.
  spec H2 (m5,v0).
  detach H2.
  destruct H2 as [w [? ?]].
  destruct w.
  destruct H2.
  subst.
  exists (m6,v).
  split.
  simpl; split; auto.
  destruct H10.
  split.
  auto.
  rewrite box_all in H.
  spec H v.
  rewrite box_all in H.
  spec H b2.
  rewrite <- (box_refl_trans extendM) in H.
  rewrite <- later_commute in H.
  spec H (m0,v1).
  detach H.
  eapply pred_nec_hereditary in H.
  2: instantiate (1:=(m1,v1)).
  rewrite <- (box_refl_trans extendM) in H.
  rewrite <- later_commute in H.
  spec H (m2,v1); detach H.
  spec H (m5,v1).
  detach H.
  spec H (m6,v1).
  detach H.
  spec H (m6,v1) (rt_refl _ age (m6,v1)).
  apply H; auto.
  split; auto.
  simpl.
  rewrite value_knot_laterR; split; auto.
  apply Rft_Rt_trans with m4; auto.
  apply rt_trans with m3; auto.
  split; auto.
  simpl; apply R_extends_refl.
  simpl; apply R_extends_trans.
  rewrite value_knot_necR; split; auto.
  split; auto.
  simpl; apply R_extends_refl.
  simpl; apply R_extends_trans.
  simpl; rewrite value_knot_laterR; split; auto.
  simpl in H8.
  simpl; auto.
  rewrite value_knot_necR; split; auto.

  repeat intro.
  destruct a'; simpl in H8.
  spec H6 (m4,v0).
  detach H6.
  detach H6.
  auto.
  simpl; auto.
  rewrite value_knot_necR; split; auto.
  rewrite value_knot_necR in H7; intuition.
  rewrite value_knot_necR; split; auto.
  split; auto.
Qed.

Lemma expr_type_val : forall e tau k v v',
  expr_type e tau (k,v) ->
  expr_type e tau (k,v').
Proof.
  intros.
  generalize (expr_type_val' tau); intro H0.
  spec H0 (k,v) I v' e.
  spec H0 (k,v) (R_extends_refl (k,v)).
  spec H0 (k,v) (rt_refl _ age (k,v)).
  apply H0; auto.
Qed.

Lemma openValue_valid_value : forall env G a e,
  openValue e ->
  closed' (length G) e ->
  etype_valid env G a ->
  isValue (subst_env env e).
Proof.
  intros env; pattern env.
  apply rev_ind; clear env; simpl; intros.
  destruct G; auto.
  split; auto.
  elim H1.
  rewrite <- (rev_involutive G) in H2.
  case_eq (rev G); intros;
    rewrite H3 in H2; simpl in H2.
  destruct l; inv H2.
  unfold subst_env.
  rewrite subst_env_split.
  simpl.
  assert (etype_valid l (rev l0) a).
  revert H2; clear.
  generalize (rev l0); clear.
  induction l; simpl; intros; auto.
  destruct l; simpl in *; auto.
  destruct H2.
  destruct l; simpl in H0; auto.
  destruct l0; simpl in H2.
  destruct H2.
  destruct l; simpl in H0; auto.
  destruct H2.
  split.
  destruct a; simpl in *.
  auto.
  apply IHl; auto.

  eapply H with (rev l0) a.
  destruct e; simpl in *; auto.
  elim H0.
  replace (length l + 0) with (length l0).
  rewrite rev_length.
  apply subst_closed'.
  replace (S (length l0)) with (length G); auto.
  rewrite <- rev_length.
  rewrite H3; simpl.
  auto.
  rewrite <- (rev_length l0).
  revert H4; generalize (rev l0); clear.
  induction l; intros.
  destruct l; simpl in H4.
  auto.
  elim H4.
  simpl.
  destruct l0; simpl in H4.
  elim H4.
  simpl; f_equal; auto.
  apply IHl; auto.
  destruct H4; auto.
  auto.
Qed.


(** Redex rules **)

Lemma typ_beta: forall v1 v2 sigma tau w,
  forces w v1 (ty_lam sigma tau) ->
  forces w v2 (%sigma) ->
  forall v', expr_type (App (val_to_exp v1) (val_to_exp v2)) tau (w,v').
Proof.
  intros.
  rewrite expr_type_eqn.
  intros z Hz.
  destruct z as [z v].
  destruct Hz as [Hz ?]; subst.
  repeat intro; split; repeat intro.
  simpl in H4; inv H4.
  elim (values_stopped (val_to_exp v1)) with b; eauto.
  apply (projT2 v1).
  elim (values_stopped (val_to_exp v2)) with b; eauto.
  apply (projT2 v2).
  exists a'1; split.
  do 5 red; apply R_extends_refl.
  rewrite exp_to_val_to_exp.
  split.
  apply pred_nec_hereditary with a'; auto.
  apply rt_trans with a'0; auto.
  apply Rt_Rft; auto.
  destruct H as [e [He [Hjst ?]]].
  simpl in Hjst; subst v1.
  inv H9.
  rewrite <- later_commute in H.
  spec H (z,v_Lam e He).
  detach H.
  spec H (fst a'1,v_Lam e He).
  detach H.
  spec H v2 (fst a'1,v_Lam e He).
  spec H (rt_refl _ age (fst a'1,v_Lam e He)).
  detach H.
  destruct a'1; auto.
  revert H.
  apply expr_type_val.
  simpl; auto.
  simpl; intros.
  destruct a'2; destruct H; subst.
  assert (forces (fst a'1) v0 (%sigma)).
  apply pred_nec_hereditary with (z,v0).
  rewrite value_knot_necR; split; auto.
  assert (necR (z,v) a'1).
  apply rt_trans with a'; auto.
  apply rt_trans with a'0; auto.
  apply Rt_Rft; auto.
  destruct a'1.
  rewrite value_knot_necR in H4.
  intuition.
  rewrite <- (box_refl_trans extendM) in H0; auto.
  apply H0.
  split; auto.
  apply H4.
  split; auto.
  simpl; rewrite value_knot_laterR; split; auto.
  assert (laterR (z,v) a'1).
  apply Rft_Rt_trans with a'; auto.
  apply Rft_Rt_trans with a'0; auto.
  destruct a'1.
  rewrite value_knot_laterR in H.
  intuition.
  split; auto.

  elimtype False.
  simpl in H4.
  elim H4.
  destruct H as [e [He [? ?]]].
  simpl in H.
  subst v1.
  unfold v_Lam.
  unfold val_to_exp, v_Lam; simpl.
  exists b.
  exists (subst 0 (exp_to_val (projT1 v2) (projT2 v2)) e).
  apply st_App3.
Qed.

Lemma expr_ty_new: forall k v tau,
  forces k v (%tau) ->
  forall v', expr_type (New (val_to_exp v)) (ty_ref tau) (k,v').
Proof.
  intros.
  destruct v; unfold val_to_exp; simpl.
  rewrite expr_type_eqn.
  repeat intro.
  split; repeat intro.

  simpl in H4.
  inv H4.
  assert (stopped b x).
  apply values_stopped; auto.
  elim H4; eauto.
  unfold new in H8.
  destruct b; inv H8.
  destruct a'2.
  case_eq (unsquash m); intros.
  set (f' := fun a => if beq_nat a l then Some tau else f a).
  assert (R_extends (m,v0) (squash (n,f'),v0)).
  split; auto.
  hnf.
  rewrite H4.
  rewrite unsquash_squash.
  split; auto.
  intros.
  assert (mtype_valid (l,v) (m,v0)).
  apply pred_nec_hereditary with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  case_eq (f a); intros; auto.
  right.
  unfold fmap, option_map, compose, f'.
  hnf in H7.
  rewrite H4 in H7.
  case_eq (beq_nat a l); intros.
  apply beq_nat_true in H9.
  subst a.
  spec H7 l.
  cbv beta zeta in H7.
  rewrite H8 in H7.
  destruct H7.
  simpl in H7; omegac.
  cbv beta zeta in H7.
  spec H7 a.
  rewrite H8 in H7.
  simpl.
  rewrite H8.
  generalize H8.
  rewrite (unsquash_approx H4).
  simpl.
  rewrite H8.
  rewrite H9.
  auto.
  assert
    (mtype_valid
        (S l, fun a : nat => if beq_nat a l then exp_to_val x H6 else v a)
        (squash (n,f'),v0)).
  hnf. unfold f'.
  rewrite unsquash_squash.
  intro a.
  simpl fmap. simpl ffun_fmap.
  case_eq (beq_nat a l); intros.
  simpl option_map.
  unfold fidentity_fmap.
  apply beq_nat_true in H8.
  subst a.
  simpl fst.
  split; auto.

  unfold deref; simpl snd.
  case_eq (beq_nat l l); intros.
  replace H6 with i by apply proof_irr.
  rewrite later_commute.
  fold f'.
  unfold forces.
  unfold forces in H.
  cut ((%tau) (squash (n,f'),exp_to_val x i)).
  repeat intro.
  red. rewrite approx_spec.
  split; auto.
  replace (level a'3) with (level a'2).
  apply lt_le_trans with (level (fst (squash (n,f'),exp_to_val x i))).
  simpl in H10.
  destruct a'2.
  rewrite value_knot_laterR in H10.
  simpl.
  apply laterR_level; auto.
  destruct H10; auto.
  rewrite knot_level; simpl.
  rewrite unsquash_squash; auto.
  simpl in H11.
  apply extend_level; auto.
  eapply pred_nec_hereditary in H9.
  2: apply Rt_Rft; apply H10.
  spec H9 a'3 H11.
  apply pred_nec_hereditary with a'3; auto.
  destruct a'.
  assert ((%tau) (m0,exp_to_val x i)).
  rewrite <- box_refl_trans in H; auto.
  apply H.
  split; auto.
  destruct H0; auto.
  assert ((%tau) (m,exp_to_val x i)).
  apply pred_nec_hereditary with (m0,exp_to_val x i).
  rewrite value_knot_necR; split; auto.
  assert (necR (m0,v1) (m,v0)).
  apply rt_trans with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  rewrite value_knot_necR in H10.
  destruct H10; auto.
  auto.
  rewrite <- box_refl_trans in H10; auto.
  apply H10; auto.
  split; auto.
  destruct H7; auto.
  apply beq_nat_false in H8; elim H8; auto.
  case_eq (f a); intros.
  assert (mtype_valid (l,v) (m,v0)).
  apply pred_nec_hereditary with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  hnf in H10.
  rewrite H4 in H10.
  cbv beta zeta in H10.
  spec H10 a.
  rewrite H9 in H10.
  destruct H10.
  simpl in H10.
  split.
  simpl; omega.
  simpl deref.
  rewrite H8.
  unfold deref in H11.
  simpl snd in H11.
  rewrite <- box_refl_trans in H11; auto.
  fold f'.
  spec H11 (squash (n,f'),v a).
  spec H11.
  split; auto.
  destruct H7; auto.
  repeat intro.
  unfold fidentity_fmap. red. rewrite approx_spec.
  split.
  apply lt_le_trans with (level a'2).
  apply laterR_level; auto.
  destruct a'2; destruct H12; subst.
  simpl.
  rewrite knot_level.
  hnf in H12.
  rewrite unsquash_squash in H12.
  case_eq (unsquash m0); intros.
  rewrite H14 in H12; auto.
  destruct H12; simpl; subst; auto.
  eapply H11; eauto.
  simpl.
  assert (mtype_valid (l,v) (m,v0)).
  apply pred_nec_hereditary with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  hnf in H10.
  rewrite H4 in H10.
  spec H10 a.
  cbv beta zeta in H10.
  rewrite H9 in H10.
  simpl in H10.
  apply beq_nat_false in H8.
  omega.

  exists (squash (n,f'),v0).
  split; auto.
  split; auto.
  change (Loc l) with (val_to_exp (v_Loc l)).
  apply forces2exprType.
  rewrite ty_ref_extends.
  exists l; split.
  simpl; auto.
  simpl.
  rewrite unsquash_squash.
  unfold f'. simpl.
  case_eq (beq_nat l l); simpl; intros.
  hnf.
  unfold fidentity_fmap.
  change (approx n (approx n tau)) with ((approx n oo approx n) tau).
  rewrite <- (approx_approx1 0).
  auto.
  apply beq_nat_false in H9; elim H9; auto.

  simpl in H4.
  elim H4.
  case_eq (new b (exp_to_val x i)); intros.
  exists m; exists (Loc a).
  apply st_New2 with i; auto.
Qed.

Lemma expr_type_upd_Update: forall tau sigma w l v e3 v0,
  forces w (v_Loc l) (ty_ref tau) ->
  forces w v (%tau) ->
  expr_type e3 sigma (w,v0) ->
  expr_type (Update (Loc l) (val_to_exp v) e3) sigma (w,v0).
Proof.
  intros.
  rewrite expr_type_eqn; repeat intro.
  split; repeat intro.
  simpl in H6.
  inv H6.
  inv H9.
  assert (stopped b (val_to_exp v)).
  apply values_stopped.
  destruct v; auto.
  elim H6; eauto.
  exists a'2.
  split.
  simpl; apply R_extends_refl.
  split; auto.
  eapply pred_nec_hereditary in H4.
  2: instantiate (1:=a'2).
  2: apply rt_trans with a'1; auto.
  2: apply Rt_Rft; auto.
  destruct a'2.
  simpl in H4.
  simpl.
  case_eq (unsquash m); intros.
  rewrite H6 in H4.
  spec H4 a.
  revert H4.
  generalize (refl_equal (f a)).
  case_eq (f a); intros.
  rewrite exp_to_val_to_exp.
  unfold update.
  destruct b.
  simpl.
  simpl in H9.
  destruct H9; split; auto.
  case_eq (beq_nat l a); intro; auto.
  apply beq_nat_true in H11; subst a.
  hnf in H.
  destruct H.
  destruct H.
  simpl in H; inv H.
  cut (type_at x tau (m,v_Loc x)).
  intro.
  simpl in H.
  rewrite H6 in H.
  rewrite H4 in H.
  cut ((%tau) (m,v)); intros.
  spec H12 a'2 H13.
  eapply pred_nec_hereditary in H12.
  2: apply rt_trans with a'3; auto.
  2: apply Rt_Rft; auto.
  cut (approx n tau a'3).
  hnf in H.
  rewrite <- H.
  intros.
  red in H15. rewrite approx_spec in H15.
  destruct H15; auto.
  red. rewrite approx_spec.
  split; auto.
  apply lt_le_trans with (level a'2).
  apply laterR_level.
  apply Rt_Rft_trans with a'3; auto.
  destruct a'2.
  destruct H13; subst.
  simpl.
  rewrite knot_level.
  case_eq (unsquash m0); intros.
  hnf in H13.
  rewrite H6 in H13.
  rewrite H15 in H13.
  destruct H13; subst; simpl; auto.
  red in H0.
  assert ((%tau) (fst a',v)).
  rewrite <- box_refl_trans in H0; auto.
  spec H0 (fst a',v).
  spec H0.
  split; auto.
  destruct a'; destruct H2; auto.
  auto.
  apply pred_nec_hereditary with (fst a', v); auto.
  rewrite value_knot_necR; split; auto.
  assert (necR a' (m,v1)).
  apply rt_trans with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  destruct a'.
  rewrite value_knot_necR in H13.
  simpl; destruct H13; auto.
  rewrite <- type_at_extends in H11.
  spec H11 (fst a', v_Loc x).
  spec H11.
  split; auto.
  destruct a'; destruct H2; auto.
  eapply pred_nec_hereditary.
  2: apply H11.
  rewrite value_knot_necR; split; auto.
  assert (necR a' (m,v1)).
  apply rt_trans with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  destruct a'.
  rewrite value_knot_necR in H.
  destruct H; simpl; auto.
  unfold update; destruct b; simpl; auto.
  rewrite <- expr_type_extends in H1.
  spec H1 a' H2.
  eapply pred_nec_hereditary.
  2: apply H1.
  apply rt_trans with a'; auto.
  apply rt_trans with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  simpl in H6.
  elim H6.
  exists (update b l v).
  exists e3.
  destruct v.
  apply st_Upd3 with i; auto.
Qed.


Lemma expr_ty_deref_loc : forall l tau a,
  expr_type (Loc l) (ty_ref tau) a ->
  expr_type (Deref (Loc l)) tau a.
Proof.
  intros.
  rewrite expr_type_eqn; repeat intro.
  split; repeat intro.
  simpl in H4.
  inv H4.
  inv H7.
  exists a'2.
  split.
  simpl; apply R_extends_refl.
  split.
  apply pred_nec_hereditary with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  rewrite <- expr_type_extends in H.
  spec H a' H0.
  eapply pred_nec_hereditary in H.
  2: instantiate (1:=a'1).
  2: apply rt_trans with a'0; auto.
  assert (forces (fst a'1) (exp_to_val (Loc l) (isvLoc l)) (%(ty_ref tau))).
  destruct a'1.
  eapply exprType_value.
  2: apply H.
  unfold fst.
  red.
  apply pred_nec_hereditary with a'0; auto.
  apply H2.
  rewrite ty_ref_extends in H4.
  destruct a'1.
  destruct H4 as [l' [? ?]].
  simpl in H4; inv H4.
  simpl fst in H6.
  assert (mtype_valid b0 (m,v)).
  apply pred_nec_hereditary with a'0; auto.
  simpl in H6.
  hnf in H4.
  cbv beta zeta in H4.
  case_eq (unsquash m); intros;
    rewrite H7 in H4, H6.
  spec H4 l'.
  case_eq (f l'); intros.
  rewrite H8 in H4, H6.
  destruct H4.
  destruct a'2.
  eapply forces2exprType.
  rewrite later_commute in H9.
  spec H9 (m0,deref b0 l').
  detach H9.
  repeat intro.
  spec H9 a'1 H10.
  cut (approx n p a'1); intros.
  hnf in H6.
  rewrite H6 in H11.
  red in H11. rewrite approx_spec in H11.
  destruct H11; auto.
  red. rewrite approx_spec.
  split; auto.
  change (level a'1 < n).
  apply le_lt_trans with (level (m0,v0)).
  destruct a'1; destruct H10.
  simpl.
  hnf in H10.
  repeat rewrite knot_level.
  destruct (unsquash m0); destruct (unsquash m1).
  destruct H10; subst; auto.
  apply lt_le_trans with (level (m,v)).
  apply laterR_level; auto.
  simpl.
  rewrite knot_level.
  rewrite H7; simpl; auto.
  simpl in H5; rewrite value_knot_laterR in H5.
  destruct H5; subst.

  simpl; rewrite value_knot_laterR; split; auto.
  rewrite H8 in H6, H4.
  elim H6.
  simpl in H4.
  elim H4.
  exists b.
  exists (val_to_exp (deref b l)).
  apply st_Deref2; auto.
Qed.
