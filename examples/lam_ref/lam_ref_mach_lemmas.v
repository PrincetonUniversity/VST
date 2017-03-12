(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_mach_lemmas.v: various boring lemmas about the machine *)

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.
Require Import msl.msl_standard.

(* COERCIONS *)

Lemma isVal_val2exp : forall v, isValue (val_to_exp v).
Proof.
  intro.
  destruct v.
  unfold val_to_exp.
  simpl.
  trivial.
Qed.

(* DECIDABILTY *)

Lemma closed_dec : forall e n,
  { closed' n e} + { ~closed' n e}.
Proof.
  induction e; simpl; intros; auto.
  destruct (le_lt_dec n0 n); auto.
  right; abstract omega.
  destruct (IHe1 n); destruct (IHe2 n); intuition.
  destruct (IHe1 n); destruct (IHe2 n); destruct (IHe3 n);
    intuition.
Defined.

Lemma value_dec : forall e,
  { isValue e } + { ~isValue e }.
Proof.
  intros.
  destruct (closed_dec e 0).
  unfold isValue.
  destruct e; simpl; intuition.
  unfold isValue; right; intuition.
Defined.

Ltac show_stopped :=
  let m' := fresh "m'" in
  let e' := fresh "e'" in
  let H := fresh "H" in
  right; intros [m' [e' H]]; inv H.

Lemma stopped_dec : forall e m,
  { st | step (m,e) st} + { stopped m e }.
Proof.
  induction e; intros; try (show_stopped; fail).

  (* Prim *)
  destruct (IHe m) as [[[m' e'] Hstep]|Hstop].
  left; exists (m',Prim f e').
  apply st_Prim1; auto.
  destruct e.
  destruct (value_dec (f n)).
  left; exists (m,f n); apply st_Prim2; auto.
  show_stopped.
  elim Hstop; eauto.
  contradiction.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.

  (* App *)
  destruct (IHe1 m) as [[[m' e'] Hstep]|Hstop].
  left; exists (m',App e' e2); apply st_App1; auto.
  destruct e1; try (show_stopped; inv H1; fail).
  show_stopped; elim Hstop; eauto.
  destruct (IHe2 m) as [[[m' e'] Hstep]|Hstop2].
  left; exists (m', App (Lam e1) e'); apply st_App2; auto.
  destruct (value_dec e2).
  left; exists (m, subst 0 (exp_to_val e2 i) e1).
  apply st_App3.
  show_stopped; elim Hstop; eauto.
  elim Hstop2; eauto.
  contradiction.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.
  show_stopped; elim Hstop; eauto.

  (* New *)
  destruct (IHe m) as [[[m' e'] Hstep]|Hstop].
  left; exists (m',New e'); apply st_New1; auto.
  destruct (value_dec e).
  left.
  case_eq (new m (exp_to_val e i)); intros.
  exists (m0, Loc a); apply st_New2 with i; auto.
  show_stopped.
  elim Hstop; eauto.
  contradiction.

  (* Deref *)
  destruct (IHe m) as [[[m' e'] Hstep]|Hstop].
  left; exists (m',Deref e'); apply st_Deref1; auto.
  destruct e;
    try (show_stopped; elim Hstop; eauto; fail).
  left; exists (m,val_to_exp (deref m l)).
  apply st_Deref2; auto.

  (* Update *)
  destruct (IHe1 m) as [[[m' e'] Hstep]|Hstop].
  left; exists (m',Update e' e2 e3); apply st_Upd1; auto.
  destruct e1;
    try (show_stopped; elim Hstop; eauto; fail).
  destruct (IHe2 m) as [[[m' e'] Hstep]|Hstop2].
  left; exists (m',Update (Loc l) e' e3); apply st_Upd2; auto.
  destruct (value_dec e2).
  left; exists (update m l (exp_to_val e2 i),e3).
  apply st_Upd3 with i; auto.
  show_stopped.
  elim Hstop; eauto.
  elim Hstop2; eauto.
  contradiction.
Qed.

(* SUBSTITUTION *)

Lemma closed'_S : forall n e,
  closed' n e ->
  closed' (S n) e.
Proof.
  intros until e.
  revert n.
  induction e; intros; firstorder.
  unfold closed' in *.
  omega.
Qed.

Lemma closed'_le : forall m n,
  m <= n ->
  forall e,
  closed' m e ->
  closed' n e.
Proof.
  intros m n H; induction H; auto.
  intros.
  apply closed'_S; auto.
Qed.

Lemma closed'_subst: forall m e x v,
  closed' m e ->
  subst (x + m) v e = e.
Proof.
  intros until e.
  revert m.
  induction e; simpl; intros; auto.
  rewrite IHe; auto.
  case_eq (beq_nat (x+m) n); intros; auto.
  symmetry in H0.
  apply beq_nat_eq in H0.
  omegac.
  spec IHe (m + 1) x v H.
  replace (x + (m + 1)) with (x + m + 1) in IHe by omega.
  rewrite IHe.
  trivial.
  destruct H.
  rewrite IHe1; auto.
  rewrite IHe2; auto.
  rewrite IHe; auto.
  rewrite IHe; auto.
  destruct H as [? [? ?]].
  rewrite IHe1; auto.
  rewrite IHe2; auto.
  rewrite IHe3; auto.
Qed.

Lemma closed_closed_subst: forall x v e,
  closed e ->
  closed (subst x v e).
Proof.
  intros until e.
  revert x.
  unfold closed.
  remember 0.
  clear Heqn.
  revert n.
  induction e; simpl; intros; firstorder.
  case_eq (beq_nat x n); intros.
  apply closed'_le with 0.
  omega.
  destruct v; auto.
  case i; auto.
  simpl; auto.
Qed.

Lemma closed_Lam_subst: forall e x v,
  closed (Lam e) ->
  subst x v (Lam e) = Lam e.
Proof.
  intros.
  simpl.
  unfold closed in H.
  simpl in H.
  rewrite closed'_subst; auto.
Qed.

Lemma subst_env'_Nat: forall rho m n,
  subst_env' m rho (Nat n) = Nat n.
Proof.
  do 3 intro.
  revert m.
  induction rho; auto.
  simpl.
  intro.
  rewrite IHrho.
  trivial.
Qed.

Lemma subst_env'_Loc: forall rho m l,
  subst_env' m rho (Loc l) = Loc l.
Proof.
  do 3 intro.
  revert m.
  induction rho; auto.
  simpl.
  intro.
  rewrite IHrho.
  trivial.
Qed.

Lemma subst_env'_Var': forall n m rho,
  subst_env' (S (n + m)) rho (Var n) = Var n.
Proof.
  intros until rho.
  revert n m.
  induction rho; intros.
  trivial.
  simpl.
  generalize (IHrho n (m + 1)); intro.
  replace (n + (m + 1)) with (n + m + 1) in H by omega.
  rewrite H.
  simpl.
  destruct n; auto.
  case_eq (beq_nat (S n + m) n); intros; auto.
  symmetry in H0.
  apply beq_nat_eq in H0.
  omegac.
Qed.

Lemma subst_env'_Var: forall rho n v m,
  nth_error rho n = Some v ->
  subst_env' m rho (Var (n + m)) = val_to_exp v.
Proof.
  intros until n.
  revert rho.
  induction n; intros.
  simpl.
  destruct rho.
  inversion H.
  simpl in *.
  inversion H; clear H.
  subst v0.
  generalize (subst_env'_Var' m 0 rho); intro.
  replace (S (m + 0)) with (m + 1) in H by omega.
  rewrite H.
  simpl.
  case_eq (beq_nat m m); intros; auto.
  apply beq_nat_false in H0.
  elim H0; auto.

  destruct rho.
  inversion H.
  simpl in H.
  simpl.
  spec IHn rho v (m + 1) H.
  replace (n + (m + 1)) with (S (n + m)) in IHn by omega.
  rewrite IHn.
  destruct v.
  unfold val_to_exp.
  simpl.
  generalize i; intro.
  destruct i0.
  destruct x; auto; try contradiction.
  apply closed_Lam_subst.
  trivial.
Qed.

Lemma subst_env'_New: forall rho m e,
  subst_env' m rho (New e) = New (subst_env' m rho e).
Proof.
  do 3 intro.
  revert m.
  induction rho; auto.
  simpl.
  intro.
  rewrite IHrho.
  trivial.
Qed.

Lemma subst_env'_Deref: forall rho m e,
  subst_env' m rho (Deref e) = Deref (subst_env' m rho e).
Proof.
  do 3 intro.
  revert m.
  induction rho; auto.
  simpl.
  intro.
  rewrite IHrho.
  trivial.
Qed.

Lemma subst_env'_Update: forall rho m e1 e2 e3,
  subst_env' m rho (Update e1 e2 e3) =
  Update (subst_env' m rho e1) (subst_env' m rho e2) (subst_env' m rho e3).
Proof.
  do 5 intro.
  revert m.
  induction rho; auto.
  simpl.
  intro.
  rewrite IHrho.
  trivial.
Qed.

Lemma subst_env_New: forall rho e,
  subst_env rho (New e) = New (subst_env rho e).
Proof.
  intros.
  unfold subst_env.
  rewrite subst_env'_New.
  trivial.
Qed.

Lemma subst_env_Deref: forall rho e,
  subst_env rho (Deref e) = Deref (subst_env rho e).
Proof.
  intros.
  unfold subst_env.
  rewrite subst_env'_Deref.
  trivial.
Qed.

Lemma subst_env_Update: forall rho e1 e2 e3,
  subst_env rho (Update e1 e2 e3) =
  Update (subst_env rho e1) (subst_env rho e2) (subst_env rho e3).
Proof.
  intros.
  unfold subst_env.
  rewrite subst_env'_Update.
  trivial.
Qed.

Lemma subst_env_App : forall env e1 e2,
  subst_env env (App e1 e2) = App (subst_env env e1) (subst_env env e2).
Proof.
  intros; unfold subst_env; generalize 0; revert e1 e2; induction env; simpl; intuition.
  rewrite IHenv; auto.
Qed.

Lemma subst_env_Prim : forall env f e,
  subst_env env (Prim f e) = Prim f (subst_env env e).
Proof.
  intros; unfold subst_env; generalize 0; revert e; induction env; simpl; intuition.
  rewrite IHenv; auto.
Qed.

Lemma subst_subst_neq : forall e n m v1 v2,
  n <> m ->
  subst n v1 (subst m v2 e) =
  subst m v2 (subst n v1 e).
Proof.
  induction e; simpl; intuition.
  rewrite <- IHe; auto.
  case_eq (beq_nat m n); intros.
  case_eq (beq_nat n0 n); intros.
  elim H.
  apply beq_nat_true in H0.
  apply beq_nat_true in H1.
  subst; auto.
  simpl.
  rewrite H0.
  apply (closed'_subst n0 (val_to_exp v2) 0 v1).
  apply closed'_le with 0.
  omega.
  destruct v2.
  case i; auto.
  case_eq (beq_nat n0 n); intros.
  simpl.
  rewrite H1.
  symmetry.
  apply (closed'_subst m (val_to_exp v1) 0 v2).
  apply closed'_le with 0; auto.
  omega.
  destruct v1; simpl.
  case i; auto.
  simpl.
  rewrite H1.
  rewrite H0.
  auto.
  rewrite IHe; auto.
  intros.
  apply H.
  unfold var_t in *.
  omega.
  rewrite <- IHe1; auto.
  rewrite <- IHe2; auto.
  rewrite <- IHe; auto.
  rewrite <- IHe; auto.
  rewrite <- IHe1; auto.
  rewrite <- IHe2; auto.
  rewrite <- IHe3; auto.
Qed.

Lemma subst_env_split : forall env1 env2 n e,
  subst_env' n (env1 ++ env2) e =
  subst_env' n env1 (subst_env' (length env1 + n) env2 e).
Proof.
  induction env1; simpl; intros; auto.
  rewrite IHenv1.
  do 3 f_equal.
  omega.
Qed.

Lemma subst_subst_env_lt : forall env n m v e,
  n < m ->
  subst n v (subst_env' m env e) =
  subst_env' m env (subst n v e).
Proof.
  induction env; simpl; intros; auto.
  rewrite <- IHenv.
  2: omega.
  rewrite subst_subst_neq; auto.
  omega.
Qed.


(* STEP RELATION *)

Lemma subst_closed' :
  forall e n v,
    closed' (S n) e ->
    closed' n (subst n v e).
Proof.
  induction e; simpl; intuition.
  destruct (eq_nat_dec n0 n); simpl; subst; auto.
  destruct v.
  case i; intros.
  unfold val_to_exp; simpl.
  apply closed'_le with 0; auto.
  omega.
  case_eq (beq_nat n n); intros.
  auto.
  apply beq_nat_false in H0.
  elim H0; auto.
  case_eq (beq_nat n0 n); intros; auto.
  apply beq_nat_true in H0.
  subst.
  elim n1; auto.
  simpl.
  apply beq_nat_false in H0.
  omega.
Qed.

Lemma closed_subst_env : forall env e x n,
   closed' (length env + x) e ->
   closed' (x + n) (subst_env' (x + n) env e).
Proof.
  induction env; simpl; intros.
  apply closed'_le with x; auto.
  omega.
  apply subst_closed'.
  replace (x + n + 1) with (S (x + n)) by omega.
  change (S (x + n)) with (S x + n).
  eapply IHenv; eauto.
  replace (length env + S x) with (S (length env + x)) by omega; auto.
Qed.

Lemma closed_step : forall x y ,
  step x y ->
  closed (snd x) ->
  closed (snd y).
Proof.
  unfold closed.
  do 3 intro; induction H; simpl in *; intuition.
  eapply subst_closed'; auto.
  destruct v.
  unfold val_to_exp; simpl.
  case i; auto.
  destruct H; auto.
Qed.

Lemma values_stopped: forall e,
  isValue e ->
  forall m,
  stopped m e.
Proof.
  destruct e; repeat intro; destruct H; destruct H0 as [m' [e' ?]]; auto; inversion H0.
Qed.

Lemma stopped_New: forall m e,
  stopped m (New e) ->
  stopped m e.
Proof.
  intros.
  intro.
  apply H.
  destruct H0 as [m' [e' ?]].
  exists m'.
  exists (New e').
  constructor.
  trivial.
Qed.

Lemma stopped_Deref: forall m e,
  stopped m (Deref e) ->
  stopped m e.
Proof.
  intros.
  intro.
  apply H.
  destruct H0 as [m' [e' ?]].
  exists m'.
  exists (Deref e').
  constructor.
  trivial.
Qed.

Lemma stopped_Update: forall m e1 e2 e3,
  stopped m (Update e1 e2 e3) ->
  stopped m e1 \/ (isValue e1 /\ stopped m e2).
Proof.
  intros.
  destruct (stopped_dec e1 m).
  destruct s as [[m' e'] ?].
  elim H.
  exists m'; exists (Update e' e2 e3).
  apply st_Upd1; auto.
  auto.
Qed.


Lemma step_deterministic: forall m e m1 e1 m2 e2,
  step (m,e) (m1,e1) ->
  step (m,e) (m2,e2) ->
  m1 = m2 /\ e1 = e2.
Proof.
  induction e; intros; try (inversion H; discriminate).
(* PRIM *)
  inv H0; inv H1.
  destruct (IHe _ _ _ _ H3 H2).
  intuition congruence.
  inv H3.
  inv H2.
  auto.
(* APP *)
  inversion H; subst.
  inversion H0; subst; try (inversion H2; discriminate).
  spec IHe1 m1 e1' m2 e1'0.
  spec IHe1 H2 H3.
  destruct IHe1.
  subst e1'0.
  tauto.
  inversion H0; subst; try (inversion H3; discriminate).
  spec IHe2 m1 e2' m2 e2'0.
  spec IHe2 H2 H3.
  destruct IHe2.
  subst e2'0.
  tauto.
  generalize (values_stopped e2 H1 m2); firstorder.
  inversion H0; subst.
  inversion H3.
  generalize (values_stopped e2 H1 m1); firstorder.
  assert (H1 = H2) by apply proof_irr.
  rewrite H3.
  tauto.
(* NEW *)
  inversion H; subst.
  inversion H0; subst.
  spec IHe m1 e' m2 e'0.
  spec IHe H2 H3.
  destruct IHe.
  subst e'0.
  tauto.
  generalize (values_stopped e H1 m); firstorder.
  inversion H0; subst.
  generalize (values_stopped e H1 m); firstorder.
  assert (H1 = H2) by apply proof_irr.
  rewrite <- H4 in H5.
  rewrite H3 in H5.
  inversion H5.
  tauto.
(* DEREF *)
  inversion H; subst.
  inversion H0; subst.
  generalize (IHe m1 e' m2 e'0 H2 H3); intro.
  destruct H1.
  subst.
  tauto.
  inv H2.
  inv H0.
  inv H2.
  tauto.
(* UPDATE *)
  inversion H; subst.
  inversion H0; subst; try (inversion H2; discriminate).
  spec IHe1 m1 e1' m2 e1'0.
  spec IHe1 H2 H3.
  destruct IHe1.
  subst; tauto.
  inversion H0; subst; try (inversion H3; discriminate).
  spec IHe2 m1 e2' m2 e2'0.
  spec IHe2 H2 H3.
  destruct IHe2.
  subst.
  tauto.
  generalize (values_stopped e2 H1 m); firstorder.
  inv H0.
  inv H3.
  generalize (values_stopped e2 H1 m); firstorder.
  assert (H1 = H2) by apply proof_irr.
  subst H1.
  auto.
Qed.

Lemma stepn_value: forall j m v st,
  isValue v ->
  stepn j (m, v) st ->
  st = (m, v).
Proof.
  intros.
  inversion H0; subst; auto.
  destruct (values_stopped v H m).
  destruct st'.
  exists m0.
  exists e.
  trivial.
Qed.

Lemma stepstar_search : forall f m e m' e',
  (forall m e m' e',
    step (m,e) (m',e') -> step (m,f e) (m',f e')) ->
  stepstar (m,e) (m',e') ->
  stepstar (m,f e) (m', f e').
Proof.
  intros.
  remember (m,e) as s1; remember (m',e') as s2.
  revert m e m' e' Heqs1 Heqs2.
  induction H0; intuition subst.
  inv Heqs2.
  apply step_refl.
  destruct st2.
  apply step_trans with (m0,f e0).
  apply IHstepstar1; auto.
  apply IHstepstar2; auto.
  apply step1.
  apply H; auto.
Qed.

Lemma stepn_trans : forall n m st1 st2 st3,
  stepn n st1 st2 ->
  stepn m st2 st3 ->
  stepn (n+m) st1 st3.
Proof.
  induction n; simpl; intros; inv H; auto.
  constructor 2 with st'; auto.
  eapply IHn; eauto.
Qed.

Lemma stepstar_stepn : forall st st',
  stepstar st st' <-> exists n, stepn n st st'.
Proof.
  intuition.
  induction H.
  exists 0; apply step0.
  destruct IHstepstar1 as [n1 Hn1].
  destruct IHstepstar2 as [n2 Hn2].
  exists (n1 + n2).
  eapply stepn_trans; eauto.
  exists 1; eapply stepS; eauto.
  apply step0; auto.

  destruct H as [n H].
  revert st st' H.
  induction n; intros.
  inv H.
  apply step_refl.
  inv H.
  apply step_trans with st'0.
  apply step1; auto.
  apply IHn; auto.
Qed.
