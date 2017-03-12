(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

Require Import msl.msl_standard.

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.
Require Import lam_ref_mach_lemmas.
Require Import lam_ref_type_defs.
Require Import lam_ref_type_safety.
Require Import lam_ref_type_lemmas.


(* Typing rules *)

Lemma T_weaken : forall G G' e tau,
  Typ G e tau ->
  Typ (G++G') e tau.
Proof.
  intros.
  unfold Typ in *; intuition.
  apply closed'_le with (length G); auto.
  clear.
  induction G; simpl; omega.
  unfold subst_env in *.

  intro a.
  assert (forall env,
    etype_valid env G a ->
    expr_type (subst_env' 0 env e) tau a).
  intros; eapply H1; auto.
  clear H1.
  intro.
  assert (exists env1, exists env2,
    env = env1 ++ env2 /\ etype_valid env1 G a /\ etype_valid env2 G' a).
  clear -H1.
  revert env H1.
  induction G; simpl; intros.
  exists nil; exists env.
  simpl; intuition.
  destruct env; simpl in H1; destruct H1.
  destruct (IHG env H0) as [e1 [e2 [? [? ?]]]].
  exists (v::e1); exists e2.
  simpl; intuition.
  f_equal; auto.
  destruct H2 as [env1 [env2 [? [? ?]]]].
  replace (subst_env' 0 env e)
    with (subst_env' 0 env1 e).

  apply H; auto.
  subst env.
  rewrite subst_env_split.
  replace (subst_env' (length env1 + 0) env2 e) with e; auto.
  replace (length env1 + 0) with (length G).
  revert H0; generalize (length G); clear.
  revert e; induction env2; simpl; intuition.
  rewrite <- IHenv2.
  symmetry.
  apply (closed'_subst n e 0 a); auto.
  apply closed'_le with n; auto.
  omega.
  clear -H3.
  revert a G H3; induction env1; simpl; intros.
  destruct G; auto.
  elim H3.
  destruct G; auto.
  elim H3.
  simpl.
  f_equal; apply IHenv1 with a0.
  destruct H3; auto.
Qed.

Lemma T_weaken_nil : forall G e tau,
  Typ nil e tau ->
  Typ G e tau.
Proof.
  intros; apply (T_weaken nil); auto.
Qed.

Fixpoint gamma_sub (G G':etype) {struct G} : Prop :=
  match G, G' with
  | nil, nil => True
  | x::xs, y::ys => TT |-- y >=> x /\ gamma_sub xs ys
  | _, _ => False
  end.

Lemma etype_valid_sub : forall G G' env a,
  gamma_sub G G' ->
  etype_valid env G' a ->
  etype_valid env G  a.
Proof.
  induction G; simpl; intros;
    destruct G'; destruct env; intuition.
  split.
  hnf in H0; destruct H0.
  clear H0.
  eapply sub_with_val; try apply H1; eauto.
  apply sub_extend; auto.
  hnf in H0; destruct H0.
  eapply IHG; eauto.
Qed.

Lemma T_weaken_sub : forall G G' e tau,
  gamma_sub G G' ->
  Typ G  e tau ->
  Typ G' e tau.
Proof.
  intros.
  assert (length G = length G').
  clear -H; revert G' H; induction G; simpl; intuition.
  destruct G'; auto.
  elim H.
  destruct G'; auto.
  elim H.
  simpl.
  f_equal; apply IHG; auto.
  destruct H; auto.
  destruct H0; split; auto.
  rewrite <- H1; auto.
  repeat intro.
  apply H2.
  apply etype_valid_sub with G'; auto.
Qed.

Lemma T_sub : forall G tau tau' e,
  TT |-- tau >=> tau' ->
  Typ G e tau ->
  Typ G e tau'.
Proof.
  intros.
  unfold Typ in *; intuition.
  assert (tau |-- tau').
  intro.
  spec H (level a).
  spec H. hnf; auto.
  spec H a. spec H.
  auto.
  eapply H; auto.

  cut ( TT |-- %(ALL e:expr,
    (!!(closed e) && expr_type e tau) --> expr_type e tau')).
  intros.
  hnf; intros.
  spec H3 a.
  spec H3. eauto.
  eapply H3; eauto.
  apply R_extends_refl.
  split; auto. hnf.
  eapply subst_env_valid_closed; eauto.
  eapply H2. auto.

  clear -H0. rename H0 into Htau.
  apply goedel_loeb.
  apply positive_boxy.
  rewrite TT_and.
  hnf.
  rewrite later_commute.
  rewrite box_refl_trans; auto.
  rewrite TT_and.

  apply forallI; intro e.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H.
  destruct H0.
  simpl in H0.
  eapply expr_type_search_rule with (f:=@id expr).
  auto.
  apply H1.
  instantiate (1:= TT). auto.
  apply H.
  apply boxy_TT; auto.
  hnf; rewrite box_refl_trans; auto.
  intros; auto.

  clear -Htau; intros.
  unfold id.
  change e with (val_to_exp (exp_to_val e H)).
  eapply forces2exprType; auto.
  unfold forces.
  repeat intro.
  destruct a'.
  destruct H5; subst v0.
  spec H4 (m0,exp_to_val e H).
  spec H4.
  split; auto.
  apply Htau. auto.

  clear -Htau; intros.
  unfold id.
  eapply H0; eauto.
  apply R_extends_refl.
  split; auto.
Qed.


Lemma T_Nat : forall G n,
  Typ G (Nat n) ty_nat.
Proof.
  intros; split; intros.
  simpl; auto.
  do 2 intro.
  unfold subst_env.
  rewrite (subst_env'_Nat env 0).
  clear H.
  change (Nat n) with (val_to_exp (v_Nat n)).
  destruct a.
  apply forces2exprType.
  rewrite ty_nat_extends.
  hnf; eauto.
Qed.


Lemma T_Var: forall G x tau,
  nth_error G x = Some tau -> (* g(x) = tau *)
  Typ G (Var x) tau.
Proof.
  intros.
  split.
  revert x H.
  induction G; destruct x; simpl in *; intros; try discriminate.
  omega.
  apply IHG in H.
  omega.
  do 3 intro.
  destruct a.
  destruct (etype_valid_lookup _ _ _ _ _ _ H H0) as [v' [? ?]].
  unfold subst_env.
  generalize (subst_env'_Var env x v' 0 H1); intro.
  replace (x + 0) with x in H3 by omega.
  rewrite H3.
  apply forces2exprType.
  assumption.
Qed.

Lemma T_Abs: forall G sigma e tau,
  Typ (sigma :: G) e tau ->
  Typ G (Lam e) (ty_lam sigma tau).
Proof.
  repeat intro.
  split; intros.
  destruct H; simpl in *.
  replace (length G + 1) with (S (length G)) by omega; auto.
  destruct H.
  simpl in H.
  unfold subst_env.
  replace (subst_env' 0 env (Lam e))
    with (Lam (subst_env' 1 env e)).
  rewrite expr_type_eqn.
  do 2 intro.
  intros z Hz.
  repeat intro; split; repeat intro.
  simpl in H5.
  inv H5.
  simpl in H5.
  assert (closed' 1 (subst_env' 1 env e)).
  change 1 with (1 + 0).
  destruct a.
  eapply closed_subst_env; eauto.
  replace (length env + 1) with (S (length G)).
  auto.
  clear -H1.
  revert env m v H1; induction G; destruct env; simpl; intuition.
  rewrite IHG with env m v0; auto.
  exists (isvLam _ H6).
  rewrite ty_lam_extends.
  exists (subst_env' 1 env e).
  exists H6.
  split.
  simpl; auto.
  simpl; intros.
  destruct a'1.
  rewrite value_knot_laterR in H7.
  destruct H7; subst.
  destruct a'2.
  destruct H8.
  subst v.
  destruct a'3.
  rewrite value_knot_necR in H9.
  destruct H9; subst.
  simpl in H10.
  apply (H0 (b0::env)); auto.
  split; auto.
  match goal with [ |- app_pred (etype_valid env G) (m1,?X) ] =>
    generalize X
  end.
  intros.
  apply pred_nec_hereditary with (m0,v).
  rewrite value_knot_necR; split; auto.
  assert (etype_valid env G (m,v)).
  apply etype_valid_val with (snd a'0).
  apply pred_nec_hereditary with a'0.
  destruct a'0.
  rewrite value_knot_necR; split; simpl; auto.
  apply Rt_Rft; auto.
  apply pred_nec_hereditary with z; auto.
  apply rt_trans with a'; auto.
  rewrite <- etype_valid_extends in H1.
  apply H1; auto.
  rewrite <- etype_valid_extends in H11.
  apply H11.
  simpl; split; auto.

  generalize 0.
  induction env; simpl; intros; auto.
  rewrite <- IHenv.
  simpl.
  replace (n+1) with (S n) by omega.
  trivial.
Qed.

Definition prim (f:nat -> value) : expr -> expr :=
  Prim (val_to_exp oo f).

Lemma T_Prim : forall G f e sigma,
  (forall n, Typ nil (val_to_exp (f n)) sigma) ->
  Typ G e ty_nat ->
  Typ G (prim f e) sigma.
Proof.
  intros.
  destruct H0; split; auto.
  repeat intro.
  spec H1 env a H2.
  unfold prim.
  rewrite subst_env_Prim.
  cut ( TT |-- %(ALL e:expr,
        !!(closed e) && expr_type e ty_nat --> expr_type (Prim (val_to_exp oo f) e) sigma)).
  intros; eapply H3; eauto.
  apply R_extends_refl.
  simpl; auto.
  split; auto.
  eapply subst_env_valid_closed; eauto.
  clear -H.

  apply goedel_loeb.
  rewrite TT_and.
  apply positive_boxy.
  hnf; rewrite later_commute; rewrite box_refl_trans; auto.
  apply forallI; intro e.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H0.
  destruct H1.
  simpl in H1.
  eapply expr_type_search_rule with (f:= fun x => Prim (val_to_exp oo f) x).
  auto.
  apply H2.
  instantiate (1:=TT); simpl; auto.
  apply H0.
  apply TT_boxy.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_Prim1; auto.

  clear -H.
  intros.
  rewrite expr_type_eqn; repeat intro.
  split; repeat intro.
  simpl in H10.
  inv H10.
  assert (stopped b e) by (apply values_stopped; auto).
  elim H10; eauto.
  exists a'2; split; auto.
  simpl; apply R_extends_refl.
  split.
  apply pred_nec_hereditary with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  spec H n.
  destruct H.
  spec H10 (nil:env) a'2 I.
  apply H10.
  rewrite ty_nat_extends in H5.
  destruct H5.
  inv H5.
  simpl in H10.
  elim H10.
  exists b.
  exists ((val_to_exp oo f) x).
  apply st_Prim2.
  unfold compose.
  destruct (f x); auto.

  clear; intros.
  eapply H0; eauto.
  apply R_extends_refl.
  split; auto.
Qed.

Lemma T_New: forall G e tau,
  Typ G e tau ->
  Typ G (New e) (ty_ref tau).
Proof.
  intros; destruct H; split; simpl; auto.
  repeat intro.
  rewrite subst_env_New.
  spec H0 env a H1.
  assert (closed (subst_env env e)).
  eapply subst_env_valid_closed; eauto.

  cut (TT |-- %(ALL e:expr, !!(closed e) && expr_type e tau --> expr_type (New e) (ty_ref tau))).
  intros.
  eapply H3; eauto.
  apply R_extends_refl.
  simpl; auto.

  clear.
  apply goedel_loeb.
  rewrite TT_and.
  apply positive_boxy.
  hnf.
  rewrite later_commute.
  rewrite box_refl_trans; auto.
  apply forallI; intro e.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H.
  destruct H0.
  simpl in H0.
  eapply expr_type_search_rule.
  unfold closed; simpl; auto.
  apply H1.
  instantiate (1:=TT); simpl; auto.
  apply H.
  apply TT_boxy.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_New1; auto.

  intros.
  change e0 with (val_to_exp (exp_to_val e0 H2)).
  eapply expr_ty_new; auto.

  intros.
  eapply H3; eauto.
  apply R_extends_refl.
  split; auto.
Qed.

Lemma T_App: forall G e1 sigma tau e2,
  Typ G e1 (ty_lam sigma tau) ->
  Typ G e2 sigma ->
  Typ G (App e1 e2) tau.
Proof.
  intros.
  destruct H; destruct H0; split.
  simpl; split; auto.
  repeat intro.

  rewrite subst_env_App.
  spec H1 env a H3.
  spec H2 env a H3.
  cut (TT |-- %(ALL e1:expr, ALL e2:expr, (!!(closed e1 /\ closed e2)) && expr_type e1 (ty_lam sigma tau) && expr_type e2 sigma --> expr_type (App e1 e2) tau)).
  intros; eapply H4; eauto.
  apply R_extends_refl.
  hnf; auto.
  simpl; repeat split; auto.
  eapply subst_env_valid_closed; eauto.
  eapply subst_env_valid_closed; eauto.

  clear.
  apply goedel_loeb.
  rewrite TT_and.
  apply positive_boxy.
  hnf; rewrite later_commute; rewrite box_refl_trans; auto.
  apply forallI; intro e1.
  apply forallI; intro e2.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H.
  destruct H0.
  destruct H0.
  simpl in H0; destruct H0.

  eapply expr_type_search_rule with (f:= fun x => App x e2).
  compute; auto.
  apply H2.
  apply H1.
  apply H.
  hnf; rewrite expr_type_extends; auto.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_App1; auto.

  intros.
  rewrite ty_lam_extends in H9.
  generalize H9; intros.
  destruct H9 as [e' [He [? ?]]].
  inv H9.
  eapply expr_type_search_rule with (f:= fun x => (App (Lam e') x)).
  auto.
  eauto.
  instantiate (1:=(with_val (exp_to_val (Lam e') H4) (ty_lam sigma tau))); auto.
  apply H6.
  hnf; rewrite with_val_extends; rewrite ty_lam_extends; auto.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_App2; auto.
  intros.
  change (Lam e') with (val_to_exp (exp_to_val _ H4)).
  change e with (val_to_exp (exp_to_val _ H9)).
  apply typ_beta with sigma; auto.

  intros.
  eapply H12; eauto.
  apply R_extends_refl.
  repeat split; simpl; auto.
  destruct H9; auto.
  destruct a0.
  change (Lam e') with (val_to_exp (exp_to_val _ H4)).
  apply forces2exprType; auto.
  rewrite ty_lam_extends; auto.

  intros.
  eapply H5; eauto.
  apply R_extends_refl.
  repeat split; simpl; auto.
  destruct H4; auto.
Qed.

Lemma T_Deref: forall G e tau,
  Typ G e (ty_ref tau) ->
  Typ G (Deref e) tau.
Proof.
  intros.
  destruct H.
  split.
  simpl; auto.
  repeat intro.
  spec H0 env a H1.

  rewrite subst_env_Deref.
  cut ( TT |-- %(ALL e:expr, !!(closed e) && expr_type e (ty_ref tau) --> expr_type (Deref e) tau)).
  intros.
  eapply H2.
  2: apply R_extends_refl.
  2: apply rt_refl.
  simpl; auto.
  split; auto.
  simpl; auto.
  eapply subst_env_valid_closed; eauto.

  clear.
  apply goedel_loeb.
  rewrite TT_and.
  apply positive_boxy.
  hnf.
  rewrite later_commute.
  rewrite box_refl_trans; auto.
  apply forallI; intro e.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H.
  destruct H0.
  simpl in H0.
  eapply expr_type_search_rule.
  unfold closed; simpl; auto.
  apply H1.
  instantiate (1:=TT); simpl; auto.
  apply H.
  apply TT_boxy.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_Deref1; auto.

  intros.
  rewrite ty_ref_extends in H7.
  assert (exists l, e0 = Loc l).
  hnf in H7.
  destruct (unsquash k).
  destruct H7 as [l [Hl ?]].
  exists l; inv Hl; auto.
  destruct H8 as [l Hl].
  subst e0.
  eapply expr_ty_deref_loc; auto.
  change (Loc l) with (val_to_exp (exp_to_val (Loc l) H2)).
  eapply forces2exprType.
  rewrite ty_ref_extends.
  auto.

  intros.
  eapply H3; eauto.
  apply R_extends_refl.
  split; auto.
Qed.

Lemma T_Update: forall G e1 tau e2 e3 sigma,
  Typ G e1 (ty_ref tau) ->
  Typ G e2 tau ->
  Typ G e3 sigma ->
  Typ G (Update e1 e2 e3) sigma.
Proof.
  unfold Typ; simpl; intuition.
  repeat intro.
  spec H3 env a H1.
  spec H4 env a H1.
  spec H5 env a H1.

  rewrite subst_env_Update.
  cut ( TT |-- %(ALL e1:expr, ALL e2:expr, ALL e3:expr,
                 !!(closed e1 /\ closed e2 /\ closed e3) &&
                 expr_type e1 (ty_ref tau) &&
                 expr_type e2 tau &&
                 expr_type e3 sigma -->
                 expr_type (Update e1 e2 e3) sigma)).
  intros.
  eapply H6; eauto.
  apply R_extends_refl.
  simpl; auto.
  split; auto.
  split; auto.
  split; auto.
  repeat split; eapply subst_env_valid_closed; eauto.

  clear.
  apply goedel_loeb.
  rewrite TT_and.
  apply positive_boxy.
  hnf; rewrite later_commute; rewrite box_refl_trans; auto.
  apply forallI; intro e1.
  apply forallI; intro e2.
  apply forallI; intro e3.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H.
  destruct H0.
  destruct H0.
  destruct H0.
  simpl in H0; destruct H0.
  destruct H4.
  eapply expr_type_search_rule with (f:= fun x => Update x e2 e3).
  compute; auto.
  apply H3.
  instantiate (1 := expr_type e2 tau && expr_type e3 sigma).
  split; auto.
  apply H.
  hnf; rewrite box_and; do 2  rewrite expr_type_extends; auto.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_Upd1; auto.

  clear; intros.
  destruct H2.
  rewrite ty_ref_extends in H4.
  assert (exists l, e = Loc l).
  hnf in H4.
  destruct (unsquash k); destruct H4 as [l [Hl ?]]; inv Hl; eauto.
  destruct H6 as [l Hl]; subst e.
  eapply expr_type_search_rule with (f := fun x => Update (Loc l) x e3).
  compute; auto.
  apply H2.
  instantiate (1:= with_val (exp_to_val _ H) (ty_ref tau) && expr_type e3 sigma).
  split; auto.
  apply H1.
  hnf; rewrite box_and.
  rewrite expr_type_extends; auto.
  rewrite with_val_extends.
  rewrite ty_ref_extends; auto.
  hnf; rewrite box_refl_trans; auto.
  intros; apply st_Upd2; auto.

  clear; intros.
  change e with (val_to_exp (exp_to_val e H0)).
  destruct H3.
  eapply expr_type_upd_Update; eauto.
  unfold v_Loc.
  replace (isvLoc l) with H by apply proof_irr; auto.

  clear; intros.
  destruct H2.
  eapply H1; eauto.
  apply R_extends_refl.
  simpl; repeat (split; auto).
  destruct a.
  change (Loc l) with (val_to_exp (exp_to_val _ H)).
  apply forces2exprType.
  rewrite ty_ref_extends; auto.

  clear; intros.
  destruct H1.
  eapply H0; eauto.
  apply R_extends_refl.
  simpl; repeat (split; auto).
Qed.


(* Bounded Universal Quantification *)

Definition AllBnd (T:pred world) (X:pred world -> pred world)
  := ALL tau:pred world, !!(TT |-- tau >=> T) --> X tau.

Lemma sub_AllBnd : forall T1 T2 (X1 X2:pred world -> pred world),
  TT |-- T2 >=> T1 ->
  (forall x, TT |-- x >=> T2 -> TT |-- X1 x >=> X2 x) ->
  TT |-- AllBnd T1 X1 >=> AllBnd T2 X2.
Proof.
  intros.
  unfold AllBnd.
  apply subp_allp; intro tau.
  spec H0 tau.
  repeat intro.
  eapply H0; eauto.
  eapply H4; eauto.
  repeat intro.
  eapply H; eauto.
  eapply H6; eauto.
Qed.

Lemma AllBnd_ALL : forall (X:pred world -> pred world),
  allp X = AllBnd TT X.
Proof.
  intros.
  apply pred_ext; simpl; repeat intro; intuition.
  eapply pred_nec_hereditary; eauto.
  apply H; auto.
  simpl; split; auto.
Qed.

Lemma T_UnivBoundedI : forall G e T (X:pred world -> pred world),
  openValue e ->
  (forall tau, TT |-- tau >=> T -> Typ G e (X tau)) ->
  Typ G e (AllBnd T X).
Proof.
  intros.
  assert (Hcl:closed' (length G) e).
  destruct (H0 FF).
  apply subp_bot.
  auto.
  split; auto.
  repeat intro.

  rewrite expr_type_eqn.
  repeat intro.
  split.
  repeat intro.
  simpl in H6.
  assert (stopped b (subst_env env e)).
  apply values_stopped; auto.
  eapply openValue_valid_value; eauto.
  elim H8; eauto.

  repeat intro.
  simpl in H6.
  assert (Hv : isValue (subst_env env e)).
  eapply openValue_valid_value; eauto.
  exists Hv.
  repeat intro.
  spec H0 b0.
  simpl in H9.
  destruct H0; auto.
  spec H10 env a H1.
  rewrite expr_type_eqn in H10.
  spec H10 a' H2.
  spec H10 b a'0 H3 H4.
  destruct H10.
  spec H11 a'1 H5.
  detach H11.
  destruct H11.
  apply pred_nec_hereditary with a'2; auto.
  simpl in H11.
  apply H11.
  replace x with Hv by apply proof_irr.
  auto.
  simpl; auto.
Qed.

Lemma T_UnivBoundedE : forall G e T (X:pred world -> pred world) tau,
  TT |-- tau >=> T ->
  Typ G e (AllBnd T X) ->
  Typ G e (X tau).
Proof.
  do 6 intro.
  apply T_sub.
  unfold AllBnd.
  repeat intro.
  apply H3; auto.
Qed.

(* Unbounded allps *)
Lemma T_UnivI : forall G e (X:pred world -> pred world),
  openValue e ->
  (forall tau, Typ G e (X tau)) ->
  Typ G e (allp X).
Proof.
  intros; rewrite AllBnd_ALL.
  apply T_UnivBoundedI; auto.
Qed.

Lemma T_UnivE : forall G e (X:pred world -> pred world) tau,
  Typ G e (allp X) ->
  Typ G e (X tau).
Proof.
  do 4 intro; apply T_sub; apply subp_allp_spec.
Qed.


Definition ty_ex (F:pred world -> pred world) : pred world :=
  EX tau:pred world, !!(boxy extendM tau) && F tau.

Lemma T_ExtI : forall G e (X:pred world -> pred world) tau
  (Hext : forall tau, boxy extendM tau -> boxy extendM (X tau)),
  boxy extendM tau ->
  Typ G e (X tau) ->
  Typ G e (ty_ex X).
Proof.
  intros.
  revert H0; apply T_sub.
  unfold ty_ex.
  repeat intro; auto.
  exists tau; split; auto.
Qed.

Lemma T_ExtE : forall G e f (X:pred world -> pred world) sigma
  (Hext : forall tau, boxy extendM tau -> boxy extendM (X tau)),
  Typ G e (ty_ex X) ->
  (forall tau, Typ (X tau::G) f sigma) ->
  Typ G (App (Lam f) e) sigma.
Proof.
  intros.
  generalize (H0 FF).
  intros.
  destruct H1 as [H1 _].
  simpl in H1.
  destruct H.
  split; auto.
  simpl.
  replace (length G + 1) with (S (length G)); auto.
  omega.
  repeat intro.
  spec H2 env a H3.
  rewrite subst_env_App.
  replace (subst_env env (Lam f)) with (Lam (subst_env' 1 env f)).
  cut (TT |-- %(ALL e:expr,
        (!!(closed e /\ closed' 1 (subst_env' 1 env f)) && (etype_valid env G)) && expr_type e (ty_ex X) -->
        expr_type (App (Lam (subst_env' 1 env f)) e) sigma)).
  intros.
  eapply H4; eauto.
  apply R_extends_refl.
  simpl; auto.
  simpl; repeat (split; auto).
  eapply subst_env_valid_closed; eauto.
  apply (closed_subst_env env f 1 0).
  replace (length env + 1) with (S (length G)); auto.
  clear -H3.
  revert a env H3; induction G; intros; destruct env; simpl in H3; try contradiction;
    simpl; auto.
  destruct H3.
  f_equal; eapply IHG; eauto.

  clear e H H1 H2.
  apply goedel_loeb.
  rewrite TT_and.
  apply positive_boxy.
  hnf; rewrite later_commute; rewrite box_refl_trans; auto.
  apply forallI; intro e.
  rewrite <- imp_andp_adjoint.
  repeat intro.
  destruct H.
  destruct H1.
  destruct H1.
  simpl in H1; destruct H1.

  eapply expr_type_search_rule with (f:=fun x => (App (Lam (subst_env' 1 env f)) x)).
  hnf; auto.
  apply H2.
  apply H4.
  apply H.
  hnf; apply etype_valid_extends.
  hnf; rewrite box_refl_trans; eauto.
  intros; apply st_App2; auto.

  clear -Hext H0; intros.
  spec H5 (k,exp_to_val e H) (R_extends_refl (k,exp_to_val e H)).
  destruct H5 as [tau H5].
  destruct H5.
  simpl in H5.
  spec H0 tau.
  destruct H0.
  rewrite <- Hext in H6; auto.
  spec H7 (exp_to_val e H :: env) (k,v).
  spec H7.
  split; auto.
  rewrite expr_type_eqn.
  repeat intro.
  split; repeat intro.
  simpl in H12.
  inv H12.
  inv H15.
  assert (stopped b e).
  apply values_stopped; auto.
  elim H12; eauto.
  exists a'2; split; auto.
  simpl; apply R_extends_refl.
  split.
  apply pred_nec_hereditary with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  unfold subst_env in H7.
  simpl in H7.
  replace H14 with H by apply proof_irr; auto.
  rewrite <- expr_type_extends in H7.
  spec H7 a' H8.
  apply pred_nec_hereditary with a'; auto.
  apply rt_trans with a'0; auto.
  apply rt_trans with a'1; auto.
  apply Rt_Rft; auto.
  simpl in H12.
  elim H12.
  exists b; exists (subst 0 (exp_to_val e H) (subst_env' 1 env f)).
  apply st_App3.

  clear; intros.
  eapply H0; eauto.
  apply R_extends_refl.
  simpl; repeat (split; auto).
  destruct H; auto.
  destruct H; auto.

  unfold subst_env.
  clear.
  generalize 0; revert f.
  induction env; simpl; intuition.
  rewrite <- IHenv.
  simpl.
  replace (n+1) with (S n) by omega; auto.
Qed.
