(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_type_defs.v: the definition of the type system; this is the main event. *)

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.
Require Import msl.msl_standard.

Require Export lam_ref_type_prelim.

Open Scope pred.

(* From introduction; this is the judgment psi |- v : tau *)
Definition forces (psi : mtype) (v : value) (tau : pred world) :=
  tau (psi, v).

(* Section 4.1, equation 17 *)
Program Definition ty_nat : pred world :=
  fun w => match w with (k, v) =>
    exists n, v = v_Nat n
  end.
Next Obligation.
  destruct a; destruct a'.
  replace v0 with v; auto.
  assert (necR (m,v) (m0,v0)).
  apply rt_step; auto.
  rewrite value_knot_necR in H1.
  intuition.
Qed.

Lemma ty_nat_extends :
  boxy extendM ty_nat.
Proof.
  apply boxy_i.
  apply R_extends_refl.
  simpl; intros.
  destruct w; destruct w'; destruct H; subst.
  auto.
Qed.

Program Definition type_at (l:addr) (tau:pred world) : pred world :=
  fun w:world =>
    let (n,psi) := unsquash (fst w) in
      match psi l with
        | None => False
        | Some p => approx_eq n p tau
      end.
Next Obligation.
  unfold age, age1 in H.
  destruct a; destruct a'.
  simpl in *.
  rewrite knot_age1 in H.
  case_eq (unsquash m); intros; rewrite H1 in H, H0.
  destruct n; try discriminate.
  inv H.
  rewrite unsquash_squash.
  simpl.
  case_eq (f l); simpl; intros; rewrite H in H0.
  unfold approx_eq in *.
  unfold fidentity_fmap.
  change (approx n (approx n p)) with
    ((approx n oo approx n) p).
  rewrite <- (approx_approx1 0).
  rewrite (approx_approx1 1).
  unfold compose; simpl.
  rewrite H0; auto.
  auto.
Qed.

Lemma type_at_extends : forall l tau,
  %(type_at l tau) = type_at l tau.
Proof.
  intros; apply boxy_i.
  apply R_extends_refl.
  intros; simpl in *.
  destruct w; destruct w'.
  destruct H; subst; simpl in *.
  case_eq (unsquash m); intros; rewrite H1 in H0.
  case_eq (unsquash m0); intros.
  hnf in H.
  rewrite H1 in H; rewrite H2 in H.
  destruct H; subst.
  destruct (H3 l).
  rewrite H in H0; elim H0.
  rewrite H.
  auto.
Qed.

Program Definition just (v:value) : pred world :=
  fun w => snd w = v.
Next Obligation.
  destruct a; destruct a'; simpl in *.
  hnf in H; simpl in H.
  rewrite knot_age1 in H.
  case_eq (unsquash m); intros; rewrite H1 in H.
  destruct n; inv H; auto.
Qed.

Program Definition with_val (v:value) (p:pred world) : pred world :=
  fun w => p (fst w,v).
Next Obligation.
  apply pred_hereditary with (fst a,v).
  unfold age, age1 in *; simpl in *.
  rewrite knot_age1 in *.
  destruct a; destruct a'; simpl in *.
  case_eq (unsquash m); intros; rewrite H1 in H; auto.
  destruct n; inv H; auto.
  auto.
Qed.

Definition ty_ref (tau: pred world) : pred world :=
  EX a:addr, just (v_Loc a) && type_at a tau.

(* Section 5.1, equation 28 *)
Program Definition mtype_valid (m : mem) : pred world :=
  fun w =>
  match w with (k, v) =>
   let (n,phi) := unsquash k in
    forall (a : addr),
      match phi a with
      | None => fst m <= a
      | Some tau => fst m > a /\ forces k (deref m a) (%|>tau)
      end
  end.
Next Obligation.
  unfold age, age1 in H.
  simpl in H.
  rewrite knot_age1 in H.
  destruct a; destruct a'.
  simpl in *.
  case_eq (unsquash m0); intros; rewrite H1 in H.
  destruct n; try discriminate.
  inv H.
  rewrite H1 in H0.
  rewrite unsquash_squash; simpl; intros.
  spec H0 a.
  case_eq (f a); simpl; intros.
  rewrite H in H0.
  intuition.
  unfold fidentity_fmap. red.
  rewrite approx_spec. split; auto.
  apply lt_le_trans with (level (fst a')).
  apply laterR_level in H4. auto.
  destruct a'. simpl.
  hnf in H0.
  destruct H0.  hnf in H0.
  rewrite unsquash_squash in H0.
  simpl; rewrite knot_level.
  case_eq (unsquash m1); intros; rewrite H6 in H0.
  destruct H0; subst.
  simpl; auto.
  eapply pred_nec_hereditary.
  apply Rt_Rft; auto.  apply H4.
  assert ((%|> p) (m0,deref m a)); auto.
  rewrite later_commute in H5.
  eapply H5.
  hnf; apply t_step.
  unfold age, age1; simpl.
  rewrite knot_age1.
  rewrite H1; auto.
  auto.
  rewrite H in H0. auto.
Qed.

Definition expr_typeF (tau:pred world) (F: expr -> pred world) (e : expr) : pred world :=
  %ALL m:mem, mtype_valid m -->
    (ALL m':mem, ALL e':expr, !!(step (m,e) (m',e')) -->
      |>(predicates_hered.diamond contractsM (mtype_valid m' && F e'))) &&
    (!!(stopped m e) --> EX H:isValue e,
         with_val (exp_to_val e H) (%tau)).

Lemma sub_with_val : forall G P P' e,
  G |-- P >=> P' ->
  G |-- with_val e P >=> with_val e P'.
Proof.
  intros.
  apply derives_trans with (P >=> P'); auto.
  clear; repeat intro.
  rewrite <- fash_fash in H.
  spec H (level a').
  spec H.
  red. apply le_trans with (level y); auto.
  apply necR_level in H1. auto.
  destruct a'. simpl in *.
  eapply H; eauto.
  simpl; auto.
Qed.

Lemma extend_level : forall w1 w2,
  R_extends w1 w2 -> level w1 = level w2.
Proof.
  intros. hnf in H.
  destruct w1. destruct w2.
  destruct H. simpl.
  hnf in H.
  do 2 rewrite knot_level.
  destruct (unsquash m). destruct (unsquash m0).
  simpl; intuition.
Qed.

Lemma sub_extend :
  forall G P Q,
    G |-- P >=> Q  ->
    G |-- %P >=> %Q.
Proof.
  intros.
  hnf; intros.
  spec H a H0.
  repeat intro.
  spec H a'0.
  eapply H; eauto.
  red. apply le_trans with (level y); auto.
  apply le_trans with (level a'); auto.
  2: apply necR_level in H2; auto.
  rewrite (extend_level _ _ H4).
  auto.
Qed.

Lemma sub_contract :
  forall G P Q,
    G |-- P >=> Q ->
    G |-- predicates_hered.diamond contractsM P >=>
          predicates_hered.diamond contractsM Q.
Proof.
  intros.
  repeat intro.
  destruct H3 as [w' [??]].
  exists w'; split; auto.
  spec H a H0.
  spec H w'.
  eapply H; eauto.
  red.
  apply le_trans with (level y); auto.
  apply le_trans with (level a'); auto.
  2: apply necR_level in H2; auto.
  simpl in H3.
  rewrite (extend_level _ _ H3).
  auto.
Qed.

Lemma expr_type_sub1 :
  forall tau P Q,
    ALL e:expr, |>(P e >=> Q e)
      |-- ALL e:expr, expr_typeF tau P e >=> expr_typeF tau Q e.
Proof.
  intros.
  intros w H e.
  revert w H.
  unfold expr_typeF.
  apply sub_extend.
  apply subp_allp. intro m.
  apply subp_imp.
  apply subp_refl.
  apply subp_andp.
  apply subp_allp. intro m'.
  apply subp_allp. intro e'.
  apply subp_imp.
  apply subp_refl.
  rewrite <- box_all.
  rewrite <- subp_later.
  apply box_positive.
  apply sub_contract.
  apply subp_andp.
  apply subp_refl.
  hnf; intuition.
  apply subp_refl.
Qed.

Lemma expr_type_cont : forall tau, HOcontractive (expr_typeF tau).
Proof.
  intros.
  apply prove_HOcontractive1.
  apply expr_type_sub1.
Qed.

Definition expr_type e tau := HORec (expr_typeF tau) e.

Lemma expr_type_eqn : forall tau e,
  expr_type e tau =
  %ALL m:mem, mtype_valid m -->
    (ALL m':mem, ALL e':expr, !!(step (m,e) (m',e')) -->
      |>(predicates_hered.diamond contractsM (mtype_valid m' && expr_type e' tau)))
    &&
    (!!(stopped m e) --> EX H:isValue e, with_val (exp_to_val e H) (%tau)).
Proof.
  intros.
  change (expr_type e tau = expr_typeF tau (fun e => expr_type e tau) e).
  unfold expr_type at 1.
  rewrite HORec_fold_unfold.
  unfold expr_type.
  auto.
  apply expr_type_cont.
Qed.

Definition ty_lam (tau1 tau2 : pred world) : pred world :=
  EX e:expr, EX H:closed' 1 e, just (v_Lam e H) &&
  |>%(ALL v':value, with_val v' (%tau1) --> expr_type (subst 0 v' e) tau2).

Definition etype : Type := list (pred world).

Fixpoint etype_valid (e : env) (G : etype) : pred world :=
  match (e,G) with
   | (v :: es, tau :: Gs) => with_val v (%tau) && etype_valid es Gs
   | (nil, nil) => TT
   | _ => FF
  end.

(* Not in paper, but should add.  Taken from VMM. *)
Definition Typ (G : etype) (exp : expr) (tau : pred world) : Prop :=
  closed' (length G) exp  /\
  forall env, etype_valid env G |-- expr_type (subst_env env exp) tau.

Lemma expr_type_sub2 :
  forall X e P Q,
    P >=> Q |-- expr_typeF P X e >=> expr_typeF Q X e.
Proof.
  intros.
  unfold expr_typeF.
  apply sub_extend.
  apply subp_allp. intro m.
  apply subp_imp.
  apply subp_refl.
  apply subp_andp.
  apply subp_allp. intro m'.
  apply subp_allp. intro e'.
  apply subp_imp.
  apply subp_refl.
  apply subp_refl.
  apply subp_imp.
  apply subp_refl.
  apply subp_exp. intro H.
  apply sub_with_val.
  apply sub_extend.
  hnf; auto.
Qed.

Lemma subp_expr_type : forall G P P',
  G |-- P >=> P' ->
  G |-- ALL e:expr, expr_type e P >=> expr_type e P'.
Proof.
  intros.
  unfold expr_type.
  apply HORec_sub; auto.
  intros. apply expr_type_cont.
  apply expr_type_sub2.
  intros; apply expr_type_sub1.
Qed.

Lemma ty_lam_sub : forall G P P' Q Q',
  G |-- |>(P' >=> P) ->
  G |-- |>(Q >=> Q') ->
  G |-- (ty_lam P Q) >=> (ty_lam P' Q').
Proof.
  unfold ty_lam; intros.
  apply subp_exp; intro e.
  apply subp_exp; intro He.
  apply subp_andp.
  apply subp_refl.
  rewrite <- subp_later.
  apply derives_trans with (|>( (P' >=> P) && (Q >=> Q'))).
  rewrite box_and.
  do 2 intro; split; auto.
  apply box_positive.
  apply sub_extend.
  apply subp_allp; intro v'.
  apply subp_imp.
  apply sub_with_val.
  apply sub_extend.
  intros a H1; destruct H1; auto.
  intros a H1; destruct H1; auto.
  eapply subp_expr_type; eauto.
Qed.

Lemma subp_type_at : forall G P Q l,
  G |-- |>(P <=> Q) ->
  G |-- type_at l P >=> type_at l Q.
Proof.
  intros.
  apply derives_trans with (|>(P <=> Q)); auto.
  clear; repeat intro; destruct a'.
  simpl in H2; simpl.
  case_eq (unsquash m); intros; rewrite H3 in H2.
  generalize (refl_equal (f l)).
  case_eq (f l); intros.
  2: rewrite H4 in H2; auto.
  rewrite H4 in H2.
  unfold approx_eq in *.
  rewrite H2.
  apply approx_eq_sub.
  hnf; intros.
  spec H (level a').
  apply H.
  simpl.
  rewrite later_nat.
  apply lt_le_trans with n.
  simpl in H5.
  apply later_nat in H5. auto.
  replace n with (level m).
  apply le_trans with (level y); auto.
  apply necR_level in H1.
  auto.
  rewrite knot_level.
  rewrite H3. auto.
Qed.

Lemma ty_ref_sub : forall G P Q,
  G |-- |>(P <=> Q) ->
  G |-- ty_ref P >=> ty_ref Q.
Proof.
  intros.
  unfold ty_ref.
  apply subp_exp; intro l.
  apply subp_andp.
  apply subp_refl.
  apply subp_type_at.
  auto.
Qed.

Lemma extend_nonexpansive : forall F,
  nonexpansive F ->
  nonexpansive (fun X => %(F X)).
Proof.
  intros. hnf; simpl.
  intros.
  spec H P Q.
  apply subp_eqp.
  apply sub_extend.
  apply eqp_subp.
  auto.
  apply sub_extend.
  apply eqp_subp2.
  auto.
Qed.

Lemma with_val_nonexpansive : forall F v,
  nonexpansive F ->
  nonexpansive (fun X => with_val v (F X)).
Proof.
  intros.
  hnf; intros; cbv beta.
  apply subp_eqp.
  apply sub_with_val.
  apply eqp_subp.
  apply H.
  apply sub_with_val.
  apply eqp_subp2.
  apply H.
Qed.

Lemma expr_type_nonexpansive : forall F e,
  nonexpansive F ->
  nonexpansive (fun X => (expr_type e (F X))).
Proof.
  intros; hnf; intros; cbv beta.
  apply subp_eqp.
  do 2 intro; eapply subp_expr_type; eauto.
  eapply eqp_subp; eauto.
  do 2 intro; eapply subp_expr_type; eauto.
  eapply eqp_subp2; eauto.
Qed.

Lemma ty_lam_contractive : forall F G,
  nonexpansive F ->
  nonexpansive G ->
  contractive (fun X => ty_lam (F X) (G X)).
Proof.
  intros; hnf; intros.
  apply subp_eqp.
  apply ty_lam_sub.
  apply box_positive.
  apply eqp_subp2; apply H.
  apply box_positive.
  apply eqp_subp; apply H0.
  apply ty_lam_sub.
  apply box_positive.
  apply eqp_subp; apply H.
  apply box_positive.
  apply eqp_subp2; apply H0.
Qed.

Lemma type_at_contractive : forall l F,
  nonexpansive F ->
  contractive (fun X => type_at l (F X)).
Proof.
  intros; hnf; intros.
  cbv beta.
  apply subp_eqp; apply subp_type_at; apply box_positive.
  apply H.
  apply subp_eqp; [ apply eqp_subp2 | apply eqp_subp ]; apply H.
Qed.

Lemma ty_ref_contractive : forall F,
  nonexpansive F ->
  contractive (fun X => ty_ref (F X)).
Proof.
  intros; unfold ty_ref.
  apply exists_contractive; intros.
  apply conj_contractive.
  repeat intro; split; repeat intro; eauto.
  apply type_at_contractive; auto.
Qed.

Lemma just_extends : forall v,
  %just v = just v.
Proof.
  intros.
  eapply boxy_i.
  apply R_extends_refl.
  intros.
  destruct w; destruct w'.
  destruct H; subst.
  auto.
Qed.

Lemma ty_ref_extends : forall tau,
  %(ty_ref tau) = ty_ref tau.
Proof.
  intros.
  unfold ty_ref.
  apply boxy_i.
  simpl; apply R_extends_refl.
  intros.
  revert w' H.
  apply (box_ex addr extendM).
  destruct H0 as [a [? ?]]; exists a.
  rewrite box_and; split.
  rewrite just_extends; auto.
  rewrite type_at_extends; auto.
Qed.

(*
Lemma fashionable_extends : forall P,
  %(box fashionM P) = box fashionM P.
Proof.
  intros; apply equiv_eq; repeat intro.
  spec H a (R_extends_refl a); auto.
  eapply H.
  simpl; apply fashionR_trans with a'; auto.
  apply extends_fashionable; auto.
Qed.
*)

Lemma with_val_extends : forall v P,
  %(with_val v P) = with_val v (%P).
Proof.
  intros; apply pred_ext; repeat intro.
  destruct a; destruct a'.
  simpl in H0; destruct H0; subst.
  spec H (m0,v0).
  apply H.
  split; auto.
  destruct a; destruct a'.
  simpl in H0; destruct H0; subst.
  simpl in *.
  apply H; split; auto.
Qed.

Lemma expr_type_extends : forall e tau,
  %expr_type e tau = expr_type e tau.
Proof.
  intros e tau.
  rewrite expr_type_eqn.
  rewrite box_refl_trans; auto.
Qed.

Lemma etype_valid_extends : forall G env,
  %etype_valid env G = etype_valid env G.
Proof.
  intros.
  apply boxy_i.
  simpl; apply R_extends_refl.
  revert env; induction G; destruct env; simpl; intuition.
  apply H1; auto.
  destruct w; destruct w'.
  destruct H; subst.
  destruct a'.
  destruct H0; subst.
  simpl; split; auto.
  apply knot_extends_trans with m0; auto.
  eapply IHG; eauto.
Qed.

Lemma ty_lam_extends : forall sigma tau,
  %ty_lam sigma tau = ty_lam sigma tau.
Proof.
  intros.
  apply boxy_i.
  simpl; apply R_extends_refl.
  unfold ty_lam; intros.
  destruct H0 as [e [He [? ?]]].
  exists e; exists He.
  split.
  destruct w; destruct w'; destruct H; subst.
  auto.
  rewrite <- (box_refl_trans extendM) in H1; auto.
  rewrite <- later_commute in H1.
  apply H1; auto.
Qed.
