(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_type_safety.v: typing imp safety *)

Require Import msl.msl_standard.

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.
Require Import lam_ref_mach_lemmas.
Require Import lam_ref_type_defs.

Lemma expr_type_safen: forall k v e tau,
  expr_type e tau (k,v) ->
    forall m, mtype_valid m (k,v) ->
      safen (level k) (m,e).
Proof.
  repeat intro.
  remember (level k) as n.
  revert e k v n' m H H0 Heqn st' H1 H2.
  pattern n; apply (well_founded_induction lt_wf); clear n.
  intros n Hind; intros.
  destruct st'.
  rewrite expr_type_eqn in H.
  spec H (k,v).
  detach H.
  spec H m.
  spec H (k,v) (rt_refl _ age (k,v)).
  spec H H0.
  destruct H.

  inv H2.
  destruct (stopped_dec e0 m0).
  destruct s.
  left; hnf; eauto.
  spec H3 (k,v) (rt_refl _ age (k,v)).
  destruct H3.
  simpl; auto.
  auto.

  destruct st'.
  spec H m1 e1.
  spec H (k,v) (rt_refl _ age (k,v)).
  detach H.
  case_eq (unsquash k); intros.
  rewrite knot_level in H1, Hind.
  rewrite H2 in H1, Hind.
  simpl in H1.
  destruct n.
  inv H1.
  simpl fst in *.
  spec H (squash (n,f),v).
  detach H.
  destruct H as [[k' v'] [? ?]].
  destruct H; subst v'.
  destruct H6.
  eapply Hind.
  instantiate (1:=n).
  omega.
  apply H7.
  apply H6.
  unfold knot_extends in H.
  rewrite unsquash_squash in H.
  case_eq (unsquash k'); intros; rewrite H8 in H.
  destruct H; subst n1.
  rewrite knot_level; auto.
  rewrite H8; simpl; auto.
  2: apply H5.
  auto with arith.
  simpl.
  apply t_step.
  hnf; simpl.
  rewrite knot_age1.
  rewrite H2; auto.
  simpl; auto.

  apply R_extends_refl.
Qed.

Theorem typing_implies_safety: forall e tau,
  Typ nil e tau ->
  safe_prog e.
Proof.
  unfold safe_prog, safe.
  intros.
  rewrite stepstar_stepn in H0.
  destruct H0 as [n H0].
  set (psi := fun l => if le_lt_dec (fst m) l then None else Some TT).
  set (mtype := squash (S n,psi)).
  eapply expr_type_safen.
  destruct H.
  apply (H1 nil (mtype,v_Nat 0) I).
  subst mtype.
  hnf.
  rewrite unsquash_squash.
  cbv beta zeta.
  simpl.
  intros.
  subst psi.
  simpl.
  destruct (le_lt_dec (fst m) a); simpl; auto.
  eauto.
  split; auto.
  intros.
  unfold fidentity_fmap.
  red. rewrite approx_spec.
  hnf; split; auto.
  apply lt_le_trans with (level (fst a')).
  apply laterR_level in H2. auto.
  destruct a'; simpl in H1.
  destruct H1; subst.
  hnf in H1.
  rewrite unsquash_squash in H1.
  simpl; rewrite knot_level.
  case_eq (unsquash m0); intros.
  rewrite H3 in H1.
  destruct H1; subst.
  simpl; eauto.
  hnf. auto.
  instantiate (1:=n).
  subst mtype.
  rewrite knot_level.
  rewrite unsquash_squash; auto.
  auto.
Qed.
