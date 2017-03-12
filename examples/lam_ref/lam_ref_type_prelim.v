(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_type_defs.v: the definition of the type system; this is the main event. *)

Require Import msl.msl_standard.

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.


Module TFP <: TY_FUNCTOR_PROP.
(* From section 4.1 *)
  Definition F : Type -> Type := fun K => addr -> option K.

  Definition f_F := f_fun addr (f_option f_identity).

  Definition other : Type := value.
End TFP.

Export TFP.

Module K := KnotHered(TFP). (* Wow, that was easy... *)
Module KL := KnotHered_Lemmas(K).

Export K.
Export KL.

(* Let's define our typing system on values *)

Definition mtype : Type := knot.
Definition world : Type := (mtype * value)%type.

Definition world_ag : ageable world :=
  ag_prod mtype value ag_knot.
Existing Instance world_ag.

Definition knot_extends (k1 k2 : knot) : Prop :=
  match (unsquash k1, unsquash k2) with
    ((n, psi), (n', psi')) => n = n' /\ forall a, (psi a = None) \/ (psi' a = psi a)
  end.

Definition R_extends (w1 w2 : world) : Prop :=
  match (w1, w2) with
    ((k1, v1), (k2, v2)) => knot_extends k1 k2 /\ v1 = v2
  end.

Lemma knot_extends_refl : forall k, knot_extends k k.
Proof.
  intros; hnf.
  destruct (unsquash k); intuition.
Qed.

Lemma knot_extends_trans : forall k1 k2 k3,
  knot_extends k1 k2 ->
  knot_extends k2 k3 ->
  knot_extends k1 k3.
Proof.
  unfold knot_extends; intuition.
  destruct (unsquash k1); destruct (unsquash k2); destruct (unsquash k3).
  intuition; subst.
  destruct (H2 a); destruct (H3 a); subst; auto.
  rewrite <- H; auto.
  rewrite H0; rewrite H; auto.
Qed.

Lemma knot_extends_age_commute1 : forall x y z,
  age x y /\ knot_extends y z -> exists y',
  knot_extends x y' /\ age y' z.
Proof.
  intros.
  case_eq (unsquash x); intros n1 fx Hx.
  case_eq (unsquash y); intros n2 fy Hy.
  case_eq (unsquash z); intros n3 fz Hz.
  destruct H.
  unfold age in H; rewrite knot_age1 in H.
  rewrite Hx in H.
  destruct n1; try discriminate.
  inv H.
  rewrite unsquash_squash in Hy.
  inv Hy.
  hnf in H0.
  rewrite unsquash_squash in H0.
  rewrite Hz in H0.
  destruct H0; subst n3.
  set (f := fun a =>
             match fx a with
             | Some x => Some x
             | None => fz a
             end).
  exists (squash (S n2, f)).
  split.
  hnf.
  case_eq (unsquash x); intros.
  rewrite unsquash_squash.
  rewrite Hx in H.
  inversion H; subst n f0.
  split; auto.
  intros.
  destruct (H0 a).
  left.
  simpl in H1.
  destruct (fx a); try discriminate; auto.
  simpl in *. unfold f.
  case_eq (fx a); intros; auto.
  right.
  generalize H2.
  rewrite (unsquash_approx Hx).
  simpl.
  rewrite H2; auto.
  unfold age; rewrite knot_age1.
  rewrite unsquash_squash.
  f_equal.
  apply unsquash_inj.
  rewrite unsquash_squash.
  rewrite Hz.
  f_equal.
  rewrite fmap_app.
  change (S n2) with (1+n2).
  rewrite <- (approx_approx1 1 n2).
  extensionality q. unfold f; simpl.
  destruct (H0 q). simpl in *.
  case_eq (fx q); intros; rewrite H1 in H; try discriminate.
  case_eq (fz q); intros; auto.
  generalize H2.
  rewrite (unsquash_approx Hz).
  simpl.
  rewrite H2; auto.
  simpl in *.
  case_eq (fx q); intros; rewrite H1 in H; try discriminate; auto.
  rewrite H; auto.
Qed.

Lemma knot_extends_age_commute2 : forall x y z,
  knot_extends x y /\ age y z -> exists y',
  age x y' /\ knot_extends y' z.
Proof.
  intros.
  case_eq (unsquash x); intros n1 fx Hx.
  case_eq (unsquash y); intros n2 fy Hy.
  case_eq (unsquash z); intros n3 fz Hz.
  destruct H.
  unfold age in H0; rewrite knot_age1 in H0.
  rewrite Hy in H0.
  destruct n2; try discriminate.
  inv H0.
  rewrite unsquash_squash in Hz.
  inversion Hz.
  subst n3 fz.
  hnf in H.
  rewrite Hx in H.
  rewrite Hy in H.
  destruct H; subst n1.
  clear Hz.
  exists (squash (n2,fx)).
  split.
  unfold age; rewrite knot_age1.
  rewrite Hx; auto.
  hnf; repeat rewrite unsquash_squash; split; auto.
  intros.
  destruct (H0 a).
  left.
  simpl. rewrite H; auto.
  right.
  simpl. rewrite H; auto.
Qed.

Lemma R_extends_valid_rel :
  valid_rel R_extends.
Proof.
  split; hnf; intros.
  destruct x; destruct y; destruct z; simpl in *.
  unfold age, age1 in H; simpl in H.
  hnf in H0.
  destruct H0; subst v1.
  case_eq (age1 m0); intros.
  rewrite H1 in H; inv H.
  destruct (knot_extends_age_commute2 m1 m0 m); auto.
  exists (x,v); hnf; intuition.
  unfold age1; simpl.
  hnf in H2.
  unfold mtype in *.
  rewrite H2; auto.
  rewrite H1 in H; discriminate.

  destruct x; destruct y; destruct z; simpl in *.
  unfold age in H0; simpl in H0.
  hnf in H.
  destruct H; subst v0.
  case_eq (age1 m1); intros; rewrite H1 in H0; try discriminate.
  inv H0.
  destruct (knot_extends_age_commute1 m1 m0 m); auto.
  exists (x,v); simpl.
  unfold age, age1; simpl.
  destruct H0.
  hnf in H2.
  unfold mtype in *.
  rewrite H2; auto.
  hnf; intuition.
Qed.

Lemma R_extends_refl : reflexive _ R_extends.
Proof.
  hnf; intros.
  hnf; destruct x; split; auto.
  apply knot_extends_refl.
Qed.

Lemma R_extends_trans : transitive _ R_extends.
Proof.
  hnf; intros.
  destruct x; destruct y; destruct z.
  destruct H; destruct H0.
  subst.
  split; auto.
  eapply knot_extends_trans; eauto.
Qed.

(*
Lemma extends_fashionable : forall x y,
  R_extends x y -> fashionR x y.
Proof.
  intros.
  destruct x; destruct y; destruct H.
  subst v0.
  hnf in H.
  hnf; simpl.
  repeat rewrite knot_level.
  destruct (unsquash m); destruct (unsquash m0).
  simpl; intuition.
Qed.
*)


Definition knot_contracts := transp _ knot_extends.

Lemma knot_contracts_age_commute1 : forall x y z,
  age x y /\ knot_contracts y z -> exists y',
  knot_contracts x y' /\ age y' z.
Proof.
  unfold knot_contracts, transp; intros.
  case_eq (unsquash x); intros n1 fx Hx.
  case_eq (unsquash y); intros n2 fy Hy.
  case_eq (unsquash z); intros n3 fz Hz.
  destruct H.
  hnf in H0.
  rewrite Hz in H0.
  rewrite Hy in H0.
  destruct H0; subst.
  unfold age in H; rewrite knot_age1 in H.
  rewrite Hx in H.
  destruct n1; try discriminate.
  inv H.
  rewrite unsquash_squash in Hy; inv Hy.
  set (f := fun a =>
        match fz a with
        | Some _ => fx a
        | None => None
        end).
  exists (squash (S n2,f)).

  split.
  hnf.
  rewrite unsquash_squash.
  rewrite Hx.
  split; auto.
  intros. unfold f; simpl.
  destruct (H1 a).
  rewrite H; auto.
  right. simpl.
  rewrite <- H.
  simpl.
  case_eq (fx a); simpl; auto.
  intros.
  rewrite <- H0.
  rewrite (unsquash_approx Hx).
  simpl.
  rewrite H0. simpl. auto.

  unfold age; rewrite knot_age1.
  rewrite unsquash_squash.
  apply f_equal.
  apply unsquash_inj.
  rewrite unsquash_squash.
  rewrite Hz.
  apply f_equal.
  rewrite fmap_app.
  rewrite <- (approx_approx1 1).
  extensionality a; simpl.
  unfold f. simpl.
  destruct (H1 a).
  rewrite H; auto.
  rewrite <- H. simpl.
  case_eq (fx a); auto.
Qed.

Lemma knot_contracts_age_commute2 : forall x y z,
  knot_contracts x y /\ age y z -> exists y',
  age x y' /\ knot_contracts y' z.
Proof.
  unfold knot_contracts, transp; intros.
  case_eq (unsquash x); intros n1 fx Hx.
  case_eq (unsquash y); intros n2 fy Hy.
  case_eq (unsquash z); intros n3 fz Hz.
  destruct H.
  unfold age in H0; rewrite knot_age1 in H0.
  rewrite Hy in H0.
  destruct n2; try discriminate.
  inv H0.
  hnf in H.
  rewrite Hy in H.
  rewrite Hx in H.
  destruct H; subst n1.
  rewrite unsquash_squash in Hz; inv Hz.
  exists (squash (n3,fx)).
  split.
  unfold age; rewrite knot_age1.
  rewrite Hx; auto.
  hnf; repeat rewrite unsquash_squash.
  split; auto.
  intros. simpl.
  destruct (H0 a).
  rewrite H; auto.
  rewrite <- H.
  auto.
Qed.

Definition R_contracts := transp _ R_extends.

Lemma R_contracts_valid_rel :
  valid_rel R_contracts.
Proof.
  unfold R_contracts, transp; split; hnf; simpl; intros.
  destruct x; destruct y; destruct z; simpl in *.
  destruct H0; subst.
  unfold age, age1 in H; simpl in H.
  destruct (knot_contracts_age_commute2 m1 m0 m).
  split; auto.
  hnf; unfold mtype in *.
  destruct (age1 m0); congruence.
  destruct H1.
  exists (x,v); auto.
  split; auto.
  unfold age, age1; simpl.
  destruct (age1 m0).
  inv H.
  hnf in H1.
  unfold mtype in *.
  rewrite H1.
  auto.
  discriminate.

  destruct x; destruct y; destruct z; simpl in *.
  unfold age, age1 in H0; simpl in H0.
  destruct H; subst v0.
  destruct (knot_contracts_age_commute1 m1 m0 m).
  split; auto.
  unfold age.
  unfold mtype in *.
  destruct (age1 m1); congruence.
  destruct H1.
  exists (x,v).
  hnf; simpl.
  unfold mtype in *; rewrite H2.
  auto.
  split; auto.
  destruct (age1 m1); congruence.
Qed.


Definition extendM : modality :=
  exist _ R_extends R_extends_valid_rel.
Definition contractsM : modality :=
  exist _ R_contracts R_contracts_valid_rel.

Notation "'%' e"  := (box extendM e)(at level 30, right associativity): pred.


Lemma value_knot_laterR : forall k k' v v',
  laterR (A:=world) (k,v) (k',v') <-> clos_trans _ age k k' /\ v = v'.
Proof.
  split; intros.
  remember (k,v) as x.
  remember (k',v') as y.
  revert k k' v v' Heqx Heqy.
  induction H; intros; subst; auto.
  unfold age, age1 in H; simpl in H.
  case_eq (age1 k); intros.
  rewrite H0 in H; inv H.
  split; auto.
  apply t_step; auto.
  rewrite H0 in H; discriminate.
  destruct y.
  destruct (IHclos_trans1 k m v v0); auto.
  subst.
  destruct (IHclos_trans2 m k' v0 v'); auto.
  subst.
  split; auto.
  apply t_trans with m; auto.
  destruct H.
  subst v'.
  induction H.
  apply t_step.
  hnf; simpl.
  hnf in H.
  rewrite H; auto.
  eapply t_trans; eauto.
Qed.

Lemma value_knot_necR : forall k k' v v',
  necR (A:=world) (k,v) (k',v') <-> clos_refl_trans _ age k k' /\ v = v'.
Proof.
  split; intros.
  remember (k,v) as x.
  remember (k',v') as y.
  revert k k' v v' Heqx Heqy.
  induction H; intros; subst; auto.
  unfold age, age1 in H; simpl in H.
  case_eq (age1 k); intros.
  rewrite H0 in H; inv H.
  split; auto.
  apply rt_step; auto.
  rewrite H0 in H; discriminate.
  inv Heqy.
  split; auto.
  destruct y.
  destruct (IHclos_refl_trans1 k m v v0); auto.
  subst.
  destruct (IHclos_refl_trans2 m k' v0 v'); auto.
  subst.
  split; auto.
  apply rt_trans with m; auto.
  destruct H.
  subst v'.
  induction H.
  apply rt_step.
  unfold age, age1; simpl.
  hnf in H.
  rewrite H; auto.
  apply rt_refl.
  eapply rt_trans; eauto.
Qed.

Open Scope pred.

(* Section 4.1, equation 19 *)
Definition approx_eq (n : nat) (tau1 tau2 : predicate) : Prop :=
  approx n tau1 = approx n tau2.

Lemma approx_eq_downward : forall n m p q,
  m <= n ->
  approx_eq n p q ->
  approx_eq m p q.
Proof.
  unfold approx_eq; intros.
  apply pred_ext'.
  extensionality ko.
  assert (approx n p ko <-> approx n q ko).
  rewrite H0. split; auto.
  unfold app_pred in *.
  repeat rewrite approx_spec in *.
  apply prop_ext.
  intuition. spec H1. omega. spec H1; auto.
  destruct H1; auto.
  spec H2. omega. spec H2. auto.
  destruct H2; auto.
Qed.

Lemma approx_eq_sub n P Q :
    ((|> (P <=> Q)) n -> approx_eq n P Q).
Proof.
  intros. hnf.
  apply pred_ext'.
  extensionality ko.
  unfold app_pred in *.
  apply prop_ext. split; intros.
  rewrite approx_spec in H0.
  rewrite approx_spec.
  destruct H0. split; auto.
  spec H (level ko). spec H.
  simpl. rewrite later_nat. auto.
  spec H ko. spec H. auto.
  destruct H.
  eapply H; eauto.
  unfold app_pred in *.
  rewrite approx_spec in H0.
  rewrite approx_spec.
  destruct H0. split; auto.
  spec H (level ko). spec H.
  simpl. rewrite later_nat. auto.
  spec H ko. spec H. auto.
  destruct H.
  eapply H2; eauto.
Qed.

Hint Resolve R_extends_refl R_extends_trans.
