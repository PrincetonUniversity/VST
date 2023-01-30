(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.predicates_hered.

Import Arith.

Local Open Scope pred.

Section Fash.

Context {A : Type} {AG : ageable A} {EO : Ext_ord A}.

Lemma valid_rel_fashion : valid_rel fashionR.
Proof.
  split; hnf; intros.
  unfold fashionR in *.
  hnf in H.
  case_eq (age1 z); intros.
  exists a.
  rewrite (af_level2 age_facts y x) in H0; auto.
  rewrite (af_level2 age_facts z a) in H0; auto.
  auto.
  rewrite (af_level1 age_facts) in H1; auto.
  rewrite H1 in H0.
  symmetry in H0.
  rewrite <- (af_level1 age_facts) in H0.
  rewrite H in H0; discriminate.

  split; hnf; intros.
  hnf in H.
  destruct (af_unage age_facts x). exists x0. apply H1.
  hnf.
  rewrite (af_level2 age_facts x0 x); auto.
  rewrite (af_level2 age_facts z y); auto.

(*  split; hnf; intros.*)
  eexists; [reflexivity|].
  apply ext_level in H0; hnf in *; lia.
(*  eexists; [|reflexivity].
  apply ext_level in H; hnf in *; lia.*)
Qed.

Definition fashionM : modality
  := exist _ fashionR valid_rel_fashion.

#[global] Existing Instance ag_nat.
#[global] Program Instance nat_ext : Ext_ord nat := { ext_order := eq }.
Next Obligation.
Proof.
  hnf; intros; subst; eauto.
Qed.
Next Obligation.
Proof.
  hnf; intros; subst; eauto.
Qed.
(*Next Obligation.
Proof.
  hnf; intros; subst; eauto.
Qed.*)

Program Definition fash (P: pred A): pred nat :=
      fun n => forall y, n >= level y -> P y.
Next Obligation.
split; repeat intro.
destruct P as [P HP].
simpl in *.
apply H0.
unfold age, age1, ag_nat,natAge1 in H.
destruct a; inv H.
lia.

subst; auto.
Qed.

Notation "'#' e" := (fash e) (at level 20, right associativity): pred.

Lemma fash_K : forall (P Q: pred A),
                 # (P --> Q) |-- # P --> # Q.
Proof.
intros.
intros n ?.
simpl in H.
simpl.
intros w ? ? ? ? ? HP; subst.
eapply H; eauto.
apply necR_level in H0; simpl in H0.
unfold natLevel in H0; lia.
Qed.

Lemma laterR_nat: forall (n n': nat), laterR n n' <-> (n > n')%nat.
Proof.
intros.
split; induction 1; simpl; intros.
unfold age, age1 in H; simpl in H; unfold natAge1 in H. destruct x; inv H.
auto.
apply Nat.lt_trans with y; auto.
constructor 1. unfold age, age1; simpl. auto.
constructor 2 with m; auto.
constructor 1. unfold age, age1; simpl. auto.
Qed.

Lemma fash_derives :
     forall (P Q: pred A), (P |-- Q)  ->  # P |-- # Q.
Proof.
intros.
intros w ?.
intro; intros.
apply H.
eapply H0; auto.
Qed.

Lemma fash_and : forall (P Q:pred A),
  # (P && Q) = # P && # Q.
Proof.
  intros; apply pred_ext; hnf; intros.
  split; hnf; intros; destruct (H y H0); auto.
  hnf; intros.
  destruct H.
  split; auto.
Qed.

End Fash.

#[export] Hint Resolve ag_nat : core.

Notation "'#' e" := (fash e) (at level 20, right associativity): pred.

Lemma fash_triv : forall (P : pred nat), # P = P.
Proof.
  intros; apply pred_ext; repeat intro; auto.
  eapply pred_nec_hereditary, H.
  rewrite nec_nat; auto.
Qed.

Section Subtypes.

Context {A : Type} {AG : ageable A} {EO : Ext_ord A}.

Definition fashionable  (P: pred nat) := # P = P.

Notation "P '>=>' Q" := (# (P --> Q)) (at level 55, right associativity) : pred.
Notation "P '<=>' Q" := (# (P <--> Q)) (at level 57, no associativity) : pred.

Lemma subp_eqp : forall G (P Q: pred A),
  (G |-- P >=> Q) ->
  (G |-- Q >=> P) ->
  G |-- P <=> Q.
Proof.
  repeat intro.
  split.
  eapply H; eauto.
  eapply H0; eauto.
Qed.

Lemma eqp_subp : forall G P Q,
  (G |-- P <=> Q) ->
  G |-- P >=> Q.
Proof.
  repeat intro.
  apply H in H0.
  simpl in H0.
  destruct (H0 _ H1); eauto.
Qed.

Lemma eqp_subp2 : forall G P Q,
  (G |-- P <=> Q) ->
  G |-- Q >=> P.
Proof.
  repeat intro.
  apply H in H0.
  simpl in H0.
  destruct (H0 _ H1); eauto.
Qed.

Lemma eqp_comm : forall (P Q:pred A),
  P <=> Q = Q <=> P.
Proof.
  intros. apply pred_ext.
  apply subp_eqp.
    apply eqp_subp2. hnf; auto.
    apply eqp_subp. hnf; auto.
  apply subp_eqp.
    apply eqp_subp2. hnf; auto.
    apply eqp_subp. hnf; auto.
Qed.

Lemma subp_refl : forall G P,
  G |-- P >=> P.
Proof.
  repeat intro; auto.
Qed.

Lemma subp_trans : forall G P Q R,
  (G |-- P >=> Q) ->
  (G |-- Q >=> R) ->
  G |-- P >=> R.
Proof.
  repeat intro.
  eapply H0; eauto.
  eapply H; eauto.
Qed.

Lemma subp_top : forall G P,
  G |-- P >=> TT.
Proof.
  repeat intro; simpl; auto.
Qed.

Lemma subp_bot : forall G P,
  G |-- FF >=> P.
Proof.
  repeat intro; simpl in *; intuition.
Qed.

Lemma subp_andp : forall G P P' Q Q',
  (G |-- P >=> P') ->
  (G |-- Q >=> Q') ->
  G |-- P && Q >=> (P' && Q').
Proof.
  repeat intro.
  destruct H5; split.
  eapply H; eauto.
  eapply H0; eauto.
Qed.

Lemma subp_imp : forall G P P' Q Q',
  (G |-- P' >=> P) ->
  (G |-- Q >=> Q') ->
  G |-- (P --> Q) >=> (P' --> Q').
Proof.
  repeat intro.
  assert (a >= level a'').
  { apply necR_level in H3; apply ext_level in H4; lia. }
  eapply (H0); eauto.
  eapply H5; eauto.
  eapply H; eauto.
Qed.

Lemma subp_orp : forall G P P' Q Q',
  (G |-- P >=> P') ->
  (G |-- Q >=> Q') ->
  G |-- (P || Q) >=> (P' || Q').
Proof.
  repeat intro.
  destruct H5; [ left | right ].
  eapply H; eauto.
  eapply H0; eauto.
Qed.

Lemma subp_subp :
  forall (G: pred nat) (P Q R S: pred A),
   (G |-- (R >=> P)) ->
   (G |-- (Q >=> S)) ->
   G |-- (P >=> Q) >=> (R >=> S).
Proof.
 intros.
 intros w ?.
 specialize (H _ H1). specialize (H0 _ H1). clear G H1.
 intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
 assert (w >= level y0).
 { apply necR_level in H2. apply ext_level in H3. simpl in *; unfold natLevel in *. lia. }
 eapply H0, H4, H; eassumption.
Qed.

Lemma subp_allp : forall G B (X Y:B -> pred A),
  (forall x:B, G |-- X x >=> Y x) ->
  G |-- allp X >=> allp Y.
Proof.
  repeat intro.
  eapply H; eauto.
Qed.

Lemma subp_exp : forall G B (X Y:B -> pred A),
  (forall x:B, G |-- X x >=> Y x) ->
  G |-- exp X >=> exp Y.
Proof.
  repeat intro.
  destruct H4; exists x.
  eapply H; eauto.
Qed.

Lemma subp_allp_spec : forall G B (X:B -> pred A) x,
  G |-- allp X >=> X x.
Proof.
  repeat intro; eauto.
Qed.

Lemma subp_exp_spec : forall G B(X:B -> pred A) x,
  G |-- X x >=> exp X.
Proof.
  repeat intro.
  exists x; auto.
Qed.


Lemma later_fash1 :
   forall P, |> # P |-- # |> P.
Proof.
intros.
intros w ?.
intros w' ? w'' ?.
simpl in *.
eapply (H (level w'')); auto.
apply later_nat.
apply laterR_level in H1.
lia.
Qed.

Lemma later_fash :
    forall P, |> # P = # |> P.
Proof.
intros.
apply pred_ext.
apply later_fash1.
(** backward direction **)
intros w ? w' ?.
simpl in *.
intros.
destruct (af_unage age_facts y).
apply (H x).
apply later_nat in H0.
apply age_level in H2.
lia.
constructor 1; auto.
Qed.

Lemma subp_later1 : forall P Q,
   |>(P >=> Q)  |--   |>P >=> |>Q.
Proof.
intros.
rewrite later_fash.
apply fash_derives, axiomK.
Qed.

(*Lemma subp_later : forall P Q,
   |>(P >=> Q) = |>P >=> |>Q.
Proof.
intros.
apply pred_ext.
apply subp_later1.
rewrite later_fash.
intros ???????????.
eapply H.
f_equal.
apply later_imp.
Qed.*)

Lemma eqp_later1 : forall P Q,
   |>(P <=> Q)  |--   |>P <=> |>Q.
Proof.
intros.
rewrite later_fash.
apply fash_derives.
rewrite later_and.
apply andp_derives; apply axiomK.
Qed.

(*Lemma eqp_later : forall P Q,
    (|>(P <=> Q) = |>P <=> |>Q)%pred.
Proof.
intros.
rewrite later_fash.
f_equal.
rewrite later_and.
repeat rewrite later_imp.
auto.
Qed.*)


Program Definition unfash  (P: pred nat) : pred A :=
     fun x => P (level x).
Next Obligation.
 split; hnf; intros.
 apply age_level in H.
 rewrite H in H0.
 eapply pred_hereditary; eauto. unfold age; simpl. auto.

 apply ext_level in H as <-; auto.
Qed.

Notation "'!' e" := (unfash e) (at level 20, right associativity): pred.

Lemma level_later : forall {w: A} {n': nat},
         laterR (level w) n' ->
       exists w', laterR w w' /\ n' = level w'.
Proof.
intros.
remember (level w) as n.
revert w Heqn; induction H; intros; subst.
case_eq (age1 w); intros.
exists a; split. constructor; auto.
symmetry; unfold age in H; simpl in H.
  unfold natAge1 in H; simpl in H. revert H; case_eq (level w); intros; inv H1.
  apply age_level in H0. congruence. rewrite age1_level0 in H0.
   rewrite H0 in H. inv H.
 specialize (IHclos_trans1 _ (refl_equal _)).
  destruct IHclos_trans1 as [w2 [? ?]].
  subst.
  specialize (IHclos_trans2 _ (refl_equal _)).
  destruct IHclos_trans2 as [w3 [? ?]].
  subst.
  exists w3; split; auto. econstructor 2; eauto.
Qed.

Lemma later_unfash :
     forall P, |> (unfash P: pred A) = unfash ( |> P).
Proof.
unfold unfash; intros.
apply pred_ext; intros w ?; hnf in *.
intros n' ?.
simpl in H0. destruct (level_later H0) as [w' [? ?]].
  subst. apply H. auto.
 intros ? ?. simpl in H0. apply H. simpl.
  apply laterR_level in H0. rewrite laterR_nat; auto.
Qed.

Lemma subp_derives  :
  forall (P P' Q Q': pred A),
    (P' |-- P) ->
    (Q |-- Q') ->
    (P >=> Q) |-- (P' >=> Q').
Proof.

intros.
intros w ?.
intros ? ? ? ? ? ? ?.
apply H0.
eapply H1; eauto.
Qed.

Lemma derives_subp  :
      forall (P Q: pred A) (st: nat), (P |-- Q) -> (P >=> Q) st.
Proof.

intros.
intros w' ? w'' ? ?.
eauto.
Qed.

Lemma exp_subp' :
  forall (T: Type) (P Q: T -> pred A) (st: nat),
                (forall x, (P x >=> Q x) st) -> ((EX x : T, P x) >=> (EX x : T, Q x)) st.
Proof.
intros.
repeat intro.
destruct H3 as [x ?]; exists x.
eapply H; eauto.
Qed.

Lemma fash_fash :  forall P: pred A,  # # P = # P.
Proof.
intros.
apply pred_ext; intro; simpl in *; intros.
apply H with a; auto.
subst.
apply H.
unfold natLevel in H0. lia.
Qed.

Lemma fash_subp :
    forall (P Q: pred A), fashionable (P >=> Q).
Proof.
intros.
unfold fashionable.
rewrite fash_fash. auto.
Qed.
#[local] Hint Resolve fash_subp : core.

Lemma fash_allp :
  forall  (B: Type) (F: B -> pred A),
      # (allp F) = allp (fun z: B => # F z).
Proof.
intros.
apply pred_ext; intros w ?.
intro z.
intros ? ?.
eapply H; eauto.
intros ? ? ?.
eapply H; auto.
Qed.

 Lemma subp_i1 :
  forall (P : pred nat) (Q R: pred A ), (!P && Q |-- R) -> P |-- Q >=> R.
Proof. intros.
 intros n ?. intros ? ? ? ? ? ? ?. apply H. split; auto.
 assert (P (level a')). eapply pred_nec_hereditary; try apply H0.
 apply nec_nat. apply necR_level in H2. lia.
 hnf. apply ext_level in H3 as <-. auto.
Qed.

Lemma subp_eq :
  forall (P : pred nat) (Q R: pred A ), (!P && Q |-- R) <-> (P |-- Q >=> R).
Proof. intros. split; [apply subp_i1|].
  intros ?? []. eapply H; eauto. auto.
Qed.

Lemma eqp_nat: forall P Q: pred nat, (P <=> Q) = (P <--> Q).
Proof.
intros.
apply pred_ext; intros w ?.
specialize (H _ (Nat.le_refl _)); auto.
intros n' ?. inv H0; auto.
eapply pred_nec_hereditary; try apply H.
apply nec_nat.
unfold level in H1. simpl in H1. unfold natLevel in H1. lia.
Qed.

Lemma prop_andp_subp :
  forall (P: Prop) Q R w, (P -> app_pred (Q >=> R) w) -> app_pred ((!!P && Q) >=> R) w.
Proof.
intros.
repeat intro.
destruct H3.
apply H in H3.
eapply H3; eauto.
Qed.

Lemma subp_e : forall P Q : pred A, (TT |-- P >=> Q) -> P |-- Q.
Proof.
intros.
repeat intro.
eapply H; eauto.
Qed.

Lemma eqp_unfash : forall G P Q, G |-- P <=> Q -> G |-- (!P <=> !Q).
Proof.
  intros.
  eapply derives_trans; [apply H|].
  intros ????.
  split; intros ?????; eapply H0; eauto; apply necR_level in H2; apply ext_level in H3; simpl; unfold natLevel; lia.
Qed.

Lemma eqp_subp_subp : forall G (P Q R S : pred A),
  G |-- P <=> R -> G |-- Q <=> S ->
  G |-- (P >=> Q) <=> (R >=> S).
Proof.
  intros.
  rewrite fash_triv.
  apply andp_right; rewrite <- imp_andp_adjoint; eapply subp_trans, subp_trans.
  - apply andp_left1, eqp_subp2, H.
  - apply andp_left2, derives_refl.
  - apply andp_left1, eqp_subp, H0.
  - apply andp_left1, eqp_subp, H.
  - apply andp_left2, derives_refl.
  - apply andp_left1, eqp_subp2, H0.
Qed.

Lemma eqp_trans : forall G (P Q R : pred A),
  G |-- P <=> Q -> G |-- Q <=> R ->
  G |-- P <=> R.
Proof.
  intros.
  eapply subp_eqp; eapply subp_trans; eapply eqp_subp.
  - apply H.
  - apply H0.
  - rewrite eqp_comm; apply H0.
  - rewrite eqp_comm; apply H.
Qed.

Lemma eqp_eqp : forall G (P Q R S : pred A),
  G |-- P <=> R -> G |-- Q <=> S ->
  G |-- (P <=> Q) <=> (R <=> S).
Proof.
  intros.
  rewrite fash_triv.
  apply andp_right; rewrite <- imp_andp_adjoint; eapply eqp_trans, eqp_trans.
  - apply andp_left1; rewrite eqp_comm; apply H.
  - apply andp_left2, derives_refl.
  - apply andp_left1, H0.
  - apply andp_left1, H.
  - apply andp_left2, derives_refl.
  - apply andp_left1; rewrite eqp_comm; apply H0.
Qed.

End Subtypes.

Notation "'#' e" := (fash e) (at level 20, right associativity): pred.
Notation "'!' e" := (unfash e) (at level 20, right associativity): pred.
Notation "P '>=>' Q" := (# (P --> Q)) (at level 55, right associativity) : pred.
Notation "P '<=>' Q" := (# (P <--> Q)) (at level 57, no associativity) : pred.

#[export] Hint Resolve ag_nat : core.
#[export] Hint Resolve fash_subp : core.
