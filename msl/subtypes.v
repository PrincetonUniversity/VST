(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.ageable.
Require Import msl.predicates_hered.

Local Open Scope pred.

Lemma valid_rel_fashion {A} `{AG: ageable A} : valid_rel fashionR.
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

  hnf in H.
  destruct (af_unage age_facts x). exists x0. apply H1.
  hnf.
  rewrite (af_level2 age_facts x0 x); auto.
  rewrite (af_level2 age_facts z y); auto.
Qed.

Definition fashionM {A} `{ageable A} : modality
  := exist _ fashionR valid_rel_fashion.

Existing Instance ag_nat. Hint Resolve ag_nat.

Program Definition fash {A: Type} `{NA: ageable A} (P: pred A): pred nat :=
      fun n => forall y, n >= level y -> P y.
Next Obligation.
destruct P as [P HP].
simpl in *.
apply H0.
unfold age, age1, ag_nat,natAge1 in H.
destruct a; inv H.
omega.
Qed.

Notation "'#' e" := (fash e) (at level 30, right associativity): pred.

Lemma fash_K {A} `{H: ageable A}: forall (P Q: pred A), 
                 # (P --> Q) |-- # P --> # Q.
Proof.
intros.
intros n ?.
simpl in H.
simpl.
intros w ? ? ? ?.
apply (pred_nec_hereditary _ _ _ H1) in H0.
clear n H1.
specialize (H2 _ H3).
simpl in H0.
eapply H0; eauto.
Qed.

Lemma laterR_nat: forall (n n': nat), laterR n n' <-> (n > n')%nat.
Proof.
intros.
split; induction 1; simpl; intros.
unfold age, age1 in H; simpl in H; unfold natAge1 in H. destruct x; inv H.
auto.
apply gt_trans with y; auto.
constructor 1. unfold age, age1; simpl. auto.
constructor 2 with m; auto.
constructor 1. unfold age, age1; simpl. auto.
Qed.

Lemma fash_fash {A} `{NA: ageable A}:  forall P: pred A,  # # P = # P.
Proof.
intros.
apply pred_ext; intro; simpl in *; intros.
apply H with a; auto.
subst.
apply H.
unfold natLevel in H0. omega.
Qed.

Lemma fash_derives {A} `{agA : ageable A}:  
     forall (P Q: pred A), P |-- Q  ->  # P |-- # Q.
Proof.
intros.
intros w ?.
intro; intros.
apply H.
eapply H0; auto.
Qed.

Lemma fash_and {A} `{H : ageable A}: forall (P Q:pred A),
  # (P && Q) = # P && # Q.
Proof.
  intros; apply pred_ext; hnf; intros.
  split; hnf; intros; destruct (H0 y H1); auto.
  hnf; intros.
  destruct H0.
  split; auto.
Qed.

Definition fashionable  (P: pred nat) := # P = P.

Notation "P '>=>' Q" := (# (P --> Q)) (at level 55, right associativity) : pred.
Notation "P '<=>' Q" := (# (P <--> Q)) (at level 57, no associativity) : pred.

Lemma subp_eqp {A} `{ageable A} : forall G (P Q: pred A),
  G |-- P >=> Q ->
  G |-- Q >=> P ->
  G |-- P <=> Q.
Proof.
  repeat intro.
  split.
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Lemma eqp_subp {A} `{ageable A} : forall G P Q,
  G |-- P <=> Q ->
  G |-- P >=> Q.
Proof.
  repeat intro.
  apply H0 in H1.
  simpl in H1.
  destruct (H1 _ H2); auto.
Qed.

Lemma eqp_subp2 {A} `{ageable A} : forall G P Q,
  G |-- P <=> Q ->
  G |-- Q >=> P.
Proof.
  repeat intro.
  apply H0 in H1.
  simpl in H1.
  destruct (H1 _ H2); auto.
Qed.

Lemma eqp_comm : forall {A} `{ageable A} (P Q:pred A),
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

Lemma subp_refl {A} `{ageable A} : forall G P,
  G |-- P >=> P.
Proof.
  repeat intro; auto.
Qed.

Lemma subp_trans {A} `{ageable A} : forall G P Q R,
  G |-- P >=> Q ->
  G |-- Q >=> R ->
  G |-- P >=> R.
Proof.
  repeat intro.
  eapply H1; eauto.
  eapply H0; eauto.
Qed.

Lemma subp_top {A} `{ageable A} : forall G P,
  G |-- P >=> TT.
Proof.
  repeat intro; simpl; auto.
Qed.

Lemma subp_bot {A} `{ageable A} : forall G P,
  G |-- FF >=> P.
Proof.
  repeat intro; simpl in *; intuition.
Qed.

Lemma subp_andp {A} `{ageable A} : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- P && Q >=> (P' && Q').
Proof.
  repeat intro.
  destruct H5; split.
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Lemma subp_imp {A} `{ageable A} : forall G P P' Q Q',
  G |-- P' >=> P ->
  G |-- Q >=> Q' ->
  G |-- (P --> Q) >=> (P' --> Q').
Proof.
  repeat intro.
  eapply H1; eauto.
  apply H5; auto.
  eapply H0; eauto.
Qed.

Lemma subp_orp {A} `{ageable A} : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- (P || Q) >=> (P' || Q').
Proof.
  repeat intro.
  destruct H5; [ left | right ].
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Lemma subp_subp {A}{agA: ageable A}:
  forall (G: pred nat) (P Q R S: pred A), 
   G |-- (R >=> P) ->
   G |-- (Q >=> S) ->
   G |-- (P >=> Q) >=> (R >=> S).
Proof.
 intros.
 intros w ?.
 specialize (H _ H1). specialize (H0 _ H1). clear G H1.
 intros ? ? ? ? ? ? ? ? ? ?.
 eapply H0.
 3: eapply H3.
 5: eapply H; auto.
 2: eassumption. 3: eassumption.
 apply necR_level in H2. apply le_trans with (level y); auto. apply le_trans with (level a'); auto.
 auto.
 apply necR_level in H5. 
 apply le_trans with (level y0); auto. apply le_trans with a'; auto.
 apply necR_level in H2.  apply le_trans with (level y); auto. 
Qed.

Lemma subp_allp {A} `{ageable A} : forall G B (X Y:B -> pred A),
  (forall x:B, G |-- X x >=> Y x) ->
  G |-- allp X >=> allp Y.
Proof.
  repeat intro.
  eapply H0; eauto.
Qed.

Lemma subp_exp {A} `{ageable A} : forall G B (X Y:B -> pred A),
  (forall x:B, G |-- X x >=> Y x) ->
  G |-- exp X >=> exp Y.
Proof.
  repeat intro.
  destruct H4; exists x.
  eapply H0; eauto.
Qed.

Lemma subp_allp_spec {A} `{ageable A} : forall G B (X:B -> pred A) x,
  G |-- allp X >=> X x.
Proof.
  repeat intro; eauto.
Qed.

Lemma subp_exp_spec {A} `{ageable A} : forall G B(X:B -> pred A) x,
  G |-- X x >=> exp X.
Proof.
  repeat intro.
  exists x; auto.
Qed.


Lemma later_fash1 {A} `{agA: ageable A}:
   forall P, |> # P |-- # |> P.
Proof.
intros.
intros w ?.
intros w' ? w'' ?.
simpl in *.
eapply (H (level w'')); auto.
apply later_nat.
apply laterR_level in H1.
omega.
Qed.

Lemma later_fash {A} `{agA : ageable A}: 
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
omega.
constructor 1; auto.
Qed.

Lemma subp_later1 {A} `{ageable A} : forall P Q,
   |>(P >=> Q)  |--   |>P >=> |>Q.
Proof.
intros.
eapply derives_trans; [apply later_fash1 | ].
rewrite later_imp.
intros ? ?; auto.
Qed.

Lemma subp_later {A} `{ageable A} : forall P Q,
   |>(P >=> Q) = |>P >=> |>Q.
Proof.
intros.
rewrite later_fash.
f_equal.
apply later_imp.
Qed.

Lemma eqp_later1 {A} `{ageable A} : forall P Q,
   |>(P <=> Q)  |--   |>P <=> |>Q.
Proof.
intros.
eapply derives_trans; [apply later_fash1 | ].
rewrite later_and.
repeat rewrite later_imp. auto.
Qed.

Lemma eqp_later {A} `{ageable A} : forall P Q,
    (|>(P <=> Q) = |>P <=> |>Q)%pred.
Proof.
intros.
rewrite later_fash.
f_equal.
rewrite later_and.
repeat rewrite later_imp.
auto.
Qed.


Program Definition unfash {A} `{agA: ageable A} (P: pred nat) : pred A :=
     fun x => P (level x).
Next Obligation.
 apply age_level in H. 
 rewrite H in H0.
 eapply pred_hereditary; eauto. unfold age;  simpl. auto.
Qed.

Notation "'!' e" := (unfash e) (at level 30, right associativity): pred.

Lemma level_later {A} `{H : ageable A}: forall {w: A} {n': nat}, 
         laterR (level w) n' ->
       exists w', laterR w w' /\ n' = level w'.
Proof.
intros.
remember (level w) as n.
revert w Heqn; induction H0; intros; subst.
case_eq (age1 w); intros.
exists a; split. constructor; auto.
symmetry; unfold age in H0; simpl in H0. 
  unfold natAge1 in H0; simpl in H0. revert H0; case_eq (level w); intros; inv H2.
  apply age_level in H1. congruence. rewrite age1_level0 in H1.
   rewrite H1 in H0. inv H0.
 specialize (IHclos_trans1 _ (refl_equal _)).
  destruct IHclos_trans1 as [w2 [? ?]].
  subst.
  specialize (IHclos_trans2 _ (refl_equal _)).
  destruct IHclos_trans2 as [w3 [? ?]].
  subst.
  exists w3; split; auto. econstructor 2; eauto.
Qed.

Lemma later_unfash {A} `{H : ageable A}:
     forall P, |> (unfash P: pred A) = unfash ( |> P).
Proof.
unfold unfash; intros.
apply pred_ext; intros w ?; hnf in *.
intros n' ?.
simpl in H1. destruct (level_later H1) as [w' [? ?]].
  subst. apply H0. auto.
 intros ? ?. simpl in H1. apply H0. simpl.
  apply laterR_level in H1. rewrite laterR_nat; auto.
Qed.

Lemma subp_derives {A} `{agA : ageable A} :
  forall (P P' Q Q': pred A),
    P' |-- P ->
    Q |-- Q' -> 
    (P >=> Q) |-- (P' >=> Q').
Proof.

intros.
intros w ?.
intros ? ? ? ? ?.
apply H0.
eapply H1; eauto.
Qed.

Lemma derives_subp {A} `{agA : ageable A} :
      forall (P Q: pred A) (st: nat), (P |-- Q) -> (P >=> Q) st.
Proof.

intros.
intros w' ? w'' ? ?.
eauto.
Qed.

Lemma exp_subp' {A} `{H : ageable A}: 
  forall (T: Type) (P Q: T -> pred A) (st: nat),
                (forall x, (P x >=> Q x) st) -> ((EX x : T, P x) >=> (EX x : T, Q x)) st.
Proof.
intros.
repeat intro.
destruct H3 as [x ?]; exists x.
eapply H0; eauto.
Qed.

Lemma fash_subp {A} `{agA: ageable A}: 
    forall (P Q: pred A), fashionable (P >=> Q).
Proof.
intros.
unfold fashionable.
rewrite fash_fash. auto.
Qed.
Hint Resolve @fash_subp.

Lemma fash_allp {A} {agA:ageable A}:
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

 Lemma subp_i1 {A}{agA: ageable A}:
  forall (P : pred nat) (Q R: pred A ), !P && Q |-- R -> P |-- Q >=> R.
Proof. intros.
  intros n ?. intros ? ? ? ? ?. apply H. split; auto.
 eapply pred_nec_hereditary. apply H2.
 assert (P (level y)). eapply pred_nec_hereditary; try apply H0. 
 apply nec_nat. auto. apply H4.
Qed.

Lemma eqp_nat: forall P Q: pred nat, (P <=> Q) = (P <--> Q).
Proof.
intros.
apply pred_ext; intros w ?.
specialize (H _ (le_refl _)); auto.
intros n' ?. inv H0; auto.
eapply pred_nec_hereditary; try apply H. 
apply nec_nat.
unfold level in H1. simpl in H1. unfold natLevel in H1. omega.
Qed.

Lemma prop_andp_subp {A}{agA : ageable A}:
  forall (P: Prop) Q R w, (P -> app_pred (Q >=> R) w) -> app_pred ((!!P && Q) >=> R) w.
Proof.
intros.
repeat intro.
destruct H2.
apply H in H2.
eapply H2; eauto.
Qed.

Lemma subp_e {A}{agA : ageable A}: forall P Q : pred A, TT |-- P >=> Q -> P |-- Q.
Proof.
intros.
repeat intro.
apply (H (@level _ agA a) I a (le_refl _) a (necR_refl _) H0).
Qed.


