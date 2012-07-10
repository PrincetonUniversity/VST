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
  destruct (af_unage age_facts _ _ _ H H0) as [x0 ?].
  exists x0; auto. 
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

Lemma sub_equ {A} `{ageable A} : forall G (P Q: pred A),
  G |-- P >=> Q ->
  G |-- Q >=> P ->
  G |-- P <=> Q.
Proof.
  repeat intro.
  split.
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Lemma equ_sub {A} `{ageable A} : forall G P Q,
  G |-- P <=> Q ->
  G |-- P >=> Q.
Proof.
  repeat intro.
  apply H0 in H1.
  simpl in H1.
  destruct (H1 _ H2); auto.
Qed.

Lemma equ_sub2 {A} `{ageable A} : forall G P Q,
  G |-- P <=> Q ->
  G |-- Q >=> P.
Proof.
  repeat intro.
  apply H0 in H1.
  simpl in H1.
  destruct (H1 _ H2); auto.
Qed.

Lemma equ_comm : forall {A} `{ageable A} (P Q:pred A),
  P <=> Q = Q <=> P.
Proof.
  intros. apply pred_ext.
  apply sub_equ.
    apply equ_sub2. hnf; auto.
    apply equ_sub. hnf; auto.
  apply sub_equ.
    apply equ_sub2. hnf; auto.
    apply equ_sub. hnf; auto.
Qed.    

Lemma sub_refl {A} `{ageable A} : forall G P,
  G |-- P >=> P.
Proof.
  repeat intro; auto.
Qed.

Lemma sub_trans {A} `{ageable A} : forall G P Q R,
  G |-- P >=> Q ->
  G |-- Q >=> R ->
  G |-- P >=> R.
Proof.
  repeat intro.
  eapply H1; eauto.
  eapply H0; eauto.
Qed.

Lemma sub_top {A} `{ageable A} : forall G P,
  G |-- P >=> TT.
Proof.
  repeat intro; simpl; auto.
Qed.

Lemma sub_bot {A} `{ageable A} : forall G P,
  G |-- FF >=> P.
Proof.
  repeat intro; simpl in *; intuition.
Qed.

Lemma sub_andp {A} `{ageable A} : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- P && Q >=> (P' && Q').
Proof.
  repeat intro.
  destruct H5; split.
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Lemma sub_imp {A} `{ageable A} : forall G P P' Q Q',
  G |-- P' >=> P ->
  G |-- Q >=> Q' ->
  G |-- (P --> Q) >=> (P' --> Q').
Proof.
  repeat intro.
  eapply H1; eauto.
  apply H5; auto.
  eapply H0; eauto.
Qed.

Lemma sub_orp {A} `{ageable A} : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- (P || Q) >=> (P' || Q').
Proof.
  repeat intro.
  destruct H5; [ left | right ].
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Lemma sub_sub {A}{agA: ageable A}:
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

Lemma sub_allp {A} `{ageable A} : forall G B (X Y:B -> pred A),
  (forall x:B, G |-- X x >=> Y x) ->
  G |-- allp X >=> allp Y.
Proof.
  repeat intro.
  eapply H0; eauto.
Qed.

Lemma sub_exp {A} `{ageable A} : forall G B (X Y:B -> pred A),
  (forall x:B, G |-- X x >=> Y x) ->
  G |-- exp X >=> exp Y.
Proof.
  repeat intro.
  destruct H4; exists x.
  eapply H0; eauto.
Qed.

Lemma sub_allp_spec {A} `{ageable A} : forall G B (X:B -> pred A) x,
  G |-- allp X >=> X x.
Proof.
  repeat intro; eauto.
Qed.

Lemma sub_exp_spec {A} `{ageable A} : forall G B(X:B -> pred A) x,
  G |-- X x >=> exp X.
Proof.
  repeat intro.
  exists x; auto.
Qed.

Class natty (A: Type) {agA: ageable A} : Prop :=
   mkNatty: forall x': A, exists x, age x x'.

Instance nat_natty : natty nat.
Proof.
unfold natty; intros.
exists (S x'); simpl; auto.
unfold age, age1. simpl. auto.
Qed.
Hint Resolve nat_natty.

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

Lemma later_fash {A} `{NA : natty A}: 
    forall P, |> # P = # |> P.
Proof.
intros.
apply pred_ext.
apply later_fash1.
(** backward direction **) 
intros w ? w' ?.
simpl in *.
intros.
destruct (NA y).
apply (H x).
apply later_nat in H0.
apply age_level in H2. 
omega.
constructor 1; auto.
Qed.

Lemma sub_later1 {A} `{ageable A} : forall P Q,
   |>(P >=> Q)  |--   |>P >=> |>Q.
Proof.
intros.
eapply derives_trans; [apply later_fash1 | ].
rewrite later_imp.
intros ? ?; auto.
Qed.

Lemma sub_later {A} `{natty A} : forall P Q,
   |>(P >=> Q) = |>P >=> |>Q.
Proof.
intros.
rewrite later_fash.
f_equal.
apply later_imp.
Qed.

Lemma eq_later1 {A} `{ageable A} : forall P Q,
   |>(P <=> Q)  |--   |>P <=> |>Q.
Proof.
intros.
eapply derives_trans; [apply later_fash1 | ].
rewrite later_and.
repeat rewrite later_imp. auto.
Qed.

Lemma eq_later {A} `{natty A} : forall P Q,
    (|>(P <=> Q) = |>P <=> |>Q)%pred.
Proof.
intros.
rewrite later_fash.
f_equal.
rewrite later_and.
repeat rewrite later_imp.
auto.
Qed.


Program Definition fash' {A} `{agA: ageable A} (P: pred nat) : pred A :=
     fun x => P (level x).
Next Obligation.
 apply age_level in H. 
 rewrite H in H0.
 eapply pred_hereditary; eauto. unfold age;  simpl. auto.
Qed.

Notation "'!' e" := (fash' e) (at level 30, right associativity): pred.

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

Lemma later_fash' {A} `{H : ageable A}:
     forall P, |> (fash' P: pred A) = fash' ( |> P).
Proof.
unfold fash'; intros.
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
                (forall x, (P x >=> Q x) st) -> ((Ex x : T, P x) >=> (Ex x : T, Q x)) st.
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
