Require Import msl.base.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.
Require Import msl.age_sepalg.
Require Import msl.predicates_hered.
Require Import msl.predicates_sl.
Require Import msl.subtypes.

Local Open Scope pred.


Lemma unfash_derives {A} `{agA : ageable A}:
  forall {P Q}, (P |-- Q) -> @derives A _ (! P) (! Q).
Proof.
intros. intros w ?. simpl in *. apply H. auto.
Qed.

Lemma subp_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- P * Q >=> P' * Q'.
Proof.
  pose proof I.
  repeat intro.
  specialize (H0 _ H2).
  specialize (H1 _ H2).
  clear G H2.
  destruct H5 as [w1 [w2 [? [? ?]]]].
  exists w1; exists w2; split; auto.
  split.
  eapply H0; auto.
  assert (level w1 = level a').
  apply comparable_fashionR.  eapply join_sub_comparable; eauto.
 apply necR_level in H4. omega.
  eapply H1; auto.
  assert (level w2 = level a').
  apply comparable_fashionR. eapply join_sub_comparable; eauto.
 apply necR_level in H4. omega.
Qed.

Lemma sub_wand {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall G P P' Q Q',
  G |-- P' >=> P ->
  G |-- Q >=> Q' ->
  G |-- (P -* Q) >=> (P' -* Q').
Proof.
  pose proof I.
  repeat intro.
  specialize (H0 _ H2); specialize (H1 _ H2); clear G H2; pose (H2:=True).
  eapply H0 in H8; try apply necR_refl.
  eapply H1; try apply necR_refl.
  apply necR_level in H4. apply necR_level in H6. apply join_comparable in H7. 
  apply comparable_fashionR in H7. unfold fashionR in H7. omega.
  eapply H5; eauto.
  apply necR_level in H4. apply necR_level in H6.
   apply join_comparable2 in H7. 
  apply comparable_fashionR in H7. unfold fashionR in H7. omega.
Qed.

Lemma find_superprecise {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}: 
   forall Q, Q |-- EX P:_, P && !(P >=> Q) && !!superprecise (P).
Proof.
intros.
intros w ?.
exists (exactly w).
split; auto.
split; auto.
hnf; apply necR_refl.
intros w' ? w'' ? ?.
hnf in H2.
apply pred_nec_hereditary with w; auto.
do 3 red.
apply superprecise_exactly.
Qed.

Lemma sepcon_subp' {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall (P P' Q Q' : pred A) (st: nat),  
    (P >=> P') st -> 
    (Q >=> Q') st -> 
    (P * Q >=> P' * Q') st.
Proof.
 pose proof I.
intros.
intros w' ? w'' ? [w1 [w2 [? [? ?]]]].
destruct (nec_join4 _ _ _ _ H4 H3) as [w1' [w2' [? [? ?]]]].
exists w1; exists w2; repeat split; auto.
eapply (H0 w1'); eauto.
simpl in *.
subst.
replace (level w1') with (level w'); auto.
symmetry; apply comparable_fashionR; eapply join_comparable; eauto.
eapply (H1 w2'); eauto.
replace (level w2') with (level w'); auto.
symmetry. apply comparable_fashionR.
eapply join_comparable; eauto.
Qed.

Lemma subp_refl'  {A} `{agA : ageable A} :  forall (Q: pred A) (st: nat), (Q >=> Q) st.
Proof.
intros.
intros ? ? ? ?; auto.
Qed.

Lemma subp_trans' {A} `{agA : ageable A}:
  forall (B C D: pred A) (w: nat), (B >=> C)%pred w -> (C >=> D)% pred w -> (B >=> D)%pred w.
Proof.
intros.
intros w' ? w'' ? ?.
eapply H0; eauto.
eapply H; eauto.
Qed.

Lemma andp_subp'  {A} `{agA : ageable A} :
 forall (P P' Q Q': pred A) (w: nat), (P >=> P') w -> (Q >=> Q') w -> (P && Q >=> P' && Q') w.
Proof.
intros.
intros w' ? w'' ? [? ?]; split.
eapply H; eauto.
eapply H0; eauto.
Qed.

Lemma allp_subp' {A} `{agA : ageable A}: forall T (F G: T -> pred A) (w: nat), 
   (forall x,  (F x >=> G x) w) -> (allp (fun x:T => (F x >=> G x)) w).
Proof.
intros.
intro x; apply H; auto.
Qed.


Lemma pred_eq_e1 {A} `{agA : ageable A}: forall (P Q: pred A) w, 
       ((P <=> Q) w -> (P >=> Q) w).
Proof.
intros.
intros w' ? w'' ? ?.
eapply H; eauto.
Qed.

Lemma pred_eq_e2 {A} `{agA : ageable A}: forall (P Q: pred A)  w, 
     ((P <=> Q) w -> (Q >=> P) w).
Proof.
Proof.
intros.
intros w' ? w'' ? ?.
eapply H; eauto.
Qed.

Hint Resolve @sepcon_subp'.
Hint Resolve @subp_refl'.
Hint Resolve @andp_subp'.
Hint Resolve @allp_subp'.
Hint Resolve @derives_subp.
Hint Resolve @pred_eq_e1.
Hint Resolve @pred_eq_e2.


Lemma allp_imp2_later_e2 {B}{A}{agA: ageable A}:
   forall (P Q: B -> pred A) (y: B) ,
      (ALL x:B, |> P x <=> |> Q x) |-- |> Q y >=> |> P y.
Proof. 
  intros.  intros w ?. specialize (H y). apply pred_eq_e2. auto.
Qed.
Lemma allp_imp2_later_e1 {B}{A}{agA: ageable A}:
   forall (P Q: B -> pred A) (y: B) ,
      (ALL x:B, |> P x <=> |> Q x) |-- |> P y >=> |> Q y.
Proof. 
  intros.  intros w ?. specialize (H y). apply pred_eq_e1. auto.
Qed.

(*
Lemma subp_later {A} `{agA:  ageable A} (SS: natty A):
 forall (P Q: pred A), |> (P >=> Q) |-- |> P >=> |> Q.
Proof.
intros.
rewrite later_fash; auto.
apply fash_derives.
apply axiomK.
Qed.
*)

Lemma extend_unfash {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall (P: pred nat), boxy extendM (! P).
Proof.
intros.
apply boxy_i; auto; intros.
unfold unfash in *.
simpl in H. destruct H.
hnf in H0|-*.
replace (level w') with (level w); auto.
apply comparable_fashionR.
eapply join_comparable; eauto.
Qed.

Hint Resolve @extend_unfash.

Lemma subp_unfash {A} `{Age_alg A}:
  forall (P Q : pred nat) (n: nat), (P >=> Q) n -> ( ! P >=> ! Q) n.
Proof.
intros.
intros w ?. specialize (H0 _ H1).
intros w' ? ?. apply (H0 _ (necR_level' H2)).
auto.
Qed.
Hint Resolve @subp_unfash.


Lemma unfash_sepcon_distrib: 
        forall {T}{agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} 
           (P: pred nat) (Q R: pred T),
               unfash P && (Q*R) = (unfash P && Q) * (unfash P && R).
Proof.
intros.
apply pred_ext.
intros w [? [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; repeat split; auto.
apply join_level in H0. destruct H0.
hnf in H|-*. congruence.
apply join_level in H0. destruct H0.
hnf in H|-*. congruence.
intros w [w1 [w2 [? [[? ?] [? ?]]]]].
split.
apply join_level in H. destruct H.
hnf in H0|-*. congruence.
exists w1; exists w2; repeat split; auto.
Qed.


