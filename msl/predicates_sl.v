 (*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.cross_split.

(* rules about ext_order, join, and core *)
Class Ext_alg (A : Type) `{EO : Ext_ord A} {J : Join A} {SA : Sep_alg A} :=
  { ext_join_commut : forall {x y z z'}, join x y z -> ext_order z z' ->
      exists x', ext_order x x' /\ join x' y z';
    join_ext_commut : forall {x x' y' z'}, ext_order x x' -> join x' y' z' ->
      exists z, join x y' z /\ ext_order z z';
    (* emp is implemented in terms of a minimum element, but we can
       have different mins for different elements *)
    id_exists : forall x, exists e, identity e /\ unit_for e x
  }.

Section Predicates.

Context {A : Type} {JA : Join A} {PA : Perm_alg A} {SA : Sep_alg A} {AG : ageable A} {XA : Age_alg A} {EO : Ext_ord A} {EA : Ext_alg A}.

(*Definition compareR : relation A := comparable.*)
Definition extendR : relation A := join_sub.

(*Lemma valid_rel_compare {FA: Flat_alg A} : valid_rel compareR.
Proof.
  split; hnf; intros.

  apply comparable_common_unit in H0.
  destruct H0 as [w [? ?]].
  destruct (age1_join2  _ H1 H)
    as [u [v [? [? ?]]]].
  destruct (age1_join _ H0 H3)
    as [u' [v' [? [? ?]]]].
  assert (u' = v').
  unfold age in *; congruence.
  subst v'.
  exists u'; auto.
  assert (x = v).
  unfold age in *; congruence.
  subst v.
  apply common_unit_comparable.
  exists u; auto.

  split; hnf; intros.
  apply comparable_common_unit in H.
  destruct H as [w [? ?]].
  destruct (unage_join2 _ H H0)
    as [u [v [? [? ?]]]].
  destruct (unage_join _ H1 H3)
    as [u' [v' [? [? ?]]]].
  exists v'; auto.
  apply common_unit_comparable.
  destruct (join_ex_units u) as [uu Huu].
  red in Huu.
  exists uu; split.
  destruct (join_assoc Huu H2) as [q [? ?]].
  assert (q = z).
  eapply join_eq; eauto.
  subst q; auto.
  destruct (join_assoc Huu H5) as [q [? ?]].
  assert (q = v').
  eapply join_eq; eauto.
  subst q.
  auto.

  split; hnf; intros.
  hnf in H.
Qed.*)

Lemma valid_rel_extend  : valid_rel extendR.
Proof.
  split; hnf; intros.
  destruct H0 as [w ?].
  destruct (age1_join2 _ H0 H)
    as [u [v [? [? ?]]]].
  exists u; auto.
  exists v; auto.

  split; hnf; intros.
  destruct H.
  destruct (unage_join _ H H0)
    as [u [v [? [? ?]]]].
  exists v; auto.
  exists u; auto.

  destruct H.
  eapply join_ext_commut in H as (? & ? & ?); eauto.
  eexists; eauto; eexists; eauto.
Qed.

(*Definition compareM  : modality
  := exist _ compareR valid_rel_compare.*)
Definition extendM : modality
  := exist _ extendR valid_rel_extend.

(* Definitions of the BI connectives. *)
Obligation Tactic := unfold hereditary; intros; try solve [intuition].

(* This is the key point of the ordered logic: emp is true of anything
   that's in the extension order with an identity.
   In VeriC, this means the resources are cores but the ghost state
   can be anything. *)
Program Definition emp : pred A := fun w => exists e, identity e /\ ext_order e w.
Next Obligation.
  split; intros.
  - destruct H0 as (? & ? & ?).
    eapply age_ext_commut in H1 as [?? Hage]; eauto.
    apply age_identity in Hage; eauto.
  - destruct H0 as (? & ? & ?).
    do 2 eexists; eauto.
    etransitivity; eauto.
Qed.

Program Definition sepcon  (p q:pred A) : pred A := fun x:A =>
  exists y:A, exists z:A, join y z x /\ p y /\ q z.
Next Obligation.
  split; intros.
  destruct H0 as (y & z & J & ? & ?).
  destruct (age1_join2 _ J H) as [y' [z' [? [? ?]]]].
  do 3 eexists; eauto.
  split; eapply pred_hereditary; eauto.

  destruct H0 as (y & z & J & ? & ?).
  eapply ext_join_commut in J as (? & ? & ?); eauto.
  do 3 eexists; eauto; split; auto.
  eapply pred_upclosed; eauto.
Qed.

Program Definition wand  (p q:pred A) : pred A := fun x =>
  forall x' y z, necR x x' -> join x' y z -> p y -> q z.
Next Obligation.
  split; intros.
  eapply (H0 x'); eauto.
  apply rt_trans with a'; auto.
  apply rt_step; auto.

  eapply nec_ext_commut in H1 as []; eauto.
  eapply join_ext_commut in H2 as (? & ? & ?); eauto.
  eapply pred_upclosed; eauto.
  eapply H0; eauto.
Qed.

Notation "P '*' Q" := (sepcon P Q) : pred.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : pred.
Notation "'%' e"  := (box extendM e)(at level 30, right associativity): pred.

Lemma extendM_refl : reflexive _ extendM.
Proof.
intros; intro; simpl; apply join_sub_refl.
Qed.

(*Lemma compareM_refl {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{FA: Flat_alg A}{AG: ageable A}{XA: Age_alg A} : reflexive _ compareM.
Proof.
intros; intro; simpl.
apply comparable_refl.
Qed.*)

#[local] Hint Resolve extendM_refl : core.
(*#[export] Hint Resolve compareM_refl : core.*)


(* Rules for the BI connectives *)

Lemma wand_sepcon_adjoint  : forall (P Q R:pred A),
  ((P * Q) |-- R) = (P |-- (Q -* R)).
Proof.
  intros. apply prop_ext.
  split; intros.
  hnf; intros; simpl; intros.
  apply H.
  exists x'; exists y.
  intuition.
  apply pred_nec_hereditary with a; auto.
  hnf; intros.
  hnf in H.
  unfold wand in H; simpl in H.
  destruct H0 as [w [v [? [? ?]]]].
  eapply H; eauto.
Qed.

Lemma sepcon_assoc  : forall (P Q R:pred A),
  ((P * Q) * R = P * (Q * R))%pred.
Proof.
  pose proof I.
  intros; apply pred_ext; hnf; intros.
  destruct H0 as [x [y [? [? ?]]]].
  destruct H1 as [z [w [? [? ?]]]].
  destruct (join_assoc H1 H0) as [q [? ?]].
  exists z; exists q; intuition.
  exists w; exists y; intuition.
  destruct H0 as [x [y [? [? ?]]]].
  destruct H2 as [z [w [? [? ?]]]].
  apply join_comm in H0.
  apply join_comm in H2.
  destruct (join_assoc H2 H0) as [q [? ?]].
  exists q; exists w; intuition.
  exists x; exists z; intuition.
Qed.

Lemma sepcon_comm  : forall (P Q:pred A),
  (P * Q = Q * P)%pred.
Proof.
  pose proof I.
  intros; apply pred_ext; hnf; intros.
  destruct H0 as [x [y [? [? ?]]]].
  exists y; exists x; intuition; apply join_comm; auto.
  destruct H0 as [x [y [? [? ?]]]].
  exists y; exists x; intuition; apply join_comm; auto.
Qed.

Lemma split_sepcon  : forall (P Q R S:pred A),
  (P |-- Q) ->
  (R |-- S) ->
  (P * R) |-- (Q * S).
Proof.
  intros; hnf; intros.
  destruct H1 as [x [y [? [? ?]]]].
  exists x; exists y; intuition.
Qed.

Lemma sepcon_cut  : forall (P Q R S:pred A),
  (P |-- (Q -* R)) ->
  (S |-- Q) ->
  (P * S) |-- R.
Proof.
  intros.
  rewrite wand_sepcon_adjoint.
  hnf; intros.
  simpl; intros.
  eapply H; eauto.
Qed.

Lemma id_emp : forall w, identity w -> emp w.
Proof.
  intros; exists w; split; auto; reflexivity.
Qed.
#[local] Hint Resolve id_emp : core.

Lemma emp_sepcon  : forall (P:pred A),
  (emp * P = P)%pred.
Proof.
  intros; apply pred_ext; hnf; intros.
  destruct H as [x [y [J [(? & Hid & ?) ?]]]].
  eapply join_ext_commut in J as (? & J & ?); eauto.
  eapply pred_upclosed; eauto.
  apply Hid in J; subst; auto.

  destruct (id_exists a) as (? & ? & ?).
  do 3 eexists; eauto; split; auto.
Qed.

Lemma sepcon_emp   : forall (P:pred A),
  (P * emp = P)%pred.
Proof.
  intros.
  rewrite sepcon_comm.
  apply emp_sepcon.
Qed.

(*Lemma emp_sepcon : forall {A} `{Age_alg A} (P:pred A), emp * P = P.
Proof. exact @emp_sepcon. Qed.
Lemma sepcon_emp : forall {A} `{Age_alg A} (P:pred A), P * emp = P.
Proof. exact @sepcon_emp. Qed.
*)
	
Lemma later_wand  : forall P Q,
  (|>(P -* Q) = |>P -* |>Q)%pred.
Proof.
  pose proof I.
  intros.
  repeat rewrite later_age.
  apply pred_ext; hnf; intros.
  simpl; intros.
  simpl in H0.
  case_eq (age1 a); intros.
  specialize ( H0 a0 H5).
  apply nec_refl_or_later in H1.
  destruct H1; subst.
  destruct (age1_join2 _ H2 H4) as [w [v [? [? ?]]]].
  eapply H0; eauto.
  replace a0 with w; auto.
  congruence.
  assert (necR a0 x').
  eapply age_later_nec; eauto.
  destruct (age1_join2 _ H2 H4) as [w [v [? [? ?]]]].
  apply H0 with w v; auto.
  apply rt_trans with x'; auto.
  apply rt_step; auto.
  apply nec_refl_or_later in H1; destruct H1; subst.
  destruct (age1_join2 _  H2 H4) as [w [v [? [? ?]]]].
  hnf in H6.
  rewrite H5 in H6; discriminate.
  clear -H1 H5.
  exfalso.
  revert H5; induction H1; auto.
  intros.
  unfold age in H.
  rewrite H in H5; discriminate.

  simpl; intros.
  simpl in H0.
  destruct (valid_rel_nec) as (_ & H6 & _).
  destruct (H6 _ _ H2 _ H1).
  destruct (unage_join _ H3 H5) as [w [v [? [? ?]]]].
  apply H0 with x w v; auto.
  intros.
  replace a'0 with y; auto.
  congruence.
Qed.

Lemma later_sepcon  : forall P Q,
  (|>(P * Q) = |>P * |>Q)%pred.
Proof.
  pose (H:=True).
  intros.
  repeat rewrite later_age.
  apply pred_ext; hnf; intros.
  simpl in H0.
  case_eq (age1 a); intros.
  destruct (H0 a0) as [w [v [? [? ?]]]]; auto.
  destruct (unage_join2 _ H2 H1) as [w' [v' [? [? ?]]]].
  exists w'; exists v'; intuition.
  simpl; intros.
  replace a' with w; auto.
  unfold age in *; congruence.
  simpl; intros.
  replace a' with v; auto.
  unfold age in *; congruence.
  destruct (join_ex_units a).
  exists x; exists a.
  intuition.
  hnf; intros.
  red in u.
  simpl in H2.
  destruct (age1_join _ u H2) as [s [t [? [? ?]]]].
  unfold age in H5.
  rewrite H1 in H5; discriminate.
  hnf; intros.
  simpl in H2.
  unfold age in H2.
  rewrite H1 in H2; discriminate.

  destruct H0 as [w [v [? [? ?]]]].
  hnf; intros.
  simpl in H3.
  destruct (age1_join2 _ H0 H3) as [w' [v' [? [? ?]]]].
  exists w'; exists v'; intuition.
Qed.

Lemma FF_sepcon : forall (P:pred A),
  (FF * P = FF)%pred.
Proof.
  intros. apply pred_ext; repeat intro.
  destruct H as [? [? [? [? ?]]]].  elim H0.
  elim H.
Qed.

Lemma sepcon_derives :
  forall p q p' q', (p |-- p') -> (q |-- q') -> (p * q |-- p' * q').
Proof.
intros.
do 2 intro.
destruct H1 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; repeat split ;auto.
Qed.

Lemma exp_sepcon1 :
  forall T (P: T ->  pred A) Q,  (exp P * Q = exp (fun x => P x * Q))%pred.
Proof.
intros.
apply pred_ext; intros ? ?.
destruct H as [w1 [w2 [? [[x ?] ?]]]].
exists x; exists w1; exists w2; split; auto.
destruct H as [x [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; split; auto.
split; auto.
exists x; auto.
Qed.

Lemma exp_sepcon2 :
  forall T (P: pred A) (Q: T -> pred A),  (P * exp Q = exp (fun x => P * Q x))%pred.
Proof.
intros.
apply pred_ext; intros ? ?.
destruct H as [w1 [w2 [? [? [x ?]]]]].
exists x; exists w1; exists w2; split; auto.
destruct H as [x [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; split; auto.
split; auto.
exists x; auto.
Qed.

Lemma extend_later : forall P, (%|>P = |>%P)%pred.
Proof.
  intros; rewrite later_commute; auto.
Qed.

Lemma extend_later' : forall P, boxy extendM P -> boxy extendM (|> P)%pred.
Proof.
intros. unfold boxy in *. rewrite later_commute. rewrite H. auto.
Qed.
#[local] Hint Resolve extend_later' : core.

Lemma age_sepcon  :
      forall P Q, (box ageM (P * Q) = box ageM P * box ageM Q)%pred.
Proof.
  pose proof I.
  intros.
  apply pred_ext; hnf; intros.
  hnf in H0.
  case_eq (age1 a); intros.
  destruct (H0 a0) as [u [v [? [? ?]]]]; auto.
  red.
  destruct (unage_join2 _ H2 H1) as [x [y [? [? ?]]]].
  exists x; exists y.
  intuition.
  hnf; intros.
  replace a' with u; auto.
  unfold age in *; congruence.
  hnf; intros.
  replace a' with v; auto.
  unfold age in *; congruence.
  destruct (join_ex_units a).
  exists x; exists a.
  intuition.
  hnf; intros.
  red in u.
  destruct (age1_join _ u H2)
    as [p [q [? [? ?]]]]; auto.
  unfold age in *.
  rewrite H1 in H4; discriminate.
  hnf; intros.
  simpl in *.
  unfold age in *.
  rewrite H1 in H2; discriminate.

  destruct H0 as [u [v [? [? ?]]]].
  hnf; intros.
  destruct (age1_join2 _ H0 H3)
    as [p [q [? [? ?]]]]; auto.
  exists p; exists q; intuition.
Qed.


Lemma age_twin {FA:Flat_alg A} :
  forall phi1 phi2 n phi1',
  comparable phi1 phi2 ->
  ageN n phi1 = Some phi1' ->
  exists phi2', ageN n phi2 = Some phi2' /\ comparable phi1' phi2'.
Proof.
intros until n; revert n phi1 phi2.
induction n; intros.
exists phi2.
split; trivial.
inversion H0.
subst phi1'.
trivial.
unfold ageN in H0.
simpl in H0.
revert H0; case_eq (age1 phi1); intros; try discriminate.
rename a into phi.
assert (exists ophi2, age phi2 ophi2 /\ comparable phi ophi2).
destruct (comparable_common_unit H) as [e [? ?]].
destruct (age1_join _ (join_comm H2) H0) as [eo [phi1'a [eof [? ?]]]].
destruct (age1_join _ H3 H4) as [phi2' [phi2'a [eof' [? ?]]]].
unfold age in H7. rewrite H6 in H7. symmetry in H7; inv H7.
rewrite H5 in H0. inv H0.
exists phi2'. split; auto.
apply common_unit_comparable; exists eo; split; auto.
destruct H2 as [ophi2 [? ?]].
specialize (IHn _ _ _ H3 H1).
destruct IHn as [phi2' [? ?]].
exists phi2'.
split; trivial.
unfold ageN.
simpl.
rewrite H2.
trivial.
Qed.

Lemma ageN_different {FA: Flat_alg A} : forall n phi phi', ageN (S n) phi = Some phi' ->
    ~ comparable phi phi'.
Proof.
   intros.
   intro.
   generalize (age_noetherian' phi); intros [k [[? [? ?]] H4]].
   assert (k <= n \/ k > n)%nat by lia.
   destruct H3.
   replace (S n) with (k + (S n - k))%nat in H by lia.
   destruct (ageN_compose' _ _ _ _ H) as [b [? ?]].
   rewrite H1 in H5; inv H5.
   replace (S n - k)%nat with (S (n-k))%nat in H6 by lia.
   unfold ageN in H6; simpl in H6. rewrite H2 in H6; inv H6.
   replace k with (S n + (k - S n))%nat in H1 by lia.
   destruct (ageN_compose' _ _ _ _ H1) as [c [? ?]].
   rewrite H in H5; inv H5.
   destruct (age_twin phi c _ _ H0 H1) as [b [? ?]].
   replace (S n + (k - S n))%nat with ((k - S n) + S n)%nat in H5 by lia.
   destruct (ageN_compose' _ _ _ _ H5) as [d [? ?]].
   rewrite H6 in H8; inv H8.
   clear - H9 H2.
   unfold ageN in H9; simpl  in H9; rewrite H2 in H9; inv H9.
Qed.

Lemma necR_comparable {FA: Flat_alg A} :
  forall w w', necR w w' -> comparable w w' -> w=w'.
Proof.
intros.
rewrite necR_evolve in H.
destruct H as [n H].
destruct n.
inv H; auto.
contradiction (ageN_different _ _ _ H); auto.
Qed.


Lemma sepcon_andp_prop :
  forall P Q R, (P * (!!Q && R) = !!Q && (P * R))%pred.
Proof.
intros.
apply pred_ext; intros w ?.
destruct H as [w1 [w2 [? [? [? ?]]]]].
split. apply H1.
exists w1; exists w2; split; [|split]; auto.
destruct H.
destruct H0 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; repeat split; auto.
Qed.

Lemma TT_sepcon_TT : (TT * TT = TT)%pred.
Proof.
intros.
apply pred_ext; intros w ?; auto.
destruct (join_ex_units w).
exists x; exists w; split; auto.
Qed.


Lemma join_exactly {FA:Flat_alg A}:
  forall w1 w2 w3, join w1 w2 w3 ->  (exactly w1 * exactly w2 = exactly w3)%pred.
Proof.
pose proof I.
intros.
unfold exactly.
apply pred_ext; intros w ?; simpl in *.
destruct H1 as (? & ? & J & (? & ? & ?) & (w2' & ? & ?)).
eapply join_ext_commut in J as (? & J & ?); eauto.
eapply join_comm, join_ext_commut in J as (? & J & ?); eauto.
destruct (nec_join H0 H1) as [a [b [J' [? ?]]]].
assert (w2'=a); subst.
 eapply necR_linear'; eauto.
 repeat match goal with H : ext_order _ _ |- _ => apply ext_level in H
                      | H : join _ _ _ |- _ => apply join_level in H as [] end; lia.
eapply join_comm, join_eq in J; eauto; subst.
do 2 eexists; eauto; etransitivity; eauto.

destruct H1 as (? & ? & ?).
eapply nec_join2 in H0 as (? & ? & J & ? & ?); eauto.
eapply ext_join_commut in J as (? & ? & ?); eauto.
do 3 eexists; eauto.
split; do 2 eexists; eauto.
Qed.

Lemma extend_sepcon_andp :
  forall P Q R, boxy extendM Q -> P * (Q && R) |-- Q && (P * R).
Proof.
intros.
intros ?w [?w [?w [? [? [? ?]]]]].
split.
rewrite <- H in H2.
eapply H2.
exists w0.
apply join_comm; auto.
exists w0; exists w1; auto.
Qed.
Arguments extend_sepcon_andp : clear implicits.

Lemma distrib_sepcon_andp :
  forall P Q R, P * (Q && R) |-- (P * Q) && (P * R).
Proof.
intros. intros w [w1 [w2 [? [? ?]]]].
destruct H1.
split; exists w1; exists w2; split; auto.
Qed.

Lemma modus_wand :
  forall P Q,  P * (P -* Q) |-- Q.
Proof.
intros.
intros w  [?w [?w [? [? ?]]]].
eapply H1; eauto.
Qed.

Lemma extend_sepcon :
  forall {Q R: pred A}, boxy extendM Q ->  Q * R |-- Q.
Proof.
intros.
intros w [w1 [w2 [? [? _]]]].
rewrite <- H in H1. eapply H1; eauto.
simpl; eauto.
exists w2; auto.
Qed.

Definition precise  (P: pred A) : Prop :=
     forall w w1 w2, P w1 -> P w2 -> join_sub w1 w -> join_sub w2 w -> w1=w2.

Definition precise2   (P: pred A) : Prop :=
     forall Q R, (P * (Q && R) = (P * Q) && (P * R))%pred.

(*Lemma precise_eq {CA: Canc_alg A}: precise =
                 fun P : pred A => forall Q R, (P * (Q && R) = (P * Q) && (P * R))%pred.
Proof.
extensionality P.
unfold precise.
apply prop_ext; split; intros.
apply pred_ext; unfold derives; intros; rename a into w.
destruct H0 as [phi1 [phi2 [? [? [? ?]]]]].
split; exists phi1; exists phi2; auto.
destruct H0 as [[phi1a [phi2a [? [? ?]]]] [phi1b [phi2b [? [? ?]]]]].
specialize (H w _ _ H1 H4).
spec H.
econstructor; eauto.
spec H.
econstructor; eauto.
subst phi1b.
generalize (join_canc (join_comm H0) (join_comm H3)).
intro; subst phi2b.
exists phi1a; exists phi2a; split; auto.
split; auto.
split; auto.
rename w1 into w1a.
rename w2 into w1b.
destruct H2 as [w2a ?].
destruct H3 as [w2b ?].
assert (((P * exactly w2a) && (P * exactly w2b)) w)%pred.
split; do 2 econstructor; repeat split;
try solve [simpl; do 2 eexists; [apply necR_refl | reflexivity]].
eassumption. auto. eassumption. auto.
rewrite <- H in H4.
destruct H4 as [w1 [w2 [? [? [? ?]]]]].
destruct H6 as (? & ? & ?), H7 as (? & ? & ?).
rewrite (necR_comparable _ _ H6) in H2.
rewrite (necR_comparable _ _ H7) in H3.
eapply join_canc; eauto.
apply comparable_trans with w.
apply join_comparable with w1b; auto.
apply comparable_sym; apply join_comparable with w1; auto.
apply comparable_trans with w.
apply join_comparable with w1a; auto.
apply comparable_sym; apply join_comparable with w1; auto.
Qed.*)

Lemma derives_precise :
  forall P Q, (P |-- Q) -> precise Q -> precise P.
Proof.
intros; intro; intros; eauto.
Qed.

(*Lemma precise_emp : precise emp.
Proof.
repeat intro.
eapply join_sub_same_identity with (a := w1)(c := w); auto.
apply identity_unit'; auto.
eapply join_sub_unit_for; eauto.
apply identity_unit'; auto.
Qed.*)

Definition superprecise  (P: pred A) :=
   forall w1 w2, P w1 -> P w2 -> comparable w1 w2 -> w1=w2.

(*Lemma superprecise_exactly : forall w, superprecise (exactly w).
Proof.
unfold superprecise; intros.
destruct H as (? & ? & ?), H0 as (? & ? & ?).
eapply necR_linear' in H; eauto; subst.
apply comparable_fashionR; auto.
Qed.
#[export] Hint Resolve superprecise_exactly : core.*)

(*Lemma superprecise_precise : forall (P: pred A) , superprecise P -> precise P.
Proof.
  pose proof I.
  unfold precise. unfold superprecise.
  intros.
  assert (comparable w1 w2). assert (comparable w1 w) by apply (join_sub_comparable H3).
  assert (comparable w w2).
    apply comparable_sym; destruct H4; eapply join_comparable; eauto.
    apply (comparable_trans H5 H6).
  apply (H0 _ _ H1 H2 H5).
Qed.*)

(* EXistential Magic Wand *)

Program Definition ewand  (P Q: pred A) : pred A :=
  fun w => forall w' w'', necR w w' -> ext_order w' w'' -> exists w1, exists w2, join w1 w'' w2 /\ P w1 /\ Q w2.
Next Obligation.
split; intros.
eapply H0; [|eauto].
eapply rt_trans, H1. apply rt_step; auto.

eapply nec_ext_commut in H as []; [|eauto].
eapply H0; eauto.
etransitivity; eauto.
Qed.

Lemma later_0 : forall a P, level a = 0 -> (|> P)%pred a.
Proof.
  repeat intro.
  apply age1_level0 in H.
  apply laterR_power_age in H0 as (? & ? & ? & ?); congruence.
Qed.

(*Lemma later_ewand  : forall P Q,
  (|>(ewand P Q) = ewand (|>P) (|>Q))%pred.
Proof.
intros.
apply pred_ext.
intros w ? ????.
apply nec_refl_or_later in H0 as [|].
subst w'.
case_eq (age1 w); intros.
eapply ext_age_compat in H1 as (? & ? & Hext); eauto.
specialize (H _ (t_step _ _ _ _ H0) _ _ (necR_refl _) Hext).
destruct H as [a1 [a2 [? [? ?]]]].
destruct (unage_join _ (join_comm H) H1) as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; split; [|split]; auto.
hnf; intros.
apply pred_nec_hereditary with a1; auto.
eapply age_later_nec; eauto.
hnf; intros.
apply pred_nec_hereditary with a2; auto.
eapply age_later_nec; eauto.
apply age1_level0 in H0.
apply ext_level in H1.
rewrite H0 in H1.
eexists _, _.
split.
apply core_unit.
split; apply later_0; auto.
rewrite level_core; auto.
specialize (H _ H0 _ _ (necR_refl _) H1).
destruct H as [a1 [a2 [? [? ?]]]].
do 3 eexists; eauto.
split; intros ??; eapply pred_nec_hereditary; try apply laterR_necR; eauto.

intros w ???????.
hnf in H.
destruct (H w' w'') as (? & ? & ? & ? & ?); auto.
{ eapply rt_trans, H1. apply laterR_necR; auto. }
eapply join_ext_commut in H2 as (? & ? & ?); eauto.
Search necR laterR.
intros w [w1 [w2 [? [? ?]]]].
intros w' ?.
hnf in H2. apply clos_trans_t1n in H2.
revert w1 w2 H H0 H1; induction H2; intros.
destruct (age1_join _ (join_comm H0) H) as [w1' [w2' [? [? ?]]]].
exists w1'; exists w2'; split; auto.
split.
eapply H1. hnf; apply clos_t1n_trans. constructor 1; auto.
eapply H2. hnf; apply clos_t1n_trans. constructor 1; auto.
destruct (age1_join _ (join_comm H0) H) as [w1' [w2' [? [? ?]]]].
apply (IHclos_trans_1n _ _ (join_comm H4)); auto; eapply pred_hereditary; eauto.
Qed.*)

Notation "P '-o' Q" := (ewand P Q) (at level 60, right associativity).

(*Lemma emp_ewand :
      forall P, ewand emp P = P.
Proof.
intros.
apply pred_ext; intros w ?.
specialize (H _ _ (necR_refl _) (ext_refl _)).
destruct H as [w1 [w2 [? [? ?]]]].
hnf in H0.
replace w with w2; auto.
eapply join_eq; eauto.
eapply identity_unit; eauto.
destruct (join_ex_identities w) as [e [He [? Hj]]].
exists e; exists w.
split; auto.
specialize (He _ _ Hj); subst; auto.
Qed.


Lemma pry_apart {CA: Canc_alg A}{DA: Disj_alg A}{CrA: Cross_alg A}:
  forall G P Q, superprecise G -> P = ewand G (G * P)%pred ->
                       (P * Q) && (G * TT) |-- (P * G * (ewand G Q)).
Proof.
 pose proof I. intros.
intros w [? ?].
destruct H2 as [w2 [w3 [? [? Hq]]]].
destruct H3 as [w4 [w5 [? [? _]]]].
rewrite H1 in H4.
destruct H4 as [wa [wb [? [? ?]]]].
assert (wa = w4). apply H0; auto.
apply comparable_trans with w2. apply join_comparable2 with wb; auto.
apply comparable_trans with w. apply join_comparable with w3; auto.
apply comparable_sym. apply join_comparable with w5; auto.
subst wa; clear H6.
destruct H7 as [w4' [w2' [? [? ?]]]].
assert (w4' = w4). apply H0; auto.
apply comparable_trans with wb. eapply join_comparable; eauto.
apply comparable_sym.  eapply join_comparable; eauto.
subst w4'; clear H7.
assert (w2' = w2). eapply join_canc; try apply join_comm; eauto.
subst w2'; clear H6.
destruct (CrA _ _ _ _ _ H2 H3) as [[[[w24 w25] w34] w35] [? [? [? ?]]]].
assert (identity w24).
  destruct (join_assoc (join_comm H9) H4) as [f [? ?]].
  destruct (join_assoc (join_comm H6) (join_comm H11)) as [g [? ?]].
  eapply join_self; eauto.
assert (w34=w4). eapply join_eq; [eapply identity_unit; eauto | auto ].
subst w34.
assert (w25 = w2). eapply join_eq; [eapply identity_unit; eauto | auto ].
subst w25.
clear H11 H9 H6 w24.
destruct (join_assoc (join_comm H10) (join_comm H3)) as [h [? ?]].
generalize (join_eq H6 (join_comm H4)); clear H6; intro; subst h.
destruct (join_assoc (join_comm H4) (join_comm H9)) as [h [? ?]].
generalize (join_eq H6 H7); clear H6; intro; subst h.
clear H11.
exists wb; exists w35.
split. apply join_comm; auto.
split; auto.
exists w2; exists w4; split; auto.
unfold ewand.
exists w4; exists w3; split; auto.
Qed.*)

Definition wk_split :=
      forall a b c d e : A, join a b c -> join d e c -> joins a d -> join_sub d b.

Lemma crosssplit_wkSplit {DA: Disj_alg A}{CrA: Cross_alg A}:
    wk_split.
Proof.
unfold wk_split; intros.
destruct (CrA _ _ _ _ _ H H0) as [[[[ad ae] bd] be] [myH1 [myH2 [myH3 myH4]]]].
destruct H1 as [x H_x].
assert (exists X, join ad X be) as [X HX].
2:{   exists X.
               destruct (join_assoc (join_comm HX) (join_comm myH2)) as [y [myH5 myH6]].
               assert (y=d) by apply (join_eq myH5 myH3).  subst y.
               apply (join_comm myH6).
}
destruct (join_assoc (join_comm myH1) H_x) as [y [myH5 myH6]].
destruct (join_assoc (join_comm myH3) (join_comm myH5)) as [? [Had ?]].
apply join_self in Had.
pose proof (Had _ _ myH1); subst.
destruct (join_assoc (join_comm myH1) myH4) as [? [Hbe ?]].
specialize (Had _ _ Hbe); subst; eauto.
Qed.

(*Lemma wk_pry_apart {CA: Canc_alg A}{DA: Disj_alg A}{CrA: Cross_alg A}:
  forall G P Q, wk_split -> superprecise G -> P = ewand G (G * P) ->
                       (P * Q) && (G * TT) |-- (P * G * (ewand G Q)).
Proof.
intros.
intros w [? ?]. unfold ewand.
destruct H2 as [w2 [w3 [? [? Hq]]]].
destruct H3 as [w4 [w5 [? [? _]]]].
rewrite H1 in H4.
destruct H4 as [wa [wb [? [? ?]]]].
assert (wa = w4). apply H0; auto.
apply comparable_trans with w2. eapply join_comparable2; eauto.
apply comparable_trans with w. eapply join_comparable; eauto.
apply comparable_sym.  eapply join_comparable; eauto.
subst wa; clear H6.
destruct H7 as [w4' [w2' [? [? ?]]]].
assert (w4' = w4). apply H0; auto.
apply comparable_trans with wb. eapply join_comparable; eauto.
apply comparable_sym.  eapply join_comparable; eauto.
subst w4'; clear H7.
assert (w2' = w2). eapply join_canc; try apply join_comm; eauto.
subst w2'; clear H6.
assert (exists y, join w2 y w5).
    destruct (H _ _ _ _ _ H2 H3 (join_joins (join_comm H4))).
    destruct (join_assoc H6 (join_comm H2)) as [y [myH1 myH2]].
    assert (y=w5) by apply (join_canc  (join_comm myH2) (join_comm H3)). subst y.
    exists x. apply (join_comm myH1).
exists wb.
destruct H6 as [y w2_y_w5].
               destruct (join_assoc w2_y_w5 (join_comm H3)) as [x [myH1 myH2]].
               destruct (join_assoc  (join_comm myH1) (join_comm myH2)) as [z [myH3 myH4]].
                                        assert (w5=z) by apply  (join_canc (join_comm H3) (join_comm myH4)). subst w5.
                                        assert (w3=x) by apply (join_canc (join_comm H2) (join_comm myH2)).  subst w3.
                                        destruct (join_assoc myH3 (join_comm myH4)) as [u [myH5 myH6]].
                                        assert (wb=u) by apply (join_eq H4 (join_comm myH5)). subst wb.
               exists y. split. apply (join_comm myH6).
               split. exists w2. exists w4. split. apply (join_comm H4). split; assumption.
               exists w4. exists x; split. apply (join_comm myH1). split; assumption.
Qed.

Lemma ewand_overlap {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{DA: Disj_alg A}{CrA: Cross_alg A}{AG: ageable A}{XA: Age_alg A}:
    forall (P Q: pred A),
       superprecise Q ->
       ewand TT (P * Q) * Q |-- ewand TT (P * Q).
Proof.
intros P Q PrecQ.
intros w [w1 [w2 [? [? ?]]]].
destruct H0 as [w5 [w6 [? [_ ?]]]].
destruct H2 as [w3 [w4 [? [? ?]]]].
generalize (PrecQ  _ _ H4 H1); clear H4; intro.
spec H4.
apply comparable_trans with w6.
apply join_comparable with w3; apply join_comm; auto.
apply comparable_trans with w1.
apply comparable_sym; apply join_comparable with w5; apply join_comm; auto.
eapply join_comparable2; eauto.
subst w4.
destruct (CrA _ _ _ _ _ H0 H2) as [[[[a b] c] d] [? [? [? ?]]]].
destruct (join_assoc H5 H) as [f [? ?]].
destruct (join_assoc H7 (join_comm H8)) as [g [? ?]].
generalize (join_self' H10); intro.
subst g.
assert (identity d).
eapply unit_identity; eauto.
assert (b=w2).
eapply join_canc; eauto.
subst b.
assert (f=w2).
eapply join_eq; eauto.
subst f.
clear H11 H10 H7.
assert (c=w1).
 specialize ( H12 c w1). apply H12. auto.
subst c.
clear H9 H5.
destruct (join_assoc H6 H2) as [h [? ?]].
generalize (join_eq H5 H); clear H5; intro; subst h.
exists a; exists w6; split; auto.
split; auto.
exists w3; exists w2; split; auto.
Qed.*)

Lemma ewand_derives :
  forall P P' Q Q',  (P |-- P') -> (Q |-- Q') -> ewand P Q |-- ewand P' Q'.
Proof.
intros.
intros w ? ????.
specialize (H1 _ _ H2 H3).
destruct H1 as [?w [?w [? [? ?]]]].
exists w0; exists w1; split; auto.
Qed.

(*Lemma ewand_sepcon : forall P Q R,
      (ewand (P * Q) R = ewand P (ewand Q R))%pred.
Proof.
intros; apply pred_ext; intros w ? ????.
destruct (H _ _ H0 H1) as [w1 [w2 [? [? ?]]]].
destruct H3 as [w3 [w4 [? [? ?]]]].
exists w3.
destruct (join_assoc (join_comm H3) H2) as [wf [? ?]].
exists wf.
split; [|split]; auto.
intros ????.
eapply nec_join2 in H7 as (? & ? & ? & ? & ?); eauto.
eapply ext_join_commut in H10 as (? & ? & ?); eauto.
eapply join_ext_commut in H1 as (? & ? & ?); eauto.
specialize (H 

exists w4. exists w2. split; auto.
destruct H as [w1 [w2 [? [? ?]]]].
destruct H1 as [w3 [w4 [? [? ?]]]].
destruct (join_assoc (join_comm H) (join_comm H1)) as [wf [? ?]].
exists wf. exists w4. split; [|split]; auto.
exists w1; exists w3; split; auto.
Qed.*)

(*Lemma ewand_sepcon_assoc {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{FA: Flat_alg A}{CrA: Cross_alg A}{AG: ageable A}{XA: Age_alg A}:
  Trip_alg A ->
  forall P Q R: pred A,
      (forall w1 w2 w3, join w1 w2 w3 -> P w3 -> P w1) ->
      (forall w w', comparable w w' -> P w -> R w' -> joins w w') ->
      ((ewand TT P) && (ewand TT R) |-- emp) ->
     (ewand P (Q * R) = (ewand P Q * R))%pred.
Proof.
intros TRIPLE P Q R ?H Hjoins ?H.
apply pred_ext; intros w ?.
destruct H1 as [w1 [w2 [? [? ?]]]].
destruct H3 as [w3 [w4 [? [? ?]]]].
destruct (CrA _ _ _ _ _ H1 H3) as [[[[? ?] ?] ?] [? [? [? ?]]]].
generalize (H _ _ _ (join_comm H6) H2); intro.
assert (emp a0).
apply H0.
split.
2:{ do 2 econstructor; (split; [|split]). 3: eauto. eauto. auto. }
exists a; exists w1; split; [|split]; eauto.
apply join_unit2_e in H6; auto.
subst a.
apply join_unit1_e in H9; auto.
subst a2.
exists a1; exists w4; split; [|split]; auto.
do 2 econstructor; eauto.
(*****)
destruct H1 as [w1 [wR [? [? ?]]]].
destruct H2 as [wP [wQ [? [? ?]]]].
apply join_comm in H2.
specialize (Hjoins wP wR).
spec Hjoins.
apply comparable_trans with w1; eapply join_comparable2; eauto.
destruct Hjoins as [w6 ?]; auto.
destruct (TRIPLE _ _ _ _ _ _ H1 (join_comm H6) H2) as [wQR ?].
exists wP. exists wQR.
split; [|split]; auto.
destruct (join_assoc H1 j) as [wf [? ?]].
generalize (join_eq H6 (join_comm H7)); clear H6; intros; subst w6.
destruct (join_assoc H7 (join_comm H8)) as [wg [? ?]].
generalize (join_eq H2 (join_comm H6)); clear H6; intros; subst wg.
do 2 econstructor; eauto.
Qed.


Lemma ewand_sepcon2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{DA: Disj_alg A}{CrA: Cross_alg A}{AG: ageable A}{XA: Age_alg A}:
      forall
          R (SP: superprecise R)
          P (H: P = ewand R (R * P))
          Q,
          ewand P (Q * R) |-- ewand P Q * R.
Proof.
intros.
intros w ?.
destruct H0 as [w1 [w34 [? [? [w3 [w4 [? [? ?]]]]]]]].
generalize (crosssplit_wkSplit  _ _ _ _ _ H0 (join_comm H2)); unfold wk_split; intro.
spec H5.
rewrite H in H1.
destruct H1 as [wa [wb [? [? ?]]]].
generalize (SP _ _ H6 H4); clear H4; intro.
spec H4.
apply comparable_trans with w34. apply comparable_trans with w1.
eapply join_comparable2; eauto. eapply join_comparable; eauto.
apply comparable_sym; eapply join_comparable; eauto.
subst wa.
destruct H7 as [wx [wy [? [? ?]]]].
generalize (SP _ _ H7 H6); clear H7; intro.
spec H7.
apply comparable_trans with wb.  eapply join_comparable; eauto.
apply comparable_sym; eapply join_comparable; eauto.
subst wx.
generalize (join_canc (join_comm H1) (join_comm H4)); clear H4; intro.
subst wy.
econstructor; eauto.
destruct H5 as [w5 ?].
exists w5; exists w4; split; [|split]; auto.
exists w1; exists w3; split; [|split]; auto.
destruct (join_assoc H5 (join_comm H0)) as [wf [? ?]].
generalize (join_canc (join_comm H7) H2); clear H7; intro.
subst wf.
auto.
Qed.*)

Lemma sepcon_andp_prop2 :
  forall P Q R,  (P * (!!Q && R) = !!Q && (P * R))%pred.
Proof.
intros.
apply pred_ext; intros w ?.
destruct H as [w1 [w2 [? [? [? ?]]]]].
split. apply H1.
exists w1; exists w2; split; [|split]; auto.
destruct H.
destruct H0 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; repeat split; auto.
Qed.

Lemma sepcon_andp_prop1 :
   forall (P: Prop) (Q R: pred A) , ((!! P && Q) * R = !! P && (Q * R))%pred.
Proof.
 intros. rewrite (sepcon_comm). rewrite sepcon_andp_prop2. rewrite sepcon_comm; auto.
Qed.

Lemma distrib_orp_sepcon :
  forall (P Q R : pred A), ((P || Q) * R = P * R || Q * R)%pred.
Proof.
 intros. apply pred_ext.
  intros w [w1 [w2 [? [[?|?] ?]]]]; [left|right]; exists w1; exists w2; repeat split; auto.
 intros ? [?|?];  destruct H as [w1 [w2 [? [? ?]]]]; exists w1; exists w2; repeat split; auto.
  left; auto. right; auto.
Qed.

Lemma distrib_orp_sepcon2:
  forall (P Q R : pred A),
     (R * (P || Q) = R * P || R * Q)%pred.
Proof.
intros. rewrite !(sepcon_comm R). apply distrib_orp_sepcon.
Qed.

Lemma ewand_conflict :
       forall P Q R, (sepcon P Q |-- FF) -> andp P (ewand Q R) |-- FF.
Proof.
 intros. intros w [HP Hwand].
 specialize (Hwand _ _ (necR_refl _) (ext_refl _)).
 destruct Hwand as [w1 [w2 [? [? ?]]]].
 apply (H w2). exists w; exists w1; repeat split; auto.
Qed.

(*Lemma ewand_TT_sepcon :
      forall P Q R,
(P * Q && ewand R (!!True))%pred |-- (P && ewand R (!!True) * (Q && ewand R (!!True)))%pred.
Proof.
intros.
intros w [[w1 [w2 [? [? ?]]]] Hwand].
exists w1; exists w2; repeat split; auto;
intros ?? Hnec Hext.
- eapply nec_join in Hnec as (? & ? & ? & ? & Hw); eauto.
  specialize (Hwand _ _ Hw (ext_refl _)).
  destruct Hwand as (? & ? & J & ? & _).
  Search ext_order join.
destruct (join_assoc (join_comm H) (join_comm H2)) as [f [? ?]].
exists w3; exists f; repeat split; auto.
destruct (join_assoc H (join_comm H2)) as [g [? ?]].
exists w3; exists g; repeat split; auto.
Qed.*)

End Predicates.

Notation "P '*' Q" := (sepcon P Q) : pred.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : pred.
Notation "'%' e"  := (box extendM e)(at level 30, right associativity): pred.
Notation "P '-o' Q" := (ewand P Q) (at level 60, right associativity).

#[export] Hint Resolve id_emp : core.
#[export] Hint Resolve extendM_refl : core.
#[export] Hint Resolve extend_later' : core.
