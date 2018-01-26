Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.predicates_sa.

Local Open Scope pred.

Definition corable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}
         (P: pred A) := forall w, P w = P (core w).

Lemma corable_spec: forall {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}
  (P: pred A),
    corable P = forall x y:A, core x = core y -> P x -> P y.
Proof.
  unfold corable; intros; apply prop_ext; split; intros.
  + rewrite H in H1 |- *.
    rewrite <- H0.
    auto.
  + pose proof core_idem w.
    pose proof (H _ _ H0).
    pose proof (H _ _ (eq_sym H0)).
    apply prop_ext; split; auto.
Qed.

Lemma corable_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall P Q, corable P -> corable Q -> corable (P && Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; intros [? ?]; split; congruence.
Qed.
Lemma corable_orp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall P Q, corable P -> corable Q -> corable (P || Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; (intros [?|?]; [left|right]; congruence).
Qed.
Lemma corable_allp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall {B: Type} (P:  B -> pred A) ,
      (forall b, corable (P b)) -> corable (allp P).
Proof.
 unfold corable, allp; intros.
 apply prop_ext; split; simpl; intros.
 rewrite <- H; auto. rewrite H; auto.
Qed.
Lemma corable_exp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall {B: Type} (P:  B -> pred A) ,
      (forall b, corable (P b)) -> corable (exp P).
Proof.
 unfold corable, exp; intros.
 apply prop_ext; split; simpl; intros;  destruct H0 as [b ?]; exists b.
 rewrite <- H; auto. rewrite H; auto.
Qed.
Lemma corable_prop{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall P, corable (prop P).
Proof.
 unfold corable, prop; intros.
 apply prop_ext; split; simpl; intros; auto.
Qed.

Lemma corable_imp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} :
  forall P Q, corable P -> corable Q -> corable (P --> Q).
Proof.
  intros.
  rewrite corable_spec in H, H0 |- *.
  unfold imp in *.
  simpl in *.
  intros.
  eapply H0; eauto.
Qed.

Lemma corable_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall P Q, corable P -> corable Q -> corable (P * Q).
Proof.
  intros.
  rewrite corable_spec in H, H0 |- *.
  unfold sepcon.
  intros.
  simpl in H2 |- *.
  destruct H2 as [x' [x'' [? [? ?]]]].
  pose proof join_core H2.
  pose proof join_core (join_comm H2).
  exists (core y), y.
  repeat split.
  + apply core_unit.
  + apply H with x'; auto.
    rewrite core_idem.
    congruence.
  + apply H0 with x''; auto.
    congruence.
Qed.

Lemma corable_wand: forall {A:Type} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} (P Q: pred A), corable P -> corable Q -> corable (P -* Q).
Proof.
  intros.
  rewrite corable_spec in H, H0 |- *.
  unfold wand in *.
  simpl in *.
  intros.
  pose proof join_core H3.
  pose proof join_core (join_comm H3).
  apply H0 with x; [congruence |].
  apply (H2 (core x) x).
  + apply core_unit.
  + apply H with x0; auto.
    rewrite core_idem.
    congruence.
Qed.

Lemma corable_andp_sepcon1{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
   forall P Q R, corable P ->  (P && Q) * R = P && (Q * R).
Proof.
intros.
apply pred_ext.
intros w [w1 [w2 [? [[? ?] ?]]]].
split.
apply join_core in H0.
rewrite H in H1|-*. rewrite <- H0; auto.
exists w1; exists w2; split; [| split]; auto.
intros w [? [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; split; [|split]; auto.
split; auto.
apply join_core in H1.
rewrite H in H0|-*. rewrite H1; auto.
Qed.
