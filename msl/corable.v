Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_sl.

Local Open Scope pred.

Definition corable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
         (P: pred A) := forall w, P w = P (core w).

Lemma corable_spec: forall {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
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

Lemma corable_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, corable P -> corable Q -> corable (P && Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; intros [? ?]; split; congruence.
Qed.
Lemma corable_orp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, corable P -> corable Q -> corable (P || Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; (intros [?|?]; [left|right]; congruence).
Qed.
Lemma corable_allp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall {B: Type} (P:  B -> pred A) ,
      (forall b, corable (P b)) -> corable (allp P).
Proof.
 unfold corable, allp; intros.
 apply prop_ext; split; simpl; intros.
 rewrite <- H; auto. rewrite H; auto.
Qed.
Lemma corable_exp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall {B: Type} (P:  B -> pred A) ,
      (forall b, corable (P b)) -> corable (exp P).
Proof.
 unfold corable, exp; intros.
 apply prop_ext; split; simpl; intros;  destruct H0 as [b ?]; exists b.
 rewrite <- H; auto. rewrite H; auto.
Qed.
Lemma corable_prop{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P, corable (prop P).
Proof.
 unfold corable, prop; intros.
 apply prop_ext; split; simpl; intros; auto.
Qed.

Lemma corable_imp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} {agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, corable P -> corable Q -> corable (P --> Q).
Proof.
  intros.
  rewrite corable_spec in H, H0 |- *.
  unfold imp in *.
  simpl in *.
  intros.
  rename a' into y'.
  pose proof H3.
  apply necR_power_age in H5.
  destruct H5 as [n ?H].
  destruct (power_age_parallel' _ y' _ n (eq_sym H1) H5) as [x' [?H ?H]].
  apply (H0 _ _ (eq_sym H7)).
  apply H2.
  + apply necR_power_age; exists n; auto.
  + apply (H _ _ H7); auto.
Qed.

Lemma corable_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
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

Lemma corable_wand: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} (P Q: pred A), corable P -> corable Q -> corable (P -* Q).
Proof.
  intros.
  rewrite corable_spec in H, H0 |- *.
  unfold wand in *.
  simpl in *.
  intros.
  rename x' into y'.
  rename y0 into w'.
  rename z into z'.
  apply necR_power_age in H3.
  destruct H3 as [n ?H].
  pose proof power_age_parallel' _ y' _ n (eq_sym H1) H3.
  destruct H6 as [x' [?H ?H]].
  pose proof join_core H4.
  pose proof join_core (join_comm H4).
  apply H0 with x'; [congruence |].
  apply (H2  x' (core x') x').
  + apply necR_power_age.
    exists n; auto.
  + apply join_comm, core_unit.
  + apply H with w'; auto.
    rewrite core_idem.
    congruence.
Qed.

Lemma corable_later: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} P, corable P -> corable (|> P).
Proof.
  intros.
  rewrite corable_spec in H |- *.
  intros.
  unfold box in *.
  simpl in *.
  intros.
  apply laterR_power_age in H2.
  destruct H2 as [n ?H].
  rename a' into y'.
  destruct (power_age_parallel' _ y' _ _ (eq_sym H0) H2) as [x' [? ?]].
  apply H with x'; auto.
  apply H1.
  apply laterR_power_age.
  exists n; auto.
Qed.

Hint Resolve corable_andp corable_orp corable_allp corable_exp
                    corable_imp corable_prop corable_sepcon corable_wand corable_later : core.

Lemma corable_andp_sepcon1{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
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

(* The following 3 lemmas should not be necessary *)
Lemma corable_andp_sepcon2{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
   forall P Q R, corable P ->  (Q && P) * R = P && (Q * R).
Proof.
intros. rewrite andp_comm. apply corable_andp_sepcon1. auto.
Qed.

Lemma corable_sepcon_andp1 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
   forall P Q R, corable P ->  Q  * (P && R) = P && (Q * R).
Proof.
intros. rewrite sepcon_comm. rewrite corable_andp_sepcon1; auto. rewrite sepcon_comm; auto.
Qed.

Lemma corable_sepcon_andp2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
   forall P Q R, corable P ->  Q  * (R && P) = P && (Q * R).
Proof.
intros. rewrite sepcon_comm. rewrite andp_comm. rewrite corable_andp_sepcon1; auto. rewrite sepcon_comm; auto.
Qed.

(* This hint doesn't work well, hence the extra clauses in normalize1 and normalize1_in *)
Hint Rewrite @corable_andp_sepcon1 @corable_andp_sepcon2
                    @corable_sepcon_andp1 @corable_sepcon_andp2 using solve [auto with normalize typeclass_instances] : core.