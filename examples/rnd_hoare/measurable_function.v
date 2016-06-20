Require Import RndHoare.sigma_algebra.

Record MeasurableFunction (A B: Type) {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} : Type := {
  raw_function: A -> B -> Prop;
  rf_functionality: forall a b1 b2, raw_function a b1 -> raw_function a b2 -> b1 = b2;
  rf_complete: forall a, exists b, raw_function a b;
  rf_preserve: forall (P: measurable_set B), is_measurable_set (fun a => forall b, raw_function a b -> P b)
}.

Definition MeasurableFunction_raw_function {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B): A -> B -> Prop := raw_function _ _ f.

Coercion MeasurableFunction_raw_function: MeasurableFunction >-> Funclass.

Definition PreImage_MSet {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (PB: measurable_set B): measurable_set A := exist _ _ (rf_preserve A B f PB).

Instance PreImage_MSet_Proper {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B): Proper (Same_MSet ==> Same_MSet) (PreImage_MSet f).
Proof.
  hnf; intros.
  unfold Same_MSet in *; simpl in *.
  rewrite Same_set_spec in *.
  intros a.
  hnf in H.
  firstorder.
  + apply H.
    apply H0; auto.
  + apply H.
    apply H0; auto.
Qed.

Lemma PreImage_Countable_Union_comm: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (PB: nat -> measurable_set B),
  Same_MSet (PreImage_MSet f (Countable_Union_MSet PB)) (Countable_Union_MSet (fun n => PreImage_MSet f (PB n))).
Proof.
  intros.
  unfold Same_MSet; simpl.
  rewrite Same_set_spec; intros a.
  split; intros.
  + destruct (rf_complete _ _ f a) as [b ?].
    specialize (H b H0).
    destruct H as [i ?].
    exists i; intros.
    pose proof (rf_functionality _ _ f a b b0 H0 H1).
    subst; auto.
  + destruct H as [i ?]; exists i.
    apply (H b); auto.
Qed.

Lemma PreImage_Disjoint: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (PB1 PB2: measurable_set B),
  Disjoint B PB1 PB2 ->
  Disjoint A (PreImage_MSet f PB1) (PreImage_MSet f PB2).
Admitted.

Lemma PreImage_Full: forall  {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B),
  Same_MSet (PreImage_MSet f (Full_MSet B)) (Full_MSet A).
Admitted.

Definition ConstantFunction {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (b0: B): MeasurableFunction A B.
  apply (Build_MeasurableFunction _ _ _ _ (fun a b => b = b0)).
  + intros.
    congruence.
  + intros.
    exists b0; auto.
  + intros.
    destruct (classic (P b0)).
    - eapply is_measurable_set_proper; [| apply full_measurable].
      split; hnf; unfold In; simpl; intros.
      * constructor.
      * subst; auto.
    - eapply is_measurable_set_proper; [| apply complement_measurable; apply full_measurable].
      split; hnf; unfold Complement, In; simpl; intros.
      * specialize (H0 b0); exfalso; auto.
      * exfalso; apply H0; constructor.
Defined.

Definition Indicator {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (P: measurable_set A) (b0 b1: B): MeasurableFunction A B.
  apply (Build_MeasurableFunction _ _ _ _ (fun a b => P a /\ b = b1 \/ ~ P a /\ b = b0)).
  + intros.
    destruct H as [[? ?] | [? ?]], H0 as [[? ?] | [? ?]]; try tauto; subst; auto.
  + intros.
    destruct (classic (P a)).
    - exists b1; left.
      auto.
    - exists b0; right.
      auto.
  + intros.
    destruct (classic (P0 b1)), (classic (P0 b0)).
    - eapply is_measurable_set_proper; [| apply full_measurable].
      split; hnf; unfold In; simpl; intros.
      * constructor.
      * destruct H2 as [[? ?] | [? ?]]; subst; auto.
    - eapply is_measurable_set_proper; [| apply (proj2_sig P)].
      split; hnf; unfold In; simpl; intros.
      * specialize (H1 b0).
        assert (b0 <> b1) by (intro; subst; auto).
        destruct (classic (P x)); tauto.
      * destruct H2 as [[? ?] | [? ?]]; subst; tauto.
    - eapply is_measurable_set_proper; [| apply complement_measurable; apply (proj2_sig P)].
      split; hnf; unfold Complement, In; simpl; intros.
      * specialize (H1 b1).
        assert (b1 <> b0) by (intro; subst; auto).
        tauto.
      * destruct H2 as [[? ?] | [? ?]]; subst; tauto.
    - eapply is_measurable_set_proper; [| apply complement_measurable; apply full_measurable].
      split; hnf; unfold Complement, In; simpl; intros.
      * pose proof (H1 b0).
        pose proof (H1 b1).
        tauto.
      * exfalso; apply H1; constructor.
Defined.

Lemma Indicator_True: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (P: measurable_set A) (b0 b1: B) (a: A), P a -> Indicator P b0 b1 a b1.
Proof. intros; simpl; auto. Qed.

Lemma Indicator_False: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (P: measurable_set A) (b0 b1: B) (a: A), ~ P a -> Indicator P b0 b1 a b0.
Proof. intros; simpl; auto. Qed.

Definition Compose {A B C: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} {sC: SigmaAlgebra C} (g: MeasurableFunction B C) (f: MeasurableFunction A B): MeasurableFunction A C.
  apply (Build_MeasurableFunction _ _ _ _ (fun a c => exists b, f a b /\ g b c)).
  + intros ? ? ? [? [? ?]] [? [? ?]].
    pose proof (rf_functionality _ _ f _ _ _ H H1); subst x0.
    pose proof (rf_functionality _ _ g _ _ _ H0 H2); auto.
  + intros.
    destruct (rf_complete _ _ f a) as [b ?].
    destruct (rf_complete _ _ g b) as [c ?].
    exists c, b; auto.
  + intros.
    pose proof rf_preserve _ _ g P.
    pose proof rf_preserve _ _ f (exist _ _ H).
    eapply is_measurable_set_proper; [| eassumption].
    split; hnf; unfold In; simpl; intros.
    - apply H1; exists b; auto.
    - destruct H2 as [? [? ?]].
      apply (H1 x0); auto.
Defined.

Require Import Coq.Reals.Rdefinitions.

Local Open Scope R.

Definition IndicatorR {A: Type} {sA: SigmaAlgebra A} (P: measurable_set A): MeasurableFunction A R := Indicator P 0 1.

