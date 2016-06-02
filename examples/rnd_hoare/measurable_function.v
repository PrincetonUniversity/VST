Require Export Coq.Classes.Morphisms.
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
Admitted.

Lemma PreImage_Countable_Union_comm: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (PB: nat -> measurable_set B),
  Same_MSet (PreImage_MSet f (Countable_Union_MSet PB)) (Countable_Union_MSet (fun n => PreImage_MSet f (PB n))).
Admitted.

Lemma PreImage_Disjoint: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (PB1 PB2: measurable_set B),
  Disjoint B PB1 PB2 ->
  Disjoint A (PreImage_MSet f PB1) (PreImage_MSet f PB2).
Admitted.

Lemma PreImage_Full: forall  {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B),
  Same_MSet (PreImage_MSet f (Full_MSet B)) (Full_MSet A).
Admitted.

Require Import Coq.Logic.Classical.
Require Import Coq.Reals.Rdefinitions.

Local Open Scope R.

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
    eapply is_measurable_set_proper.
    instantiate (1 := fun a => P a /\ P0 b1 \/ ~ P a /\ P0 b0).
    - split; hnf; unfold In; simpl; intros.
      * pose proof (H b0).
        pose proof (H b1).
        tauto.
      * destruct H0 as [[? ?] | [? ?]]; subst; tauto.
    - admit.
Defined.

Definition IndicatorR {A: Type} {sA: SigmaAlgebra A} (P: measurable_set A): MeasurableFunction A R := Indicator P 0 1.

Lemma Indicator_True: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (P: measurable_set A) (b0 b1: B) (a: A), P a -> Indicator P b0 b1 a b1.
Proof. intros; simpl; auto. Qed.

Lemma Indicator_False: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (P: measurable_set A) (b0 b1: B) (a: A), ~ P a -> Indicator P b0 b1 a b0.
Proof. intros; simpl; auto. Qed.

