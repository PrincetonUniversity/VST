Require Export Coq.Reals.Rdefinitions.
Require Export Coq.Reals.Rfunctions.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.

Local Open Scope R.

Record Measure (Omega: Type) {sigma: SigmaAlgebra Omega}: Type := {
  measure_function: measurable_set Omega -> R;
  measure_function_proper: Proper (Same_MSet ==> eq) measure_function;
  coutable_addictive:
    forall P: nat -> measurable_set Omega,
      (forall i j, i <> j -> Disjoint _ (P i) (P j)) ->
      infinite_sum (fun i => measure_function (P i)) (measure_function (Countable_Union_MSet P))
}.

Global Existing Instance measure_function_proper.

Definition Measure_measure_function {Omega: Type} {sigma: SigmaAlgebra Omega} (m: Measure Omega): measurable_set Omega -> R := measure_function _ m.

Coercion Measure_measure_function: Measure >-> Funclass.

Definition GeneratedMeasure {A B} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (mA: Measure A): Measure B.
  apply (Build_Measure _ _ (fun PB => mA (PreImage_MSet f PB))).
  + hnf; simpl; intros.
    apply measure_function_proper.
    apply PreImage_MSet_Proper; auto.
  + intros.
    destruct mA as [mA ?H ?H]; simpl in *.
    specialize (H1 (fun n => PreImage_MSet f (P n))).
    rewrite PreImage_Countable_Union_comm.
    apply H1.
    clear - H.
    intros.
    specialize (H i j H0).
    apply PreImage_Disjoint; auto.
Defined.

Lemma GeneratedMeasure_spec: forall {A B} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (mA: Measure A) (PB: measurable_set B),
  mA (PreImage_MSet f PB) = (GeneratedMeasure f mA) PB.
Proof.
  intros.
  reflexivity.
Qed.

Parameter Lebegue_Int: forall {Omega: Type} {sigma: SigmaAlgebra Omega} (f: MeasurableFunction Omega R) (m: Measure Omega), R.

Axiom Int_Indicator: forall {Omega: Type} {sigma: SigmaAlgebra Omega} (P: measurable_set Omega) (m: Measure Omega), Lebegue_Int (IndicatorR P) m = m P.

Record ProbabilityMeasure (Omega: Type) {sigma: SigmaAlgebra Omega}: Type := {
  PS_MS :> Measure Omega;
  universe_measure_1: PS_MS (Full_MSet _) = 1
}.

Definition ProbabilityMeasure_measure_function {Omega: Type} {sigma: SigmaAlgebra Omega} (m: ProbabilityMeasure Omega): measurable_set Omega -> R := measure_function _ (PS_MS _ m).

Coercion ProbabilityMeasure_measure_function: ProbabilityMeasure >-> Funclass.

Definition GeneratedProbabilityMeasure {A B} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (mA: ProbabilityMeasure A): ProbabilityMeasure B.
  destruct mA as [mA ?H].
  apply (Build_ProbabilityMeasure _ _ (GeneratedMeasure f mA)).
  rewrite <- GeneratedMeasure_spec.
  rewrite PreImage_Full; auto.
Defined.

Definition Probability {A} {sA: SigmaAlgebra A} (mA: ProbabilityMeasure A) (P: measurable_set A): R := mA P.

Definition Expectation {A} {sA: SigmaAlgebra A} (mA: ProbabilityMeasure A) (f: MeasurableFunction A R): R := Lebegue_Int f mA.

