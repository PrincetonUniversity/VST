Require Export Coq.Reals.Rdefinitions.
Require Export Coq.Reals.Rfunctions.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.probability_measure.

Local Open Scope R.

Class ProbabilityMeasureFamily (Omega: Type): Type := {
  is_measurable_subspace: (Ensemble Omega) -> Prop;
  sub_sigma_algebra: forall (P: Ensemble Omega | is_measurable_subspace P), SigmaAlgebra {o: Omega | proj1_sig P o};
  sub_measure: forall (P: Ensemble Omega | is_measurable_subspace P), ProbabilityMeasure {o: Omega | proj1_sig P o}
}.

Module PrFamily.

Section ProbabilityMeasureFamily.

Context {U: Type} {PMF: ProbabilityMeasureFamily U}.

Definition measurable_subspace: Type := {Omega: Ensemble U | is_measurable_subspace Omega}.

Definition measurable_subspace_Ensemble: measurable_subspace -> Ensemble U := @proj1_sig _ _.

Global Coercion measurable_subspace_Ensemble: measurable_subspace >-> Ensemble.

Definition measurable_subspace_Prop: measurable_subspace -> U -> Prop := @proj1_sig _ _.

Global Coercion measurable_subspace_Prop: measurable_subspace >-> Funclass.

Definition is_measurable_set (P: Ensemble U) (Omega: measurable_subspace) := @is_measurable_set {x: U | Omega x} (sub_sigma_algebra Omega) (sig_Set P Omega).

Definition measurable_set (Omega: measurable_subspace): Type := {P: Ensemble U | is_measurable_set P Omega}.

Definition measurable_set_inj {Omega: measurable_subspace} (P: measurable_set Omega): @sigma_algebra.measurable_set _ (sub_sigma_algebra Omega).
  destruct Omega as [Omega ?H], P as [P ?H].
  unfold is_measurable_set in H0.
  simpl in *.
  exact (exist _ _ H0).
Defined.

Record MeasurableFunction (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B}: Type := {
  raw_function: U -> B -> Prop;
  rf_partial_functionality: forall a b1 b2, raw_function a b1 -> raw_function a b2 -> b1 = b2;
  rf_complete: forall a, Omega a -> exists b, raw_function a b;
  rf_sound: forall a b, raw_function a b -> Omega a;
  rf_preserve: forall (P: sigma_algebra.measurable_set B), is_measurable_set (fun a => forall b, raw_function a b -> P b) Omega
}.

Definition MeasurableFunction_raw_function (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B): U -> B -> Prop := raw_function _ _ f.

Global Coercion MeasurableFunction_raw_function: MeasurableFunction >-> Funclass.


Definition Probability {Omega: measurable_subspace} (P: measurable_set Omega): R := Probability (sub_measure Omega) (measurable_set_inj P).

Definition Probability {Omega: measurable_subspace} (P: measurable_set Omega): R := Probability (sub_measure Omega) (measurable_set_inj P).


{ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomHistory -> Prop | is_measurable_subspace P) (Q: measurable_set P): R :=
  measure_function _
   (sub_measure P)
   (exist _ (sig_Set (proj1_sig Q) (proj1_sig P)) (proj2 (proj2_sig Q))).


Class IsDisintegration {OMEGA} {UD: UniformDisintegration OMEGA} (Omega: Ensemble OMEGA | is_measurable_subspace Omega) {A: Type} {SA: SigmaAlgebra A} (pi: MeasurableFunction {o: OMEGA | proj1_sig Omega o} A) (A1: measurable_set A): Type := {
  defined_almost_everywhere: GeneratedProbabilityMeasure pi (sub_measure Omega) A1 = 1;
  defined_MSS: forall a, A1 a -> is_measurable_subspace (unsig_Set (fun o => pi o a));
  defined_MS: forall a (def: A1 a) (E: @measurable_set {o: OMEGA | proj1_sig Omega o} (@sub_sigma_algebra OMEGA UD Omega)), @is_measurable_set _ (sub_sigma_algebra (exist _ _ (defined_MSS a def))) (sig_Set (unsig_Set E) (unsig_Set (fun o => pi o a)))
}.


