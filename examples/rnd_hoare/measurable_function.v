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