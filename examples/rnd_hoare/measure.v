Require Export Coq.Reals.Rdefinitions.
Require Export Coq.Reals.Rfunctions.
Require Import Coq.Sets.Ensembles.

Local Open Scope R.

Definition Countable_Union (A: Type) (P: nat -> Ensemble A) : Ensemble A :=
  fun x => exists i, P i x.

Record AlphaAlgebra (Omega: Type): Type := {
  measurable: Ensemble Omega -> Prop;
  universal_set_measurable: measurable (Full_set _);
  complement_measurable: forall P, measurable P -> measurable (Complement _ P);
  countable_union_measurable: forall P: nat -> Ensemble Omega, (forall i, measurable (P i)) -> measurable (Countable_Union _ P)
}.

Definition measurable_set {Omega: Type} (aa: AlphaAlgebra Omega): Type := {x: Ensemble Omega | measurable Omega aa x}.

Definition In_MSet {Omega: Type} {aa: AlphaAlgebra Omega} (P: measurable_set aa) (x: Omega) : Prop := proj1_sig P x.

Global Coercion In_MSet: measurable_set >-> Funclass.

Definition Countable_Union_MSet {Omega: Type} (aa: AlphaAlgebra Omega) (x: nat -> measurable_set aa): measurable_set aa :=
  exist _
   (Countable_Union _ (fun i => proj1_sig (x i)))
   (countable_union_measurable Omega aa _ (fun i => proj2_sig _)).

Definition Full_MSet {Omega: Type} (aa: AlphaAlgebra Omega): measurable_set aa :=
  exist _
   (Full_set _)
   (universal_set_measurable _ _).

Record Measure (Omega: Type): Type := {
  mset :> AlphaAlgebra Omega;
  measure_function: measurable_set mset -> R;
  coutable_addictive:
    forall P: nat -> measurable_set mset,
      (forall i j, i <> j -> Disjoint _ (P i) (P j)) ->
      infinite_sum (fun i => measure_function (P i)) (measure_function (Countable_Union_MSet _ P))
}.


