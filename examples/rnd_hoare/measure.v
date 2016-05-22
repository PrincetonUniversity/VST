Require Export Coq.Reals.Rdefinitions.
Require Export Coq.Reals.Rfunctions.
Require Import Coq.Sets.Ensembles.

Local Open Scope R.

Definition Countable_Union (A: Type) (P: nat -> Ensemble A) : Ensemble A :=
  fun x => exists i, P i x.

Definition Non_Empty {U: Type} (A: Ensemble U): Prop := exists x, A x.

Definition unsig_Set {U: Type} {P: U -> Prop} (A: Ensemble {x: U | P x}): Ensemble U := fun x => exists H: P x, A (exist _ x H).

Definition sig_Set {U: Type} (Q P: Ensemble U): Ensemble {x: U | P x} := fun x => Q (proj1_sig x).

Record SigmaAlgebra (Omega: Type): Type := {
  measurable: Ensemble Omega -> Prop;
  universal_set_measurable: measurable (Full_set _);
  complement_measurable: forall P, measurable P -> measurable (Complement _ P);
  countable_union_measurable: forall P: nat -> Ensemble Omega, (forall i, measurable (P i)) -> measurable (Countable_Union _ P)
}.

Definition measurable_set {Omega: Type} (sa: SigmaAlgebra Omega): Type := {x: Ensemble Omega | measurable Omega sa x}.

Definition MSet_Ensemble {Omega: Type} {sa: SigmaAlgebra Omega} (P: measurable_set sa): Ensemble Omega := proj1_sig P.
Global Coercion MSet_Ensemble: measurable_set >-> Ensemble.

Definition In_MSet {Omega: Type} {sa: SigmaAlgebra Omega} (P: measurable_set sa) (x: Omega) : Prop := proj1_sig P x.
Global Coercion In_MSet: measurable_set >-> Funclass.

Definition Countable_Union_MSet {Omega: Type} (sa: SigmaAlgebra Omega) (x: nat -> measurable_set sa): measurable_set sa :=
  exist _
   (Countable_Union _ (fun i => x i))
   (countable_union_measurable Omega sa _ (fun i => proj2_sig _)).

Definition Full_MSet {Omega: Type} (sa: SigmaAlgebra Omega): measurable_set sa :=
  exist _
   (Full_set _)
   (universal_set_measurable _ _).

Record Measure (Omega: Type): Type := {
  mset :> SigmaAlgebra Omega;
  measure_function: measurable_set mset -> R;
  coutable_addictive:
    forall P: nat -> measurable_set mset,
      (forall i j, i <> j -> Disjoint _ (P i) (P j)) ->
      infinite_sum (fun i => measure_function (P i)) (measure_function (Countable_Union_MSet _ P))
}.

Record ProbabilitySpace (Omega: Type): Type := {
  PS_MS :> Measure Omega;
  universe_measure_1: measure_function _ PS_MS (Full_MSet _) = 1
}.

(* This does not require measures to be complete, i.e. 0-measure set's subset can be unmeasurable. *)
Class PartialRegularProbabilitySpace (Omega: Type): Type := {
  measurable_subspace: (Ensemble Omega) -> Prop;
  sub_measure: forall (P: Ensemble Omega | measurable_subspace P), ProbabilitySpace {o: Omega | proj1_sig P o};
  pos_measurable_subspace: forall (LP: Ensemble Omega | measurable_subspace LP) Q (QP: measurable_set (sub_measure LP)),
    let P := proj1_sig LP in
    Included _ Q P ->
    Same_set _ QP (sig_Set Q P) ->
    measure_function _ (sub_measure LP) QP > 0 ->
    measurable_subspace Q;
  measurable_trans: forall LP LQ R,
    let P := proj1_sig LP in
    let Q := proj1_sig LQ in
    Included _ Q P ->
    Included _ R Q ->
    measurable _ (sub_measure LP) (sig_Set Q P) ->
    (measurable _ (sub_measure LQ) (sig_Set R Q) <->
     measurable _ (sub_measure LP) (sig_Set R P));
  measure_trans: forall LP LQ R (QP: measurable_set (sub_measure LP)) (RP: measurable_set (sub_measure LP)) (RQ: measurable_set (sub_measure LQ)),
    let P := proj1_sig LP in
    let Q := proj1_sig LQ in
    Included _ Q P ->
    Included _ R Q ->
    Same_set _ QP (sig_Set Q P) ->
    Same_set _ RQ (sig_Set R Q) ->
    Same_set _ RP (sig_Set R P) ->
    measure_function _ (sub_measure LP) QP *
    measure_function _ (sub_measure LQ) RQ =
    measure_function _ (sub_measure LP) RP
}.

