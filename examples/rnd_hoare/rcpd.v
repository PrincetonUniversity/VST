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
  
Class ProbabilityMeasure (Omega: Type) {sigma: SigmaAlgebra Omega}: Type := {
  PS_MS :> Measure Omega;
  universe_measure_1: PS_MS (Full_MSet _) = 1
}.

(* This does not require measures to be complete, i.e. 0-measure set's subset can be unmeasurable. *)
Class PartialRegularProbabilitySpace (Omega: Type): Type := {
  is_measurable_subspace: (Ensemble Omega) -> Prop;
  sub_measure: forall (P: Ensemble Omega | is_measurable_subspace P), ProbabilityMeasure {o: Omega | proj1_sig P o}
}.
  pos_measurable_subspace: forall (LP: Ensemble Omega | is_measurable_subspace LP) Q (QP: measurable_set (sub_measure LP)),
    let P := proj1_sig LP in
    Included _ Q P ->
    Same_set _ QP (sig_Set Q P) ->
    measure_function _ (sub_measure LP) QP > 0 ->
    is_measurable_subspace Q;
  measurable_subset_measurable: forall (LP: Ensemble Omega | is_measurable_subspace LP) (LQ: Ensemble Omega | is_measurable_subspace LQ),
    let P := proj1_sig LP in
    let Q := proj1_sig LQ in
    Included _ Q P ->
    is_measurable_set _ (sub_measure LP) (sig_Set Q P);
  measurable_trans: forall LP LQ R,
    let P := proj1_sig LP in
    let Q := proj1_sig LQ in
    Included _ Q P ->
    Included _ R Q ->
    is_measurable_set _ (sub_measure LP) (sig_Set Q P) ->
    (is_measurable_set _ (sub_measure LQ) (sig_Set R Q) <->
     is_measurable_set _ (sub_measure LP) (sig_Set R P));
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

