Require Import Coq.Sets.Ensembles.
Require Import RndHoare.random_oracle.
Require Import RndHoare.imperative.
Require Import RndHoare.measure.

Local Open Scope R.

Record RandomDistribution {ora: RandomOracle}: Type := {
  raw_ms: Measure (RandomHistory);
  pr_universe:
    measure_function _ raw_ms (Full_MSet _) = 1;
  ms_consi1:
    forall (P: Ensemble RandomHistory) h1 h2 n a,
      history_coincide n h1 h2 ->
      h1 n = None ->
      h2 n = Some a ->
      P h1 ->
      P h2 ->
      ~ measurable _ raw_ms P;
  ms_consi2:
    forall (P: Ensemble RandomHistory) h1 h2 n a1 a2,
      history_coincide n h1 h2 ->
      h1 n = Some a1 ->
      h2 n = Some a2 ->
      projT1 a1 <> projT1 a2 ->
      P h1 ->
      P h2 ->
      ~ measurable _ raw_ms P;
  pr_consi:
    forall (P1 P2: measurable_set raw_ms),
      (forall h1 h_inf,
        P1 h1 ->
        infinite_history h_inf ->
        prefix_history h1 h_inf ->
        exists h2, prefix_history h1 h2 /\ prefix_history h2 h_inf /\ P2 h2) ->
      measure_function _ raw_ms P1 = measure_function _ raw_ms P2
}.

(* TODO: Axiom/Theorem: Any ensemble on terminating states are measurable. *)

(* TODO: so, the overall probability of an event of terminating states is well defined. *)

Goal forall (A: Type) (P: A -> Prop) (a: A) (F: {a: A | P a} -> Prop), Prop.
intros.
refine (~ P a \/ exists Pr: P a, F (exist _ a Pr)).
Defined.
Print Unnamed_thm.

