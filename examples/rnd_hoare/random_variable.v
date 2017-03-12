Require Import Coq.Sets.Ensembles.
Require Import RndHoare.random_oracle.
Require Import RndHoare.max_anti_chain.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.

Class HistoryBasedSigF (ora: RandomOracle) {SFo: SigmaAlgebraFamily RandomHistory} := {
  measurable_subspace_legal: forall P, is_measurable_subspace P -> LegalHistoryAntiChain P;
  is_measurable_subspace_same_covered: forall P Q: HistoryAntiChain, same_covered_anti_chain P Q -> is_measurable_subspace P -> is_measurable_subspace Q;
  is_measurable_set_same_covered: forall (O1 O2 P1 P2: HistoryAntiChain) H1 H2, Included P1 O1 -> Included P2 O2 -> same_covered_anti_chain O1 O2 -> same_covered_anti_chain P1 P2 -> PrFamily.is_measurable_set P1 (exist is_measurable_subspace O1 H1) -> PrFamily.is_measurable_set P2 (exist is_measurable_subspace O2 H2);
  max_anti_chain_measurable: forall P, is_max_anti_chain P -> is_measurable_subspace P
}.

Section RandomVariable.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory}.

Definition RandomVarDomain {HBSFo: HistoryBasedSigF ora}: Type := PrFamily.measurable_subspace.

Definition RandomVarDomain_HistoryAntiChain {HBSFo: HistoryBasedSigF ora} (Omega: RandomVarDomain): HistoryAntiChain := Build_HistoryAntiChain _ (proj1_sig Omega) (measurable_subspace_legal _ (proj2_sig Omega)).

Global Coercion RandomVarDomain_HistoryAntiChain: RandomVarDomain >-> HistoryAntiChain.

Definition RandomVariable {HBSFo: HistoryBasedSigF ora} (Omega: RandomVarDomain) (A: Type) {SA: SigmaAlgebra A}: Type := PrFamily.MeasurableFunction Omega A.

Global Identity Coercion RandomVariable_MeasurableFunction: RandomVariable >-> PrFamily.MeasurableFunction.

Definition MeasurableSubset {HBSFo: HistoryBasedSigF ora} (Omega: RandomVarDomain): Type := PrFamily.measurable_set Omega.

Definition MeasurableSubset_HistoryAntiChain {HBSFo: HistoryBasedSigF ora} {Omega: RandomVarDomain} (P: MeasurableSubset Omega): HistoryAntiChain.
  exists (PrFamily.measurable_set_Ensemble Omega P).
  assert (Included (PrFamily.measurable_set_Ensemble Omega P) Omega).
  + unfold PrFamily.measurable_set_Ensemble.
    intros ? [? ?].
    auto.
  + eapply LegalHistoryAntiChain_Included; eauto.
    apply measurable_subspace_legal.
    destruct Omega; auto.
Defined.
Global Coercion MeasurableSubset_HistoryAntiChain: MeasurableSubset >-> HistoryAntiChain.

Context {HBSFo: HistoryBasedSigF ora}.

Lemma MeasurableSubset_in_domain: forall (Omega: RandomVarDomain) (P: MeasurableSubset Omega) h,
  P h ->
  Omega h.
Proof.
  intros.
  eapply PrFamily.measurable_set_measurable_subspace.
  exact H.
Qed.

(* TODO: check whether this is necessary. *)
Definition undistinguishable_sub_domain (O1 O2: RandomVarDomain): Prop :=
  Included O1 O2 /\
  ~ is_measurable_subspace (Intersection _ O2 (Complement _ O1)).

Definition RandomVar_local_equiv {O1} {O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A) (h1 h2: RandomHistory): Prop := forall a, v1 h1 a <-> v2 h2 a.

Definition RandomVar_global_equiv {O1} {O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A): Prop := forall h, RandomVar_local_equiv v1 v2 h h.

Definition unit_space_domain: RandomVarDomain :=
  exist is_measurable_subspace unit_space_anti_chain (max_anti_chain_measurable _ unit_anti_chain_max).

Definition constant_var (Omega: RandomVarDomain) {A: Type} (v: A) {SA: SigmaAlgebra A}: RandomVariable Omega A := PrFamily.MeasurableFunction_inv (ConstantFunction v).

Definition unit_space_var {A: Type} (v: A) {SA: SigmaAlgebra A}: RandomVariable unit_space_domain A := constant_var _ v.

Definition RandomVarMap {Omega: RandomVarDomain} {A B: Type} {SA: SigmaAlgebra A} {SB: SigmaAlgebra B} (f: MeasurableFunction A B) (v: RandomVariable Omega A): RandomVariable Omega B := PrFamily.Compose f v.

Lemma RandomVarMap_sound: forall {Omega: RandomVarDomain} {A B: Type} {SA: SigmaAlgebra A} {SB: SigmaAlgebra B} (f: MeasurableFunction A B) (v: RandomVariable Omega A) h b,
  RandomVarMap f v h b <-> exists a, v h a /\ f a b.
Proof.
  intros; simpl.
  split.
  + intros [[? ?] [? [? [? ?]]]]; simpl in *.
    subst.
    exists x0; auto.
  + intros [? [? ?]].
    pose proof PrFamily.rf_sound _ _ v _ _ H.
    exists (exist _ h H1); simpl.
    split; auto.
    exists x; auto.
Qed.

Record HeredRandomVariable (A: Type) {SA: SigmaAlgebra A}: Type := {
  well_defined_dom: RandomVarDomain -> Prop;
  well_defined_mono: forall (O1 O2: RandomVarDomain), future_anti_chain O1 O2 -> well_defined_dom O1 -> well_defined_dom O2;
  ex_value: forall Omega: RandomVarDomain, well_defined_dom Omega -> RandomVariable Omega A;
  ex_value_hered: forall (O1 O2: RandomVarDomain) (H1: well_defined_dom O1) (H2: well_defined_dom O2) (h1: O1) (h2: O2),
    future_anti_chain O1 O2 ->
    prefix_history h1 h2 ->
    RandomVar_local_equiv (ex_value O1 H1) (ex_value O2 H2) h1 h2
}.

End RandomVariable.

(*
Definition filter_var {ora: RandomOracle} {A: Type} (filter: RandomHistory -> Prop) (v: RandomVariable A): RandomVariable A.
  refine (Build_RandomVariable _ _
           (filter_domain filter (rv_domain _ v))
           (fun h a => raw_var _ v h a /\ filter h) _ _ _).
  + intros ? ? ? [? ?] [? ?].
    apply (raw_var_pf _ v h); auto.
  + intros ? ? [? ?].
    simpl; split; auto.
    apply (raw_var_sound _ v h a); auto.
  + intros ? [? ?].
    destruct (raw_var_complete _ v h H) as [a ?].
    exists a.
    split; auto.
Defined.

Definition preimage_domain {ora: RandomOracle} {A: Type} (P: A -> Prop) (v: RandomVariable A): RandomVarDomain :=
  filter_domain (fun h => forall a, raw_var _ v h a -> P a) (rv_domain _ v).


*)