Require Import Coq.Sets.Ensembles.
Require Import RndHoare.random_oracle.
Require Import RndHoare.full_domain.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.

Class HistoryBasedSigF (ora: RandomOracle) {SFo: SigmaAlgebraFamily RandomHistory} := {
  measurable_subspace_legal: forall P, is_measurable_subspace P -> LegalRandomVarDomain P;
  is_measurable_subspace_same_covered: forall P Q: RandomVarDomain, same_covered_domain P Q -> is_measurable_subspace P -> is_measurable_subspace Q;
  is_measurable_set_same_covered: forall (O1 O2 P1 P2: RandomVarDomain) H1 H2, Included _ P1 O1 -> Included _ P2 O2 -> same_covered_domain O1 O2 -> same_covered_domain P1 P2 -> PrFamily.is_measurable_set P1 (exist is_measurable_subspace O1 H1) -> PrFamily.is_measurable_set P2 (exist is_measurable_subspace O2 H2);
  full_measurable: forall P, is_full_domain P -> is_measurable_subspace P
}.

Section RandomVariable.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

(* TODO: try avoiding this name overload. *)
Definition RandomVarDomain: Type := PrFamily.measurable_subspace.

Definition RandomVarDomain_RandomVarDomain (Omega: RandomVarDomain): random_oracle.RandomVarDomain := Build_RandomVarDomain _ (proj1_sig Omega) (measurable_subspace_legal _ (proj2_sig Omega)).

Global Coercion RandomVarDomain_RandomVarDomain: RandomVarDomain >-> random_oracle.RandomVarDomain.

Definition RandomVariable (Omega: RandomVarDomain) (A: Type) {SA: sigma_algebra.SigmaAlgebra A}: Type := PrFamily.MeasurableFunction Omega A.

Global Identity Coercion RandomVariable_MeasurableFunction: RandomVariable >-> PrFamily.MeasurableFunction.

Definition MeasurableSubset (Omega: RandomVarDomain): Type := PrFamily.measurable_set Omega.

Definition MeasurableSubset_RandomVarDomain {Omega: RandomVarDomain} (P: MeasurableSubset Omega): random_oracle.RandomVarDomain.
  exists (PrFamily.measurable_set_Ensemble Omega P).
  assert (Included _ (PrFamily.measurable_set_Ensemble Omega P) Omega).
  + unfold PrFamily.measurable_set_Ensemble.
    intros ? [? ?].
    auto.
  + eapply LegalRandomVarDomain_Included; eauto.
    apply measurable_subspace_legal.
    destruct Omega; auto.
Defined.
Global Coercion MeasurableSubset_RandomVarDomain: MeasurableSubset >-> random_oracle.RandomVarDomain.

(* TODO: check whether this is necessary. *)
Definition undistinguishable_sub_domain (O1 O2: RandomVarDomain): Prop :=
  Included _ O1 O2 /\
  ~ is_measurable_subspace (Intersection _ O2 (Complement _ O1)).

Definition RandomVar_local_equiv {O1} {O2} {A: Type} {SA: sigma_algebra.SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A) (h1 h2: RandomHistory): Prop := forall a, v1 h1 a <-> v2 h2 a.

Definition RandomVar_global_equiv {O1} {O2} {A: Type} {SA: sigma_algebra.SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A): Prop := forall h, RandomVar_local_equiv v1 v2 h h.

Definition unit_space_domain: RandomVarDomain :=
  exist is_measurable_subspace unit_space_domain (full_measurable _ unit_domain_full).
  
Definition constant_var (Omega: RandomVarDomain) {A: Type} (v: A) {SA: sigma_algebra.SigmaAlgebra A}: RandomVariable Omega A := PrFamily.MeasurableFunction_inv (ConstantFunction v).

Definition unit_space_var {A: Type} (v: A) {SA: sigma_algebra.SigmaAlgebra A}: RandomVariable unit_space_domain A := constant_var _ v.

Definition RandomVarMap {Omega: RandomVarDomain} {A B: Type} {SA: sigma_algebra.SigmaAlgebra A} {SB: sigma_algebra.SigmaAlgebra B} (f: MeasurableFunction A B) (v: RandomVariable Omega A): RandomVariable Omega B := PrFamily.Compose f v.

Lemma RandomVarMap_sound: forall {Omega: RandomVarDomain} {A B: Type} {SA: sigma_algebra.SigmaAlgebra A} {SB: sigma_algebra.SigmaAlgebra B} (f: MeasurableFunction A B) (v: RandomVariable Omega A) h b,
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

Record HeredRandomVariable (A: Type) {SA: sigma_algebra.SigmaAlgebra A}: Type := {
  well_defined_dom: RandomVarDomain -> Prop;
  well_defined_mono: forall (O1 O2: RandomVarDomain), future_domain O1 O2 -> well_defined_dom O1 -> well_defined_dom O2;
  ex_value: forall Omega: RandomVarDomain, well_defined_dom Omega -> RandomVariable Omega A;
  ex_value_hered: forall (O1 O2: RandomVarDomain) (H1: well_defined_dom O1) (H2: well_defined_dom O2) (h1: O1) (h2: O2),
    future_domain O1 O2 ->
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