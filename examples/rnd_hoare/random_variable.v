Require Import RndHoare.random_oracle.
Require Import RndHoare.full_domain.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.

Class HistoryBasedSigF (ora: RandomOracle) {SFo: SigmaAlgebraFamily RandomHistory} := {
  measurable_subspace_legal: forall P, is_measurable_subspace P -> LegalRandomVarDomain P;
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

Definition RandomVar_local_equiv {O1} {O2} {A: Type} {SA: sigma_algebra.SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A) (h1 h2: RandomHistory): Prop := forall a, v1 h1 a <-> v2 h2 a.

Definition constant_var (Omega: RandomVarDomain) {A: Type} (v: A) {SA: sigma_algebra.SigmaAlgebra A}: RandomVariable Omega A := PrFamily.MeasurableFunction_inv (ConstantFunction v).

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

End RandomVariable.

(*
Definition unit_space_var {ora: RandomOracle} {A: Type} (v: A): RandomVariable A.
  refine (Build_RandomVariable _ _ unit_space_domain (fun h a => h 0 = None /\ a = v) _ _ _).
  + intros ?  ? ? [? ?] [? ?]; congruence.
  + intros ? ? [? ?]; subst.
    simpl; intros.
    rewrite (history_sound1 h 0 n) by (auto; omega).
    destruct n; auto.
  + intros.
    exists v.
    simpl in *.
    split; auto.
    rewrite <- (H 0).
    auto.
Defined.

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