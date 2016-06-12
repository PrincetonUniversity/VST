Require Export Coq.Reals.Rdefinitions.
Require Export Coq.Reals.Rfunctions.
Require Export Coq.Logic.ProofIrrelevance.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.probability_measure.

Local Open Scope R.

Class SigmaAlgebraFamily (Omega: Type): Type := {
  is_measurable_subspace: (Ensemble Omega) -> Prop;
  is_measurable_subspace_proper: Proper (Same_set ==> iff) is_measurable_subspace;
  sub_sigma_algebra: forall (P: Ensemble Omega | is_measurable_subspace P), SigmaAlgebra {o: Omega | proj1_sig P o};
  is_measurable_subspace_consi: forall (P: Ensemble Omega | is_measurable_subspace P) (Q: Ensemble Omega | is_measurable_subspace Q), Included (proj1_sig Q) (proj1_sig P) -> @is_measurable_set {x: Omega | proj1_sig P x} (sub_sigma_algebra P) (sig_Set (proj1_sig Q) (proj1_sig P))
}.

Class ProbabilityMeasureFamily (Omega: Type) {SigFamily : SigmaAlgebraFamily Omega}: Type := {
  sub_measure: forall (P: Ensemble Omega | is_measurable_subspace P), @ProbabilityMeasure {o: Omega | proj1_sig P o} (sub_sigma_algebra P)
}.

Module PrFamily.

Section ProbabilityMeasureFamily.

Context {U: Type} {SigF: SigmaAlgebraFamily U}.

Definition measurable_subspace: Type := {Omega: Ensemble U | is_measurable_subspace Omega}.

Definition measurable_subspace_Ensemble: measurable_subspace -> Ensemble U := @proj1_sig _ _.

Global Coercion measurable_subspace_Ensemble: measurable_subspace >-> Ensemble.

Definition measurable_subspace_Prop: measurable_subspace -> U -> Prop := @proj1_sig _ _.

Global Coercion measurable_subspace_Prop: measurable_subspace >-> Funclass.

Definition is_measurable_set (P: Ensemble U) (Omega: measurable_subspace) := @is_measurable_set {x: U | Omega x} (sub_sigma_algebra Omega) (sig_Set P Omega).

Lemma is_measurable_subspace_consi: forall (Omega Omega': measurable_subspace), Included Omega' Omega -> is_measurable_set Omega' Omega.
Proof.
  intros.
  apply is_measurable_subspace_consi; auto.
Qed.

Definition measurable_set (Omega: measurable_subspace): Type := {P: Ensemble U | is_measurable_set P Omega}.

Definition measurable_set_Ensemble (Omega: measurable_subspace): measurable_set Omega -> Ensemble U := fun P => Intersection _ (@proj1_sig _ _ P) Omega.

Global Coercion measurable_set_Ensemble: measurable_set >-> Ensemble.

Definition measurable_set_Prop (Omega: measurable_subspace): measurable_set Omega -> U -> Prop := fun P => Intersection _ (@proj1_sig _ _ P) Omega.

Global Coercion measurable_set_Prop: measurable_set >-> Funclass.

Definition measurable_set_inj {Omega: measurable_subspace} (P: measurable_set Omega): @sigma_algebra.measurable_set _ (sub_sigma_algebra Omega).
  destruct Omega as [Omega ?H], P as [P ?H].
  unfold is_measurable_set in H0.
  simpl in *.
  exact (exist _ _ H0).
Defined.

Definition measurable_set_inv {Omega: measurable_subspace} (P: @sigma_algebra.measurable_set _ (sub_sigma_algebra Omega)): measurable_set Omega.
  exists (unsig_Set P).
  unfold is_measurable_set, sig_Set, unsig_Set.
  destruct P as [P ?H]; simpl.
  eapply is_measurable_set_proper; [| eassumption].
  split; hnf; unfold In; intros.
  + destruct x, H0; simpl in *.
    assert (p = x0) by (apply proof_irrelevance; auto); subst; auto.
  + exists (proj2_sig x).
    destruct x; simpl; auto.
Defined.

Record MeasurableFunction (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B}: Type := {
  raw_function: U -> B -> Prop;
  rf_partial_functionality: forall a b1 b2, raw_function a b1 -> raw_function a b2 -> b1 = b2;
  rf_complete: forall a, Omega a -> exists b, raw_function a b;
  rf_sound: forall a b, raw_function a b -> Omega a;
  rf_preserve: forall (P: sigma_algebra.measurable_set B), is_measurable_set (fun a => forall b, raw_function a b -> P b) Omega
}.

Definition MeasurableFunction_raw_function (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B): U -> B -> Prop := raw_function _ _ f.

Coercion MeasurableFunction_raw_function: MeasurableFunction >-> Funclass.

Definition MeasurableFunction_inj {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B): @measurable_function.MeasurableFunction _ B (sub_sigma_algebra Omega) _.
  apply (measurable_function.Build_MeasurableFunction _ _ _ _ (fun a b => f (proj1_sig a) b)).
  + intros [a ?] ? ? ? ?; simpl in *.
    apply (rf_partial_functionality _ _ f a b1 b2); auto.
  + intros [a ?]; simpl in *.
    destruct (rf_complete _ _ f a p) as [b ?H].
    exists b; auto.
  + intros; simpl.
    exact (rf_preserve _ _ f P).
Defined.

Definition MeasurableFunction_inv {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: @measurable_function.MeasurableFunction _ B (sub_sigma_algebra Omega) _): MeasurableFunction Omega B.
  apply (Build_MeasurableFunction _ _ _ (fun a b => exists a0, proj1_sig a0 = a /\ f a0 b)).
  + intros ? ? ? [[? ?] [? ?]] [[? ?] [? ?]].
    simpl in *; subst.
    assert (p = p0) by (apply proof_irrelevance; auto); subst.
    apply (measurable_function.rf_functionality _ _ _ _ _ _ H0 H2).
  + intros ? ?.
    destruct (measurable_function.rf_complete _ _ f (exist _ a H)) as [b ?H].
    exists b, (exist _ a H); auto.
  + intros ? ? [[? ?] [? ?]].
    simpl in *; subst; auto.
  + intros.
    pose proof measurable_function.rf_preserve _ _ f P.
    unfold is_measurable_set.
    eapply sigma_algebra.is_measurable_set_proper; [| eassumption].
    split; hnf; unfold In, sig_Set; intros.
    - apply H0.
      exists x; auto.
    - apply H0; intros.
      destruct H1 as [? [? ?]]; auto.
      assert (x = x0).
      Focus 1. {
        destruct x as [x p], x0 as [x0 p0]; simpl in H1; subst.
        f_equal.
        apply proof_irrelevance; auto.
      } Unfocus.
      subst; auto.
Defined.

Lemma measurable_set_measurable_subspace: forall (Omega: measurable_subspace) (A: measurable_set Omega) x, A x -> Omega x.
Proof.
  intros.
  unfold measurable_set_Prop in H.
  rewrite Intersection_spec in H; tauto.
Qed.

Definition Compose {Omega: measurable_subspace} {B C: Type} {SB: SigmaAlgebra B} {SC: SigmaAlgebra C} (g: measurable_function.MeasurableFunction B C) (f: MeasurableFunction Omega B): MeasurableFunction Omega C := MeasurableFunction_inv (measurable_function.Compose g (MeasurableFunction_inj f)).

Definition PreImage_MSet {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B) (P: sigma_algebra.measurable_set B): measurable_set Omega := measurable_set_inv (PreImage_MSet (MeasurableFunction_inj f) P).

Definition Intersection_MSet {Omega: measurable_subspace} (A B: measurable_set Omega): measurable_set Omega :=
  measurable_set_inv (sigma_algebra.Intersection_MSet _ (measurable_set_inj A) (measurable_set_inj B)).

Definition Union_MSet {Omega: measurable_subspace} (A B: measurable_set Omega): measurable_set Omega :=
  measurable_set_inv (sigma_algebra.Union_MSet _ (measurable_set_inj A) (measurable_set_inj B)).

Context {PrF: ProbabilityMeasureFamily U}.

Definition Probability {Omega: measurable_subspace} (P: measurable_set Omega): R := Probability (sub_measure Omega) (measurable_set_inj P).

Definition Expectation {Omega: measurable_subspace} (f: MeasurableFunction Omega R): R := Expectation (sub_measure Omega) (MeasurableFunction_inj f).

End ProbabilityMeasureFamily.

End PrFamily.

Global Coercion PrFamily.MeasurableFunction_raw_function: PrFamily.MeasurableFunction >-> Funclass.

Class IsDisintegration {OMEGA} {SigF: SigmaAlgebraFamily OMEGA} {PrF: ProbabilityMeasureFamily OMEGA} (Omega: Ensemble OMEGA | is_measurable_subspace Omega) {A: Type} {SA: SigmaAlgebra A} (pi: MeasurableFunction {o: OMEGA | proj1_sig Omega o} A) (A1: measurable_set A): Type := {
  defined_almost_everywhere: GeneratedProbabilityMeasure pi (sub_measure Omega) A1 = 1;
  defined_MSS: forall a, A1 a -> is_measurable_subspace (unsig_Set (fun o => pi o a));
  defined_MS: forall a (def: A1 a) (E: @measurable_set {o: OMEGA | proj1_sig Omega o} (@sub_sigma_algebra OMEGA SigF Omega)), @is_measurable_set _ (sub_sigma_algebra (exist _ _ (defined_MSS a def))) (sig_Set (unsig_Set E) (unsig_Set (fun o => pi o a)))
}.


