Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_variable.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Inductive MetaState (state: Type): Type :=
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Instance MetaState_SigmaAlgebra (state: Type) {state_sig: SigmaAlgebra state}: SigmaAlgebra (MetaState state).
  apply (Build_SigmaAlgebra _ (fun P => is_measurable_set (fun s => P (Terminating _ s)))).
  + hnf; intros; simpl.
    apply is_measurable_set_proper.
    destruct H; split; unfold Included, In in *; hnf; intros; auto.
  + eapply is_measurable_set_proper; [| apply universal_set_measurable].
    split; hnf; unfold In; intros; constructor.
  + intros. admit.
  + intros. admit.
Defined.

Inductive raw_MetaState_pair_left (cmd state: Type) (c: cmd): MetaState state -> MetaState (cmd * state) -> Prop :=
  | Terminating_pair_left: forall s, raw_MetaState_pair_left cmd state c (Terminating _ s) (Terminating _ (c, s))
  | NonTerminating_pair_left: raw_MetaState_pair_left cmd state c (NonTerminating _) (NonTerminating _).

Definition MetaState_pair_left {cmd state: Type} {state_sig: SigmaAlgebra state} (c: cmd): @MeasurableFunction (MetaState state) (MetaState (cmd * state)) _ (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)).
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_pair_left cmd state c)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a.
    - exists (NonTerminating _); constructor.
    - exists (Terminating _ (c, s)); constructor.
  + simpl.
    intros.
    destruct P as [P ?H].
    simpl in *.
    eapply is_measurable_set_proper; [| exact (H c)].
    simpl.
    split; hnf; unfold In; intros.
    - apply H0; constructor.
    - inversion H1; auto.
Defined.

Inductive raw_MetaState_snd (cmd state: Type): MetaState (cmd * state) -> MetaState state -> Prop :=
  | Terminating_snd: forall c s, raw_MetaState_snd cmd state (Terminating _ (c, s)) (Terminating _ s)
  | NonTerminating_snd: raw_MetaState_snd cmd state (NonTerminating _) (NonTerminating _).

Definition MetaState_snd {cmd state: Type} {state_sig: SigmaAlgebra state}: @MeasurableFunction (MetaState (cmd * state)) (MetaState state) (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) _.
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_snd cmd state)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a as [ | [? ?]].
    - exists (NonTerminating _); constructor.
    - exists (Terminating _ s); constructor.
  + simpl.
    intros.
    destruct P as [P ?H].
    eapply is_measurable_set_proper; [| exact H].
    simpl.
    split; hnf; unfold In; intros.
    - apply H0; constructor.
    - inversion H1; auto.
Defined.

Section ProgState.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Record ProgState (Omega: RandomVarDomain) (state: Type) {state_sigma: SigmaAlgebra state} : Type := {
  raw_state: RandomVariable Omega (MetaState state);
  inf_history_sound: forall (h: RandomHistory) (ms: MetaState state), is_inf_history h -> raw_state h ms -> ms = NonTerminating _
}.

Definition ProgState_RandomVariable (Omega: RandomVarDomain) (state: Type) {state_sigma: SigmaAlgebra state} (s: ProgState Omega state): RandomVariable Omega (MetaState state) := @raw_state Omega state _ s.

Global Coercion ProgState_RandomVariable: ProgState >-> RandomVariable.
(*
Definition unique_state {ora: RandomOracle} {state: Type} (s: MetaState state): ProgState state.
  refine (exist _ (unit_space_var s) _).
  intros.
  exfalso.
  destruct h as [h ?H]; simpl in *.
  specialize (H 0).
  specialize (H0 0).
  destruct (h 0); simpl in *; try congruence.
  inversion H0.
Defined.
*)

Definition RandomVarDomainStream : Type := nat -> RandomVarDomain.

Definition ProgStateStream (Omegas: RandomVarDomainStream) (state: Type) {state_sigma: SigmaAlgebra state}: Type := forall n: nat, ProgState (Omegas n) state.

Record is_limit {Omegas: RandomVarDomainStream} {lim_Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: RandomVarDomainStream) (lim: ProgState lim_Omega state) : Prop := {
  dir_mono: forall n, future_domain (RandomVarDomain_RandomVarDomain (dir n)) (RandomVarDomain_RandomVarDomain (dir (S n)));
  dir_consi_uncovered: forall n h, ~ covered_by h (RandomVarDomain_RandomVarDomain (dir n)) -> RandomVar_local_equiv (l n) (l (S n)) h h;
  dir_in_domain: forall n h, RandomVarDomain_RandomVarDomain (dir n) h -> RandomVarDomain_RandomVarDomain (Omegas n) h;
  pointwise_limit: forall h s,
    lim h s <->
      (exists n, (l n) h s /\ forall n', n' >= n -> ~ RandomVarDomain_RandomVarDomain (dir n) h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ RandomVarDomain_RandomVarDomain (dir n') h')
}.

Definition Terminating_raw_domain {Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (s: ProgState Omega state): RandomHistory -> Prop := fun h => exists a, s h (Terminating _ a).

Definition Terminating_proj {Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (s: ProgState Omega state) H: RandomVariable (exist _ (Terminating_raw_domain s) H) state.
  apply (PrFamily.Build_MeasurableFunction _ _ _ (fun h a => s h (Terminating _ a))).
  + intros.
    pose proof (PrFamily.rf_partial_functionality _ _ s a _ _ H0 H1).
    inversion H2; auto.
  + intros h ?.
    auto.
  + intros h a ?.
    simpl; exists a; auto.
  + admit.
Defined.

End ProgState.

