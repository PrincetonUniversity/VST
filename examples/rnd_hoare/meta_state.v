Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_variable.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Instance MetaState_SigmaAlgebra (state: Type) {state_sig: SigmaAlgebra state}: SigmaAlgebra (MetaState state).
  apply (Build_SigmaAlgebra _ (fun P => is_measurable_set (fun s => P (Terminating _ s)))).
  + hnf; intros; simpl.
    apply is_measurable_set_proper.
    destruct H; split; unfold Included, In in *; hnf; intros; auto.
  + eapply is_measurable_set_proper; [| apply full_measurable].
    split; hnf; unfold In; intros; constructor.
  + intros. admit.
  + intros. admit.
Defined.

Inductive raw_MetaState_pair_left (cmd state: Type) (c: cmd): MetaState state -> MetaState (cmd * state) -> Prop :=
  | Error_pair_left: raw_MetaState_pair_left cmd state c (Error _) (Error _)
  | NonTerminating_pair_left: raw_MetaState_pair_left cmd state c (NonTerminating _) (NonTerminating _)
  | Terminating_pair_left: forall s, raw_MetaState_pair_left cmd state c (Terminating _ s) (Terminating _ (c, s)).

Definition MetaState_pair_left {cmd state: Type} {state_sig: SigmaAlgebra state} (c: cmd): @MeasurableFunction (MetaState state) (MetaState (cmd * state)) _ (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)).
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_pair_left cmd state c)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a.
    - exists (Error _); constructor.
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
  | Error_snd: raw_MetaState_snd cmd state (Error _) (Error _)
  | NonTerminating_snd: raw_MetaState_snd cmd state (NonTerminating _) (NonTerminating _)
  | Terminating_snd: forall c s, raw_MetaState_snd cmd state (Terminating _ (c, s)) (Terminating _ s).

Definition MetaState_snd {cmd state: Type} {state_sig: SigmaAlgebra state}: @MeasurableFunction (MetaState (cmd * state)) (MetaState state) (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) _.
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_snd cmd state)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a as [ | | [? ?]].
    - exists (Error _); constructor.
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

Definition ProgState_pair_left {cmd state: Type} {state_sigma: SigmaAlgebra state} (c: cmd) {Omega: RandomVarDomain} (s: ProgState Omega state): @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state).
  refine (Build_ProgState Omega _ _ (RandomVarMap (MetaState_pair_left c) (raw_state _ _ s)) _).
  intros.
  rewrite RandomVarMap_sound in H0.
  destruct H0 as [? [? ?]].
  pose proof inf_history_sound _ _ s h x H H0.
  inversion H1; subst; congruence.
Defined.

Definition non_branch_tstate {state: Type} {state_sigma: SigmaAlgebra state} (s: state): ProgState unit_space_domain state.
  refine (Build_ProgState _ _ _ (unit_space_var (Terminating _ s)) _).
  intros.
  exfalso.
  apply PrFamily.rf_sound in H0.
  specialize (H0 0); simpl in H0.
  specialize (H 0).
  rewrite <- H0 in H; apply H; auto.
Defined.

Record RandomVarDomainStream : Type := {
  raw_domains: nat -> RandomVarDomain;
  rdom_same_covered: forall n, same_covered_anti_chain (raw_domains n) (raw_domains (S n));
  rdom_forward: forall n, future_anti_chain (raw_domains n) (raw_domains (S n))
}.

Global Coercion raw_domains: RandomVarDomainStream >-> Funclass.

Record ConvergeDir (Omegas: RandomVarDomainStream): Type := {
  raw_direction: forall n, MeasurableSubset (Omegas n);
  rdir_forward: forall n, future_anti_chain (raw_direction n) (raw_direction (S n));
  rdir_slow: forall n h, Omegas n h -> ~ Omegas (S n) h -> raw_direction n h
}.

Global Coercion raw_direction: ConvergeDir >-> Funclass.

Definition ProgStateStream (Omegas: RandomVarDomainStream) (state: Type) {state_sigma: SigmaAlgebra state}: Type := forall n: nat, ProgState (Omegas n) state.

Definition is_limit_domain (Omegas: RandomVarDomainStream) (dir: ConvergeDir Omegas) (lim_Omega: RandomVarDomain) : Prop :=
  forall h,
    lim_Omega h <->
      (exists n, Omegas n h /\ forall n', n' >= n -> ~ dir n h) \/
      (forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h').

Definition is_limit {Omegas: RandomVarDomainStream} {lim_Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas) (lim: ProgState lim_Omega state) : Prop :=
  forall h s,
    lim h s <->
      (exists n, (l n) h s /\ forall n', n' >= n -> ~ dir n h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h').

Definition limit_domain (Omegas: RandomVarDomainStream) (dir: ConvergeDir Omegas): RandomVarDomain.
  exists (fun h =>
   (exists n, Omegas n h /\ forall n', n' >= n -> ~ dir n h) \/
   (forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
      exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h')).
  admit.
Defined.

Definition limit {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas): ProgState (limit_domain Omegas dir) state.
  refine (Build_ProgState _ _ _
           (PrFamily.Build_MeasurableFunction _ _ _ (fun h s =>
   (exists n, (l n) h s /\ forall n', n' >= n -> ~ dir n h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h')) _ _ _ _ ) _).
  Admitted.

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

Section CutLimit.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {state: Type} {state_sigma: SigmaAlgebra state}.

Variable (filter: measurable_set (MetaState state)).

Variables (Omegas: RandomVarDomainStream) (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas).

Fixpoint left_raw_dir (n: nat): HistoryAntiChain :=
  match n with
  | 0 => MeasurableSubset_HistoryAntiChain (PrFamily.Intersection_MSet (dir 0) (PrFamily.PreImage_MSet (l 0) filter))
  | S n0 => filter_anti_chain (fun h => covered_by h (left_raw_dir n0)) (MeasurableSubset_HistoryAntiChain (PrFamily.Intersection_MSet (dir n) (PrFamily.PreImage_MSet (l n) filter)))
  end.

Fixpoint left_raw_domain (n: nat): RandomHistory -> Prop :=
  match n with
  | 0 => Omegas 0
  | S n0 => Union _
             (filter_anti_chain (left_raw_domain n0) (left_raw_dir n0))
             (filter_anti_chain (fun h => covered_by h (left_raw_dir n0)) (Omegas n))
  end.

Fixpoint left_raw_state (n: nat): RandomHistory -> MetaState state -> Prop :=
  match n with
  | 0 => fun h s => l 0 h s
  | S n0 => fun h s => 
              (filter_anti_chain (left_raw_domain n0) (left_raw_dir n0)) h /\ left_raw_state n0 h s \/
              covered_by h (left_raw_dir n0) /\ l n h s
  end.

Definition right_raw_dir (n: nat): RandomHistory -> Prop :=
  fun h => exists m, covered_by h (left_raw_dir m) /\ ~ covered_by h (left_raw_dir (S m)) /\ MeasurableSubset_HistoryAntiChain (dir (n + S m)) h.

End CutLimit.