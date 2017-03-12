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
  + intros.
    change (fun s : state => Complement (MetaState state) P (Terminating state s))
      with (Complement _ (fun s : state => P (Terminating state s))).
    apply complement_measurable; auto.
  + intros.
    change (fun s : state => Countable_Union (MetaState state) P (Terminating state s))
      with (Countable_Union _ (fun i s => P i (Terminating state s))).
    apply countable_union_measurable.
    auto.
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

Definition meta_state_measurable_set {state: Type} {state_sig: SigmaAlgebra state} (P: measurable_set state) (error non_terminating: Prop): measurable_set (MetaState state).
  exists (fun x => match x with | Error => error | NonTerminating => non_terminating | Terminating s => P s end).
  simpl.
  apply (proj2_sig P).
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

Definition Terminating_raw_domain {Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (s: ProgState Omega state): MeasurableSubset Omega :=
  PrFamily.PreImage_MSet s (meta_state_measurable_set (Full_MSet _) False False).

End ProgState.

Section Limit.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

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

Definition is_limit_domain (Omegas: RandomVarDomainStream) (lim_Omega: RandomVarDomain) : Prop :=
  forall h,
    lim_Omega h <->
      (forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ Omegas n' h').

Definition is_limit {Omegas: RandomVarDomainStream} {lim_Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas) (lim: ProgState lim_Omega state) : Prop :=
  forall h s,
    lim h s <->
      (exists n, (l n) h s /\ forall n', n' >= n -> ~ dir n' h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h').

Definition limit_raw_domain (Omegas: RandomVarDomainStream): RandomHistory -> Prop :=
  fun h =>
    forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
      exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ Omegas n' h'.

Lemma RandomVarDomainStream_stable: forall (Omegas: RandomVarDomainStream) (dir: ConvergeDir Omegas) (n: nat) h,
  Omegas n h ->
  (forall m, m >= n -> ~ dir m h) ->
  (forall m, m >= n -> Omegas m h).
Proof.
  intros.
  remember (m - n) as Delta eqn:?H.
  assert (m = Delta + n) by omega.
  clear H1 H2; subst m.
  induction Delta; auto.

  pose proof rdir_slow _ dir (Delta + n) h IHDelta.
  assert (Delta + n >= n) as HH by omega; specialize (H0 (Delta + n) HH); clear HH.
  destruct (classic ((Omegas (S Delta + n)) h)); tauto.
Qed.

Lemma RandomVarDomainStream_same_covered: forall (Omegas: RandomVarDomainStream) (n1 n2: nat),
  same_covered_anti_chain (Omegas n1) (Omegas n2).
Proof.
  intros Omegas.
  assert (forall n1 n2, n1 <= n2 -> same_covered_anti_chain (Omegas n1) (Omegas n2)).
  + intros.
    remember (n2 - n1) as Delta.
    assert (n2 = Delta + n1) by omega.
    subst n2; clear HeqDelta H.
    induction Delta.
    - reflexivity.
    - transitivity (Omegas (Delta + n1)); auto.
      apply rdom_same_covered.
  + intros.
    destruct (le_dec n1 n2).
    - apply H; auto.
    - symmetry; apply H; omega.
Qed.

Lemma RandomVarDomainStream_mono: forall (Omegas: RandomVarDomainStream) (n1 n2: nat),
  n1 <= n2 ->
  future_anti_chain (Omegas n1) (Omegas n2).
Proof.
  intros.
  remember (n2 - n1) as Delta.
  assert (n2 = Delta + n1) by omega.
  subst n2; clear HeqDelta H.
  induction Delta.
  + apply future_anti_chain_refl.
  + apply future_anti_chain_trans with (Omegas (Delta + n1)); auto.
    apply rdom_forward.
Qed.

Lemma RandomVarDomainStream_hered: forall (Omegas: RandomVarDomainStream) (n1 n2: nat) h1,
  n1 <= n2 ->
  Omegas n1 h1 ->
  exists h2,
  prefix_history h1 h2 /\ Omegas n2 h2.
Proof.
  intros.
  apply same_covered_future_anti_chain_spec with (Omegas n1); auto.
  + apply RandomVarDomainStream_same_covered.
  + apply RandomVarDomainStream_mono; auto.
Qed.

Lemma limit_raw_domain_covered: forall (Omegas: RandomVarDomainStream) h n, limit_raw_domain Omegas h -> covered_by h (Omegas n).
Proof.
  intros.
  rename h into h_limit.
  assert (prefix_history (fin_history nil) h_limit) by (hnf; intros [|]; left; auto).
  specialize (H n (fin_history nil) (fin_history_fin _) H0); clear H0.
  destruct H as [n0 [h0 [? [? [? ?]]]]].

  destruct (fun HH => RandomVarDomainStream_mono Omegas n n0 HH h0 H2) as [h [? ?]]; [omega |].
  exists h.
  split; auto.
  apply prefix_history_trans with h0; auto.
Qed.

Lemma limit_raw_domain_legal: forall (Omegas: RandomVarDomainStream), LegalHistoryAntiChain (limit_raw_domain Omegas).
Proof.
  intros.
  constructor.
  hnf; intros.
  destruct H as [n [? ?]].
  destruct (H0 0 (fstn_history (S n) h1) (fstn_history_finite _ _) (fstn_history_prefix _ _)) as [m1 [h1' [? [? [? ?]]]]].
  destruct (H1 0 (fstn_history (S n) h2) (fstn_history_finite _ _) (fstn_history_prefix _ _)) as [m2 [h2' [? [? [? ?]]]]].

  destruct (raw_anti_chain_legal (Omegas (max m1 m2))) as [?H].
  destruct (limit_raw_domain_covered Omegas h1 (max m1 m2) H0) as [h1'' [? ?]].
  destruct (limit_raw_domain_covered Omegas h2 (max m1 m2) H1) as [h2'' [? ?]].

  assert (prefix_history (fstn_history (S n) h1) h1'').
  Focus 1. {
    apply prefix_history_trans with h1'; auto.
    apply (proj_in_anti_chain_unique (Omegas m1) h1' h1'' h1); auto.
    apply (RandomVarDomainStream_mono Omegas m1 (max m1 m2)); auto.
    apply Max.le_max_l.
  } Unfocus.

  assert (prefix_history (fstn_history (S n) h2) h2'').
  Focus 1. {
    apply prefix_history_trans with h2'; auto.
    apply (proj_in_anti_chain_unique (Omegas m2) h2' h2'' h2); auto.
    apply (RandomVarDomainStream_mono Omegas m2 (max m1 m2)); auto.
    apply Max.le_max_r.
  } Unfocus.

  clear h1' h2' H4 H5 H6 H8 H9 H10.

  apply (H11 h1'' h2''); auto.
  exists n.
  rewrite <- (n_conflict_proper_aux n h1 h1'' h2 h2''); auto.
  + apply squeeze_history_coincide; auto.
  + apply squeeze_history_coincide; auto.
Qed.

Definition limit_domain_anti_chain (Omegas: RandomVarDomainStream): HistoryAntiChain := Build_HistoryAntiChain _ (limit_raw_domain Omegas) (limit_raw_domain_legal Omegas).

Lemma limit_domain_anti_chain_hered: forall (Omegas: RandomVarDomainStream) (n: nat) h,
  Omegas n h ->
  exists h_limit,
  prefix_history h h_limit /\ limit_domain_anti_chain Omegas h_limit.
Proof.
  intros.
  destruct (classic (exists l, prefix_history h (fin_history l) /\ forall n0, covered_by (fin_history l) (Omegas n0))).
  + (* when h_limit is finite *)
    destruct H0 as [l ?].
    pose proof
      dec_inh_nat_subset_has_unique_least_element
        (fun m =>
           exists l0, length l0 = m /\
             prefix_history h (fin_history l0) /\
             forall n0, covered_by (fin_history l0) (Omegas n0))
        (fun n => classic (_ n))
        (ex_intro _ (length l) (ex_intro _ l (conj (@eq_refl _ (length l)) H0))).
    clear H0 l.
    destruct H1 as [m [[[l [? [? ?]]] ?] _]].
    exists (fin_history l).
    split; auto.

    assert (exists n0, Omegas n0 (fin_history l)) as HH; [| destruct HH as [n0 ?]].
    Focus 1. {
      destruct (classic (exists n0, (Omegas n0) (fin_history l))); auto; exfalso.
      admit.
    } Unfocus.
    hnf; intros.
    exists (max (S n1) n0), (fin_history l).
    split; [pose proof Max.le_max_l (S n1) n0; omega |].
    split; [auto |].
    split; [apply prefix_history_refl |].

    clear - H2 H4.
    specialize (H2 (max (S n1) n0)); destruct H2 as [h [? ?]].
    destruct (RandomVarDomainStream_mono Omegas n0 (max (S n1) n0) (Max.le_max_r _ _) h H0) as [h0 [? ?]].
    assert (prefix_history h0 (fin_history l)) by (apply prefix_history_trans with h; auto).
    pose proof anti_chain_not_comparable (Omegas n0) _ _ H2 H4 H3.
    subst h0.
    pose proof prefix_history_anti_sym _ _ H H1.
    subst h.
    auto.

  + (* when h_limit is infinite *)

SearchAbout prefix_history (@eq RandomHistory).


Lemma limit_domain_anti_chain_covered_forward: forall (Omegas: RandomVarDomainStream) h,
  is_inf_history h ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ limit_domain_anti_chain Omegas h') ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ Omegas 0 h').
Proof.
  intros.
  destruct H0 as [h' [? ?]].
  pose proof limit_raw_domain_covered _ _ 0 H1.
  destruct H2 as [h'' [? ?]].
  exists h''; split; auto.
  destruct H0.
  + left; apply prefix_history_trans with h'; auto.
  + apply (strict_conflict_prefix_left h h'' h'); auto.
Qed.

Lemma limit_domain_anti_chain_covered_backward: forall (Omegas: RandomVarDomainStream) h,
  is_inf_history h ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ Omegas 0 h') ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ limit_domain_anti_chain Omegas h').
Proof.
  intros.
  destruct (classic (exists n, exists h', strict_conflict_history h' h /\ (Omegas n) h')).
  + clear H0; destruct H1 as [n [h' [? ?]]].


Definition limit_domain (Omegas: RandomVarDomainStream) (dir: ConvergeDir Omegas): RandomVarDomain.
  exists (limit_domain_anti_chain Omegas).
  eapply is_measurable_subspace_same_covered.

  admit.
Defined.

Definition limit {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas): ProgState (limit_domain Omegas dir) state.
  refine (Build_ProgState _ _ _
           (PrFamily.Build_MeasurableFunction _ _ _ (fun h s =>
   (exists n, (l n) h s /\ forall n', n' >= n -> ~ dir n' h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h')) _ _ _ _ ) _).
  Admitted.

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