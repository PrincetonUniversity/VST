Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_variable.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Class Imperative : Type := {
  cmd: Type;
  expr: Type;
  Ssequence: cmd -> cmd -> cmd;
  cmd_rank: cmd -> nat;
  Ssequence_consi_left: forall c1 c2, cmd_rank c1 < cmd_rank (Ssequence c1 c2);
  Ssequence_consi_right: forall c1 c2, cmd_rank c2 < cmd_rank (Ssequence c1 c2)
}.

Inductive NormalImperativePatternMatchResult {imp: Imperative} : Type :=
  | PM_Ssequence: cmd -> cmd -> NormalImperativePatternMatchResult
  | PM_Sifthenelse: expr -> cmd -> cmd -> NormalImperativePatternMatchResult
  | PM_Swhile: expr -> cmd -> NormalImperativePatternMatchResult
  | PM_Other: NormalImperativePatternMatchResult
  | PM_Invalid: NormalImperativePatternMatchResult.

Definition is_PM_Ssequence {imp: Imperative} (pm: NormalImperativePatternMatchResult): Prop :=
  match pm with
  | PM_Ssequence _ _ => True
  | _ => False
  end.

Class NormalImperative {imp: Imperative}: Type := {
  Sifthenelse: expr -> cmd -> cmd -> cmd;
  Swhile: expr -> cmd -> cmd;
  Sifthenelse_consi_left: forall e c1 c2, cmd_rank c1 < cmd_rank (Sifthenelse e c1 c2);
  Sifthenelse_consi_right: forall e c1 c2, cmd_rank c2 < cmd_rank (Sifthenelse e c1 c2);
  Swhile_consi: forall e c, cmd_rank c < cmd_rank (Swhile e c);
  cmd_pattern_match: cmd -> NormalImperativePatternMatchResult;
  Ssequence_pattern_match_iff: forall (c c1 c2: cmd), c = Ssequence c1 c2 <-> cmd_pattern_match c = PM_Ssequence c1 c2;
  Ssequence_pattern_match: forall (c1 c2: cmd), is_PM_Ssequence (cmd_pattern_match (Ssequence c1 c2));
  Sifthenelse_pattern_match_iff: forall (c: cmd) (e: expr) (c1 c2: cmd), c = Sifthenelse e c1 c2 <-> cmd_pattern_match c = PM_Sifthenelse e c1 c2;
  Swhile_pattern_match_iff: forall (c: cmd) (e: expr) (c0: cmd), c = Swhile e c0 <-> cmd_pattern_match c = PM_Swhile e c0
}.

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

Module Sequential.

Class SmallStepSemantics {imp: Imperative}: Type := {
  state: Type;
  step: cmd * state -> MetaState (cmd * state) -> Prop
}.

Definition global_step {imp: Imperative} {sss: SmallStepSemantics} (flag: option unit) (s1 s2: MetaState (cmd * state)): Prop :=
  match flag with
  | Some tt =>
    match s1 with
    | NonTerminating => False
    | Terminating cs => step cs s2
    end
  | None => s1 = s2
  end.

Record step_path {imp: Imperative} {sss: SmallStepSemantics}: Type := {
  path_states: nat -> MetaState (cmd * state);
  step_domains: nat -> option unit;
  step_sound: forall n, global_step (step_domains n) (path_states n) (path_states (S n));
  domain_mono: forall n, step_domains n = None -> step_domains (S n) = None
}.

Definition is_limit {imp: Imperative} {sss: SmallStepSemantics} (l: step_path) (lim: MetaState (cmd * state)): Prop := 
  match lim with
  | NonTerminating =>
      (forall N, exists n, n > N /\ step_domains l n = Some tt) \/
      (exists n, path_states l n = NonTerminating _ /\ step_domains l n = None)
  | Terminating cs =>
      (exists n, path_states l n = Terminating _ cs /\ step_domains l n = None)
  end.

Definition access {imp: Imperative} {sss: SmallStepSemantics} (src dst: MetaState (cmd * state)): Prop :=
  exists (l: step_path) (n: nat), path_states l 0 = src /\ path_states l n = dst.

Definition omega_access {imp: Imperative} {sss: SmallStepSemantics} (src: MetaState (cmd * state)) (dst: MetaState (cmd * state)) : Prop :=
  exists (l: step_path), path_states l 0 = src /\ is_limit l dst.

Definition global_state {imp: Imperative} {sss: SmallStepSemantics} := MetaState state.

Definition global_state_command_state {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (s: global_state): MetaState (cmd * state) :=
  match s with
  | NonTerminating => NonTerminating _
  | Terminating s0 => Terminating _ (c, s0)
  end.

Definition command_oaccess {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (src dst: global_state): Prop :=
  forall k, omega_access (global_state_command_state (Ssequence c k) src) (global_state_command_state k dst).

Definition triple {imp: Imperative} {sss: SmallStepSemantics} (P: global_state -> Prop) (c: cmd)  (Q: global_state -> Prop): Prop :=
  forall s1, P s1 -> forall s2, command_oaccess c s1 s2 -> Q s2.

Definition PartialAssertion {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  {P: global_state -> Prop | forall s, P (Terminating _ s) -> P (NonTerminating _)}.

Definition TotalAssertion {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  {P: global_state -> Prop | forall s, P (NonTerminating _) -> P (Terminating _ s)}.

Definition ptriple {imp: Imperative} {sss: SmallStepSemantics} (P: PartialAssertion) (c: cmd)  (Q: PartialAssertion): Prop := triple (proj1_sig P) c (proj1_sig Q).

Definition ttriple {imp: Imperative} {sss: SmallStepSemantics} (P: TotalAssertion) (c: cmd)  (Q: TotalAssertion): Prop := triple (proj1_sig P) c (proj1_sig Q).

End Sequential.

Module Randomized.

Section ProbState.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Record ProbState (state: Type) {state_sigma: SigmaAlgebra state} : Type := {
  Omega: RandomVarDomain;
  raw_state: RandomVariable Omega (MetaState state);
  inf_history_sound: forall (h: RandomHistory) (ms: MetaState state), is_inf_history h -> raw_state h ms -> ms = NonTerminating _
}.

Definition ProbState_fun (state: Type) {state_sigma: SigmaAlgebra state}: ProbState state -> RandomHistory -> MetaState state -> Prop := @raw_state state _.

Global Coercion ProbState_fun: ProbState >-> Funclass.

Definition ProbState_RandomVariable (state: Type) {state_sigma: SigmaAlgebra state} (s: ProbState state): RandomVariable (Omega _ s) (MetaState state) := @raw_state state _ s.

Global Coercion ProbState_RandomVariable: ProbState >-> RandomVariable.
(*
Definition unique_state {ora: RandomOracle} {state: Type} (s: MetaState state): ProbState state.
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

Definition ProbStateStream {ora: RandomOracle} (state: Type) {state_sigma: SigmaAlgebra state}: Type := nat -> ProbState state.

Definition ProbConvDir {ora: RandomOracle} : Type := nat -> RandomVarDomain.

Record is_limit {ora: RandomOracle} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProbStateStream state) (dir: ProbConvDir) (lim: ProbState state) : Prop := {
  dir_mono: forall n, future_domain (RandomVarDomain_RandomVarDomain (dir n)) (RandomVarDomain_RandomVarDomain (dir (S n)));
  dir_consi_uncovered: forall n h, ~ covered_by h (RandomVarDomain_RandomVarDomain (dir n)) -> RandomVar_local_equiv (l n) (l (S n)) h h;
  dir_in_domain: forall n h, RandomVarDomain_RandomVarDomain (dir n) h -> RandomVarDomain_RandomVarDomain (Omega _ (l n)) h;
  pointwise_limit: forall h s,
    lim h s <->
      (exists n, (l n) h s /\ forall n', n' >= n -> ~ RandomVarDomain_RandomVarDomain (dir n) h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ RandomVarDomain_RandomVarDomain (dir n') h')
}.

End ProbState.

Class SmallStepSemantics {imp: Imperative} : Type := {
  state: Type;
  state_sig: SigmaAlgebra state;
  cmd_state_sig := (left_discreste_prod_sigma_alg cmd state);
  ora: RandomOracle;
  SFo: SigmaAlgebraFamily RandomHistory;
  HBSFo: HistoryBasedSigF ora;
  step: cmd * state -> ProbState (cmd * state) -> Prop
}.

Global Existing Instances state_sig cmd_state_sig ora SFo HBSFo.

Section Randomize.

Context {imp: Imperative} {sss: SmallStepSemantics}.

Record local_step (h: RandomHistory) (s1 s2: ProbState (cmd * state)): Prop := {
  cs1: cmd * state;
  cs2: ProbState (cmd * state);
  sound1: s1 h (Terminating _ cs1);
  sound2: forall h' h'', history_app h h' h'' -> (forall x, s2 h'' x <-> cs2 h' x);
  step_fact: step cs1 cs2
}.

Record global_step (P: RandomVarDomain) (s1 s2: ProbState (cmd * state)): Prop := {
  action_part:
    forall h, RandomVarDomain_RandomVarDomain P h -> local_step h s1 s2;
  stable_part:
    forall h, ~ covered_by h (RandomVarDomain_RandomVarDomain P) -> (forall x, s1 h x <-> s2 h x)
}.

Record step_path: Type := {
  path_states: nat -> ProbState (cmd * state);
  step_domains: nat -> RandomVarDomain;
  step_sound: forall n, global_step (step_domains n) (path_states n) (path_states (S n));
  domain_mono: forall n, future_domain (RandomVarDomain_RandomVarDomain (step_domains n)) (RandomVarDomain_RandomVarDomain (step_domains (S n)))
}.

Definition access (src dst: ProbState (cmd * state)): Prop :=
  exists (l: step_path) (n: nat), path_states l 0 = src /\ path_states l n = dst.

Definition omega_access (src dst: ProbState (cmd * state)): Prop :=
  exists (l: step_path), path_states l 0 = src /\ is_limit (path_states l) (step_domains l) dst.

Definition global_state: Type := ProbState state.

Global Identity Coercion global_state_ProbState: global_state >-> ProbState.

Definition global_state_command_state (c: cmd) (s: global_state): ProbState (cmd * state).
  refine (Build_ProbState _ _ (Omega _ s) (RandomVarMap (MetaState_pair_left c) (raw_state _ s)) _).
  intros.
  rewrite RandomVarMap_sound in H0.
  destruct H0 as [? [? ?]].
  pose proof inf_history_sound _ s h x H H0.
  inversion H1; subst; congruence.
Defined.

Definition command_oaccess (c: cmd) (src dst: global_state): Prop :=
  forall k, omega_access (global_state_command_state (Ssequence c k) src) (global_state_command_state k dst).

Definition triple (P: global_state -> Prop) (c: cmd) (Q: global_state -> Prop): Prop :=
  forall s1, P s1 -> forall s2, command_oaccess c s1 s2 ->
    same_covered_domain (RandomVarDomain_RandomVarDomain (Omega _ s1)) (RandomVarDomain_RandomVarDomain (Omega _ s2)) /\ Q s2.

(*
Class NormalSmallStepSemantics {imp: Imperative} {Nimp: NormalImperative} {sss: SmallStepSemantics} : Type := {
  eval_bool: state -> expr -> option bool;
  step_seq_assoc: forall c1 c2 c3 s cs, step (Ssequence c1 (Ssequence c2 c3), s) cs <-> step (Ssequence (Ssequence c1 c2) c3, s) cs;
  step_if_true: forall e c1 c2 c3 s cs, eval_bool s e = Some true -> step (Ssequence (Sifthenelse e c1 c2) c3, s) cs <-> cs = unique_state (Terminating _ (Ssequence c1 c3, s));
  step_if_false: forall e c1 c2 c3 s cs, eval_bool s e = Some false -> step (Ssequence (Sifthenelse e c1 c2) c3, s) cs <-> cs = unique_state (Terminating _ (Ssequence c2 c3, s));
  step_while_true: forall e c1 c2 s cs, eval_bool s e = Some true -> step (Ssequence (Swhile e c1) c2, s) cs <-> cs = unique_state (Terminating _ (Ssequence c1 (Ssequence (Swhile e c1) c2), s));
  step_while_false: forall e c1 c2 s cs, eval_bool s e = Some false -> step (Ssequence (Swhile e c1) c2, s) cs <-> cs = unique_state (Terminating _ (c2, s));
  step_atomic: forall c1 c2 s cs h, cmd_pattern_match c1 = PM_Other -> step (Ssequence c1 c2, s) cs -> (exists s', cs h = Some (Terminating _ (c2, s'))) \/ cs h = Some (NonTerminating _) \/ cs h = None
}.
*)

(*
Definition filter_global_state {imp: Imperative} {sss: SmallStepSemantics} (filter: RandomHistory -> Prop) (s: global_state): global_state.
  exists (filter_var filter (proj1_sig s)).
  destruct s as [s ?H]; simpl.
  intros.
  destruct h as [h [?H ?H]].
  simpl in *.
  split; auto.
  apply (H (exist _ h H1)).
  auto.
Defined.
*)
  
(*
Require Import Coq.Sets.Ensembles.

Section PrePreds.

Context {imp: Imperative} {sss: SmallStepSemantics}.

Definition tm_meta_pred (P: state -> Prop): MetaState state -> Prop :=
  fun s => match s with Terminating s' => P s' | _ => False end.

End PrePreds.
*)
End Randomize.

End Randomized.
