Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_variable.
Require Import RndHoare.meta_state.
Require Import RndHoare.probabilistic_pred.

Class Imperative : Type := {
  cmd: Type;
  expr: Type;
  Sskip: cmd;
  Ssequence: cmd -> cmd -> cmd
}.

Module Sequential.

Class SmallStepSemantics {imp: Imperative}: Type := {
  state: Type;
  step: cmd * state -> MetaState (cmd * state) -> Prop
}.

Definition global_step {imp: Imperative} {sss: SmallStepSemantics} (flag: option unit) (s1 s2: MetaState (cmd * state)): Prop :=
  match flag with
  | Some tt =>
    match s1 with
    | Error => False
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
  forall s,
  lim = s <->
    (exists n, path_states l n = s /\ step_domains l n = None) \/
    (s = NonTerminating _ /\ forall n, step_domains l n = Some tt).

Definition access {imp: Imperative} {sss: SmallStepSemantics} (src dst: MetaState (cmd * state)): Prop :=
  exists (l: step_path) (n: nat), path_states l 0 = src /\ path_states l n = dst.

Definition omega_access {imp: Imperative} {sss: SmallStepSemantics} (src: MetaState (cmd * state)) (dst: MetaState (cmd * state)) : Prop :=
  exists (l: step_path), path_states l 0 = src /\ is_limit l dst.

Definition global_state {imp: Imperative} {sss: SmallStepSemantics} := MetaState state.

Definition global_state_command_state {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (s: global_state): MetaState (cmd * state) :=
  match s with
  | Error => Error _
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

Class SmallStepSemantics {imp: Imperative} : Type := {
  state: Type;
  state_sig: SigmaAlgebra state;
  cmd_state_sig := (left_discreste_prod_sigma_alg cmd state);
  ora: RandomOracle;
  SFo: SigmaAlgebraFamily RandomHistory;
  HBSFo: HistoryBasedSigF ora;
  step: cmd * state -> forall {Omega: RandomVarDomain}, ProgState Omega (cmd * state)%type -> Prop
}.

Global Existing Instances state_sig cmd_state_sig ora SFo HBSFo.

Section Randomize.

Context {imp: Imperative} {sss: SmallStepSemantics}.

Record local_step (h: RandomHistory) {O1 O2: RandomVarDomain} (s1: ProgState O1 (cmd * state)) (s2: ProgState O2 (cmd * state)): Prop := {
  cs1: cmd * state;
  Omega: RandomVarDomain;
  cs2: ProgState Omega (cmd * state);
  sound1: s1 h (Terminating _ cs1);
  sound2: forall h' h'', history_app h h' h'' -> (forall x, s2 h'' x <-> cs2 h' x);
  step_fact: step cs1 cs2
}.

Record global_step {O1 O2: RandomVarDomain} (P: MeasurableSubset O1) (s1: ProgState O1 (cmd * state)) (s2: ProgState O2 (cmd * state)): Prop := {
  action_part:
    forall h, P h -> local_step h s1 s2;
  stable_part:
    forall h, ~ covered_by h P -> (forall x, s1 h x <-> s2 h x)
}.

Record step_path: Type := {
  path_domain: RandomVarDomainStream;
  path_states: ProgStateStream path_domain (cmd * state);
  step_domains: ConvergeDir path_domain;
  step_sound: forall n, global_step (step_domains n) (path_states n) (path_states (S n));
  domain_mono: forall n, future_anti_chain (step_domains n) (step_domains (S n))
}.

Definition access {O1 O2: RandomVarDomain} (src: ProgState O1 (cmd * state)) (dst: ProgState O2 (cmd * state)): Prop :=
  exists (l: step_path) (n: nat),
    RandomVar_global_equiv (path_states l 0) src /\
    RandomVar_global_equiv (path_states l n) dst.

Definition omega_access {O1 O2: RandomVarDomain} (src: ProgState O1 (cmd * state)) (dst: ProgState O2 (cmd * state)): Prop :=
  exists (l: step_path),
    RandomVar_global_equiv (path_states l 0) src /\
    is_limit (path_states l) (step_domains l) dst.

Definition global_state (Omega: RandomVarDomain) : Type := ProgState Omega state.

Global Identity Coercion global_state_ProgState: global_state >-> ProgState.

Definition command_oaccess (c: cmd) {O1 O2: RandomVarDomain} (src: global_state O1) (dst: global_state O2): Prop :=
  omega_access (ProgState_pair_left c src) (ProgState_pair_left Sskip dst).

Definition assertion: Type := RandomPred (MetaState (@state imp sss) :: nil).

Global Identity Coercion assertion_RandomPred: assertion >-> RandomPred.

Definition triple (P: assertion) (c: cmd) (Q: assertion): Prop :=
  forall o1 (s1: global_state o1), P o1 s1 ->
    forall o2 (s2: global_state o2), command_oaccess c s1 s2 ->
      same_covered_anti_chain o1 o2 /\ Q o2 s2.

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
