Require Import RndHoare.random_oracle.
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

(* Begin [ProbState Lemmas] *)

Definition ProbState {ora: RandomOracle} (state: Type) :=
  {s: RandomVariable (MetaState state) | forall h, infinite_history h -> s h = Some (NonTerminating _) \/ s h = None}.

Definition ProbState_RandomVariable {ora: RandomOracle} {state: Type}: ProbState state -> RandomVariable (MetaState state) := @proj1_sig _ _.

Coercion ProbState_RandomVariable: ProbState >-> RandomVariable.

Definition unique_state {ora: RandomOracle} {state: Type} (s: MetaState state): ProbState state.
  refine (exist _ (unit_space_var s) _).
  intros.
  simpl.
  specialize (H 0).
  destruct (h 0); try congruence.
  auto.
Defined.

Definition ProbStateStream {ora: RandomOracle} (state: Type) : Type := nat -> ProbState state.

Definition ProbConvDir {ora: RandomOracle} : Type := nat -> RandomVarDomain.

Definition is_limit {ora: RandomOracle} {state: Type} (l: ProbStateStream state) (dir: ProbConvDir) (lim: RandomVariable (MetaState state)) : Prop :=
 (forall n h, ~ dir n h -> l n h = l (S n) h) /\
 (forall h,
    match lim h with
    | Some (Terminating s) => (* finite_part_of_limit *)
        exists n,
          l n h = Some (Terminating _ s) /\
          (forall n' h', n' >= n -> prefix_history h' h -> ~ dir n h')
    | Some NonTerminating => (* infinite_part_of_limit *)
       (forall n h_low, finite_history h_low -> prefix_history h_low h ->
          exists n' h', n' > n /\ prefix_history h_low h' /\
                       prefix_history h' h /\ dir n' h') \/
       (exists n,
          l n h = Some (NonTerminating _) /\
          (forall n' h', n' >= n -> prefix_history h' h -> ~ dir n h'))
    | None => (* invalid_part_of_limit *)
        exists n, forall n', n' >= n ->
          l n' h = None
    end).
(* End [ProbState Lemmas] *)

Class SmallStepSemantics {imp: Imperative}: Type := {
  state: Type;
  ora: RandomOracle;
  step: cmd * state -> ProbState (cmd * state) -> Prop
}.

Global Existing Instance ora.

Record local_step {imp: Imperative} {sss: SmallStepSemantics} (h: RandomHistory) (s1 s2: ProbState (cmd * state)): Prop := {
  cs1: cmd * state;
  cs2: ProbState (cmd * state);
  sound1: s1 h = Some (Terminating _ cs1);
  sound2: forall h' h'', history_app h h' h'' -> s2 h'' = cs2 h';
  step_fact: step cs1 cs2
}.

Record global_step {imp: Imperative} {sss: SmallStepSemantics} (P: RandomVarDomain) (s1 s2: ProbState (cmd * state)): Prop := {
  action_part:
    forall h, P h -> local_step h s1 s2;
  stable_part:
    forall h,
      (forall h' h'', P h' -> ~ history_app h' h'' h) ->
      s1 h = s2 h
}.

Record step_path {imp: Imperative} {sss: SmallStepSemantics}: Type := {
  path_states: nat -> ProbState (cmd * state);
  step_domains: nat -> RandomVarDomain;
  step_sound: forall n, global_step (step_domains n) (path_states n) (path_states (S n));
  domain_mono: forall n, future_domain (step_domains n) (step_domains (S n))
}.

Definition access {imp: Imperative} {sss: SmallStepSemantics} (src dst: ProbState (cmd * state)): Prop :=
  exists (l: step_path) (n: nat), path_states l 0 = src /\ path_states l n = dst.

Definition omega_access {imp: Imperative} {sss: SmallStepSemantics} (src dst: ProbState (cmd * state)): Prop :=
  exists (l: step_path), path_states l 0 = src /\ is_limit (path_states l) (step_domains l) dst.

Definition global_state {imp: Imperative} {sss: SmallStepSemantics}: Type := ProbState state.

Identity Coercion global_state_ProbState: global_state >-> ProbState.

Definition global_state_command_state {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (s: global_state): ProbState (cmd * state).
  destruct s.
  exists (RandomVarMap
           (fun s =>
              match s with
              | NonTerminating => NonTerminating _
              | Terminating s0 => Terminating _ (c, s0)
              end)
           x).
  intros.
  specialize (o h H).
  destruct o; [left | right];
  rewrite RandomVarMap_sound;
  rewrite H0; auto.
Defined.

Definition command_oaccess {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (src dst: global_state): Prop :=
  forall k, omega_access (global_state_command_state (Ssequence c k) src) (global_state_command_state k dst).

Definition triple {imp: Imperative} {sss: SmallStepSemantics} (P: global_state -> Prop) (c: cmd)  (Q: global_state -> Prop): Prop :=
  forall s1, P s1 -> forall s2, command_oaccess c s1 s2 -> Q s2.

Class NormalSmallStepSemantics {imp: Imperative} {Nimp: NormalImperative} {sss: SmallStepSemantics} : Type := {
  eval_bool: state -> expr -> option bool;
  step_seq_assoc: forall c1 c2 c3 s cs, step (Ssequence c1 (Ssequence c2 c3), s) cs <-> step (Ssequence (Ssequence c1 c2) c3, s) cs;
  step_if_true: forall e c1 c2 c3 s cs, eval_bool s e = Some true -> step (Ssequence (Sifthenelse e c1 c2) c3, s) cs <-> cs = unique_state (Terminating _ (Ssequence c1 c3, s));
  step_if_false: forall e c1 c2 c3 s cs, eval_bool s e = Some false -> step (Ssequence (Sifthenelse e c1 c2) c3, s) cs <-> cs = unique_state (Terminating _ (Ssequence c2 c3, s));
  step_while_true: forall e c1 c2 s cs, eval_bool s e = Some true -> step (Ssequence (Swhile e c1) c2, s) cs <-> cs = unique_state (Terminating _ (Ssequence c1 (Ssequence (Swhile e c1) c2), s));
  step_while_false: forall e c1 c2 s cs, eval_bool s e = Some false -> step (Ssequence (Swhile e c1) c2, s) cs <-> cs = unique_state (Terminating _ (c2, s));
  step_atomic: forall c1 c2 s cs h, cmd_pattern_match c1 = PM_Other -> step (Ssequence c1 c2, s) cs -> (exists s', cs h = Some (Terminating _ (c2, s'))) \/ cs h = Some (NonTerminating _) \/ cs h = None
}. 



End Randomized.

(*





Definition is_non_random {cmd state ora} (step: rSmallStepSemantics cmd state ora): Prop :=
  forall src dst, ~ step src (inr dst).

Definition sequentialize {cmd state ora} (step: rSmallStepSemantics cmd state ora): sSmallStepSemantics cmd state :=
  fun src dst => step src (inl dst).


*)


(*
Lemma sequentialize_sound {cmd state ora}: forall step,
  is_non_random step ->
  ???
*)

(* TODO: what is normal definition of external call? *)
(*
Inductive sAcc {cmd state: Type} (step: sSmallStepSemantics cmd state): cmd * state -> cmd * state -> Prop :=
  | 
*)