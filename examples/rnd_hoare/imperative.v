Require Import RndHoare.random_oracle.

Class Imperative : Type := {
  cmd: Type;
  expr: Type;
  Ssequence: cmd -> cmd -> cmd
}.

Inductive NormalImperativePatternMatchResult {imp: Imperative} : Type :=
  | PM_Ssequence: cmd -> cmd -> NormalImperativePatternMatchResult
  | PM_Sifthenelse: expr -> cmd -> cmd -> NormalImperativePatternMatchResult
  | PM_Swhile: expr -> cmd -> NormalImperativePatternMatchResult
  | PM_Other: cmd -> NormalImperativePatternMatchResult
  | PM_Invalid: cmd -> NormalImperativePatternMatchResult.

Class NormalImperative {imp: Imperative}: Type := {
  Sifthenelse: expr -> cmd -> cmd -> cmd;
  Swhile: expr -> cmd -> cmd;
  cmd_pattern_match: cmd -> NormalImperativePatternMatchResult;
  Ssequence_pattern_match_iff: forall (c c1 c2: cmd), c = Ssequence c1 c2 <-> cmd_pattern_match c = PM_Ssequence c1 c2;
  Sifthenelse_pattern_match_iff: forall (c: cmd) (e: expr) (c1 c2: cmd), c = Sifthenelse e c1 c2 <-> cmd_pattern_match c = PM_Sifthenelse e c1 c2;
  Swhile_pattern_match_iff: forall (c: cmd) (e: expr) (c0: cmd), c = Swhile e c0 <-> cmd_pattern_match c = PM_Swhile e c0
}.

(* Assume type safe language. *)

Module Sequential.

Class SmallStepSemantics {imp: Imperative}: Type := {
  state: Type;
  step: cmd * state -> cmd * state -> Prop
}.

Inductive access {imp: Imperative} {sss: SmallStepSemantics}: cmd * state -> cmd * state -> Prop :=
  | access_refl: forall cs, access cs cs
  | access_step: forall src cs dst, step src cs -> access cs dst -> access cs dst.

Definition steps {imp: Imperative} {sss: SmallStepSemantics} (src: cmd * state): Prop :=
  exists dst, step src dst.

Inductive meta_state {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  | NonTerminating: meta_state
  | Terminating: state -> meta_state.

Definition global_state {imp: Imperative} {sss: SmallStepSemantics} := meta_state.

Definition eval {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (src dst: global_state): Prop :=
  match src, dst with
  | NonTerminating, NonTerminating => True
  | NonTerminating, Terminating _ => False
  | Terminating s1, NonTerminating =>
     forall s2 k, access (Ssequence c k, s1) (k, s2) -> steps (k, s2)
  | Terminating s1, Terminating s2 =>
     forall k, access (Ssequence c k, s1) (k, s2)
  end.

Definition triple {imp: Imperative} {sss: SmallStepSemantics} (P: global_state -> Prop) (c: cmd)  (Q: global_state -> Prop): Prop :=
  forall s1, P s1 -> forall s2, eval c s1 s2 -> Q s2.

End Sequential.

Module Randomized.

Class SmallStepSemantics {imp: Imperative}: Type := {
  state: Type;
  ora: RandomOracle;
  step: cmd * state ->
        (cmd * state) + {q: ro_question & ro_answer q -> cmd * state} ->
        Prop
}.

Global Existing Instance ora.

Record local_normal_step {imp: Imperative} {sss: SmallStepSemantics} (h: RandomHistory) (s1 s2: RandomVariable (cmd * state)): Prop := {
  cs1: cmd * state;
  cs2: cmd * state;
  sound1: s1 h = Some cs1;
  sound2: s2 h = Some cs2;
  step_fact: step cs1 (inl cs2)
}.

Record local_random_step {imp: Imperative} {sss: SmallStepSemantics} (h: RandomHistory) (s1 s2: RandomVariable (cmd * state)): Prop := {
  cs1: cmd * state;
  q: ro_question;
  cs2: ro_answer q -> cmd * state;
  sound1: s1 h = Some cs1;
  sound2: forall a h', history_cons h (existT ro_answer q a) h' -> s2 h' = Some (cs2 a);
  step_fact: step cs1 (inr (existT (fun x => ro_answer x -> cmd * state) q cs2))
}.

Record global_step {imp: Imperative} {sss: SmallStepSemantics} (P: RandomVarDomain) (s1 s2: RandomVariable (cmd * state)): Prop := {
  normal_domain: RandomVarDomain;
  random_domain: RandomVarDomain;
  domain_consi1:
    forall h, normal_domain h -> random_domain h -> False;
  domain_consi2:
    forall h, P h <-> normal_domain h \/ random_domain h;
  normal_step:
    forall h, normal_domain h -> local_normal_step h s1 s2;
  random_step:
    forall h, random_domain h -> local_random_step h s1 s2;
  stable_part:
    forall h,
      ~ normal_domain h ->
      ~ random_domain h ->
      (forall a h0, random_domain h0 -> ~ history_cons h0 a h) ->
      s1 h = s2 h
}.

Record step_path {imp: Imperative} {sss: SmallStepSemantics}: Type := {
  path_states: nat -> RandomVariable (cmd * state);
  step_domains: nat -> RandomVarDomain;
  step_sound: forall n, global_step (step_domains n) (path_states n) (path_states (S n));
  domain_mono: forall n, future_domain (step_domains n) (step_domains (S n))
}.

Record is_limit {imp: Imperative} {sss: SmallStepSemantics} (l: step_path) (lim: RandomVariable (option (cmd * state))): Prop := {
  finite_part_of_limit:
    forall h cs, lim h = Some (Some cs) ->
      exists n,
        path_states l n h = Some cs /\
        (forall h', prefix_history h' h -> ~ step_domains l n h');
  infinite_part_of_limit:
    forall h, lim h = Some None ->
      forall n, exists h', prefix_history h' h /\ step_domains l n h';
  invalid_part_of_limit:
    forall h, lim h = None ->
      exists n,
        path_states l n h = None /\
        (forall h', prefix_history h' h -> ~ step_domains l n h')
}.
  
Definition access {imp: Imperative} {sss: SmallStepSemantics} (src dst: RandomVariable (cmd * state)): Prop :=
  exists (l: step_path) (n: nat), path_states l 0 = src /\ path_states l n = dst.

Definition omega_access {imp: Imperative} {sss: SmallStepSemantics} (src: RandomVariable (cmd * state)) (dst: RandomVariable (option (cmd * state))) : Prop :=
  exists (l: step_path), path_states l 0 = src /\ is_limit l dst.

Inductive meta_state {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  | NonTerminating: meta_state
  | Terminating: state -> meta_state.

Definition global_state {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  {s: RandomVariable meta_state | forall h, infinite_history h -> s h = None \/ s h = Some NonTerminating}.

Definition global_state_random_variable {imp: Imperative} {sss: SmallStepSemantics}: global_state -> RandomVariable meta_state := @proj1_sig _ _.

Coercion global_state_random_variable: global_state >-> RandomVariable.
(*
Record eval {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (src dst: global_state): Prop := {
  frame: RandomVariable meta_state;
  src': RandomVariable meta_state;
  dst': RandomVariable meta_state;
  join_src: join src' frame src;
  join_dst: join dst' frame dst;
  frame_non_terminating: Forall_RandomHistory (eq NonTerminating) frame;
  src'_terminnating: Forall_RandomHistory (fun x => NonTerminating <> x) frame
}.

  match src, dst with
  | NonTerminating, NonTerminating => True
  | NonTerminating, Terminating _ => False
  | Terminating s1, NonTerminating =>
     forall s2 k, access (Ssequence c k, s1) (k, s2) -> steps (k, s2)
  | Terminating s1, Terminating s2 =>
     forall k, access (Ssequence c k, s1) (k, s2)
  end.
*)


(*





Definition is_non_random {cmd state ora} (step: rSmallStepSemantics cmd state ora): Prop :=
  forall src dst, ~ step src (inr dst).

Definition sequentialize {cmd state ora} (step: rSmallStepSemantics cmd state ora): sSmallStepSemantics cmd state :=
  fun src dst => step src (inl dst).


*)

End Randomized.

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