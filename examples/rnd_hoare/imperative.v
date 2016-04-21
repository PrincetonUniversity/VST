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

Record global_step {imp: Imperative} {sss: SmallStepSemantics} (s1 s2: RandomVariable (cmd * state)): Prop := {
  normal_domain: RandomHistory -> Prop;
  random_domain: RandomHistory -> Prop;
  domain_consi:
    forall h, normal_domain h -> random_domain h -> False;
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

Inductive access {imp: Imperative} {sss: SmallStepSemantics}:
  RandomVariable (cmd * state) -> RandomVariable (cmd * state) -> Prop :=
  | access_refl: forall cs, access cs cs
  | access_step: forall src cs dst, global_step src cs -> access cs dst -> access cs dst.

Inductive meta_state {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  | NonTerminating: meta_state
  | Terminating: state -> meta_state.

Definition global_state {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  {s: RandomVariable meta_state | forall h, infinite_history h -> s h = None \/ s h = Some NonTerminating}.

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