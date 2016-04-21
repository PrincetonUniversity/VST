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

Definition eval {imp: Imperative} {sss: SmallStepSemantics} (c: cmd) (src dst: meta_state): Prop :=
  match src, dst with
  | NonTerminating, NonTerminating => True
  | NonTerminating, Terminating _ => False
  | Terminating s1, NonTerminating =>
     forall s2 k, access (Ssequence c k, s1) (k, s2) -> steps (k, s2)
  | Terminating s1, Terminating s2 =>
     forall k, access (Ssequence c k, s1) (k, s2)
  end.

Definition triple {imp: Imperative} {sss: SmallStepSemantics} (P: meta_state -> Prop) (c: cmd)  (Q: meta_state -> Prop): Prop :=
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
(*
Inductive global_step {imp: Imperative} {sss: SmallStepSemantics}: (RandomHistory -> option (cmd * state)) -> (RandomHistory -> option (cmd * state)) -> Prop :=
  | normal_step: forall h0 s1 s2 cs1 cs2,
     s1 h0 = Some cs1 ->
     s2 h0 = Some cs2 ->
     step cs1 (inl cs2) ->
     (forall h, h0 <> h -> s1 h = s2 h) ->
     global_step s1 s2
  | random_step: forall h0 s1 s2 cs1 cs2,
     s1 h0 = Some cs1 ->
     s2 h0 = Some cs2 ->
     step cs1 (inl cs2) ->
     (forall h, h0 <> h -> s1 h = s2 h) ->
     global_step s1 s2

Inductive access {imp: Imperative} {sss: SmallStepSemantics}:
  (RandomHistory -> option (cmd * state)) -> (RandomHistory -> option (cmd * state)) -> Prop :=
  | access_refl: forall cs, access cs cs
  | access_normal_step: forall src h0 cs dst,
       step (src h0) (inl (cs h0)) ->
       (forall h, h <> h0 -> src h = cs h) ->
       access cs dst -> access cs dst.

Inductive meta_state {imp: Imperative} {sss: SmallStepSemantics}: Type :=
  | NonTerminating: meta_state
  | Terminating: state -> meta_state.







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