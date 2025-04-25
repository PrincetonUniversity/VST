(* ORA/ouPred version of lithium/proof_state.v *)
From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Export base.
From lithium Require Import hooks.
From VST.lithium Require Import definitions syntax.
Set Default Proof Using "Type".

(** This file contains some tactics for proof state management. *)

(** * Management of shelved sideconditions  *)
Definition SHELVED_SIDECOND (P : Prop) : Prop := P.
Arguments SHELVED_SIDECOND : simpl never.
Strategy expand [SHELVED_SIDECOND].

Ltac shelve_sidecond :=
  idtac;
  lazymatch goal with
  | |- ?G => change_no_check (SHELVED_SIDECOND G); shelve
  end.

Ltac unshelve_sidecond :=
  idtac;
  lazymatch goal with
  | |- SHELVED_SIDECOND ?G => change_no_check G
  | |- _ => shelve
  end.

(** * Generating typeclass instances *)
(** [generate_i2p_instance print to_tc c] generates an instance for an
[iProp_to_Prop]-based typeclass from the lemma c. The parameters not
part of the arguments of the typeclass must come last in the same
order as expected by the typeclass. This tactic tries to solve pure
[Prop] assumptions via [eq_refl]. [to_tc] is a tactic that converts
the conclusion of the lemma to the corresponding typeclass and is
called with [arg]. [print] controls whether to output debug printing.
*)
Ltac generate_i2p_instance print to_tc arg c :=
  let do_print t := tryif print then t else idtac in
  let do_to_tc c :=
    match c with
    (* to_tc must be first to allow overriding of the cases below *)
    | _ => to_tc arg c
    | subsume ?x1 ?x2 => constr:(Subsume x1 x2)
    | find_in_context ?x1 => constr:(FindInContext x1 arg)
    | simplify_hyp ?x1 => constr:(SimplifyHyp x1 (Some arg))
    | simplify_goal ?x1 => constr:(SimplifyGoal x1 (Some arg))
    end in
  let type_c := type of c in
  let type_c := eval lazy zeta in type_c in
  do_print ltac:(idtac "current:" c);
  do_print ltac:(idtac "type:" type_c);
  (* Try to find the typeclass *)
  try (
    let tc := lazymatch type_c with
    | (∀ _ _ _ _ _ _ _ _ _ _, _ ⊢ ?Q _ _ _ _ _ _ _ _ _ _) => do_to_tc Q
    | (∀ _ _ _ _ _ _ _ _ _, _ ⊢ ?Q _ _ _ _ _ _ _ _ _) => do_to_tc Q
    | (∀ _ _ _ _ _ _ _ _, _ ⊢ ?Q _ _ _ _ _ _ _ _) => do_to_tc Q
    | (∀ _ _ _ _ _ _ _, _ ⊢ ?Q _ _ _ _ _ _ _) => do_to_tc Q
    | (∀ _ _ _ _ _ _, _ ⊢ ?Q _ _ _ _ _ _) => do_to_tc Q
    | (∀ _ _ _ _ _, _ ⊢ ?Q _ _ _ _ _) => do_to_tc Q
    | (∀ _ _ _ _, _ ⊢ ?Q _ _ _ _) => do_to_tc Q
    | (∀ _ _ _, _ ⊢ ?Q _ _ _) => do_to_tc Q
    | (∀ _ _, _ ⊢ ?Q _ _) => do_to_tc Q
    | (∀ _, _ ⊢ ?Q _) => do_to_tc Q
    end in
    do_print ltac:(idtac "found typeclass:" tc);
    notypeclasses refine (_ : tc));
  (* Try to reorder hypothesis that don't occur in the goal to the
  front (e.g. TCDone assumptions or similar). Note that this code
  reverse the order if there are multiple such assumptions. *)
  let c := match type_c with
           | (∀ a1 a2 a3 a4 a5 _, _ ⊢ ?G) =>
               eval lazy beta zeta in (λ b a1 a2 a3 a4 a5, c a1 a2 a3 a4 a5 b)
           | (∀ a1 a2 a3 a4 _, _ ⊢ ?G) =>
               eval lazy beta zeta in (λ b a1 a2 a3 a4, c a1 a2 a3 a4 b)
           | (∀ a1 a2 a3 _, _ ⊢ ?G) =>
               eval lazy beta zeta in (λ b a1 a2 a3, c a1 a2 a3 b)
           | (∀ a1 a2 _, _ ⊢ ?G) =>
               eval lazy beta zeta in (λ b a1 a2, c a1 a2 b)
           | (∀ a1 _, _ ⊢ ?G) =>
               eval lazy beta zeta in (λ b a1, c a1 b)
           | _ => c
           end in
  let type_c := type of c in
  let type_c := eval lazy zeta in type_c in
  do_print ltac:(idtac "current after reorder:" c);
  do_print ltac:(idtac "type after reorder:" type_c);
  lazymatch type_c with
  | ∀ (a : ?T), @?P a =>
      (* Check if there is a sidecondition after the continuation, that we
         can solve with eq_refl. *)
      tryif (lazymatch type of T with | Prop => let x := constr:(eq_refl : T) in idtac end) then
          do_print ltac:(idtac "solve with eq_refl:" T);
          let x := constr:(eq_refl : T) in
          let y := eval lazy beta zeta in (c x) in
          generate_i2p_instance print to_tc arg y
      else
          lazymatch type of c with
          | ∀ a, @?P a =>
              let a := fresh a in
              notypeclasses refine (λ a, _);
              let y := eval lazy beta zeta in (c a) in
              generate_i2p_instance print to_tc arg y
          end
  | ?P ⊢ ?G =>
      (* Finish the instance. *)
      let Q := liFromSyntaxTerm P in
      (* Print rule in lithium syntax *)
(*    assert_fails (
          assert (⊢ Q); [
            liToSyntax;
            lazymatch goal with | |- ⊢ ?conv =>
            let P' := eval unfold li.ret in P in
            lazymatch conv with
            | P' => idtac
            | _ => idtac G ":-" conv
            end end;
            fail |] ); *)
      do_print ltac:(idtac "rule:" Q "⊢" G "term:" c);
      notypeclasses refine (@i2p _ G Q c)
  end.

Notation "'[instance' x ]" :=
  ltac:(generate_i2p_instance ltac:(fail) ltac:(generate_i2p_instance_to_tc_hook)
          constr:(tt) constr:(x)) (only parsing).
Notation "'[instance?' x ]" :=
  ltac:(generate_i2p_instance ltac:(idtac) ltac:(generate_i2p_instance_to_tc_hook)
          constr:(tt) constr:(x)) (only parsing).
Notation "'[instance' x 'with' y ]" :=
  ltac:(generate_i2p_instance ltac:(fail) ltac:(generate_i2p_instance_to_tc_hook)
          constr:(y) constr:(x)) (only parsing).
Notation "'[instance?' x 'with' y ]" :=
  ltac:(generate_i2p_instance ltac:(idtac) ltac:(generate_i2p_instance_to_tc_hook)
          constr:(y) constr:(x)) (only parsing).
Notation "'[instance' x 'as' y ]" :=
  ltac:(generate_i2p_instance ltac:(fail) ltac:(fun _ _ => y)
          constr:(tt) constr:(x)) (only parsing).
Notation "'[instance?' x 'as' y ]" :=
  ltac:(generate_i2p_instance ltac:(idtac) ltac:(fun _ _ => y)
          constr:(tt) constr:(x)) (only parsing).

(** * Optimization: Introduce let-bindings for environment *)
Notation "'HIDDEN'" := (Envs _ _ _) (only printing).

Ltac li_pm_reduce_val v :=
  let v := li_pm_reduce_hook v in
  let v := reduction.pm_eval v in v.
Ltac li_pm_reduce :=
  match goal with
  | H := Envs _ _ _ |- ?u =>
    let u := eval cbv [H] in u in
    let u := li_pm_reduce_val u in
    change u
  | |- ?u =>
    let u := li_pm_reduce_val u in
    change u
  end.
Ltac li_pm_reflexivity := li_pm_reduce; exact eq_refl.

Ltac let_bind_envs :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
    let with_H tac :=
      match goal with
      | [ H := Envs _ _ _ |- _] =>
        (** if we already have a binding, try to reuse it *)
        lazymatch Δ with H => tac H | _ => unify Δ (H); tac H end
      | [ H := Envs _ _ _ |- _] =>
        (** if reusing does not work, create a new let-binding *)
        lazymatch Δ with
        | Envs _ _ _ =>
          let H' := fresh "IPM_JANNO" in
          pose (H' := Δ);
          clear H;
          rename H' into H
        end;
        tac H
      | _ =>
        (** otherwise, create a new binding *)
        lazymatch Δ with
        | Envs _ _ _ =>
          let H := fresh "IPM_JANNO" in
          pose (H := Δ);
          hnf in (value of H);
          tac H
        end
      end in
    with_H ltac:(fun H => change_no_check (envs_entails H P))
  end.

(** * Checking if the context contains ownership of a certain assertion *)
(** Note that this implementation requires that [let_bind_envs] has
  been called previously when there was a envs_entails goal. *)
Ltac check_own_in_context P :=
  let rec go Hs :=
      lazymatch Hs with
      | Esnoc ?Hs2 ?id ?Q =>
        first [ unify Q P with typeclass_instances | go Hs2 ]
      end in
  match goal with
  | H := Envs ?Δi ?Δs _ |- _ =>
      first [ go Δs | go Δi ]
  end.
Global Hint Extern 1 (CheckOwnInContext ?P) => (check_own_in_context P; constructor; exact: I) : typeclass_instances.

(** * Optimization: Introduce let-bindings for subterms of the goal *)
Definition LET_ID {A} (x : A) : A := x.
Arguments LET_ID : simpl never.
Notation "'HIDDEN'" := (LET_ID _) (only printing).
Strategy expand [LET_ID].

(* These tactics are prefixed with "li_" because they work with
[LET_ID] and are a bit more specialized than one might expect. *)
Tactic Notation "li_let_bind" constr(T) tactic3(tac) :=
  try (assert_fails (is_var T);
       let H := fresh "LET_GOAL" in
       pose H := (LET_ID T);
       let G := tac H in
       change_no_check G).

Ltac li_unfold_lets_containing H :=
  repeat match goal with
       | Hx := context [ H ] |- _ =>
         unfold LET_ID in Hx;
         unfold Hx in *;
         clear Hx
       end.

Ltac li_unfold_lets_in_context :=
  repeat match goal with
  | H := LET_ID _ |- _ => unfold LET_ID in H; unfold H; clear H
  | H := Envs _ _ _ |- _  => unfold H; clear H
  end.
