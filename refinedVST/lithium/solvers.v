From lithium Require Export base.
From lithium Require Import hooks pure_definitions normalize.
From VST.lithium Require Import simpl_classes.
From iris.bi Require Import monpred.
(** This file provides various pure solvers. *)

(** * [refined_solver]
    Version of naive_solver which fails faster. *)
Tactic Notation "refined_solver" tactic(tac) :=
  unfold iff, not in *;
  repeat match goal with
  | H : context [∀ _, _ ∧ _ ] |- _ =>
    repeat setoid_rewrite forall_and_distr in H; revert H
  | H : context [Is_true _ ] |- _ =>
    repeat setoid_rewrite Is_true_eq in H
  | |- Is_true _ => repeat setoid_rewrite Is_true_eq
  end;
  let rec go :=
  repeat match goal with
  (**i solve the goal *)
  | |- _ => fast_done
  (**i intros *)
  | |- ∀ _, _ => intro
  (**i simplification of assumptions *)
  | H : False |- _ => destruct H
  | H : _ ∧ _ |- _ =>
     (* Work around bug https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
     let H1 := fresh in let H2 := fresh in
     destruct H as [H1 H2]; try clear H
  | H : ∃ _, _  |- _ =>
     let x := fresh in let Hx := fresh in
     destruct H as [x Hx]; try clear H
  | H : ?P → ?Q, H2 : ?P |- _ => specialize (H H2)
  (**i simplify and solve equalities *)
  (* | |- _ => progress simplify_eq/= *)
  | |- _ => progress subst; csimpl in *
  (**i operations that generate more subgoals *)
  | |- _ ∧ _ => split
  (* | |- Is_true (bool_decide _) => apply (bool_decide_pack _) *)
  (* | |- Is_true (_ && _) => apply andb_True; split *)
  | H : _ ∨ _ |- _ =>
     let H1 := fresh in destruct H as [H1|H1]; try clear H
  (* | H : Is_true (_ || _) |- _ => *)
     (* apply orb_True in H; let H1 := fresh in destruct H as [H1|H1]; try clear H *)
  (**i solve the goal using the user supplied tactic *)
  | |- _ => solve [tac]
  end;
  (**i use recursion to enable backtracking on the following clauses. *)
  match goal with
  (**i instantiation of the conclusion *)
  | |- ∃ x, _ => no_new_unsolved_evars ltac:(eexists; go)
  | |- _ ∨ _ => first [left; go | right; go]
  (* | |- Is_true (_ || _) => apply orb_True; first [left; go | right; go] *)
  | _ =>
    (**i instantiations of assumptions. *)
    match goal with
    | H : ?P → ?Q |- _ =>
      let H' := fresh "H" in
      assert P as H'; [clear H; go|];
      specialize (H H'); clear H'; go
    end
  end in go.
Tactic Notation "refined_solver" := refined_solver eauto.

(** * [normalize_and_simpl_goal] *)
Ltac normalize_and_simpl_impl handle_exist :=
  let do_intro :=
    idtac;
    match goal with
    | |- (∃ _, _) → _ =>
        lazymatch handle_exist with
        | true => case
        | false => fail 1 "exist not handled"
        end
    | |- (monPred_exist _, _) → _ =>
        lazymatch handle_exist with
        | true => case
        | false => fail 1 "monPred_exist not handled"
        end
    | |- (_ ∧ _) → _ => case
    | |- (_ = _) → _ =>
        check_injection_hook;
        let Hi := fresh "Hi" in move => Hi; injection Hi; clear Hi
    | |- False → _ => case
    | |- ?P → _ => assert_is_not_trivial P; let H := fresh "H" in intros H; subst
    | |- _ => move => _
    end in
  lazymatch goal with
  (* relying on the fact that unification variables cannot contain
  dependent variables to distinguish between dependent and non
  dependent forall *)
  | |- ?P -> ?Q =>
    lazymatch type of P with
    | Prop => first [
        (* first check if the hyp is trivial *)
        assert_is_trivial P; intros _
      | progress normalize_goal_impl
      | let changed := open_constr:(_) in
        notypeclasses refine (simpl_impl_unsafe_impl changed P _ Q _); [solve [refine _] |];
        (* We need to simpl here to make sure that we only introduce
        fully simpl'd terms into the context (and do beta reduction
        for the lemma application above). *)
        simpl;
        lazymatch changed with
        | true => idtac
        | false => do_intro
        end
      | do_intro
      ]
    (* just some unused variable, forget it *)
    | _ => move => _
    end
  end.

Lemma intro_and_True P :
  (P ∧ True) → P.
Proof. naive_solver. Qed.

Ltac normalize_and_simpl_goal_step :=
  first [
      splitting_fast_done
    | progress normalize_goal; simpl
    | lazymatch goal with
      | |- ∃ _, _ => fail 1 "normalize_and_simpl_goal stop in exist"
      end
    | lazymatch goal with
      | |- monPred_exist _ _ => fail 1 "normalize_and_simpl_goal stop in monPred_exist"
      end
    | lazymatch goal with
      | |- _ ∧ _ => split
      end
    | notypeclasses refine (simpl_and_unsafe _); [solve [refine _] |]; simpl
    | lazymatch goal with
    (* relying on the fact that unification variables cannot contain
       dependent variables to distinguish between dependent and non dependent forall *)
      | |- ?P -> ?Q =>
        normalize_and_simpl_impl true
      | |- forall _ : ?P, _ =>
        lazymatch P with
        | (prod _ _) => case
        | unit => case
        | _ => intro
        end
    end ].

Ltac normalize_and_simpl_goal := repeat normalize_and_simpl_goal_step.

(** * [compute_map_lookup] *)
Ltac compute_map_lookup :=
  lazymatch goal with
  | |- ?Q !! _ = Some _ => try (is_var Q; unfold Q)
  | _ => fail "unknown goal for compute_map_lookup"
  end;
  solve [repeat lazymatch goal with
  | |- <[?x:=?s]> ?Q !! ?y = Some ?res =>
    lazymatch x with
    | y => change_no_check (Some s = Some res); reflexivity
    | _ => change_no_check (Q !! y = Some res)
    end
  end ].

(** * Enriching the context for lia  *)
Definition enrich_marker {A} (f : A) : A := f.
Ltac enrich_context_base :=
    repeat match goal with
         | |- context C [ Z.quot ?a ?b ] =>
           let G := context C[enrich_marker Z.quot a b] in
           change_no_check G;
           try have ?:=Z.quot_lt a b ltac:(lia) ltac:(lia);
           try have ?:=Z.quot_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ Z.rem ?a ?b ] =>
           let G := context C[enrich_marker Z.rem a b] in
           change_no_check G;
           try have ?:=Z.rem_bound_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ Z.modulo ?a ?b ] =>
           let G := context C[enrich_marker Z.modulo a b] in
           change_no_check G;
           try have ?:=Z.mod_bound_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ length (filter ?P ?l) ] =>
           let G := context C[enrich_marker length (filter P l)] in
           change_no_check G;
           pose proof (filter_length P l)
           end.

Ltac enrich_context :=
  enrich_context_base;
  enrich_context_hook;
  unfold enrich_marker.

Section enrich_test.
  Local Open Scope Z_scope.
  Goal ∀ n m, 0 < n → 1 < m → n `quot` m = n `rem` m.
    move => n m ??. enrich_context.
  Abort.
End enrich_test.

(** * Instantiate foralls using ideas from SMT triggers *)
(** [trigger_foralls] instantiates [set_Forall P s] quantifiers in the
context if it can find [x ∈ s]. *)

Ltac hide_set_Forall :=
  repeat lazymatch goal with
    | H : set_Forall ?P ?s |- _  => change (set_Forall P s) with (tc_opaque set_Forall P s) in H
    end.
(** [set_unfold_trigger] is a version of [set_unfold] that is
compatible with [trigger_foralls]. In particular, it does not unfold
[set_Forall] in the context. *)
Ltac set_unfold_trigger :=
  (* For some reason, the [set_unfold] removes the [tc_opaque], so we
  don't have to do that manually. *)
  hide_set_Forall; set_unfold.

Ltac trigger_foralls :=
  repeat lazymatch goal with
    | H : set_Forall _ (_ ∪ _) |- _ =>
        pose proof (set_Forall_union_inv_1 _ _ _ H);
        pose proof (set_Forall_union_inv_2 _ _ _ H);
        clear H
    end;
  repeat lazymatch goal with
    | H : set_Forall _ ({[_]}) |- _ => move/set_Forall_singleton in H end;
  repeat match goal with
    | H1 : set_Forall _ ?s, H2 : _ ∈ ?s |- _ => learn_hyp (H1 _ H2)
    end;
  repeat match goal with
    | H1 : list_Forall _ ?l, H2 : ?l !! _ = Some _ |- _ => learn_hyp (H1 _ _ H2)
    end;
  lazy beta in *|-.

(** * [solve_goal]  *)
Ltac reduce_closed_Z :=
  idtac;
  reduce_closed_Z_hook;
  repeat match goal with
  | |- context [(?a * ?b)%nat] => progress reduce_closed (a * b)%nat
  | H : context [(?a * ?b)%nat] |- _ => progress reduce_closed (a * b)%nat
  | |- context [(?a ≪ ?b)%Z] => progress reduce_closed (a ≪ b)%Z
  | H : context [(?a ≪ ?b)%Z] |- _ => progress reduce_closed (a ≪ b)%Z
  | |- context [(?a ≫ ?b)%Z] => progress reduce_closed (a ≫ b)%Z
  | H : context [(?a ≫ ?b)%Z] |- _ => progress reduce_closed (a ≫ b)%Z
  end.


Ltac solve_goal :=
  simpl in *;
  try fast_done;
  solve_goal_prepare_hook;
  normalize_and_simpl_goal;
  solve_goal_normalized_prepare_hook; reduce_closed_Z; enrich_context;
  repeat case_bool_decide => //; repeat case_decide => //; repeat case_match => //;
  refined_solver lia.
