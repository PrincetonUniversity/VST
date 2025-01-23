From lithium Require Import definitions.
From caesium Require Import base lang.
From refinedc.typing Require Import programs.

(** This file contains a solver for location (semantic) equality based on [lia]
and an [autorewrite] hint database [refinedc_loc_eq_rewrite] that the user can
extend with more rewriting rules. *)

(** * Hint database *)

Create HintDb refinedc_loc_eq_rewrite discriminated.

(** Rules to inject [nat] operations in to [Z]. *)
#[export] Hint Rewrite Nat2Z.inj_mul : refinedc_loc_eq_rewrite.
#[export] Hint Rewrite Nat2Z.inj_add : refinedc_loc_eq_rewrite.
#[export] Hint Rewrite Nat2Z.inj_sub using lia : refinedc_loc_eq_rewrite.
#[export] Hint Rewrite Z2Nat.id using lia : refinedc_loc_eq_rewrite.

(** Rule to eliminate [Z.shiftl]. *)
#[export] Hint Rewrite Z.shiftl_mul_pow2 using lia : refinedc_loc_eq_rewrite.

(** * Tactics *)

Lemma eq_loc (l1 l2 : loc): l1.1 = l2.1 → l1.2 = l2.2 → l1 = l2.
Proof. destruct l1, l2 => /= -> -> //. Qed.

(** Turns an equality over locations into an equality over physical addresses
(in type [Z]) that has been simplified with [autorewrite]. This tactics only
succeeds if the compared locations have convertible allocation ids. *)
Ltac prepare_loc_eq :=
  (* Sanity check on the goal. *)
  lazymatch goal with
  | |- @eq val (val_of_loc _) (val_of_loc _) => f_equal
  | |- @eq ?A _ _ => unify A loc
  | |- @eq _ _ _  => fail "[simpl_loc_eq]: goal not an equality between locations"
  | |- _          => fail "[simpl_loc_eq]: goal not an equality"
  end;
  (* Remove all [offset_loc] and [shift_loc]. *)
  rewrite ?/offset_loc ?shift_loc_assoc; rewrite ?/shift_loc;
  (* Checking that both sides have the same [alloc_id]. *)
  notypeclasses refine (eq_loc _ _ _ _); [ reflexivity | simpl ];
  (* Unfold [addr] (useful if we use [ring]) and rewrite with the hints. *)
  unfold addr in *; autorewrite with refinedc_loc_eq_rewrite.

(** Solver for location equality. *)
Ltac solve_loc_eq :=
  (* We try [reflexivity] first since it very often suffices. *)
  first [ reflexivity | prepare_loc_eq; lia ].

Inductive FICLocSemantic : Set :=.
Definition find_in_context_type_loc_semantic_inst :=
  [instance @find_in_context_type_loc_id with FICLocSemantic].
Global Existing Instance find_in_context_type_loc_semantic_inst | 20.
Definition find_in_context_type_val_P_loc_semantic_inst :=
  [instance @find_in_context_type_val_P_loc_id with FICLocSemantic].
Global Existing Instance find_in_context_type_val_P_loc_semantic_inst | 20.
Definition find_in_context_loc_in_bounds_semantic_inst :=
  [instance @find_in_context_loc_in_bounds with FICLocSemantic].
Global Existing Instance find_in_context_loc_in_bounds_semantic_inst | 20.
Definition find_in_context_loc_in_bounds_type_semantic_inst :=
  [instance @find_in_context_loc_in_bounds_loc with FICLocSemantic].
Global Existing Instance find_in_context_loc_in_bounds_type_semantic_inst | 30.

Lemma tac_solve_loc_eq `{!typeG Σ} l1 β1 ty1 l2 β2 ty2:
  l1 = l2 →
  FindHypEqual FICLocSemantic (l1 ◁ₗ{β1} ty1) (l2 ◁ₗ{β2} ty2) (l1 ◁ₗ{β2} ty2).
Proof. by move => ->. Qed.

Global Hint Extern 10 (FindHypEqual FICLocSemantic (_ ◁ₗ{_} _) (_ ◁ₗ{_} _) _) =>
  (notypeclasses refine (tac_solve_loc_eq _ _ _ _ _ _ _); solve_loc_eq) : typeclass_instances.

Lemma tac_loc_in_bounds_solve_loc_eq `{!typeG Σ} l1 l2 n1 n2:
  l1 = l2 →
  FindHypEqual FICLocSemantic (loc_in_bounds l1 n1) (loc_in_bounds l2 n2) (loc_in_bounds l1 n2).
Proof. by move => ->. Qed.

Global Hint Extern 10 (FindHypEqual FICLocSemantic (loc_in_bounds _ _) (loc_in_bounds _ _) _) =>
  (notypeclasses refine (tac_loc_in_bounds_solve_loc_eq _ _ _ _ _); solve_loc_eq) : typeclass_instances.

Section test.
  Context (l : loc).
  Context (id : prov).
  Context (a : addr).
  Context (n n1 n2 n3 : Z).
  Context (i j : nat).
  Context (PAGE_SIZE : Z := 4096).

  Goal (l = l)%Z.
  solve_loc_eq. Qed.

  Goal (@eq loc (id, a) (id, a))%Z.
  solve_loc_eq. Qed.

  Goal ((l.1, l.2) = l)%Z.
  solve_loc_eq. Qed.

  Goal ((l.1, l.2 + n)%Z = l +ₗ n)%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ n1 +ₗ n2) = (l +ₗ (n1 + n2)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ 0%nat * n) = l)%Z.
  solve_loc_eq. Qed.

  Goal ((id, a + n1 + n2) = (id, a + (n1 + n2)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n + (i + j)%nat)) = (l +ₗ (n + i + j)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n * PAGE_SIZE + i ≪ 12)) = (l +ₗ (n + i) * PAGE_SIZE))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n1 + 0%nat) * n2) = (l +ₗ (n1 * n2)))%Z.
  solve_loc_eq. Qed.

  Goal ((l +ₗ (n1 + (i + j)%nat) * n2) = (l +ₗ (n1 + i + j) * n2))%Z.
  solve_loc_eq. Qed.

  Goal (l = (l.1, l.2 * 1))%Z.
  solve_loc_eq. Qed.
End test.
