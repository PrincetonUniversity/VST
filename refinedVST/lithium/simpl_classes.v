From iris.bi Require Import bi.
From lithium Require Export base.

(** This file provides the classes for the simplification
infrastructure for pure sideconditions. *)

(** * [SimplExist] and [SimplForall] *)
Class SimplExist {prop:bi} (A : Type) (Q : (A → prop) → prop) :=
  simpl_exist P : Q P ⊢ ∃ x : A, P x.
Global Hint Mode SimplExist + ! - : typeclass_instances.

(* TODO: refactor similar to SimplExist? *)
Class SimplForall (T : Type) (n : nat) (e : T → Prop) (Q: Prop) := simpl_forall_proof : Q → ∀ x, e x.

(** * [SimplImpl] and [SimplAnd] *)

(** ** [SimplImplUnsafe] and [SimplAndUnsafe] *)
(** changed = false indicates that P should be introduced into the context in addition to Ps *)
Class SimplImplUnsafe (changed : bool) (P : Prop) (Ps : Prop) := simpl_impl_unsafe : P → Ps.
Class SimplAndUnsafe (P : Prop) (Ps : Prop) := simpl_and_unsafe: Ps → P.

Lemma simpl_impl_unsafe_impl changed (P1 P2 T : Prop) `{!SimplImplUnsafe changed P1 P2} :
  (if changed then (P2 → T) else (P1 → P2 → T)) → (P1 → T).
Proof. unfold SimplImplUnsafe in *. destruct changed; naive_solver. Qed.
Lemma simpl_and_unsafe_and (P1 P2 T : Prop) `{!SimplAndUnsafe P1 P2} :
  P2 ∧ T → P1 ∧ T.
Proof. unfold SimplAndUnsafe in *. naive_solver. Qed.

Global Instance simpland_unsafe_not_neq {A} (x y : A) :
  SimplAndUnsafe (¬ (x ≠ y)) (x = y) | 1000.
Proof. move => ?. by eauto. Qed.

(** ** [SimplImpl] and [SimplAnd] *)
(** [SimplImpl] and [SimplAnd] are safe variants which ensure that no
information is lost. *)
Class SimplImpl (P : Prop) (Ps : Prop) := simpl_impl : Ps ↔ P.
Class SimplAnd (P : Prop) (Ps : Prop) := simpl_and: Ps ↔ P.
Global Instance simplimpl_simplunsafe P Ps {Hi: SimplImpl P Ps} :
  SimplImplUnsafe true P Ps.
Proof. unfold SimplImpl, SimplImplUnsafe in *. naive_solver. Qed.
Global Instance simpland_simplunsafe P Ps {Hi: SimplAnd P Ps} :
  SimplAndUnsafe P Ps.
Proof. unfold SimplAnd, SimplAndUnsafe in *. naive_solver. Qed.

(** ** [SimplImplRel] and [SimplAndRel] *)
Class SimplImplRel {A} (R : relation A) (changed : bool) (x1 x2 : A) (Ps : Prop)
  := simpl_impl_eq: Ps ↔ R x1 x2.
Class SimplAndRel {A} (R : relation A) (x1 x2 : A) (Ps : Prop)
  := simpl_and_eq: Ps ↔ R x1 x2.
Global Instance simpl_impl_rel_inst1 {A} R (x1 x2 : A) Ps `{!SimplImplRel R c x1 x2 Ps} :
  SimplImpl (R x1 x2) Ps.
Proof. unfold SimplImplRel, SimplImpl in *. naive_solver. Qed.
Global Instance simpl_impl_rel_inst2 {A} R (x1 x2 : A) Ps `{!SimplImplRel R c x2 x1 Ps} `{!Symmetric R} :
  SimplImpl (R x1 x2) Ps.
Proof. unfold SimplImplRel, SimplImpl in *. naive_solver. Qed.
Global Instance simpl_and_rel_inst1 {A} R (x1 x2 : A) Ps `{!SimplAndRel R x1 x2 Ps} :
  SimplAnd (R x1 x2) Ps.
Proof. unfold SimplAndRel, SimplAnd in *. naive_solver. Qed.
Global Instance simpl_and_rel_inst2 {A} R (x1 x2 : A) Ps `{!SimplAndRel R x2 x1 Ps} `{!Symmetric R} :
  SimplAnd (R x1 x2) Ps.
Proof. unfold SimplAndRel, SimplAnd in *. naive_solver. Qed.

(** ** [SimplBoth] *)
Class SimplBoth (P1 P2 : Prop) := simpl_both: P1 ↔ P2.
Global Instance simpl_impl_both_inst P1 P2 {Hboth : SimplBoth P1 P2}:
  SimplImpl P1 P2.
Proof. unfold SimplBoth in Hboth. split; naive_solver. Qed.
Global Instance simpl_and_both_inst P1 P2 {Hboth : SimplBoth P1 P2}:
  SimplAnd P1 P2.
Proof. unfold SimplBoth in Hboth. split; naive_solver. Qed.

(** ** [SimplBothRel] *)
Class SimplBothRel {A} (R : relation A) (x1 x2 : A) (P2 : Prop) := simpl_both_eq: R x1 x2 ↔ P2.
Global Instance simpl_both_rel_inst1 {A} R (x1 x2 : A) P2 `{!SimplBothRel R x1 x2 P2}:
  SimplBoth (R x1 x2) P2.
Proof. unfold SimplBothRel, SimplBoth in *. naive_solver. Qed.
Global Instance simpl_both_rel_inst2 {A} R (x1 x2 : A) P2 `{!SimplBothRel R x2 x1 P2} `{!Symmetric R}:
  SimplBoth (R x1 x2) P2.
Proof. unfold SimplBothRel, SimplBoth in *. naive_solver. Qed.
