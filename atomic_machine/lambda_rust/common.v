(**
  Heap-cell-polymorphic operations shared by the reference and event
  semantics.

  The two semantics use different heap cells, but both heaps are finite maps
  over lambda-Rust locations.  Keeping these definitions polymorphic in the
  cell type lets both semantics use the same operations and relations
  directly.  These are factored from the reference port of the pinned
  lambda-Rust development described in [UPSTREAM.md].
*)

From Stdlib Require Import ZArith.
From stdpp Require Import base gmap.

From lrust.lang Require Export lang.

Open Scope Z_scope.
Open Scope loc_scope.

Set Default Proof Using "Type".

(** Initialize and free a consecutive range of gmap cells. *)

Fixpoint alloc_gmap {A : Type}
    (initial : A) (l : loc) (n : nat) (sigma : gmap loc A)
    : gmap loc A :=
  match n with
  | O => sigma
  | S n =>
      <[l := initial]> (alloc_gmap initial (l +ₗ 1)%L n sigma)
  end.

Fixpoint free_gmap {A : Type}
    (l : loc) (n : nat) (sigma : gmap loc A) : gmap loc A :=
  match n with
  | O => sigma
  | S n => delete l (free_gmap (l +ₗ 1)%L n sigma)
  end.

(** The literal relations keep upstream's names, so they are qualified. *)

Module sq_mem.

(**
  Equality of dangling pointers is intentionally nondeterministic.  The cell
  type is irrelevant: only whether a location is allocated is observed.
*)
Inductive lit_eq {A : Type} (sigma : gmap loc A)
    : base_lit -> base_lit -> Prop :=
| IntRefl z :
    lit_eq sigma (LitInt z) (LitInt z)
| LocRefl l :
    lit_eq sigma (LitLoc l) (LitLoc l)
| LocUnallocL l1 l2 :
    sigma !! l1 = None ->
    lit_eq sigma (LitLoc l1) (LitLoc l2)
| LocUnallocR l1 l2 :
    sigma !! l2 = None ->
    lit_eq sigma (LitLoc l1) (LitLoc l2).

Inductive bin_op_eval {A : Type} (sigma : gmap loc A)
    : bin_op -> base_lit -> base_lit -> base_lit -> Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval sigma PlusOp
      (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval sigma MinusOp
      (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval sigma LeOp
      (LitInt z1) (LitInt z2)
      (lit_of_bool (bool_decide (z1 <= z2)))
| BinOpEqTrue l1 l2 :
    lit_eq sigma l1 l2 ->
    bin_op_eval sigma EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq l1 l2 ->
    bin_op_eval sigma EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z :
    bin_op_eval sigma OffsetOp
      (LitLoc l) (LitInt z) (LitLoc (l +ₗ z)%L).

End sq_mem.

(** The definitions mostly coincide with lambda-rust's when [sigma := state]. *)

Lemma init_mem_equiv l n (sigma : state) :
  init_mem l n sigma = alloc_gmap (RSt 0, LitV LitPoison) l n sigma.
Proof. revert l. induction n as [ | n IH ]; intros l; simpl; [ done | by rewrite IH ]. Qed.

Lemma free_mem_equiv l n (sigma : state) :
  free_mem l n sigma = free_gmap l n sigma.
Proof. revert l. induction n as [ | n IH ]; intros l; simpl; [ done | by rewrite IH ]. Qed.

Lemma lit_eq_equiv (sigma : state) lit1 lit2 :
  lit_eq sigma lit1 lit2 <-> sq_mem.lit_eq sigma lit1 lit2.
Proof. split; destruct 1; eauto using lit_eq, sq_mem.lit_eq. Qed.

Lemma bin_op_eval_equiv (sigma : state) op lit1 lit2 lit' :
  bin_op_eval sigma op lit1 lit2 lit' <-> sq_mem.bin_op_eval sigma op lit1 lit2 lit'.
Proof. split; destruct 1; constructor; by try apply lit_eq_equiv. Qed.
