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

Require Export VST.atomic_machine.lambda_rust.syntax.

Open Scope Z_scope.
Open Scope lambda_rust_loc_scope.

Set Default Proof Using "Type".

(** Initialize and free a consecutive range of heap cells. *)

Fixpoint init_mem {A : Type}
    (initial : A) (l : loc) (n : nat) (sigma : gmap loc A)
    : gmap loc A :=
  match n with
  | O => sigma
  | S n =>
      <[l := initial]> (init_mem initial (l +ₗ 1)%L n sigma)
  end.

Fixpoint free_mem {A : Type}
    (l : loc) (n : nat) (sigma : gmap loc A) : gmap loc A :=
  match n with
  | O => sigma
  | S n => delete l (free_mem (l +ₗ 1)%L n sigma)
  end.

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

Inductive lit_neq {A : Type} (sigma : gmap loc A)
    : base_lit -> base_lit -> Prop :=
| IntNeq z1 z2 :
    z1 <> z2 ->
    lit_neq sigma (LitInt z1) (LitInt z2)
| LocNeq l1 l2 :
    l1 <> l2 ->
    lit_neq sigma (LitLoc l1) (LitLoc l2)
| LocNeqNullR l :
    lit_neq sigma (LitLoc l) (LitInt 0)
| LocNeqNullL l :
    lit_neq sigma (LitInt 0) (LitLoc l).

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
    lit_neq sigma l1 l2 ->
    bin_op_eval sigma EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z :
    bin_op_eval sigma OffsetOp
      (LitLoc l) (LitInt z) (LitLoc (l +ₗ z)%L).
