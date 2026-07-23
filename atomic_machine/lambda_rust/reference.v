(**
  Frozen reference operational semantics for the POPL'18 lambda-Rust core
  language, ported to Rocq 9 and modern stdpp.

  The operational rules are kept separate from the new event semantics.
  See UPSTREAM.md for the exact source revision and a porting manifest.
*)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import base gmap list.

Require Export VST.atomic_machine.lambda_rust.syntax.

Import ListNotations.
Open Scope Z_scope.
Open Scope lambda_rust_loc_scope.

Set Default Proof Using "Type".

(** The reference state stores the race-detector state beside each value. *)

Inductive lock_state : Type :=
| WSt
| RSt (n : nat).

Definition state : Type := gmap loc (lock_state * val).

Fixpoint init_mem (l : loc) (n : nat) (sigma : state) : state :=
  match n with
  | O => sigma
  | S n =>
      <[l := (RSt 0, LitV LitPoison)]>
        (init_mem (l +ₗ 1)%L n sigma)
  end.

Fixpoint free_mem (l : loc) (n : nat) (sigma : state) : state :=
  match n with
  | O => sigma
  | S n => delete l (free_mem (l +ₗ 1)%L n sigma)
  end.

(**
  Equality of dangling pointers is intentionally nondeterministic.  This is
  why equality and inequality can overlap, and why the explicit CAS-stuck
  rule below is semantically significant.
*)
Inductive lit_eq (sigma : state) : base_lit -> base_lit -> Prop :=
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

Inductive lit_neq (sigma : state) : base_lit -> base_lit -> Prop :=
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

Inductive bin_op_eval (sigma : state)
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

(** The original head-step relation. *)

Inductive head_step : expr -> state -> expr -> state -> list expr -> Prop :=
| BinOpS op l1 l2 l' sigma :
    bin_op_eval sigma op l1 l2 l' ->
    head_step
      (BinOp op (Lit l1) (Lit l2)) sigma
      (Lit l') sigma []
| BetaS f xl e e' el sigma :
    Forall (fun ei => is_Some (to_val ei)) el ->
    Closed (cons_binder f (app_binder xl [])) e ->
    subst_l (f :: xl) (Rec f xl e :: el) e = Some e' ->
    head_step (App (Rec f xl e) el) sigma e' sigma []
| ReadScS l n v sigma :
    sigma !! l = Some (RSt n, v) ->
    head_step
      (Read ScOrd (Lit (LitLoc l))) sigma
      (of_val v) sigma []
| ReadNa1S l n v sigma :
    sigma !! l = Some (RSt n, v) ->
    head_step
      (Read Na1Ord (Lit (LitLoc l))) sigma
      (Read Na2Ord (Lit (LitLoc l)))
      (<[l := (RSt (S n), v)]> sigma) []
| ReadNa2S l n v sigma :
    sigma !! l = Some (RSt (S n), v) ->
    head_step
      (Read Na2Ord (Lit (LitLoc l))) sigma
      (of_val v)
      (<[l := (RSt n, v)]> sigma) []
| WriteScS l e v v' sigma :
    to_val e = Some v ->
    sigma !! l = Some (RSt 0, v') ->
    head_step
      (Write ScOrd (Lit (LitLoc l)) e) sigma
      (Lit LitPoison)
      (<[l := (RSt 0, v)]> sigma) []
| WriteNa1S l e v v' sigma :
    to_val e = Some v ->
    sigma !! l = Some (RSt 0, v') ->
    head_step
      (Write Na1Ord (Lit (LitLoc l)) e) sigma
      (Write Na2Ord (Lit (LitLoc l)) e)
      (<[l := (WSt, v')]> sigma) []
| WriteNa2S l e v v' sigma :
    to_val e = Some v ->
    sigma !! l = Some (WSt, v') ->
    head_step
      (Write Na2Ord (Lit (LitLoc l)) e) sigma
      (Lit LitPoison)
      (<[l := (RSt 0, v)]> sigma) []
| CasFailS l n e1 lit1 e2 lit2 litl sigma :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    sigma !! l = Some (RSt n, LitV litl) ->
    lit_neq sigma lit1 litl ->
    head_step
      (CAS (Lit (LitLoc l)) e1 e2) sigma
      (Lit (lit_of_bool false)) sigma []
| CasSucS l e1 lit1 e2 lit2 litl sigma :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    sigma !! l = Some (RSt 0, LitV litl) ->
    lit_eq sigma lit1 litl ->
    head_step
      (CAS (Lit (LitLoc l)) e1 e2) sigma
      (Lit (lit_of_bool true))
      (<[l := (RSt 0, LitV lit2)]> sigma) []
| CasStuckS l n e1 lit1 e2 lit2 litl sigma :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    sigma !! l = Some (RSt n, LitV litl) ->
    (0 < n)%nat ->
    lit_eq sigma lit1 litl ->
    head_step
      (CAS (Lit (LitLoc l)) e1 e2) sigma
      stuck_term sigma []
| AllocS n l sigma :
    0 < n ->
    (forall m, sigma !! (l +ₗ m)%L = None) ->
    head_step
      (Alloc (Lit (LitInt n))) sigma
      (Lit (LitLoc l))
      (init_mem l (Z.to_nat n) sigma) []
| FreeS n l sigma :
    0 < n ->
    (forall m,
        is_Some (sigma !! (l +ₗ m)%L) <-> 0 <= m < n) ->
    head_step
      (Free (Lit (LitInt n)) (Lit (LitLoc l))) sigma
      (Lit LitPoison)
      (free_mem l (Z.to_nat n) sigma) []
| CaseS i el e sigma :
    0 <= i ->
    el !! Z.to_nat i = Some e ->
    head_step
      (Case (Lit (LitInt i)) el) sigma e sigma []
| ForkS e sigma :
    head_step
      (Fork e) sigma
      (Lit LitPoison) sigma [e].

(**
  Standalone versions of Iris's evaluation-context closure and concurrent
  thread-pool closure at the pinned revision.  Keeping these definitions
  here avoids importing the 2017 Iris API merely to state the reference
  transition system.
*)

Inductive prim_step : expr -> state -> expr -> state -> list expr -> Prop :=
| EctxStep K e1 sigma1 e2 sigma2 spawned :
    head_step e1 sigma1 e2 sigma2 spawned ->
    prim_step
      (fill K e1) sigma1
      (fill K e2) sigma2
      spawned.

Definition thread_pool : Type := list expr.
Definition configuration : Type := (thread_pool * state)%type.

Inductive step : configuration -> configuration -> Prop :=
| ThreadStep t1 e1 t2 sigma1 e2 sigma2 spawned :
    prim_step e1 sigma1 e2 sigma2 spawned ->
    step
      (t1 ++ e1 :: t2, sigma1)
      ((t1 ++ e2 :: t2) ++ spawned, sigma2).

Definition initial_configuration (e : expr) (sigma : state)
    : configuration :=
  ([e], sigma).

Definition head_reducible (e : expr) (sigma : state) : Prop :=
  exists e' sigma' spawned, head_step e sigma e' sigma' spawned.

Definition reducible (e : expr) (sigma : state) : Prop :=
  exists e' sigma' spawned, prim_step e sigma e' sigma' spawned.
