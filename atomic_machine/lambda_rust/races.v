(**
  The access and race predicates from POPL'18 lambda-Rust, ported to use the
  standalone reference semantics.

  The large [safe_nonracing] proof from upstream is intentionally not copied:
  the new development should prove the corresponding result through the
  atomic-machine equivalence.  The predicates themselves are part of the
  observable reference specification.
*)

From Stdlib Require Import ZArith List.
From stdpp Require Import base list.

Require Export VST.atomic_machine.lambda_rust.reference.

Import ListNotations.
Open Scope Z_scope.
Open Scope lambda_rust_loc_scope.

Set Default Proof Using "Type".

Inductive access_kind : Type :=
| ReadAcc
| WriteAcc
| FreeAcc.

Inductive next_access_head
    : expr -> state -> access_kind * order -> loc -> Prop :=
| AccessRead ord l sigma :
    next_access_head
      (Read ord (Lit (LitLoc l))) sigma
      (ReadAcc, ord) l
| AccessWrite ord l e sigma :
    is_Some (to_val e) ->
    next_access_head
      (Write ord (Lit (LitLoc l)) e) sigma
      (WriteAcc, ord) l
| AccessCasFail l st e1 lit1 e2 lit2 litl sigma :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    lit_neq sigma lit1 litl ->
    sigma !! l = Some (st, LitV litl) ->
    next_access_head
      (CAS (Lit (LitLoc l)) e1 e2) sigma
      (ReadAcc, ScOrd) l
| AccessCasSuc l st e1 lit1 e2 lit2 litl sigma :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    lit_eq sigma lit1 litl ->
    sigma !! l = Some (st, LitV litl) ->
    next_access_head
      (CAS (Lit (LitLoc l)) e1 e2) sigma
      (WriteAcc, ScOrd) l
| AccessFree n l sigma i :
    0 <= i < n ->
    next_access_head
      (Free (Lit (LitInt n)) (Lit (LitLoc l))) sigma
      (FreeAcc, Na2Ord) (l +ₗ i)%L.

Definition next_access_thread
    (e : expr) (sigma : state)
    (a : access_kind * order) (l : loc) : Prop :=
  exists K e',
    next_access_head e' sigma a l /\
    e = fill K e'.

Definition next_accesses_thread_pool
    (threads : thread_pool) (sigma : state)
    (a1 a2 : access_kind * order) (l : loc) : Prop :=
  exists t1 e1 t2 e2 t3,
    threads = t1 ++ e1 :: t2 ++ e2 :: t3 /\
    next_access_thread e1 sigma a1 l /\
    next_access_thread e2 sigma a2 l.

Definition nonracing_accesses
    (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_thread_pool
    (threads : thread_pool) (sigma : state) : Prop :=
  forall l a1 a2,
    next_accesses_thread_pool threads sigma a1 a2 l ->
    nonracing_accesses a1 a2.
