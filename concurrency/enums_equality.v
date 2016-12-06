Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.addressFiniteMap. (*The finite maps*)
Require Import concurrency.threads_lemmas.
Require Import concurrency.rmap_locking.
Require Import concurrency.lksize.
Require Import concurrency.semantics.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

(*From msl get the juice! *)
Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.jstep.
Require Import veric.res_predicates.


(**)
Require Import veric.res_predicates. (*For the precondition of lock make and free*)

(*  This shoul be replaced by global: 
    Require Import concurrency.lksize.  *)

Require Import (*compcert_linking*) concurrency.permissions concurrency.threadPool.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(* given n <= m, returns the list [n-1,...,0] with proofs of < m *)
    Program Fixpoint enum_from n m (pr : le n m) : list (ordinal m) :=
      match n with
        O => nil
      | S n => (@Ordinal m n ltac:(rewrite <-Heq_n in *; apply (introT leP pr)))
                :: @enum_from n m ltac:(rewrite <-Heq_n in *; apply le_Sn_le, pr)
      end.
    
    Definition enum n := Coq.Lists.List.rev (@enum_from n n (le_refl n)).

Axiom ord_enum_enum:
  forall n : nat, @eq (list (ordinal n)) (ord_enum n) (enum n).
