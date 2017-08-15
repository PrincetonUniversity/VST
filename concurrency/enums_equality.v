Require Import compcert.lib.Axioms.

Require Import VST.concurrency.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.pos.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.addressFiniteMap. (*The finite maps*)
Require Import VST.concurrency.threads_lemmas.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.semantics.
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
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.jstep.
Require Import VST.veric.res_predicates.


(**)
Require Import VST.veric.res_predicates. (*For the precondition of lock make and free*)

(*  This shoul be replaced by global:
    Require Import VST.concurrency.lksize.  *)

Require Import (*compcert_linking*) VST.concurrency.permissions VST.concurrency.threadPool.

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
