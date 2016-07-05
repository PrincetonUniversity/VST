Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.dry_machine. Import Concur.
(*Require Import concurrency.dry_machine_lemmas. *)
Require Import concurrency.lksize.
Require Import concurrency.permissions.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import concurrency.ssromega. (*omega in ssrnat *)

(*The simulations*)
Require Import sepcomp.wholeprog_simulations.

(*General erasure*)
Require Import concurrency.erasure_signature.
Require Import concurrency.erasure_proof. Import Parching.

From mathcomp.ssreflect Require Import ssreflect seq.

Import addressFiniteMap.

(* I will import this from CLight once we port it*)
(*Module ClightSEM<: Semantics.
  Definition G:= nat.
  Definition C:= nat.
  Definition M:= Mem.mem.
  Definition  
End ClightSEM.*)

    (*



(** BEHOLD THE THEOREM :) *)
(*Just to be explicit*)


Module ClightErasure:= ErasureFnctr Parching.

Theorem clight_erasure:
  forall (U : DryMachine.Sch) rmap pmap,
    match_rmap_perm rmap pmap -> 
    Wholeprog_sim.Wholeprog_sim (JMachineSem U (Some rmap)) 
                                (DMachineSem U (Some pmap))
                                erasure_proof.Parching.genv
                                erasure_proof.Parching.genv
                                erasure_proof.Parching.main
                                ClightErasure.ge_inv
                                ClightErasure.init_inv
                                ClightErasure.halt_inv.
Proof.
  Proof. intros. apply ClightErasure.erasure. assumption. Qed.*)


  