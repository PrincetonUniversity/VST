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
Require Import concurrency.erasure_proof.

From mathcomp.ssreflect Require Import ssreflect seq.

Import addressFiniteMap.

