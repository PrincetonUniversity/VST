Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.semantics.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.dry_machine. Import Concur.
(*Require Import concurrency.dry_machine_lemmas. *)
Require Import concurrency.lksize.
Require Import concurrency.permissions.

(*Semantics*)
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import sepcomp.event_semantics.

Module ClightSEM <: Semantics.
  Definition F: Type := fundef.
  Definition V: Type := type.
  Definition G := genv.
  Definition C := corestate.
  Definition getEnv (g:G): Genv.t F V := genv_genv g.
  (* We might want to define this properly or
     factor the machines so we don't need events here. *)
  Parameter CLN_evsem : @EvSem G C.
  Parameter CLN_msem :
    msem CLN_evsem = CLN_memsem.
  Definition Sem := CLN_evsem.
  Parameter step_decay: forall g c m tr c' m',
      event_semantics.ev_step (Sem) g c m tr c' m' ->
      decay m m'.
End ClightSEM.