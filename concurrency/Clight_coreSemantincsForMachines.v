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
Require Import veric.Clight_core.
Require Import sepcomp.event_semantics.

Module ClightSEM_core <: Semantics.
  Definition F: Type := fundef.
  Definition V: Type := type.
  Definition G := genv.
  Definition C := CC_core.
  Definition getEnv (g:G): Genv.t F V := genv_genv g.
  (* We might want to define this properly or
     factor the machines so we don't need events here. *)
  Parameter CLNC_evsem : @EvSem G C.
  Parameter CLNC_msem :
    msem CLNC_evsem = CLNC_memsem.
  Definition Sem := CLNC_evsem.
  Parameter step_decay: forall g c m tr c' m',
      event_semantics.ev_step (Sem) g c m tr c' m' ->
      decay m m'.
End ClightSEM_core.