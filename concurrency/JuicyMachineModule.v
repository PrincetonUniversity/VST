Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.dry_machine. Import Concur.
(*Require Import VST.concurrency.dry_machine_lemmas. *)
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.

Require Import VST.concurrency.TheSchedule.

(*Semantics*)
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.ClightSemantincsForMachines.

Module THE_JUICY_MACHINE.
  Module SCH:= THESCH.
  Module SEM:= ClightSEM.
  Import SCH SEM.

  (* JuicyMachineShell : Semantics -> ConcurrentSemanticsSig *)
  Module JSEM := JuicyMachineShell SEM.
  (* CoarseMachine : Schedule -> ConcurrentSemanticsSig -> ConcurrentSemantics *)
  Module JuicyMachine := CoarseMachine SCH JSEM.
  Notation JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=JuicyMachine.SIG.ThreadPool.
  Import JSEM.JuicyMachineLemmas.

End THE_JUICY_MACHINE.