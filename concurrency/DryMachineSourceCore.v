Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.TheSchedule.

Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.dry_machine. Import Concur.
(*Require Import VST.concurrency.dry_machine_lemmas. *)
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.

Require Import VST.concurrency.dry_context.
Require Import VST.concurrency.dry_machine_lemmas.
Require Import VST.concurrency.erased_machine.

(*Semantics*)
Require Import veric.Clight_core.
Require Import veric.Clightcore_coop.
Require Import VST.sepcomp.event_semantics.
Require Import veric.Clight_sim.
Require Import VST.concurrency.ClightCoreSemantincsForMachines.
Require Import VST.concurrency.Clight_bounds.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.ssromega. (*omega in ssrnat *)
Set Bullet Behavior "Strict Subproofs".

Import Concur threadPool.

  Module SCH:= THESCH.
  Module SEM:= ClightCoreSEM.
  (*Import SCH SEM.*)

  (*Module DSEM := DryMachineShell SEM.
  Module DryMachine <: ConcurrentMachine:= CoarseMachine SCH DSEM.
  Notation DMachineSem:= DryMachine.MachineSemantics.
  Notation new_DMachineSem:= DryMachine.new_MachineSemantics.
  Notation dstate:= DryMachine.SIG.ThreadPool.t.
  Notation dmachine_state:= DryMachine.MachState.
  (*Module DTP:= DryMachine.SIG.ThreadPool.*)
  Import DSEM.DryMachineLemmas event_semantics.*)

  Module DMS  <: MachinesSig with Module SEM := ClightCoreSEM.
     Module SEM:= ClightCoreSEM .

     (*Old DSEM*)
     Module DryMachine <: DryMachineSig SEM := DryMachineShell SEM.
     Module ErasedMachine :=  ErasedMachineShell SEM.

     Module DryConc <: ConcurrentMachine :=
      CoarseMachine SCH DryMachine.
     Notation DMachineSem:= DryConc.MachineSemantics.
     Notation new_DMachineSem:= DryConc.new_MachineSemantics.

     Module FineConc := concurrent_machine.FineMachine SCH DryMachine.
     (** SC machine*)
     Module SC := concurrent_machine.FineMachine SCH ErasedMachine.
     Module DTP<: ThreadPoolSig:= DryConc.SIG.ThreadPool.

     Import DryMachine DTP.

  End DMS.
  Module DryMachineLemmas := ThreadPoolWF SEM DMS.
