Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.TheSchedule.

Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.HybridMachine. Import Concur.
(*Require Import VST.concurrency.HybridMachine_lemmas. *)
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.

Require Import VST.concurrency.dry_context.
Require Import VST.concurrency.HybridMachine_lemmas.
Require Import VST.concurrency.erased_machine.

(*Semantics*)
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_sim.
Require Import VST.concurrency.Clight_coreSemantincsForMachines.
Require Import VST.concurrency.Clight_bounds.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.ssromega. (*omega in ssrnat *)
Set Bullet Behavior "Strict Subproofs".

Import Concur threadPool.

Module THE_DRY_MACHINE_SOURCE.
  Module SCH:= THESCH.
  Module SEM:= ClightSEM_core.
  (*Import SCH SEM.*)

  (*Module DSEM := DryMachineShell SEM.
  Module DryMachine <: ConcurrentMachine:= CoarseMachine SCH DSEM.
  Notation DMachineSem:= DryMachine.MachineSemantics.
  Notation new_DMachineSem:= DryMachine.new_MachineSemantics.
  Notation dstate:= DryMachine.SIG.ThreadPool.t.
  Notation dmachine_state:= DryMachine.MachState.
  (*Module DTP:= DryMachine.SIG.ThreadPool.*)
  Import DSEM.DryMachineLemmas event_semantics.*)

  Module DMS  <: MachinesSig with Module SEM := ClightSEM_core.
     Module SEM:= ClightSEM_core .

     About mySchedule.
     (*Old DSEM*)
     Module DryMachine <: DryMachineSig SEM := DryMachineShell SEM.
     Module ErasedMachine :=  ErasedMachineShell SEM.

     Module DryConc <: ConcurrentMachine :=
      CoarseMachine SCH DryMachine.
     Notation DMachineSem:= DryConc.MachineSemantics.
     Notation new_DMachineSem:= DryConc.new_MachineSemantics.

     Module FineConc := HybridMachineSig.FineMachine SCH DryMachine.
     (** SC machine*)
     Module SC := HybridMachineSig.FineMachine SCH ErasedMachine.
     Module DTP<: ThreadPoolSig:= DryConc.SIG.ThreadPool.

     Import DryMachine DTP.

  End DMS.
  Module DryMachineLemmas := ThreadPoolWF SEM DMS.


End THE_DRY_MACHINE_SOURCE.

