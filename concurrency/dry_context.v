Require Import concurrency.dry_machine.
Require Import concurrency.erased_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import compcert.common.Globalenvs.
Import Concur.
  
Module Type MachinesSig.
  Declare Module SEM: Semantics.
  
  Module DryMachine := DryMachineShell SEM.
  Module ErasedMachine := ErasedMachineShell SEM.

  Module DryConc := CoarseMachine mySchedule DryMachine.
  (** FineConc machine instantiated for low-level language*)
  Module FineConc := FineMachine mySchedule DryMachine.
  (** SC machine*)
  Module SC := FineMachine mySchedule ErasedMachine.
End MachinesSig.


Module Type AsmContext (SEM : Semantics)
       (Machines : MachinesSig with Module SEM := SEM).

  Import Machines.
  Parameter initU: mySchedule.schedule.

  Parameter init_mem : option Memory.Mem.mem.
  Definition init_perm : option access_map :=
    match init_mem with
    | Some m => Some (getCurPerm m)
    | None => None
    end.
  
  Parameter the_ge : SEM.G.
  
  Definition coarse_semantics:=
    DryConc.MachineSemantics initU init_perm.
  
  Definition fine_semantics:=
    FineConc.MachineSemantics initU init_perm.
  
  Definition sc_semantics :=
    SC.MachineSemantics initU None.
  
End AsmContext.

