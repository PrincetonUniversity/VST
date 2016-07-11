Require Import concurrency.dry_machine.
Require Import concurrency.erased_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import ccc26x86.Asm_coop.
Require Import ccc26x86.Asm_event.
Require Import compcert.common.Globalenvs.
Import Concur.

Module X86SEM <: Semantics.
               Definition G := Asm.genv.
               Definition C := state.
               Definition Sem := Asm_EvSem.
End X86SEM.
  
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


Module AsmContext (SEM : Semantics) (Machines : MachinesSig with Module SEM := SEM).

  Import Machines.
  Parameter initU: mySchedule.schedule.
  Parameter F : Type.
  Parameter V : Type.
  Parameter the_program: AST.program F V.
  
  Definition init_mem := Genv.init_mem the_program.
  Definition init_perm : option access_map :=
    match init_mem with
    | Some m => Some (getCurPerm m)
    | None => None
    end.
  
  Definition the_ge := Globalenvs.Genv.globalenv the_program.
  
  Definition coarse_semantics:=
    DryConc.MachineSemantics initU init_perm.
  
  Definition fine_semantics:=
    FineConc.MachineSemantics initU init_perm.
  
  Definition sc_semantics :=
    SC.MachineSemantics initU None.
  
End AsmContext.
  
  

