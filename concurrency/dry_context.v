Require Import concurrency.dry_machine.
Require Import concurrency.erased_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import ccc26x86.Asm_coop.
Require Import ccc26x86.Asm_event.
Require Import compcert.common.Globalenvs.
Import Concur.

Module SEM <: Semantics.
               Definition G := Asm.genv.
               Definition C := state.
               Definition Sem := Asm_EvSem.               
End SEM.


Module DryMachine:= DryMachineShell SEM.
Module ErasedMachine := ErasedMachineShell SEM.
Module mySchedule := mySchedule.
(** DryConc machine instantiated for X86*)
Module DryConc :=
  CoarseMachine mySchedule DryMachine.

(** FineConc machine instantiated for X86*)
Module FineConc :=
  FineMachine mySchedule DryMachine.

(** X86-SC machine*)
Module X86SC :=
  FineMachine mySchedule ErasedMachine.

Parameter initU: mySchedule.schedule.
Parameter the_program: Asm.program.

Definition init_mem := Genv.init_mem the_program.
Definition init_perm : option access_map :=
  match init_mem with
  | Some m => Some (getMaxPerm m)
  | None => None
  end.

Definition the_ge := Globalenvs.Genv.globalenv the_program.

Definition coarse_semantics:=
  DryConc.MachineSemantics initU init_perm.

Definition fine_semantics:=
  FineConc.MachineSemantics initU init_perm.

Definition x86_sc_semantics :=
  X86SC.MachineSemantics initU None.
  

