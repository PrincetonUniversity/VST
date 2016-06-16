Require Import concurrency.dry_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import ccc26x86.Asm_coop.
Import Concur.

Parameter hf : I64Helpers.helper_functions.
Module SEM <: Semantics.
               Definition G := Asm.genv.
               Definition C := state.
               Definition Sem := Asm_mem_sem hf.               
End SEM.
               
Module DryMachine:= DryMachineShell SEM.
Module myCoarseSemantics :=
  CoarseMachine mySchedule DryMachine.
Module myFineSemantics :=
  FineMachine mySchedule  DryMachine.
Module mySchedule := mySchedule.

Parameter initU: mySchedule.schedule.
Parameter the_ge : SEM.G.

Definition coarse_semantics:=
  myCoarseSemantics.MachineSemantics initU.

Definition fine_semantics:=
  myFineSemantics.MachineSemantics initU.
