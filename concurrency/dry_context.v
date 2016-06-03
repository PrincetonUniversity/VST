Require Import concurrency.dry_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.

Import Concur.
Declare Module SEM:Semantics.
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