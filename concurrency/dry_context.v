Require Import concurrency.dry_machine.
Require Import concurrency.erased_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Axioms.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Import Concur.
  
Module Type MachinesSig.
  Declare Module SEM: Semantics.
  
  Module DryMachine := DryMachineShell SEM.
  Module ErasedMachine := ErasedMachineShell SEM.

  Module DryConc := CoarseMachine mySchedule DryMachine.
  Module FineConc := FineMachine mySchedule DryMachine.
  (** SC machine*)
  Module SC := FineMachine mySchedule ErasedMachine.

  Import DryMachine ThreadPool.
  Global Ltac pf_cleanup :=
    repeat match goal with
           | [H1: invariant ?X, H2: invariant ?X |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
               subst H2
           | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
               subst H2
           | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M, H2: containsThread ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
             apply cntUpdateC' in H2;
               assert (H1 = H2) by (by eapply cnt_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
             apply cntUpdate' in H2;
               assert (H1 = H2) by (by eapply cnt_irr); subst H2
           end.
  
End MachinesSig.


Module Type AsmContext (SEM : Semantics)
       (Machines : MachinesSig with Module SEM := SEM).

  Import Machines.
  Parameter initU: mySchedule.schedule.

  Parameter init_mem : option Memory.Mem.mem.
  Definition init_perm  :=
    match init_mem with
    | Some m => Some (getCurPerm m, empty_map)
    | None => None
    end.
  
  Parameter the_ge : SEM.G.
  
  Definition coarse_semantics:=
    DryConc.MachineSemantics initU init_perm.
  
  Definition fine_semantics:=
    FineConc.MachineSemantics initU init_perm.
  
  Definition sc_semantics :=
    SC.MachineSemantics initU None.

  Definition tpc_init f arg := initial_core coarse_semantics the_ge f arg.
  Definition tpf_init f arg := initial_core fine_semantics the_ge f arg.
  Definition sc_init f arg := initial_core sc_semantics the_ge f arg.
  
End AsmContext.

