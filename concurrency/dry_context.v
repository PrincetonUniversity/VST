(** * Instances of machines for Assembly languages *)

(*TODO: rename to Asm_context.v *)

Require Import VST.concurrency.HybridMachine.
Require Import VST.concurrency.erased_machine.
Require Import VST.concurrency.threads_lemmas.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.threadPool.
Require Import VST.concurrency.HybridMachineSig.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Axioms.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.


Module AsmContext.
  Import HybridMachineSig.

  Section AsmContext.
    (** Assuming some Assembly semantics *)
    Context {asmSem : Semantics}.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.dryResources.
    
    (** Instantiating the Dry Fine Concurrency Machine *)
    Instance FineDilMem : DiluteMem :=
      {| diluteMem := setMaxPerm |}.
    intros.
    split; auto.
    Defined.
    Instance dryFineMach : HybridMachine :=
      @HybridFineMachine.HybridFineMachine
        DryHybridMachine.dryResources _ _
        (@DryHybridMachine.DryHybridMachineSig _ _) FineDilMem.
    
    (** Instantiating the Dry Coarse Concurrency Machine *)
    Instance dryCoarseMach : HybridMachine  :=
      @HybridCoarseMachine.HybridCoarseMachine DryHybridMachine.dryResources _ _ (@DryHybridMachine.DryHybridMachineSig _ _).

    (** Instatiating the Bare Concurrency Machine *)
    Existing Instance BareMachine.resources.
    
    Instance BareDilMem : DiluteMem :=
      {| diluteMem := erasePerm |}.
    intros.
    split; auto.
    Defined.
    Instance bareMach : @HybridMachine BareMachine.resources _ OrdinalPool.OrdinalThreadPool :=
      @HybridFineMachine.HybridFineMachine BareMachine.resources _ _ BareMachine.BareMachineSig BareDilMem.

    Variable initU : seq nat.
    Variable init_mem : option Memory.Mem.mem.
    Definition init_perm  :=
      match init_mem with
      | Some m => Some (getCurPerm m, empty_map)
      | None => None
      end.

    Definition coarse_semantics:=
      @MachineSemantics _ _ _ dryCoarseMach initU init_perm.

    Definition fine_semantics:=
      @MachineSemantics _ _ _ dryFineMach initU init_perm.

    Definition bare_semantics :=
      @MachineSemantics _ _ _ bareMach initU None.

    Definition tpc_init the_ge m f arg := initial_core coarse_semantics 0 the_ge m f arg.
    Definition tpf_init the_ge m f arg := initial_core fine_semantics 0 the_ge m f arg.
    Definition bare_init the_ge m f arg := initial_core bare_semantics 0 the_ge m f arg.

  End AsmContext.
End AsmContext.


