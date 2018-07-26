(** * Instances of machines for Assembly languages *)

(*TODO: rename to Asm_context.v *)

Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
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
    Existing Instance DryHybridMachine.DryHybridMachineSig.

    (** Instantiating the Dry Fine Concurrency Machine *)
    Instance FineDilMem : DiluteMem :=
      {| diluteMem := setMaxPerm |}.
    intros.
    split; auto.
    Defined.
    Instance dryFineMach : @HybridMachine _ _ _ _ _ _ :=
      HybridFineMachine.HybridFineMachine.

    Existing Instance HybridCoarseMachine.DilMem.

    (** Instantiating the Dry Coarse Concurrency Machine *)
    Instance dryCoarseMach : @HybridMachine _ _ _ _ _ _ :=
      HybridCoarseMachine.HybridCoarseMachine.

    (** Instatiating the Bare Concurrency Machine *)
    Existing Instance BareMachine.resources.

    Instance BareDilMem : DiluteMem :=
      {| diluteMem := erasePerm |}.
    intros.
    split; auto.
    Defined.
    Instance bareMach : @HybridMachine BareMachine.resources _ OrdinalPool.OrdinalThreadPool _ _ _ :=
      @HybridFineMachine.HybridFineMachine BareMachine.resources _ _ BareMachine.BareMachineSig BareDilMem.

    Variable initU : seq nat.

    Definition coarse_semantics:=
      MachineSemantics(HybridMachine := dryCoarseMach) initU None.

    Definition fine_semantics:=
      MachineSemantics(HybridMachine := dryFineMach) initU None.

    Definition bare_semantics :=
      MachineSemantics(HybridMachine := bareMach) initU None.

    Definition tpc_init m c f arg := initial_core coarse_semantics 0 m c f arg.
    Definition tpf_init m c f arg := initial_core fine_semantics 0 m c f arg.
    Definition bare_init m c f arg := initial_core bare_semantics 0 m c f arg.

  End AsmContext.
End AsmContext.


