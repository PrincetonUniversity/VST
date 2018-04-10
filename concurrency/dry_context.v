(** * Instances of machines for Assembly languages *)

(*TODO: rename to Asm_context.v *)

Require Import VST.concurrency.HybridMachine.
Require Import VST.concurrency.erased_machine.
Require Import VST.concurrency.threads_lemmas.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.semantics.
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

    Instance dryPool : ThreadPool.ThreadPool := OrdinalPool.OrdinalThreadPool.
    
    (** Instantiating the Dry Fine Concurrency Machine *)
    Definition dryFineMach : @HybridMachine DryHybridMachine.resources asmSem dryPool :=

      @HybridFineMachine.HybridFineMachine DryHybridMachine.resources _ _ (@DryHybridMachine.DryHybridMachineSig asmSem dryPool).
    (** Instantiating the Dry Coarse Concurrency Machine *)
    Definition dryCoarseMach : @HybridMachine DryHybridMachine.resources asmSem dryPool :=
      @HybridCoarseMachine.HybridCoarseMachine DryHybridMachine.resources _ _ (@DryHybridMachine.DryHybridMachineSig asmSem dryPool).


    Instance bareRes : Resources := BareMachine.resources.
    Instance barePool : @ThreadPool.ThreadPool bareRes asmSem := @BareMachine.ordinalPool asmSem.
    (** Instatiating the Bare Concurrency Machine *)
    Definition bareMach : @HybridMachine BareMachine.resources asmSem barePool :=
      @HybridFineMachine.HybridFineMachine bareRes _ _ (@BareMachine.BareMachineSig asmSem).

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

    Definition tpc_init the_ge f arg := initial_core coarse_semantics 0 the_ge f arg.
    Definition tpf_init the_ge f arg := initial_core fine_semantics 0 the_ge f arg.
    Definition bare_init the_ge f arg := initial_core bare_semantics 0 the_ge f arg.

  End AsmContext.
End AsmContext.


