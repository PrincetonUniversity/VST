(** * Instances of machines for Assembly languages *)

Require Import concurrency.HybridMachine.
Require Import concurrency.erased_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.semantics.
Require Import concurrency.HybridMachineSig.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Axioms.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.


Module AsmContext.
  Import HybridMachineSig.

  Section AsmContext.
    (** Assuming some Assembly semantics *)
    Context {asmSem : Semantics}.

    Instance dryPool : ThreadPool.ThreadPool := @DryHybridMachine.ordinalPool asmSem.
    
    (** Instantiating the Dry Fine Concurrency Machine *)
    Definition dryFineMach : @HybridMachine DryHybridMachine.resources asmSem dryPool :=
      @HybridFineMachine.HybridFineMachine DryHybridMachine.resources _ _ (@DryHybridMachine.DryHybridMachineSig asmSem).
    (** Instantiating the Dry Coarse Concurrency Machine *)
    Definition dryCoarseMach : @HybridMachine DryHybridMachine.resources asmSem dryPool :=
      @HybridCoarseMachine.HybridCoarseMachine DryHybridMachine.resources _ _ (@DryHybridMachine.DryHybridMachineSig asmSem).


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

  Ltac pf_cleanup :=
    repeat match goal with
           | [H1: invariant ?X, H2: invariant ?X |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M, H2: ThreadPool.containsThread ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M,
                  H2: ThreadPool.containsThread (@ThreadPool.updThreadC _ ?TP _ _) ?M |- _] =>
             apply ThreadPool.cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply ThreadPool.cnt_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M,
                  H2: ThreadPool.containsThread (@ThreadPool.updThread _ ?TP _ _ _) ?M |- _] =>
             apply ThreadPool.cntUpdate' in H2;
             assert (H1 = H2) by (by eapply ThreadPool.cnt_irr); subst H2
           end.

End AsmContext.


