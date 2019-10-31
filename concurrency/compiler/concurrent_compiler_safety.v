(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
 *)


Require Import compcert.common.Globalenvs.

Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.lib.tactics.

Set Implicit Arguments.

Section ConcurrentCopmpilerSafety.
  Import HybridMachineSig HybridCoarseMachine.

  (*This definitions are specialized to dry machines
    Why? to show that the initial res is defined by the initial mem
   *)
  Notation resources:= HybridMachine.DryHybridMachine.dryResources.
  Context {SemSource SemTarget: Semantics}
          {SourceThreadPool : @ThreadPool.ThreadPool resources SemSource}
          {TargetThreadPool : @ThreadPool.ThreadPool resources SemTarget}
          {SourceMachineSig: @MachineSig _ _ SourceThreadPool}
          {TargetMachineSig: @MachineSig _ _ TargetThreadPool}.
  
  Definition SourceHybridMachine:=
    @HybridCoarseMachine resources SemSource SourceThreadPool SourceMachineSig.
  
  Definition TargetHybridMachine:=
    @HybridCoarseMachine resources SemTarget TargetThreadPool TargetMachineSig.

  Definition part_sem_target:=
    event_semantics.msem(@semSem (SemTarget)).
  Notation SourceSemantics:= (fun m => ConcurMachineSemantics(HybridMachine:=SourceHybridMachine) m).
  Notation TargetSemantics:= (fun m => ConcurMachineSemantics(HybridMachine:=TargetHybridMachine) m).
  Variable opt_init_mem_source: option Memory.Mem.mem.
  Variable opt_init_mem_target: option Memory.Mem.mem.
  Definition concurrent_simulation_safety_preservation:=
    forall U init_mem_source init_mem_source' init_thread main args,
      let res1:= permissions.getCurPerm init_mem_source in
      let res := (res1,permissions.empty_map) in
      let init_tp_source:= ThreadPool.mkPool
                             (ThreadPool:=SourceThreadPool)
                             (Krun init_thread) res in
      let init_MachState_source U:= (U, nil, init_tp_source) in
      opt_init_mem_source = Some init_mem_source ->
      machine_semantics.initial_machine 
        (SourceSemantics (Some init_mem_source))
        (Some res) init_mem_source init_tp_source init_mem_source' main args ->
      (forall n U, HybridCoarseMachine.csafe (init_MachState_source U) init_mem_source' n) ->
      exists init_mem_target init_mem_target' init_thread_target,
        let res_target:= permissions.getCurPerm init_mem_target' in
        let init_tp_target:= ThreadPool.mkPool
                               (Krun init_thread_target)
                               (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        opt_init_mem_target = Some init_mem_target /\
        machine_semantics.initial_machine
          (TargetSemantics opt_init_mem_target) (Some res) init_mem_target init_tp_target init_mem_target' main args /\
        (forall n, HybridCoarseMachine.csafe init_MachState_target init_mem_target' n).

  
    Section CleanSafetyPreservation.
      Definition empty_trace: event_trace:= nil. 
      Definition init_thread_pool {S} {TP:ThreadPool.ThreadPool(Sem:=S)}
                 (U:schedule) init_mem_source init_thread:=
        let res1:= permissions.getCurPerm init_mem_source in
        let res := (res1,permissions.empty_map) in
        let init_tp_source:= ThreadPool.mkPool
                               (ThreadPool:= TP )
                               (Krun init_thread) res in
        (init_tp_source). (*(U, empty_trace, init_tp_source).*)
      Definition first_cpm {S} {TP: @ThreadPool.ThreadPool _ S} U init_tp :MachState(ThreadPool:=TP):=
        (U, empty_trace, init_tp).

      (*also defined in main_definitions.v. TODO: unify*)
      Definition main_ptr (prog:Ctypes.program Clight.function):=
        Values.Vptr (Ctypes.prog_main prog) Integers.Ptrofs.zero.
      
      Import HybridCoarseMachine Memory.Mem.
      
      Inductive initial_machine_state
                {S G}
                {TP: @ThreadPool.ThreadPool resources S}
                SS
        : mem -> @ThreadPool.t resources S TP  -> Prop :=
      | Build_init_mach_state:
          forall init_tp U src_m src_m' src_tp main args
            (res: (permissions.access_map * permissions.access_map)),
            init_tp = init_thread_pool U src_m' src_tp ->
            machine_semantics.initial_machine
              (G:=G)(TID:=nat)(SCH:=schedule)(TR:=event_trace)
              (SS (Some src_m))
              (Some res) src_m init_tp src_m' main args ->
            initial_machine_state SS src_m' init_tp.

      Definition main_safety_preservation
                 {S1 S2 G1 G2 TP1 TP2}
                 {MS1: @MachineSig _ S1 TP1}
                 {MS2: @MachineSig _ S2 TP2}
                 sem1
                 sem2:=
        forall (Asm_program:Asm.program) (C_program:Clight.program),
        forall src_m' src_tp,
          @initial_machine_state S1 G1 TP1 sem1 src_m' src_tp ->
          (forall n U, csafe (U, empty_trace, src_tp) src_m' n) ->
        exists  tgt_tp tgt_m',
          @initial_machine_state S2 G2 TP2 sem2 tgt_m' tgt_tp ->
          (forall n U, csafe (U, empty_trace, tgt_tp) tgt_m' n).
      
      
        
        
        
End CleanSafetyPreservation.
        
End ConcurrentCopmpilerSafety.

  
