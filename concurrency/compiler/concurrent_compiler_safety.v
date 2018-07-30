(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
 *)


Require Import compcert.common.Globalenvs.

Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.

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

  Notation SHM U:= (ConcurMachineSemantics(HybridMachine:=SourceHybridMachine) U).
  Notation THM U:= (ConcurMachineSemantics(HybridMachine:=TargetHybridMachine) U).
  Variable opt_init_mem_source: option Memory.Mem.mem.
  Variable opt_init_mem_target: option Memory.Mem.mem.
  Definition concurrent_simulation_safety_preservation:=
    forall U init_mem_source init_mem_source' init_thread main args,
      let res1:= permissions.getCurPerm init_mem_source in
      let res := (res1,permissions.empty_map) in
      let init_tp_source:= ThreadPool.mkPool(ThreadPool:=SourceThreadPool) (Krun init_thread) res in
      let init_MachState_source U:= (U, nil, init_tp_source) in
      opt_init_mem_source = Some init_mem_source ->
      machine_semantics.initial_machine (SHM opt_init_mem_source) (Some res) init_mem_source init_tp_source init_mem_source' main args ->
      (forall n U, HybridCoarseMachine.csafe (init_MachState_source U) init_mem_source' n) ->
      exists init_mem_target init_mem_target' init_thread_target,
        let res_target:= permissions.getCurPerm init_mem_target' in
        let init_tp_target:= ThreadPool.mkPool (Krun init_thread_target) (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        opt_init_mem_target = Some init_mem_target /\
        machine_semantics.initial_machine (THM opt_init_mem_target) (Some res) init_mem_target init_tp_target init_mem_target' main args /\
        (forall n, HybridCoarseMachine.csafe init_MachState_target init_mem_target' n).





(*

  
  
  Definition concurrent_simulation_safety_preservation 
    init_U
      (SIM: HybridMachine_simulation 
              (ConcurMachineSemantics(HybridMachine:=SourceHybridMachine) init_U)
              (ConcurMachineSemantics(HybridMachine:=TargetHybridMachine) init_U)):=
    forall U init_mem_source init_thread main args,
      initial_source_thread SIM init_mem_source init_thread main args ->
      let res:= permissions.getCurPerm init_mem_source in
      let init_tp_source:= ThreadPool.mkPool (Krun init_thread) (res,permissions.empty_map) in
      let init_MachState_source:= (U, nil, init_tp_source) in
      (forall n, HybridCoarseMachine.csafe init_MachState_source init_mem_source n) ->
      exists init_mem_target init_thread_target,
        initial_target_thread SIM init_mem_target init_thread_target main args /\
        let res_target:= permissions.getCurPerm init_mem_target in
        let init_tp_target:= ThreadPool.mkPool (Krun init_thread_target) (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        (forall n, HybridCoarseMachine.csafe init_MachState_target init_mem_target n).

  
  (* We define a simpler version that doesn't depend on SIM,
     then we reduce it to the previous version by showing:
     match_initial_thread SIM -> source_init_state
   *)
  Definition concurrent_simulation_safety_preservation_export
             (source_init_state:
                Memory.mem -> @semC SemSource -> Values.val -> list Values.val -> Prop) 
             (target_init_state:
                Memory.mem -> @semC SemTarget -> Values.val -> list Values.val -> Prop)   :=
    forall U init_mem_source init_thread main args,
      source_init_state init_mem_source init_thread main args ->
      let res:= permissions.getCurPerm init_mem_source in
      let init_tp_source:= ThreadPool.mkPool
                             (Sem:=SemSource)
                             (Krun init_thread) (res,permissions.empty_map) in
      let init_MachState_source:= (U, nil, init_tp_source) in
      (forall n, HybridCoarseMachine.csafe
              (Sem:=SemSource)
              (ThreadPool:=SourceThreadPool)
              (machineSig:=SourceMachineSig)
              init_MachState_source init_mem_source n) ->
      exists init_mem_target init_thread_target,
        target_init_state init_mem_target init_thread_target main args /\
        let res_target:= permissions.getCurPerm init_mem_target in
        let init_tp_target:= ThreadPool.mkPool
                               (Sem:=SemTarget) (Krun init_thread_target) (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        (forall n, HybridCoarseMachine.csafe
                (Sem:=SemTarget)
                (ThreadPool:=TargetThreadPool)
                (machineSig:=TargetMachineSig)
                init_MachState_target init_mem_target n).

  Lemma forall_exists_commute:
      forall {A} (P Q: A -> Prop),
        (forall k, P k -> Q k) ->
        (exists k, P k) ->
        (exists k, Q k).
    Proof.
      intros ? ? ? ? (?&?); eexists; eauto.
    Qed.
    
  Lemma concur_safety_preserv_equiv:
    forall (source_init_state:
         Memory.mem -> @semC SemSource -> Values.val -> list Values.val -> Prop)
      (target_init_state:
       Memory.mem -> @semC SemTarget -> Values.val -> list Values.val -> Prop)
      init_U SIM,
      (forall init_mem_source init_thread main args,
        source_init_state init_mem_source init_thread main args ->
        initial_source_thread SIM init_mem_source init_thread main args) ->
      (forall init_mem_target init_thread main args,
        initial_target_thread SIM init_mem_target init_thread main args ->
        target_init_state init_mem_target init_thread main args) ->
    @concurrent_simulation_safety_preservation init_U SIM ->
    concurrent_simulation_safety_preservation_export source_init_state target_init_state.
  Proof.
    intros ?????? H ?; intros.
    eapply forall_exists_commute; [ intros H4 |eapply H; eauto].
    eapply forall_exists_commute; intros ? (?&?); auto.
  Qed.*)
    
End ConcurrentCopmpilerSafety.

  
