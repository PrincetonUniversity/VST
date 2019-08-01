Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.compiler.pair.


Require Import VST.concurrency.memsem_lemmas.
Import BinNums.
Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.
 
Set Bullet Behavior "Strict Subproofs".
Set Nested Proofs Allowed.

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.


Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Require Import VST.concurrency.compiler.single_thread_simulation_proof.


Instance inject_delta_map_monotonic:
  Inject_Monotonic Events.inject_delta_map.
Proof.
  intros ??????.
Admitted.

Module Concurrent_correctness
       (CC_correct: CompCert_correctness)
       (Args: ThreadSimulationArguments).
  Module TSim:= (ThreadedSimulation CC_correct Args).
  Import TSim.
  Import MySyncSimulation.MySimulationTactics.MyConcurMatch.MyThreadSimulationDefinitions.

  
  Section TrivialSimulations.
    Definition lift_state {resources Sem1 Sem2}
               (f: @semC Sem1 -> @semC Sem2):
      @OrdinalPool.t resources Sem1 ->
      @OrdinalPool.t resources Sem2.
      intros X; inv X.
      econstructor; eauto.
      intros h; specialize (pool h).
      inv pool; [econstructor 1|
                 econstructor 2|
                 econstructor 3|
                 econstructor 4]; eauto.
    Defined.
    Inductive refl_match {st_t:Type}: unit -> meminj -> st_t -> mem -> st_t -> mem -> Prop :=
    | Build_refl_match:
        forall m st, refl_match tt (Mem.flat_inj (Mem.nextblock m)) st m st m.
    Definition trivial_order: unit -> unit -> Prop := (fun _ _=> False).
    Lemma trivial_order_wf: well_founded trivial_order.
    Proof. do 2 econstructor. inv H. Qed.
    
    Lemma trivial_clight_simulation:
      (HybridMachine_simulation
           (ClightMachine.DMS.ClightConcurSem
              (ge:=Clight_g)
              (Genv.init_mem (Ctypes.program_of_program C_program)))
           (HybConcSem (Some 0)%nat (Genv.init_mem (Ctypes.program_of_program C_program)))).
    Proof.
        intros.
        unshelve econstructor.
        - exact unit.
        - simpl; intros; eapply refl_match; eauto.
        - unshelve econstructor.
          + exact trivial_order.
          + exact trivial_order_wf.
          + (*initial_setup*)

            simpl; intros.
            exists (Mem.flat_inj (Mem.nextblock s_mem')), tt.
            unshelve eexists.
            eapply lift_state;
              [|eapply s_mach_state]; apply SState. (*needs to go after*)
            exists s_mem, s_mem', r1; split.
            2: { econstructor. }
            inv H; econstructor; eauto.
            simpl in *.
            destruct r1; inv H1.
            econstructor; simpl in *.
            normal.
            2: { simpl. unfold lift_state.
                 rewrite e; simpl.
                 unfold  OrdinalPool.mkPool.
                 f_equal. }
            econstructor.
            admit. (* wrong order! *)
            split; eauto.

          + (*thread_diagram*)
            intros; unfold Clight_g; auto.
            unshelve eexists. {
              simpl.
              eapply lift_state;
                [|eapply st1']; apply SState. }
            
        
        
      Admitted.
      Lemma trivial_asm_simulation:
        forall ap (Hsafe:Asm_core.safe_genv (@the_ge ap)), 
        (HybridMachine_simulation
           (HybConcSem None (Genv.init_mem ap))
           (X86Context.AsmConcurSem
              (the_program:=ap)
              (Hsafe:=Hsafe)
              (Genv.init_mem ap))).
      Admitted.
    End TrivialSimulations.


    (* NOTE: This section could be moved to where the simulations are defined. *) 
    Section SimulationTransitivity.
      Lemma HBSimulation_transitivity:
        forall G1 G2 G3 TID SCH C1 C2 C3 res,
        forall (Machine1 : @machine_semantics.ConcurSemantics G1 TID SCH _ C1 mem res)
               (Machine2 : @machine_semantics.ConcurSemantics G2 TID SCH _ C2 mem res)
               (Machine3 : @machine_semantics.ConcurSemantics G3 TID SCH _ C3 mem res),
          HybridMachine_simulation Machine1 Machine2 -> 
          HybridMachine_simulation Machine2 Machine3 ->
          HybridMachine_simulation Machine1 Machine3.
      Proof.
        destruct 1 as [index1 match_state1 SIM1].
        destruct 1 as [index2 match_state2 SIM2].
        eapply Build_HybridMachine_simulation with (index := (index1 * index2)%type)
                                                   (match_state := fun a j c1 m1 c3 m3 => exists j1 j2 c2 m2, j = compose_meminj j1 j2 /\
                                                                                                              match_state1 (fst a) j1 c1 m1 c2 m2 /\ match_state2 (snd a) j2 c2 m2 c3 m3).
        inversion SIM1; inversion SIM2; econstructor.
        - apply Coqlib.wf_lex_ord; eauto.
        - intros.
          destruct (initial_setup _ _ _ _ _ _ H) as (? & ? & ? & ? & ? & ? & H2 & ?).
          destruct (initial_setup0 _ _ _ _ _ _ H2) as (? & ? & ? & ? & ? & ? & ? & ?).
          eexists; eexists (_, _); eauto 12.
        - intros.
          (* Where should the second ge come from?
      destruct (thread_diagram _ _ _ _ _ _ _ H _ _ _ _ H0) as (? & ? & ? & ? & ? & ?). *)
          admit.
        (*      edestruct thread_diagram0 as (? & ? & ? & ? & ? & ?); eauto.*)
        - intros.
          (* Where should the second ge come from?
      destruct (machine_diagram _ _ _ _ _ _ _ _ _ _ H _ _ _ _ H0) as (? & ? & ? & ? & ? & ?). *)
          admit.
        - intros ???????? (? & ? & ? & ? & ? & ? & ?) ?.
          edestruct thread_halted; eauto.
        - intros ?????? (? & ? & ? & ? & ? & ? & ?) ?.
          erewrite thread_running; eauto.
      Admitted.
    End SimulationTransitivity.

  Lemma initial_memories_are_equal:
    forall (p : Clight.program) (tp : Asm.program),
      Genv.init_mem tp = Genv.init_mem (Ctypes.program_of_program p).
  Proof.
    intros p tp.
  Admitted.
  
  Lemma ConcurrentCompilerCorrectness:
    forall (tp:Asm.program),
      CC_correct.CompCert_compiler C_program = Some tp ->
      forall asm_genv_safety,
        ConcurrentCompilerCorrectness_specification Clight_g tp asm_genv_safety
          (Genv.init_mem (Ctypes.program_of_program C_program)) (Genv.init_mem tp)
  .
  Proof.
    unfold ConcurrentCompilerCorrectness_specification.
    intros.
    eapply HBSimulation_transitivity; eauto.
    - eapply trivial_clight_simulation; eauto.
    - eapply HBSimulation_transitivity.
      + econstructor.
        eapply compile_all_threads.
      + replace (Genv.init_mem (Ctypes.program_of_program C_program))
          with (Genv.init_mem tp) by
            eapply initial_memories_are_equal.
        eapply trivial_asm_simulation; eauto.
  Qed.

  
End Concurrent_correctness.
