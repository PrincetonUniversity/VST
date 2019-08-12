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
    Definition lift_c_state:
      @OrdinalPool.t dryResources (@ClightMachine.DMS.DSem Clight_g) ->
      @OrdinalPool.t dryResources (HybridSem (@Some nat O)).
    Proof.
      eapply lift_state. simpl; intros XX.
      apply SState; exact XX.
    Defined.
    Inductive refl_match {st_t:Type}: unit -> meminj -> st_t -> mem -> st_t -> mem -> Prop :=
    | Build_refl_match:
        forall m st, refl_match tt (Mem.flat_inj (Mem.nextblock m)) st m st m.
    Definition trivial_order: unit -> unit -> Prop := (fun _ _=> False).
    Lemma trivial_order_wf: well_founded trivial_order.
    Proof. do 2 econstructor. inv H. Qed.

    Lemma clight_step_nextblock:
      forall g f s m t s' m',
        ClightSemanticsForMachines.clc_evstep g f s m t s' m' ->
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Admitted.
    
    

    
    Lemma contains_lift_c_state:
      forall c j,
        OrdinalPool.containsThread (lift_c_state c) j <->
        OrdinalPool.containsThread c j.
    Proof.
    Admitted.
    Lemma invariant_lift_c_state:
      forall (st:ThreadPool.t),
        invariant(tpool:=OrdinalPool.OrdinalThreadPool) st ->
        invariant(tpool:=OrdinalPool.OrdinalThreadPool)
                 (lift_c_state st).
    Proof.
    Admitted.
    
    Lemma internal_step_lift_c_state:
      forall U (st1:HybridMachineSig.HybridMachineSig.machine_state)
        m2 st1' m1',
        HybridMachineSig.HybridMachineSig.internal_step
          (ThreadPool:=OrdinalPool.OrdinalThreadPool) U st1 m2 st1' m1' ->
        HybridMachineSig.HybridMachineSig.internal_step
          (ThreadPool:=OrdinalPool.OrdinalThreadPool)
          U (lift_c_state st1) m2 (lift_c_state st1') m1'.
    Proof.
    Admitted.

    Lemma internal_step_nextblock:
      let TP:= (@OrdinalPool.OrdinalThreadPool _
                                               (@ClightMachine.DMS.DSem Clight_g)) in
      forall U st m st' m',
        (HybridMachineSig.HybridMachineSig.internal_step(ThreadPool:=TP))
          U st m st' m' ->
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      inv H; inv Htstep.
      eapply clight_step_nextblock in Hcorestep.
      simpl in *; eauto.
    Qed.
    Lemma machine_step_nextblock:
      forall res DM MS Sch,
        let TP:= (@OrdinalPool.OrdinalThreadPool _
                                                 (@ClightMachine.DMS.DSem Clight_g)) in
        forall  U U' st m st' m' tr tr',
          (@HybridMachineSig.HybridMachineSig.external_step
             res _ TP DM MS Sch)
            U tr st m U' tr' st' m' ->
          (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
    Admitted.
    Lemma machine_step_trace_C:
      forall init_m ge sge U tr st m U' tr' st' m',
        machine_semantics.machine_step 
          (@ClightMachine.DMS.ClightConcurSem ge init_m)
          sge U tr st m U' tr' st' m' ->
        exists tr_tail,
          tr' = tr ++ tr_tail.
    Proof.
    Admitted.
    Lemma external_step_event_injectable:
      forall SM MS Sch U tr st m U' tr_tail st' m',
        @HybridMachineSig.HybridMachineSig.external_step
          _ _ (@OrdinalPool.OrdinalThreadPool dryResources (@ClightMachine.DMS.DSem Clight_g))
          SM MS Sch
          U tr st m U' (tr ++ tr_tail) st' m' ->
        Forall2 (inject_mevent (Mem.flat_inj (Mem.nextblock m'))) tr_tail tr_tail.
    Admitted.
    Notation scheduler:=HybridMachineSig.HybridMachineSig.HybridCoarseMachine.scheduler.
    Local Ltac cat_find_and_replace_nil:=
        match goal with
        | [H: ?t = ?t ++ ?x |- _ ] =>
          eapply threads_lemmas.app_eq_refl_nil in H;
          subst x; try rewrite app_nil_r in *
        | [H: seq.cat ?t ?y = ?t ++ ?x |- _ ] =>
          rewrite Coqlib3.cat_app in H;
          apply app_inv_head in H; subst x
        end.
      
    Lemma external_step_lift_c_state:
      forall U U' tr tr' m st st' m',
        @HybridMachineSig.HybridMachineSig.external_step
          _ _ _ _ (@DryHybridMachineSig (@ClightMachine.DMS.DSem Clight_g)
                                        OrdinalPool.OrdinalThreadPool)
          scheduler U tr st m U' tr' st' m' ->
        @HybridMachineSig.HybridMachineSig.external_step
          _ _ _ _ (@DryHybridMachineSig (HybridSem (@Some nat 0%nat)) OrdinalPool.OrdinalThreadPool)
          scheduler U tr (lift_c_state st) m U' tr' (lift_c_state st') m'.
    Proof.
      intros.
      (* this ltac rewrites the traces in the right way*)
      inv H; try cat_find_and_replace_nil.
      - econstructor 1; eauto.
        try solve[econstructor; eauto].
    Admitted.
    Lemma external_step_anytrace:
      forall U U' tr1 tr_trail m st st' m',
        @HybridMachineSig.HybridMachineSig.external_step
          _ _ _ _ (@DryHybridMachineSig (@ClightMachine.DMS.DSem Clight_g)
                                        OrdinalPool.OrdinalThreadPool)
          scheduler U tr1 st m U' (tr1++tr_trail) st' m' ->
        forall tr2,
          @HybridMachineSig.HybridMachineSig.external_step
            _ _ _ _ (@DryHybridMachineSig (@ClightMachine.DMS.DSem Clight_g)
                                          OrdinalPool.OrdinalThreadPool)
            scheduler U tr2 st m U' (tr2++tr_trail) st' m'.
    Proof.
      intros.
      (* this ltac rewrites the traces in the right way*)
      inv H; try cat_find_and_replace_nil;
        try solve[econstructor; eauto].
    Qed.
    Lemma halted__lift_c_state:
      forall U x c1 v1,
        @HybridMachineSig.HybridMachineSig.halted_machine
          _ _ OrdinalPool.OrdinalThreadPool (U, x, c1) = @Some val v1 ->
        @HybridMachineSig.HybridMachineSig.halted_machine
          _ _ (TP (@Some nat 0%nat)) (U, x, lift_c_state c1) = @Some val v1.
    Proof.
      unfold HybridMachineSig.HybridMachineSig.halted_machine; simpl.
      intros *; match_case.
    Qed.
        
    Lemma unique_Krun_lift_c_state:
      forall c i,
        @HybridMachineSig.HybridMachineSig.unique_Krun _ _ OrdinalPool.OrdinalThreadPool c i <->
        @HybridMachineSig.HybridMachineSig.unique_Krun _ _ (TP (@Some nat 0%nat)) (lift_c_state c) i.
    Proof.
      unfold HybridMachineSig.HybridMachineSig.unique_Krun in *.
      split; intros HH; simpl; intros.
      - unfold OrdinalPool.getThreadC,OrdinalPool.pool in *.
        destruct c; simpl in *. 
        match_case in H.
        unshelve eapply HH; debug eauto.
      - unshelve eapply HH.
        + apply contains_lift_c_state; assumption.
        + apply SState, q.
        + unfold OrdinalPool.getThreadC,OrdinalPool.pool.
          destruct c; simpl in *.
          match goal with
            |- (match ?X with _ => _ end) = _ => replace X with (Krun q)
          end.
          * reflexivity.
          * rewrite <- H. f_equal. simpl. f_equal.
            match_case; simpl.
            eapply Axioms.proof_irr.
    Qed.
    Definition lifted_refl_match :=
      fun cd j st1 m1 st2 m2 =>
         refl_match cd j (lift_c_state st1) m1 st2 m2.
    Lemma trivial_clight_simulation:
      (HybridMachine_simulation
         (ClightMachine.DMS.ClightConcurSem
            (ge:=Clight_g)
            (Genv.init_mem (Ctypes.program_of_program C_program)))
         (HybConcSem (Some 0)%nat (Genv.init_mem (Ctypes.program_of_program C_program)))).
    Proof.
      intros.
      eapply Build_HybridMachine_simulation with (match_state:=lifted_refl_match).
      unshelve econstructor.
      - exact trivial_order.
      - exact trivial_order_wf.
      - (*initial_setup*)
        simpl; intros.
        exists (Mem.flat_inj (Mem.nextblock s_mem')), tt.
        unshelve eexists. eapply lift_c_state; eauto.
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
        econstructor; simpl; auto.

      - (*thread_diagram*)
        intros; unfold Clight_g; auto.
        exists (lift_c_state st1').
        inv H0. normal.
        + econstructor.
        + simpl in H.
          eapply inject_incr_trace; try eassumption.
          eapply flat_inj_lt, internal_step_nextblock; eauto.
        + left. exists 0%nat; simpl.
          do 2 eexists; split; eauto.
          apply internal_step_lift_c_state; auto.
      - (*machine_diagram*)
        intros; unfold Clight_g; auto.
        unshelve (exploit machine_step_trace_C;
          simpl in *; eauto); eauto.
        eapply Some; assumption. 
        intros [tr_tail Htr].
        subst tr1'.
        exists (tr2 ++ tr_tail), (lift_c_state st1').
        normal. 
        + econstructor. 
        
        + inv H0; simpl in H.
          eapply Forall_cat; auto.
          eapply inject_incr_trace; try eassumption.
          eapply flat_inj_lt, machine_step_nextblock; eauto.
          eapply external_step_event_injectable; eauto.
        + inv H0.
          eauto. simpl in *.
          eapply external_step_anytrace in H.
          eapply external_step_lift_c_state; eauto.
      - intros. revert H0.
        inv H. simpl.
        intros. exists v1. simpl in *.
        eapply halted__lift_c_state; auto.
      - intros; simpl. inv H.
        apply unique_Krun_lift_c_state.
    Qed.
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
