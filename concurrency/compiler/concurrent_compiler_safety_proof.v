
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype.

Require Import compcert.common.Globalenvs.
Require Import VST.concurrency.paco.src.paco.

Require Import VST.concurrency.common.HybridMachineSig.
Import HybridMachineSig.
Set Bullet Behavior "Strict Subproofs".
  
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_safety.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.
Require Import VST.concurrency.compiler.safety_equivalence.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.common.HybridMachine.
Require Import Omega.
            

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

Module Concurrent_Safety (CC_correct: CompCert_correctness).
  (*Import the Clight Hybrid Machine*)
  Import ClightMachine.
  Import DMS.
  (*Import the Asm X86 Hybrid Machine*)
  Import X86Context.

  Module ConcurCC_correct:= (Concurrent_correctness CC_correct).
  Import ConcurCC_correct.
  
  Definition Clight_init_state (p: Clight.program):=
    Clight.start_stack (Clight.globalenv p).
  
  Definition Asm_init_state (p: Asm.program):=
    Asm.start_stack (@the_ge p).

  Notation valid Sem:=
    (valid dryResources Sem OrdinalPool.OrdinalThreadPool).

  

  Definition opt_init_mem_source (p : Clight.program):=
      (Genv.init_mem (Ctypes.program_of_program p)).
  Definition opt_init_mem_target {F V} (tp:AST.program F V ):=
    (Genv.init_mem tp).
  Lemma explicit_safety_step:
    forall (p : Clight.program) (tp : Asm.program) (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemSource:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)) in
         let SemTarget:= @X86Sem tp asm_genv_safety in
         forall (U : schedule) (m_s m_t : Memory.Mem.mem)
             (j : Values.Val.meminj) (c : Asm.state)
             (C_source : OrdinalPool.t(Sem:=SemSource))
             (C_target : OrdinalPool.t(Sem:=SemTarget)) tr
             (SIM : HybridMachine_simulation (ClightConcurSem (opt_init_mem_source p))
                                             (AsmConcurSem (opt_init_mem_target tp))) (cd : index SIM),
           match_state SIM cd j C_source m_s C_target
                    m_t ->
        (forall U,
          (valid SemSource) (tr, C_source, m_s) U ->
            explicit_safety
              HybridMachine.DryHybridMachine.dryResources
              SemSource
              (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
              HybridMachine.DryHybridMachine.DryHybridMachineSig
              U tr C_source m_s) ->
        forall U,
          (valid SemTarget) (tr, C_target, Asm.get_mem c) U ->
            explicit_safety
              HybridMachine.DryHybridMachine.dryResources
              SemTarget
              (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
              HybridMachine.DryHybridMachine.DryHybridMachineSig
              U tr C_target m_t.
    Proof.
    Admitted.

    Lemma match_valid_equiv:
      forall U (p : Clight.program) (tp : Asm.program) (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemSource:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)) in
        let SemTarget:= @X86Sem tp asm_genv_safety in
        forall (m_s m_t : Memory.Mem.mem)
          (j : Values.Val.meminj)
          (C_source : OrdinalPool.t(Sem:=SemSource))
          (C_target : OrdinalPool.t(Sem:=SemTarget)) tr
          (SIM : HybridMachine_simulation (ClightConcurSem (opt_init_mem_source p))
                                          (AsmConcurSem (opt_init_mem_target tp))) (cd : index SIM)
          (Hmatch: match_state SIM cd j C_source m_s C_target m_t),
          (valid SemSource) (tr, C_source, m_s) U <-> (valid SemTarget) (tr, C_target, m_t) U.
    Proof.
      intros.
      unfold valid. simpl.
      unfold correct_schedule.
      destruct (schedPeek U); [|now auto].
      (* now eapply (thread_running _ _ j _ _ _ _ Hmatch).  *)
    Admitted.


    (* Note, unused right now *)
    Lemma thread_stepN_schedule_irr:
      forall (tp : Asm.program)
        (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemTarget:= @X86Sem tp asm_genv_safety in
        forall  n U U' (c c':  OrdinalPool.t(Sem:=SemTarget)) m m'
           (Hsched: schedPeek U = schedPeek U')
           (HstepN: machine_semantics_lemmas.thread_stepN
                      (AsmConcurSem (opt_init_mem_target tp)) (@the_ge tp) n U c m c' m'),
          machine_semantics_lemmas.thread_stepN
            (AsmConcurSem (opt_init_mem_target tp)) (@the_ge tp) n U' c m c' m'.
    Proof.
      induction n.
      - intros. simpl in *.
        inversion HstepN;
          now auto.
      - intros.
        simpl in HstepN.
        destruct HstepN as [c'' [m'' [Hstep HstepN]]].
        simpl.
        exists c'', m''.
        split; eauto.
        inversion Hstep; subst.
        econstructor; eauto.
        rewrite <- Hsched;
          now auto.
    Qed.
  
    Lemma explicit_safety_step':
      forall (p : Clight.program) (tp : Asm.program) (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemSource:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)) in
        let SemTarget:= @X86Sem tp asm_genv_safety in
        forall (m_s m_t : Memory.Mem.mem)
          (j : Values.Val.meminj)
          (C_source : OrdinalPool.t(Sem:=SemSource))
          (C_target : OrdinalPool.t(Sem:=SemTarget)) tr1 tr2
          (SIM : HybridMachine_simulation (ClightConcurSem (opt_init_mem_source p))
                                          (AsmConcurSem (opt_init_mem_target tp))) (cd : index SIM)
          (Hmatch: match_state SIM cd j C_source m_s C_target m_t)
          (Hmatch_events: List.Forall2 (inject_mevent j) tr1 tr2)
          (HsafeS: forall U,
              (valid SemSource) (tr1, C_source, m_s) U ->
              explicit_safety
                HybridMachine.DryHybridMachine.dryResources
                SemSource
                (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
                HybridMachine.DryHybridMachine.DryHybridMachineSig
                U tr1 C_source m_s)
           U (HvalidT: (valid SemTarget) (tr2, C_target, m_t) U),
            explicit_safety
              HybridMachine.DryHybridMachine.dryResources
              SemTarget
              (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
              HybridMachine.DryHybridMachine.DryHybridMachineSig
              U tr2 C_target m_t.
    Proof.
      intros.
      eapply coinductive_safety.exp_safety_paco_correct.
      eapply coinductive_safety.safetyN_equivalence.
      simpl; now auto.
      eapply coinductive_safety.speach_therapy with (cd := cd).
      now eapply (core_ord_wf SIM).
      generalize dependent m_t.
      generalize dependent C_target.
      generalize dependent tr2.
      generalize dependent tr1.
      generalize dependent U.
      generalize dependent m_s.
      generalize dependent j.
      generalize dependent C_source.
      generalize dependent cd.
      pcofix HsafeT.
      intros.
      assert (HvalidS: (valid SemSource) (tr1, C_source, m_s) U)
        by (eapply match_valid_equiv; eauto).
      specialize (HsafeS U HvalidS).
      inversion HsafeS as [HhaltedS | stS' Hstep CIH | U' stS' Hstep CIH].
      - (* halted case *)
        pfold.
        econstructor 1.
        simpl in *.
        remember (machine_semantics.conc_halted (ClightConcurSem (opt_init_mem_source p)) U
                                                C_source) as v1 eqn:Hhalted.
        symmetry in Hhalted.
        simpl in Hhalted.
        unfold halted_machine in *.
        simpl in *.
        destruct (schedPeek U);
          now auto.
      - (* internal step case *)
        destruct stS' as [[evS C_source'] m_s'].
        simpl in Hstep.
        pose proof Hstep as HstepS.
        eapply (thread_diagram SIM) with (sge := Clight.globalenv p) (tge := the_ge) in Hstep;
          eauto.
        destruct Hstep as [C_target' [m_t' [cd' [j' [Hmatch' [Hevs' HstepT]]]]]].
        destruct HstepT as [HstepT | [HstepT Hdec]].
        + (* Step Plus case *)
          destruct HstepT as [n HstepN].
          pfold.
          econstructor 2 with (y' := (tr2, C_target', m_t')) (n:=n); eauto.
          * clear CIH HsafeT HvalidT HvalidS HsafeS Hmatch' HstepS Hmatch.
            generalize dependent m_t'.
            generalize dependent C_target'.
            generalize dependent m_t.
            generalize dependent C_target.
            induction n.
            ** intros.
               simpl in HstepN.
               destruct HstepN as [? [? [? Heq]]].
               inversion Heq; subst.
               econstructor 2 with (_y := (tr2, C_target', m_t')); simpl; eauto.
               econstructor 1.
               auto.
            ** intros.
               simpl in HstepN.
               destruct HstepN as [C_target'' [m_t'' [HstepT' HstepN]]].
               econstructor 2 with (_y := (tr2, C_target'', m_t'')); simpl; eauto.
          * intros.
            simpl in H.
            right.
            eapply HsafeT; try apply Hevs'; eauto.
            intros.
            eapply explicit_safety_trace_irr with (tr := evS).
            eapply CIH.
            simpl.
            now eauto.
        + (* Step Star case *)
          eapply paco3_pfold; eauto.
          destruct HstepT as [n HstepN].
          destruct n.
          * simpl in HstepN; inversion HstepN; subst.
            econstructor 4; eauto.
            eapply HsafeT; try apply Hevs'; eauto.
            intros.
            eapply explicit_safety_trace_irr with (tr := evS).
            eapply CIH.
            simpl.
            now eauto.
          * econstructor 2 with (y' := (tr2, C_target', m_t')) (n:=n); eauto.
            (* this part here is exactly the same as the step plus case and I can 
               probably factor into a lemma,
               but right now I am just trying to get things to work *)
            ** clear CIH HsafeT HvalidT HvalidS HsafeS Hmatch' HstepS Hmatch.
               generalize dependent m_t'.
               generalize dependent C_target'.
               generalize dependent m_t.
               generalize dependent C_target.
               induction n.
               *** intros.
                   simpl in HstepN.
                   destruct HstepN as [? [? [? Heq]]].
                   inversion Heq; subst.
                   econstructor 2 with (_y := (tr2, C_target', m_t')); simpl; eauto.
                   econstructor 1.
                   auto.
               *** intros.
                   simpl in HstepN.
                   destruct HstepN as [C_target'' [m_t'' [HstepT' HstepN]]].
                   econstructor 2 with (_y := (tr2, C_target'', m_t'')); simpl; eauto.
            ** intros.
               eapply HsafeT; try apply Hevs'; eauto.
               intros.
               eapply explicit_safety_trace_irr with (tr := evS); eauto.
               eapply CIH; eauto.
      - (* external step case*)
        destruct stS' as [[evS C_source'] m_s'].
        simpl in Hstep.
        pose proof Hstep as HstepS.
        eapply (machine_diagram SIM) with (sge := Clight.globalenv p) (tge := the_ge) in Hstep;
          eauto.
        destruct Hstep as [tr2' [C_target' [m_t' [cd' [j' [Hmatch' [Hevs' HstepT]]]]]]].
        simpl in HstepT.
        pfold.
        econstructor 3 with (y' := (tr2', C_target', m_t'));
          eauto.
        Unshelve. all:auto.
    Qed.
        
    Lemma Clight_finite_branching:
      let ClightSem:= ClightSemanticsForMachines.ClightSem in 
            forall (p : Clight.program)
                   (x : kstate dryResources (ClightSem (Clight.globalenv p)) OrdinalPool.OrdinalThreadPool),
              safety.finite_on_x
                (safety.possible_image
                   (fun
                       (x0 : kstate dryResources (ClightSem (Clight.globalenv p))
                                    OrdinalPool.OrdinalThreadPool) (y : schedule)
                       (x' : kstate dryResources (ClightSem (Clight.globalenv p))
                                    OrdinalPool.OrdinalThreadPool) =>
                       exists y' : schedule,
                         kstep dryResources (ClightSem (Clight.globalenv p)) OrdinalPool.OrdinalThreadPool
                               DryHybridMachineSig x0 y x' y') (valid (ClightSem (Clight.globalenv p))) x).
          Proof.
          Admitted.
    Lemma csafety_step:
      forall (p : Clight.program) (tp : Asm.program) (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemSource:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)) in
         let SemTarget:= @X86Sem tp asm_genv_safety in
         forall (U : schedule) (init_mem_source' : Memory.Mem.mem)
             (j : Values.Val.meminj) (c : Asm.state)
             (C_source : OrdinalPool.t(Sem:=SemSource))
             (C_target : OrdinalPool.t) tr
             (SIM : HybridMachine_simulation (ClightConcurSem (opt_init_mem_source p))
                                             (AsmConcurSem (opt_init_mem_target tp))) (cd : index SIM),
        match_state SIM cd j C_source init_mem_source' C_target
                    (Asm.get_mem c) ->
        (forall (n : nat) U,
            (valid SemSource) (tr, C_source, init_mem_source') U ->
            HybridCoarseMachine.csafe(Sem:=SemSource)
                                     (resources:=HybridMachine.DryHybridMachine.dryResources)
                                     (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
                                     (U, tr, C_source)
                                     init_mem_source' n) ->
        forall (n : nat) U ,
          (valid SemTarget) (tr, C_target, Asm.get_mem c) U ->
          HybridCoarseMachine.csafe (Sem:=SemTarget)
                                     (resources:=HybridMachine.DryHybridMachine.dryResources)
                                     (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
                                     (U, tr, C_target)
                                     (Asm.get_mem c) n.
    Proof.
      intros until n.
      eapply explicit_safety_csafe; eauto.      
      eapply explicit_safety_step; eauto.
      eapply csafe_explicit_safety.
      + eapply Clight_finite_branching.
      + eapply H0. 
    Qed.



    (** for the initial state, it's enough to prove csafety for the valid schedules,
        we can derive safety for all others. *)
    Lemma initial_csafe_all_schedule:
      forall  prog asm_genv_safety tr c m r,
        let SemTarget:= @X86Sem prog asm_genv_safety in
        let tp:=OrdinalPool.mkPool (Krun c) r in
        (forall U (n : nat),
            (valid SemTarget) (tr, tp, m) U ->
            HybridCoarseMachine.csafe
              (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
              (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
              (U, nil,
               OrdinalPool.mkPool
                 (Krun c) r) m n)  ->
        forall U (n : nat),
          HybridCoarseMachine.csafe
            (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
            (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
            (U, nil,
             OrdinalPool.mkPool (Krun c) r) m n.
    Proof.
      intros.
      revert U.
      induction n; try solve[econstructor].
      intros U.
      destruct U as [|i U]; [|destruct i].
      - econstructor; eauto.
      - eapply H.
        unfold safety_equivalence.valid, correct_schedule; simpl.
        intros ????.
        simpl in cnti.
        unfold OrdinalPool.containsThread in cnti; simpl in cnti.
        clear - cnti.
        eapply semax_invariant.ssr_leP_inv in cnti.
        destruct j; simpl; [auto| omega].
      - intros.
        eapply HybridCoarseMachine.AngelSafe; simpl.
        eapply schedfail; simpl.
        * reflexivity.
        * unfold OrdinalPool.containsThread; simpl.
          intros LEQ; eapply semax_invariant.ssr_leP_inv in LEQ.
          omega.
        * assert ((valid SemTarget) (tr, tp, m) (cons 0 nil) ).
          { subst tp; auto.
          unfold safety_equivalence.valid, correct_schedule; simpl.
          intros ????.
          simpl in cnti.
          unfold OrdinalPool.containsThread in cnti; simpl in cnti.
          clear - cnti.
          eapply semax_invariant.ssr_leP_inv in cnti.
          destruct j; simpl; [auto| omega]. }
          apply (H _ 1) in H0.
          admit. (*Should be able to pull the invariant from H0*)
        * admit. (*Should be able to pull the invariant from H0*)
        * reflexivity.
        * intros U''; eapply IHn.
    Admitted.

    
    Lemma ConcurrentCompilerSafety:
      forall (p : Clight.program) (tp : Asm.program),
        CC_correct.CompCert_compiler p = Some tp ->
        forall asm_genv_safety : Asm_core.safe_genv (@the_ge tp),
          let SemSource:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)) in
          let SemTarget:= @X86Sem tp asm_genv_safety in
          concurrent_simulation_safety_preservation
            (Genv.init_mem (Ctypes.program_of_program p))
            (Genv.init_mem tp)
            (SemSource:= SemSource)
            (SourceThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
            (SourceMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
            (SemTarget :=  SemTarget)
            (TargetThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
            (TargetMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    .
      unfold concurrent_simulation_safety_preservation; intros.
      pose proof (ConcurrentCompilerCorrectness p tp H asm_genv_safety) as SIM.
      unfold ConcurrentCompilerCorrectness_specification in SIM.
      (*Construct the initial state*)
      apply (HybridMachine_simulation.initial_setup SIM) in H1 as
          (j&cd&t_mach_state&t_mem&t_mem'&r2&(INIT_mem & INIT)&?).
      assert(INIT':= INIT).
      destruct r2; try solve[inversion INIT'].
      destruct INIT' as (c&?&?).
      subst t_mach_state; simpl in *.
      do 3 eexists; repeat split; eauto.
      eapply INIT.
      
      destruct H3 as (H21 & H22); subst.
      clear INIT H21.

      (* Now, we strip out the scheudle, until it starts with 1*)
      eapply initial_csafe_all_schedule.
      intros; eapply csafety_step; eauto.
      eapply H1.
    Qed.
    
End Concurrent_Safety.
