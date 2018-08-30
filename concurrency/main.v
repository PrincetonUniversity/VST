(* Main File putting all together. *)

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert.common.Globalenvs.

Require Import compcert.cfrontend.Clight.
Require Import VST.concurrency.juicy.erasure_safety.

Require Import VST.concurrency.compiler.concurrent_compiler_safety_proof.
Require Import VST.concurrency.compiler.sequential_compiler_correct.

Require Import VST.concurrency.sc_drf.mem_obs_eq.
Require Import VST.concurrency.sc_drf.x86_inj.
Require Import VST.concurrency.sc_drf.x86_safe.
Require Import VST.concurrency.sc_drf.executions.
Require Import VST.concurrency.sc_drf.spinlocks.

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.HybridMachineSig.


Set Bullet Behavior "Strict Subproofs".

Module Main (CC_correct: CompCert_correctness).
  (*Import the *)
  (*Import the safety of the compiler for concurrent programs*)
  
  (* Module ConcurCC_safe:= (SafetyStatement CC_correct). *)
  Module ConcurCC_safe := (Concurrent_Safety CC_correct).
  Import ConcurCC_safe.

  (*Importing the definition for ASM semantics and machines*)
  Import dry_context.AsmContext.

  (*Use a section to contain the parameters.*)
  Section MainTheorem.
  (*Assumptions *)
  Context (CPROOF : semax_to_juicy_machine.CSL_proof).
  Definition Clight_prog:= semax_to_juicy_machine.CSL_prog CPROOF.
  Definition Main_ptr:=Values.Vptr (Ctypes.prog_main Clight_prog) Integers.Ptrofs.zero.
  Context (Asm_prog: Asm.program).
  Context (compilation : CC_correct.CompCert_compiler Clight_prog = Some Asm_prog).
  Context (asm_genv_safe: Asm_core.safe_genv (@x86_context.X86Context.the_ge Asm_prog)).
  Instance SemTarget : Semantics:= @x86_context.X86Context.X86Sem Asm_prog asm_genv_safe.
  Existing Instance X86Inj.X86Inj.

  Variable init_mem_wd:
    forall m,
      Genv.init_mem Asm_prog = Some m ->
      mem_obs_eq.MemoryWD.valid_mem m /\
      mem_obs_eq.CoreInjections.ge_wd (Renamings.id_ren m) the_ge.
        
  (* This should be instantiated:
     it says initial_Clight_state taken from CPROOF, is an initial state of CompCert.
   *)
  Context (CPROOF_initial:
             Clight.start_stack (Clight.globalenv Clight_prog)
                                (init_mem CPROOF)
                                (Clight_safety.initial_Clight_state CPROOF)
                                Main_ptr nil).

 (* MOVE THIS TO ANOTHER FILE *)
  Lemma CPROOF_initial_mem:  Genv.init_mem (Ctypes.program_of_program Clight_prog) = Some (init_mem CPROOF).
  Proof.
  unfold Clight_prog, init_mem, semax_to_juicy_machine.init_mem, 
    semax_initial.init_m, semax_to_juicy_machine.prog, Ctypes.program_of_program.
  clear.
  set (H := (semax_to_juicy_machine.init_mem_not_none CPROOF)).
  clearbody H.
  set (p := semax_to_juicy_machine.CSL_prog CPROOF) in *.
  unfold Ctypes.program_of_program in H.
  clearbody p.
  set (m := Genv.init_mem
          {|
          AST.prog_defs := Ctypes.prog_defs p;
          AST.prog_public := Ctypes.prog_public p;
          AST.prog_main := Ctypes.prog_main p |}) in *.
 clearbody m.
 destruct m. reflexivity. contradiction H; auto.
Qed. 

  (*Safety from CSL to Coarse Asm*)
  Definition SemSource p:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)).
  Definition THM m:=
    (HybridMachineSig.HybridMachineSig.ConcurMachineSemantics
       (Sem:=SemTarget)
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
       (HybridMachine:=concurrent_compiler_safety.TargetHybridMachine)
       (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig) m).

  Definition EHM m:=
    (HybridMachineSig.HybridMachineSig.ConcurMachineSemantics
       (Sem:=SemTarget)
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
       (HybridMachine:=@bareMach SemTarget)
       (machineSig:= BareMachine.BareMachineSig) m).

  Context {SW : Clight_safety.spawn_wrapper CPROOF}.
  
  (* Variable ConcurrentCompilerSafety:
    ConcurrentCompilerSafety_statement. *)
  
  Lemma CSL2CoarseAsm_safety:
    forall U,
    exists init_mem_target init_mem_target' init_thread_target,
      let res_target := permissions.getCurPerm init_mem_target' in
      let res:=(res_target, permissions.empty_map) in
  let init_tp_target :=
      threadPool.ThreadPool.mkPool
        (Sem:=SemTarget)
        (resources:=erasure_proof.Parching.DR)
        (Krun init_thread_target)
      res in
  let init_MachState_target := (U, nil, init_tp_target) in  
      machine_semantics.initial_machine (THM (Genv.init_mem Asm_prog)) (Some res) init_mem_target init_tp_target init_mem_target' Main_ptr nil /\
  forall n,
    HybridMachineSig.HybridMachineSig.HybridCoarseMachine.csafe
      (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                     (Sem:=SemTarget))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      init_MachState_target init_mem_target' n.
  Proof.
    intros.
    pose proof (@ConcurrentCompilerSafety _ _ compilation asm_genv_safe) as H.
    unfold concurrent_compiler_safety.concurrent_simulation_safety_preservation in *.
    specialize (H U (init_mem CPROOF) (init_mem CPROOF) (Clight_safety.initial_Clight_state CPROOF) Main_ptr nil).
    match type of H with
      | ?A -> _ => cut A
    end.
    intros HH; specialize (H HH);
    match type of H with
      | ?A -> _ => cut A
    end.
    intros HH'; specialize (H HH');
      match type of H with
      | ?A -> _ => cut A; try (intros; eapply Clight_initial_safe; auto)  (*That didn't work?*)
      end.
    intros HH''; specialize (H HH'').

    - destruct H as (mem_t& mem_t' & thread_target & INIT_mem & INIT & SAFE).
      exists mem_t, mem_t', thread_target; split (*;[|split] *).
      + eauto. (*Initial memory*)
        (*
      + (**) 
        clear - INIT.
        simpl in INIT.
        destruct INIT as (INIT_mem' & c & (INIT&mem_eq) & EQ); simpl in *.
        cut (c = thread_target).
        * intros ?; subst c; eauto.
        * clear - EQ.
          cut (Krun c = Krun thread_target).
          { intros HH; inversion HH; eauto. }
          match type of EQ with
          | ?A = ?B =>
            remember A as C1; remember B as C2
          end.
          assert (cnt1: OrdinalPool.containsThread C1 0).
          { clear - HeqC1. unfold OrdinalPool.containsThread.
            subst C1; auto. }
          assert (cnt2: OrdinalPool.containsThread C2 0).
          { clear - HeqC2. unfold OrdinalPool.containsThread.
            subst C2; auto. }
          replace (Krun c) with (OrdinalPool.getThreadC cnt2) by (subst C2; simpl; auto).
          replace (Krun thread_target) with (OrdinalPool.getThreadC cnt1) by (subst C1; simpl; auto).
          clear - EQ.
          subst C1; auto.
          f_equal. eapply Axioms.proof_irr. *)
      + eapply SAFE.

    - clear H. split; eauto; econstructor; repeat split; try reflexivity; eauto.
    - apply CPROOF_initial_mem.
  Qed.

  Notation sc_execution := (@Executions.fine_execution _ BareDilMem BareMachine.resources
                                            BareMachine.BareMachineSig).
  Theorem CSL2FineBareAsm_safety:
    forall U,
    exists init_mem_target init_mem_target' init_thread_target,
      let init_tp_target :=
          threadPool.ThreadPool.mkPool
            (Sem:=SemTarget)
            (resources:=BareMachine.resources)
            (Krun init_thread_target) tt in  
      machine_semantics.initial_machine (EHM (Genv.init_mem Asm_prog)) (Some tt) init_mem_target
                                        init_tp_target init_mem_target' Main_ptr nil /\

      (forall n,
        HybridMachineSig.HybridMachineSig.HybridFineMachine.fsafe
          (dilMem:= BareDilMem)
          (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                         (resources:=BareMachine.resources)
                         (Sem:=SemTarget))
          (machineSig:= BareMachine.BareMachineSig)
          init_tp_target (@HybridMachineSig.diluteMem BareDilMem init_mem_target') U n) /\
      (forall final_state final_mem tr,
          sc_execution (U, [::], init_tp_target)
                       (@HybridMachineSig.diluteMem BareDilMem init_mem_target')
                       ([::], tr, final_state) final_mem ->
          SpinLocks.spinlock_synchronized tr).
  Proof.
    intros U.
    destruct (CSL2CoarseAsm_safety U) as
        (init_mem_target & init_mem_target' & init_thread_target & INIT & Hsafe).
    simpl in INIT.
    unfold HybridMachineSig.init_machine'' in INIT.
    destruct INIT as [Hinit_mem Hinit].
    simpl in Hinit.
    unfold HybridMachine.DryHybridMachine.init_mach in Hinit.
    destruct Hinit as [c [Hinit Heq]].
    exists init_mem_target, init_mem_target',
    init_thread_target.
    assert (init_thread_target = c).
    { inversion Heq.
      assert (0 < 1)%nat by auto.
      eapply Extensionality.EqdepTh.inj_pair2 in H0.
      apply equal_f in H0.
      inversion H0; subst.
      reflexivity.
      simpl.
      econstructor;
        now eauto.
    }
    subst.
    split.
    - simpl.
      unfold HybridMachineSig.init_machine''.
      split; auto.
      simpl.
      unfold BareMachine.init_mach.
      exists c.
      split; auto.
    - intros.
      destruct (init_mem_wd  Hinit_mem ) as [Hvalid_mem Hvalid_ge].
      pose (fineConc_safe.FineConcInitial.Build_FineInit Hvalid_mem Hvalid_ge).
      eapply @X86Safe.x86SC_safe with (Main_ptr := Main_ptr) (FI := f); eauto.
      intro; apply Classical_Prop.classic.
      (* proof of safety for new schedule *)
      intros.
      pose proof (CSL2CoarseAsm_safety sched) as
          (init_mem_target2 & init_mem_target2' & init_thread_target2 & INIT2 & Hsafe2).
      simpl in INIT2.
      unfold HybridMachineSig.init_machine'' in INIT2.
      destruct INIT2 as [Hinit_mem2 Hinit2].
      rewrite Hinit_mem2 in Hinit_mem.
      inversion Hinit_mem; subst.
      simpl in Hinit2.
      unfold HybridMachine.DryHybridMachine.init_mach in Hinit2.
      destruct Hinit2 as [c2 [Hinit2 Heq2]].
      destruct (Asm.semantics_determinate Asm_prog).
      simpl in sd_initial_determ.
      simpl in Hinit, Hinit2.
      destruct Hinit as [Hinit ?], Hinit2 as [Hinit2 ?]; subst.
      specialize (sd_initial_determ _ _ _ _ _ Hinit Hinit2); subst.
      now eauto.
  Qed.
    
  End MainTheorem.
  
End Main.


(* Test an instantiation of Main theorem. *)
Module CC_correct: CompCert_correctness.
  Axiom CompCert_compiler : Clight.program -> option Asm.program.
  Axiom simpl_clight_semantic_preservation :
    forall (p : Clight.program) (tp : Asm.program),
      CompCert_compiler p = Some tp ->
      ExposedSimulations.fsim_properties_inj (Clight.semantics2 p) (Asm.semantics tp)
                                             Clight.get_mem Asm.get_mem.

End CC_correct.

Module Test_Main:= (Main CC_correct).
Import Test_Main.

Check CSL2FineBareAsm_safety.
Print Assumptions CSL2FineBareAsm_safety.
