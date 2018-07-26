(** ** Erased X86 machine is safe*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.
Require Import compcert.x86.Asm.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.common.Asm_core.
Require Import VST.concurrency.sc_drf.x86_erasure.
Require Import VST.concurrency.sc_drf.x86_inj.
Require Import VST.concurrency.sc_drf.fineConc_safe.
Require Import VST.concurrency.sc_drf.SC_erasure.
Require Import VST.concurrency.sc_drf.SC_spinlock_safe.

Require Import Coqlib.
Require Import VST.msl.Coqlib2.

Module X86Safe.

  Import AsmContext SCErasure X86Context X86SEMAxioms HybridMachine
         HybridMachineSig HybridCoarseMachine HybridFineMachine
         FineConcSafe FineConcInitial.

  Section X86Safe.

    Context {U: seq.seq nat}
            {the_program: Asm.program}
            {Hsafe: Asm_core.safe_genv (@the_ge the_program)}.
    
    Instance X86Sem : Semantics := @X86Sem the_program Hsafe.
    Instance X86Axioms : CoreLanguage.SemAxioms := @X86Axioms U the_program Hsafe.
    Existing Instance X86CoreErasure.X86Erasure.
    Existing Instance X86Inj.X86Inj.
    (* We don't really have an instance for that, it would require to prove that
                                the initial memory has no invalid pointers *)
    Context {FI : FineInit}. 
    Variable em : ClassicalFacts.excluded_middle.
    Existing Instance dryCoarseMach.
    Existing Instance dryFineMach.
    Existing Instance bareMach.


    Lemma x86SC_safe:
      forall Main_ptr init_thread_target new_mem_target,
        initial_core (event_semantics.msem semSem) 0 init_mem init_thread_target new_mem_target Main_ptr nil ->
        let init_perm_target := permissions.getCurPerm init_mem in
        let new_perm_target := permissions.getCurPerm new_mem_target in
        let init_tpc_target := DryHybridMachine.initial_machine new_perm_target init_thread_target in
        forall
          (* (Hinit_state: tpc_init U init_mem init_mem_target init_MachState_target Main_ptr nil) *)
          (Hcsafe: forall n sched,
              csafe
                (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool)
                (resources:= DryHybridMachine.dryResources)
                (Sem:= _)
                (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
                (sched, nil, init_tpc_target) (@diluteMem HybridCoarseMachine.DilMem new_mem_target) n),
          let init_tp_bare := ThreadPool.mkPool
                                (resources:=BareMachine.resources)
                                (Krun init_thread_target) tt  in
          forall n,
            fsafe
              (dilMem:= BareDilMem)
              (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                             (resources:=erased_machine.BareMachine.resources)
                             (Sem:=_))
              (machineSig:= BareMachine.BareMachineSig)
              init_tp_bare (@diluteMem BareDilMem new_mem_target) U n.
    Proof.
      intros.
      (** Fine to Erased safety *)
      eapply init_fsafe_implies_scsafe with (m := init_mem) (f := Main_ptr) (arg := nil) (tpf := init_tpc_target); eauto.
      econstructor; eauto.
      simpl.
      unfold BareMachine.init_mach.
      exists init_thread_target.
      split;
        now eauto.
      unfold tpf_init.
      simpl.
      split; auto.
      unfold DryHybridMachine.init_mach.
      eexists; split;
        now eauto.
      (** Coarse to Fine safety *)
      eapply init_fine_safe with (f := Main_ptr) (arg := nil); eauto.
      intros sched tpc mem' n0 Htpc.
      destruct Htpc as [_ Hinit_tpc].
      simpl in Hinit_tpc.
      unfold DryHybridMachine.init_mach in Hinit_tpc.
      destruct Hinit_tpc as [c_new [Hinit_core_new ?]].
      simpl in Hcsafe.
      specialize (Hcsafe n0 sched).
      unfold init_tpc_target in Hcsafe.
      simpl in Hcsafe.
      assert (Heq: c_new = init_thread_target /\ mem' = new_mem_target)
        by (eapply initial_core_det with (args := nil); eauto). 
      destruct Heq; subst c_new mem'.
      assert (tpc = OrdinalPool.mkPool (Krun init_thread_target) (new_perm_target, empty_map)).
      { subst.
        simpl.
        unfold new_perm_target.
        eapply f_equal2; try reflexivity.
      }
      subst; now eauto.
      econstructor; eauto.
      simpl.
      eexists; now eauto.
      now econstructor.
      Unshelve. now auto.
    Qed.

  End X86Safe.
End X86Safe.
