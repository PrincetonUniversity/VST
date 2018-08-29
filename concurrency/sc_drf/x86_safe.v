(** ** Erased X86 machine is safe*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Require Import FunInd.
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
Require Import VST.concurrency.sc_drf.mem_obs_eq.
Require Import VST.concurrency.sc_drf.x86_erasure.
Require Import VST.concurrency.sc_drf.x86_inj.
Require Import VST.concurrency.sc_drf.fineConc_safe.
Require Import VST.concurrency.sc_drf.executions.
Require Import VST.concurrency.sc_drf.SC_erasure.
Require Import VST.concurrency.sc_drf.SC_spinlock_safe.
Require Import VST.concurrency.sc_drf.spinlocks.

Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.

Module InitialMemWD.

  Import Memory CoreInjections Renamings ValueWD.

  Lemma valid_genv_alloc: forall ge (m m1:mem) lo hi b
                            (ALLOC: Mem.alloc m lo hi = (m1,b))
                            (G: X86WD.ge_wd (id_ren m) ge),
      X86WD.ge_wd (id_ren m1) ge.
  Proof.
    intros. destruct G. intros. unfold X86WD.ge_wd.
    split.
    - intros b0 Hge.
      specialize (H _ Hge).
      unfold id_ren in H.
      destruct (valid_block_dec m b0); simpl in H; try discriminate.
      eapply Mem.valid_block_alloc with (b' := b0) in v; eauto.
      destruct (id_ren m1 b0) eqn:Hcontra; auto.
      eapply id_ren_validblock in v.
      congruence.
    - intros. specialize (H0 _ _ _ H1).
      destruct v; simpl in *; auto.
      destruct H0 as [b' Hid_ren].
      unfold id_ren in Hid_ren.
      destruct (valid_block_dec m b0); simpl in Hid_ren; try discriminate.
      eapply Mem.valid_block_alloc with (b' := b0) in v; eauto.
      inv Hid_ren.
      exists b'.
      eapply id_ren_validblock in v.
      now eauto.
  Qed.
  
Lemma valid_genv_store: forall ge m m1 b ofs v chunk
    (STORE: Mem.store chunk m b ofs v = Some m1)
     (G: X86WD.ge_wd (id_ren m) ge), X86WD.ge_wd (id_ren m1) ge.
Proof.
  intros. case G; intros.
  - constructor; intros.
    specialize (H _ H1).
    unfold id_ren in *.
    destruct (valid_block_dec m b0); simpl in H; try discriminate.
    eapply Mem.store_valid_block_1 in v0; eauto.
    destruct (valid_block_dec m1 b0); now eauto.
  - eapply MemoryWD.wd_val_valid; eauto using id_ren_domain.
    eapply MemoryWD.valid_val_store; eauto.
    eapply MemoryWD.wd_val_valid;
      now eauto using id_ren_domain.
Qed.

Lemma valid_genv_store_zeros: forall ge m m1 b y z
    (STORE_ZERO: store_zeros m b y z = Some m1)
    (G: X86WD.ge_wd (id_ren m) ge), X86WD.ge_wd (id_ren m1) ge.
Proof.
  intros. case G; intros.
  apply Genv.store_zeros_nextblock in STORE_ZERO.
  constructor; intros.
  - specialize (H _ H1).
    rewrite id_ren_validblock; eauto.
    unfold id_ren in H.
    destruct (valid_block_dec m b0); simpl in H; [|now exfalso].
    unfold Mem.valid_block in *.
    rewrite STORE_ZERO;
      now assumption.
  - specialize (H0 _ _ _ H1).
    destruct v; auto.
    simpl in *.
    destruct H0 as [b' H0].
    exists b'.
    erewrite id_ren_validblock.
    apply id_ren_correct in H0; subst; eauto.
    unfold id_ren in H0.
    destruct (valid_block_dec m b0); simpl in H; [|now exfalso].
    unfold Mem.valid_block in *.
    rewrite STORE_ZERO;
      now assumption.
Qed.

Lemma mem_wd_store_zeros: forall m b p n m1
                            (STORE_ZERO: store_zeros m b p n = Some m1)
                            (WD: MemoryWD.valid_mem m),
    MemoryWD.valid_mem m1.
Proof. intros until n. functional induction (store_zeros m b p n); intros.
  inv STORE_ZERO; tauto.
  apply (IHo _ STORE_ZERO); clear IHo.
  eapply (MemoryWD.store_wd_domain); eauto.
  now eapply id_ren_domain.
  simpl; auto.
  inv STORE_ZERO.
Qed.

    Lemma validblock_id_ren : forall (m : mem) (b : block),
        id_ren m b ->  Mem.valid_block m b.
    Proof.
      intros.
      unfold id_ren in H.
      destruct (valid_block_dec m b); simpl in H; auto; discriminate.
    Qed.

Lemma valid_genv_drop: forall ge (m m1:mem) b lo hi p
    (DROP: Mem.drop_perm m b lo hi p = Some m1) (G: X86WD.ge_wd (id_ren m) ge),
    X86WD.ge_wd (id_ren m1) ge.
Proof.
  intros. case G; intros. constructor; intros.
  - specialize (H _ H1).
    erewrite id_ren_validblock; eauto.
    eapply validblock_id_ren in H.
    apply (Mem.drop_perm_valid_block_1 _ _ _ _ _ _ DROP);
      auto.
  - specialize (H0 _ _ _ H1).
    destruct v; simpl in *; auto.
    destruct H0 as [? H0].
    exists b0.
    eapply id_ren_validblock.
    apply (Mem.drop_perm_valid_block_1 _ _ _ _ _ _ DROP).
    eapply validblock_id_ren.
    erewrite H0;
      now eauto.
Qed.

Lemma mem_wd_store_init_data: forall ge a (b:block) (z:Z)
  m1 m2 (SID:Genv.store_init_data ge m1 b z a = Some m2),
  X86WD.ge_wd (id_ren m1) ge -> MemoryWD.valid_mem m1 -> MemoryWD.valid_mem m2.
Proof.
  intros ge a.
  destruct a; simpl; intros;
    try (eapply (MemoryWD.store_wd_domain); eauto using id_ren_domain; simpl; now trivial).
  inv SID.
  now auto.
  destruct (Genv.find_symbol ge i) eqn:Hfind.
  eapply MemoryWD.store_wd_domain; eauto using id_ren_domain.
  simpl.
  destruct H.
  specialize (H1 i i0 (Vptr b0 i0)).
  unfold Senv.symbol_address, Senv.find_symbol in H1.
  simpl in H1.
  rewrite Hfind in H1.
  specialize (H1 ltac:(reflexivity)).
  destruct H1 as [b' H1].
  eapply validblock_id_ren.
  erewrite H1;
    now eauto.
  discriminate.
Qed.

Lemma valid_genv_store_init_data:
  forall ge a (b:block) (z:Z) m1 m2
    (SID: Genv.store_init_data ge m1 b z a = Some m2),
    X86WD.ge_wd (id_ren m1) ge -> X86WD.ge_wd (id_ren m2) ge.
Proof.
  intros ge a.
  destruct a; simpl; intros; inv H; constructor;
  try (intros b0 X;
       erewrite id_ren_validblock; eauto;
       eapply Mem.store_valid_block_1 with (b' := b0); eauto;
       eapply validblock_id_ren; eauto);
  try (intros id ofs v Hsenv;
       specialize (H1 _ _ _ Hsenv);
       eapply MemoryWD.wd_val_valid; eauto using id_ren_domain;
       eapply MemoryWD.valid_val_store; eauto;
       eapply MemoryWD.wd_val_valid; eauto using id_ren_domain);
  inv SID; auto;
  intros;
  destruct (Genv.find_symbol ge i) eqn:Hfind; try discriminate.
  erewrite id_ren_validblock; eauto.
  eapply Mem.store_valid_block_1; eauto.
  eapply validblock_id_ren; now eauto.
  intros .
  specialize (H1 _ _ _ H).
  eapply MemoryWD.wd_val_valid; eauto using id_ren_domain;
    eapply MemoryWD.valid_val_store; eauto;
      eapply MemoryWD.wd_val_valid;
      now eauto using id_ren_domain.
Qed.

Lemma mem_wd_store_init_datalist: forall ge l (b:block)
  (z:Z) m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
  X86WD.ge_wd (id_ren m1) ge -> MemoryWD.valid_mem m1 -> MemoryWD.valid_mem m2.
Proof.
  intros ge l.
  induction l; simpl; intros.
    inv SID. trivial.
  destruct (Genv.store_init_data ge m1 b z a) eqn:Hstore; try discriminate.
  inv SID.
  apply (IHl _ _ _ _ H2); clear IHl H2.
     eapply valid_genv_store_init_data; eauto.
  eapply mem_wd_store_init_data;
    now eauto.
Qed.

Lemma valid_genv_store_init_datalist: forall ge l (b:block)
  (z:Z) m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
    X86WD.ge_wd (id_ren m1) ge -> X86WD.ge_wd (id_ren m2) ge.
Proof.
  intros ge l.
  induction l; simpl; intros.
    inv SID. trivial.
  destruct (Genv.store_init_data ge m1 b z a) eqn:Hstore; try discriminate.
  inv SID.
  apply (IHl _ _ _ _ H1); clear IHl H1.
  eapply valid_genv_store_init_data;
    now eauto.
Qed.

Lemma mem_valid_drop :
  forall (m : mem) (b : block) (lo hi : Z) (p : permission) (m' : mem),
    Mem.drop_perm m b lo hi p = Some m' ->
    MemoryWD.valid_mem m -> MemoryWD.valid_mem m'.
Proof.
  intros.
  unfold Mem.drop_perm in H.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv H.
  unfold MemoryWD.valid_mem, mem_wd.val_valid, Mem.valid_block in *.
  simpl in *.
  now auto.
Qed.

Lemma mem_wd_alloc_global: forall ge a m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   MemoryWD.valid_mem m0 -> X86WD.ge_wd (id_ren m0) ge -> MemoryWD.valid_mem m1.
Proof.
  intros ge a.
  destruct a; simpl. intros.
  destruct g.
  remember (Mem.alloc m0 0 1) as mm. destruct mm.
  symmetry in Heqmm.
  specialize (X86Inj.mem_valid_alloc ltac:(eauto using id_ren_domain) H Heqmm).
  intros (? & ?).
  eapply mem_valid_drop;
    now eauto.
  (* apply (Mem.valid_new_block _ _ _ _ _ Heqmm). *)
  remember (Mem.alloc m0 0 (init_data_list_size (AST.gvar_init v)) ) as mm.
  destruct mm. symmetry in Heqmm.
  destruct (store_zeros m b 0 (init_data_list_size (AST.gvar_init v))) eqn:Hzeros;
    try discriminate.
  destruct (Genv.store_init_data_list ge m2 b 0 (AST.gvar_init v)) eqn:Hinit_data;
    try discriminate.
  eapply mem_valid_drop in GA; eauto.
  eapply mem_wd_store_init_datalist; eauto.
  eapply valid_genv_store_zeros; eauto.
  eapply valid_genv_alloc; eauto.
  eapply mem_wd_store_zeros; eauto.
  eapply X86Inj.mem_valid_alloc;
    now eauto using id_ren_domain.
Qed.

Lemma valid_genv_alloc_global: forall ge a m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   X86WD.ge_wd (id_ren m0) ge -> X86WD.ge_wd (id_ren m1) ge.
Proof.
  intros ge a.
  destruct a; simpl. intros.
  destruct g.
  destruct (Mem.alloc m0 0 1) eqn:Hmem.
  eapply valid_genv_drop in GA; eauto.
  eapply valid_genv_alloc in Hmem; eauto.
  destruct  (Mem.alloc m0 0 (init_data_list_size (AST.gvar_init v))) eqn:Halloc;
    try discriminate.
  destruct (store_zeros m b 0
                        (init_data_list_size (AST.gvar_init v))) eqn:SZ;
    try discriminate.
  destruct (Genv.store_init_data_list ge m2 b 0 (AST.gvar_init v)) eqn:init_data;
    try discriminate.
  eapply valid_genv_drop in GA; eauto.
  eapply valid_genv_store_init_datalist in init_data; eauto.
  eapply valid_genv_store_zeros in SZ; eauto.
  eapply valid_genv_alloc in Halloc;
    now eauto.
Qed.

Lemma valid_genv_alloc_globals:
   forall ge init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
     X86WD.ge_wd (id_ren m0) ge -> X86WD.ge_wd (id_ren m) ge.
Proof.
  intros ge l.
  induction l; intros; simpl in *.
  inv GA. assumption.
  destruct (Genv.alloc_global ge m0 a) eqn:Halloc; try discriminate.
  eapply (IHl  _ _  GA).
  eapply valid_genv_alloc_global;
    now eauto.
Qed.

Lemma mem_wd_alloc_globals:
   forall ge init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
   MemoryWD.valid_mem m0 -> X86WD.ge_wd (id_ren m0) ge -> MemoryWD.valid_mem m.
Proof.
  intros ge l.
  induction l; intros; simpl in *.
  inv GA. assumption.
  destruct (Genv.alloc_global ge m0 a) eqn:Halloc; try discriminate.
  eapply (IHl  _ _ GA).
  eapply mem_wd_alloc_global;
    eauto.
  eapply valid_genv_alloc_global;
    now eauto.
Qed.

(*Lemma  genv_init_mem_valid:
  forall (p : Asm.program) m1,
    Globalenvs.Genv.init_mem p = Some m1 ->
    MemoryWD.valid_mem m1.
Proof.
  intros.
  unfold Globalenvs.Genv.init_mem in H.
  eapply InitialMemWD.mem_wd_alloc_globals;
    eauto.
  intros b Hcontra ? ? ?.
  clear - Hcontra.
  unfold Mem.valid_block, Plt in Hcontra. simpl in Hcontra.
  exfalso.
  zify; now omega.
  assert (X86WD.ge_wd (id_ren m1) (Genv.globalenv p)).
  { econstructor.
    intros.
    destruct ( (Genv.genv_defs (Genv.globalenv p)) ! b) eqn:Hgenv.
    eapply Genv.genv_defs_range in Hgenv.
    erewrite Genv.init_mem_genv_next in Hgenv by eauto.
    (*easy*)
    now exfalso.
    intros.
    unfold Senv.symbol_address in H0.
    destruct (Senv.find_symbol (Genv.globalenv p) id) eqn:Hfind; subst; simpl; auto.
    apply Senv.find_symbol_below in Hfind.
    unfold Senv.nextblock in Hfind.
    simpl in Hfind.
    erewrite Genv.init_mem_genv_next in Hfind by eauto.
    (*easy*)
  } *)

End InitialMemWD.


Module X86Safe.

  Import AsmContext SCErasure X86Context X86SEMAxioms HybridMachine
         HybridMachineSig HybridCoarseMachine HybridFineMachine
         FineConcSafe FineConcInitial Executions SpinLocks.

  Section X86Safe.

    Context {U: seq.seq nat}
            {the_program: Asm.program}
            {Hsafe: Asm_core.safe_genv (@the_ge the_program)}.
    
    Instance X86Sem : Semantics := @X86Sem the_program Hsafe.
    Instance X86Axioms : CoreLanguage.SemAxioms := @X86Axioms the_program Hsafe.
    Instance X86Det : CoreLanguage.SemDet := @X86Det the_program Hsafe.
    Existing Instance X86CoreErasure.X86Erasure.
    Existing Instance X86Inj.X86Inj.
    (* We don't really have an instance for that, it would require to prove that
                                the initial memory has no invalid pointers *)
    Context {FI : FineInit}. 
    Variable em : ClassicalFacts.excluded_middle.
    Existing Instance dryCoarseMach.
    Existing Instance dryFineMach.
    Existing Instance bareMach.

    Notation fexecution := (@fine_execution _ FineDilMem DryHybridMachine.dryResources DryHybridMachine.DryHybridMachineSig).
    Notation sc_execution := (@fine_execution _ BareDilMem BareMachine.resources BareMachine.BareMachineSig).
    Notation fsafe := (@HybridFineMachine.fsafe DryHybridMachine.dryResources _
                                                OrdinalPool.OrdinalThreadPool
                                                DryHybridMachine.DryHybridMachineSig FineDilMem).
    Notation sc_safe := (@HybridFineMachine.fsafe BareMachine.resources _
                                                  OrdinalPool.OrdinalThreadPool
                                                  BareMachine.BareMachineSig BareDilMem).

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
          (forall n,
              sc_safe
              init_tp_bare (@diluteMem BareDilMem new_mem_target) U n) /\
            (forall final_state final_mem tr,
                sc_execution  (U, [::], init_tp_bare) (@diluteMem BareDilMem new_mem_target)
                              ([::], tr, final_state) final_mem ->
                spinlock_synchronized tr).
    Proof.
      intros.
      (** Fine to Erased safety *)
      assert (HscSafe:
                 (forall n,
                    fsafe init_tpc_target (@diluteMem FineDilMem new_mem_target) U n) /\
                (forall n,
                    sc_safe
                      init_tp_bare (@diluteMem BareDilMem new_mem_target) U n) /\
                (forall tpf' mf' tr,
                    fexecution (U, [::], init_tpc_target) (@diluteMem FineDilMem new_mem_target)
                               ([::], tr, tpf') mf' ->
                    exists tpsc' msc' tr',
                       sc_execution (U, [::], init_tp_bare) (@diluteMem BareDilMem new_mem_target)
                                   ([::], tr', tpsc') msc' /\
                       ThreadPoolErasure.threadPool_erasure tpf' tpsc' /\
                       MemErasure.mem_erasure mf' msc' /\
                       TraceErasure.trace_erasure tr tr')).
      { (** Coarse to Fine safety *)
        assert (forall n : nat, fsafe init_tpc_target (@diluteMem FineDilMem new_mem_target) U n).
        { intros n.
          eapply init_fine_safe with (f := Main_ptr) (arg := nil); eauto.
          intros sched tpc mem' n1 Htpc.
          destruct Htpc as [_ Hinit_tpc].
          simpl in Hinit_tpc.
          unfold DryHybridMachine.init_mach in Hinit_tpc.
          destruct Hinit_tpc as [c_new [Hinit_core_new ?]].
          simpl in Hcsafe.
          specialize (Hcsafe n1 sched).
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
          now econstructor. }
        split; eauto.
        eapply sc_erasure with (m := init_mem) (f := Main_ptr) (arg := nil)
                               (tpf := init_tpc_target); eauto.
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

      }
      destruct HscSafe as [Hfsafe [HscSafe Hexec]].
      split; eauto.
      intros final_state final_mem tr HSCexec.
      eapply @fsafe_execution with (tr := [::]) in Hfsafe.
      destruct Hfsafe as [tpf' [mf' [trf' HexecF]]].
      destruct (Hexec _ _ _ HexecF) as [tpsc' [msc' [tr' [HexecSC' [_ [_ Htr_erasure]]]]]].
      eapply fine_execution_multi_step in HexecF.
      simpl in HexecF.
      pose proof (@bare_execution_det _ X86Det _ _ _ _ _ _ HSCexec HexecSC') as Heq.
      destruct Heq as [Heq1 Heq2].
      inversion Heq1; subst.
      simpl in Htr_erasure.
      eapply fineConc_spinlock in HexecF; eauto.
      eapply SpinLocksSC.trace_erasure_spinlock_synchronized;
        eauto.
      auto.
      Unshelve. auto.
    Qed.

  End X86Safe.
End X86Safe.
