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
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.


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
Require Import VST.concurrency.compiler.multiple_thread_simulation_proof.


Section Concurrent_correctness.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  Context (Hlimited_builtins: Asm_core.safe_genv Asm_g).
    
  (*Import TSim.
  Import MySyncSimulation.MySimulationTactics.MyConcurMatch.MyThreadSimulationDefinitions.
*)

  
    Existing Instance HybridSem.
    Existing Instance dryResources.
    Existing Instance DryHybridMachineSig.
    
  
  Section TrivialSimulations.
    Notation scheduler:=HybridMachineSig.HybridMachineSig.HybridCoarseMachine.scheduler.
    
    Definition ctl_lifting {c1 c2} (f:c1 -> c2) (C:@ctl c1) :=
      match C with
      | Krun X0 => Krun (f X0)
      | Kblocked X0 => Kblocked (f X0)
      | Kresume X0 X1 => Kresume (f X0) X1
      | Kinit X0 X1 => Kinit X0 X1
      end.
    Definition lift_state {resources Sem1 Sem2}
               (f: @semC Sem1 -> @semC Sem2):
      @OrdinalPool.t resources Sem1 ->
      @OrdinalPool.t resources Sem2.
    Proof. intros X; inv X.
           econstructor; try eassumption.
           intros h. eapply ctl_lifting; swap 1 2.
           eapply pool; auto.
           exact f.
    Defined.
    Definition lift_c_state:
      @OrdinalPool.t dryResources (@ClightMachine.DMS.DSem Clight_g) ->
      @OrdinalPool.t dryResources (HybridSem (@Some nat O)).
    Proof.
      eapply lift_state. simpl; intros XX.
      apply SState; exact XX.
    Defined.

    Definition ctl_c_lifting:=
      ctl_lifting (fun XX : Clight.state => SState Clight.state Asm.state XX).
      Definition trivial_order: unit -> unit -> Prop := (fun _ _=> False).
    Lemma trivial_order_wf: well_founded trivial_order.
    Proof. do 2 econstructor. inv H. Qed.

    Lemma clight_step_nextblock:
      forall g s m t s' m',
        ClightSemanticsForMachines.clc_evstep
          g (ClightSemanticsForMachines.function_entryT2 g) s m t s' m' ->
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      eapply ClightSemanticsForMachines.CLC_evsem_obligation_3 in H.
      eapply event_semantics.ev_elim_mem_fw; eauto.
    Qed.
    Lemma contains_lift_c_state:
      forall c j,
        OrdinalPool.containsThread (lift_c_state c) j <->
        OrdinalPool.containsThread c j.
    Proof.
      intros. unfold lift_c_state, lift_state, OrdinalPool.containsThread; simpl.
      destruct c; simpl; reflexivity.
    Qed.
    Lemma invariant_lift_c_state:
      forall (st:ThreadPool.t),
        invariant(tpool:=OrdinalPool.OrdinalThreadPool) st ->
        invariant(tpool:=OrdinalPool.OrdinalThreadPool)
                 (lift_c_state st).
    Proof.
      intros. unfold lift_c_state, lift_state, OrdinalPool.containsThread; simpl.
      destruct st.
      inv H; simpl in *.
      econstructor; eauto.
    Qed.
    Lemma mem_compatible_lift_c_state:
      forall st1 m2,
        @mem_compatible _ OrdinalPool.OrdinalThreadPool st1 m2 ->
        @HybridMachineSig.HybridMachineSig.mem_compatible
          _ _ _ (@DryHybridMachineSig _ (TP _)) (lift_c_state st1) m2.
    Proof.
      intros. unfold lift_c_state, lift_state, OrdinalPool.containsThread; simpl.
      destruct st1.
      inv H; simpl in *.
      econstructor; eauto.
    Qed.
    Lemma internal_step_lift_c_state:
      forall U (st1:HybridMachineSig.HybridMachineSig.machine_state)
        m2 st1' m1',
        HybridMachineSig.HybridMachineSig.internal_step
          (ThreadPool:=OrdinalPool.OrdinalThreadPool) U st1 m2 st1' m1' ->
        HybridMachineSig.HybridMachineSig.internal_step
          (ThreadPool:=OrdinalPool.OrdinalThreadPool)
          U (lift_c_state st1) m2 (lift_c_state st1') m1'.
    Proof.
      intros.
      inv H; simpl in *.
      replace m' with  (HybridMachineSig.HybridMachineSig.diluteMem m') by
          reflexivity.
      unshelve econstructor; eauto.
      - eapply contains_lift_c_state; assumption.
      - eapply mem_compatible_lift_c_state; eauto.
      - repeat clean_proofs.
        match goal with 
          |- HybridMachineSig.HybridMachineSig.threadStep ?X _ _ _ _ =>
          remember X as HH eqn:HHclear; clear HHclear
        end.
        clear - m2 m' st1 st1' tid ev Htid Hcmpt Htstep.
        revert m2 m' st1 st1' tid ev Htid Hcmpt Htstep abs_proof HH.
        Lemma thread_step_lift_c_state:
          forall (m2 m' : Mem.mem)
            (st1 st1' : OrdinalPool.t)
            tid (ev : list event_semantics.mem_event)
            (Htid : OrdinalPool.containsThread st1 tid)
            (Hcmpt : @mem_compatible _ OrdinalPool.OrdinalThreadPool st1 m2),
            @threadStep _ OrdinalPool.OrdinalThreadPool tid st1 m2 Htid Hcmpt st1' m' ev ->
            forall (Hcmpt' : @HybridMachineSig.HybridMachineSig.mem_compatible
                           _ _ OrdinalPool.OrdinalThreadPool DryHybridMachineSig 
                           (lift_c_state st1) m2)
            (Hcnt : OrdinalPool.containsThread (lift_c_state st1) tid),
            @HybridMachineSig.HybridMachineSig.threadStep _ _
                                                          OrdinalPool.OrdinalThreadPool
                                                          _ _
                                                          (lift_c_state st1)
                                                          m2 Hcnt
                                                          Hcmpt' (lift_c_state st1') m' ev.
        Proof.
          intros. unfold lift_c_state, lift_state, OrdinalPool.containsThread; simpl.
          destruct st1.
          inv H; simpl in *.
          clean_proofs.
          econstructor; eauto.
          - exploit invariant_lift_c_state; eauto.
          - simpl in *. rewrite Hcode. reflexivity.
          - unshelve econstructor 1; simpl; eauto.
            clean_proofs. eauto.
          - simpl.
            unfold OrdinalPool.updThread; simpl.
            f_equal. simpl.
            extensionality n.
            match_case; eauto; try(
             match_case in Heqc0; rewrite Heqc0; auto).
        Qed.
        apply thread_step_lift_c_state.
    Qed.

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
      simpl in Hcorestep.
      eapply clight_step_nextblock in Hcorestep.
      simpl in *; eauto.
    Qed.
    Lemma machine_step_nextblock:
      forall Sch,
        let TP:= (@OrdinalPool.OrdinalThreadPool _
                                                 (@ClightMachine.DMS.DSem Clight_g)) in
        forall  U U' st m st' m' tr tr',
          (@HybridMachineSig.HybridMachineSig.external_step
             _ _ TP HybridMachineSig.HybridMachineSig.HybridCoarseMachine.DilMem
             (@DryHybridMachineSig (@ClightMachine.DMS.DSem Clight_g)
                                   _) Sch)
            U tr st m U' tr' st' m' ->
          (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros. inv H; eauto; simpl; try reflexivity.
      - inv Htstep. inv Hinitial; simpl in *.
        inv Hperm. inv H. reflexivity.
      - inv Htstep; try reflexivity.
        + eapply Mem.nextblock_store in Hstore; rewrite Hstore; reflexivity.
        + eapply Mem.nextblock_store in Hstore; rewrite Hstore; reflexivity.
        + eapply Mem.nextblock_store in Hstore; rewrite Hstore; reflexivity.
    Qed.
    Lemma machine_step_trace_C:
      forall init_m ge sge U tr st m U' tr' st' m',
        machine_semantics.machine_step 
          (@ClightMachine.DMS.ClightConcurSem ge init_m)
          sge U tr st m U' tr' st' m' ->
        exists tr_tail,
          tr' = tr ++ tr_tail.
    Proof.
      intros. inv H; econstructor; try apply app_nil_end.
      - reflexivity.
    Qed.
    Lemma external_step_event_injectable:
      forall SM U tr st m U' tr_tail st' m',
        @HybridMachineSig.HybridMachineSig.external_step
          _ _ (@OrdinalPool.OrdinalThreadPool dryResources (@ClightMachine.DMS.DSem Clight_g))
          SM (@DryHybridMachineSig (@ClightMachine.DMS.DSem Clight_g)
           (@OrdinalPool.OrdinalThreadPool dryResources
              (@ClightMachine.DMS.DSem Clight_g))) scheduler
          U tr st m U' (tr ++ tr_tail) st' m' ->
        Forall2 (inject_mevent (Mem.flat_inj (Mem.nextblock m'))) tr_tail tr_tail.
      intros. inv H;
      try (match goal with
        [ H: ?x = ?x ++ _ |- _ ] =>
        eapply threads_lemmas.app_eq_refl_nil in H; inv H
           end; constructor).
      rewrite Coqlib3.cat_app in H6.
      eapply app_inv_head in H6. subst tr_tail.
      econstructor; try solve[econstructor].
      econstructor.
      simpl in Htstep. inv Htstep.
      - econstructor; simpl. 
        + econstructor. unfold Mem.flat_inj. 
          * match_case; eauto.
            clear Heqs. contradict n.
            erewrite Mem.nextblock_store; eauto; simpl.
            eapply memory_lemmas.MemoryLemmas.load_valid_block in Hload as HH.
            eapply HH.
          * omega.
        + econstructor.
      - econstructor; simpl. 
        + econstructor. unfold Mem.flat_inj. 
          * match_case; eauto.
            clear Heqs. contradict n. 
            erewrite Mem.nextblock_store; eauto; simpl.
            eapply memory_lemmas.MemoryLemmas.load_valid_block in Hload as HH.
            eapply HH.
          * omega.
        + econstructor.
      - econstructor; simpl. 
        + econstructor. unfold Mem.flat_inj. 
          * match_case; eauto.
            clear Heqs. contradict n.
            move Hf_ptr_nonempty at bottom.
            simpl in Hf_ptr_nonempty.
            unfold HybridMachineSig.HybridMachineSig.isCoarse in Hf_ptr_nonempty.
            eapply Mem.perm_valid_block; eauto.
          * omega.
        + econstructor.
        + econstructor.
      - econstructor; simpl. 
        + econstructor. unfold Mem.flat_inj. 
          * match_case; eauto.
            clear Heqs. contradict n. 
            eapply Mem.load_store_same in Hstore.
            eapply memory_lemmas.MemoryLemmas.load_valid_block in Hstore as HH.
            eapply HH.
          * omega.
      - econstructor; simpl. 
        + econstructor. unfold Mem.flat_inj. 
          * match_case; eauto.
            clear Heqs. contradict n.
            eapply Mem.perm_valid_block.
            instantiate(1:= Writable).
            eapply perm_range_perm in Hfreeable.
            instantiate(1:= intval ofs) in Hfreeable.
            eapply Mem.perm_cur_max in Hfreeable.
            unfold Mem.perm in *.
            repeat rewrite_getPerm.
            rewrite getMax_restr in Hfreeable.
            instantiate(1:=Max).
            instantiate(1:=intval ofs).
            rewrite_getPerm. auto.
            hnf; simpl. pose proof LKSIZE_pos; omega.
          * omega.    
      - econstructor; simpl. 
        + econstructor. unfold Mem.flat_inj. 
          * match_case; eauto.
            clear Heqs. contradict n. 
            eapply memory_lemmas.MemoryLemmas.load_valid_block in Hload as HH.
            eapply HH.
          * omega.

    Qed.
    Local Ltac cat_find_and_replace_nil:=
        match goal with
        | [H: ?t = ?t ++ ?x |- _ ] =>
          eapply threads_lemmas.app_eq_refl_nil in H;
          subst x; try rewrite app_nil_r in *
        | [H: seq.cat ?t ?y = ?t ++ ?x |- _ ] =>
          rewrite Coqlib3.cat_app in H;
          apply app_inv_head in H; subst x
        end.
    Lemma getC_lift_c_state:
      forall (st:OrdinalPool.t) tid c
        (cnt: OrdinalPool.containsThread st tid)
        (cnt': OrdinalPool.containsThread (lift_c_state st) tid),
        OrdinalPool.getThreadC cnt = c ->
        OrdinalPool.getThreadC cnt' =
        ctl_c_lifting c.
    Proof.
      intros *. unfold OrdinalPool.getThreadC; destruct st; simpl in *.
      clean_proofs; intros ->; reflexivity.
    Qed.
    Lemma getR_lift_c_state:
      forall (st:OrdinalPool.t) tid
        (cnt: OrdinalPool.containsThread st tid)
        (cnt': OrdinalPool.containsThread (lift_c_state st) tid),
        OrdinalPool.getThreadR cnt' = OrdinalPool.getThreadR cnt.
    Proof.
      intros *. unfold OrdinalPool.getThreadR; destruct st; simpl in *.
      clean_proofs; reflexivity.
    Qed.
    Lemma updThread_lift:
      forall (st:OrdinalPool.t) tid c perms
        (cnt: OrdinalPool.containsThread st tid)
        (cnt': OrdinalPool.containsThread (lift_c_state st) tid),
        lift_c_state  (OrdinalPool.updThread cnt c perms) =
        OrdinalPool.updThread cnt' (ctl_c_lifting c) perms.
    Proof.
      intros. destruct st; simpl.
      unfold OrdinalPool.updThread; simpl.
      f_equal. extensionality n.
      clean_proofs.
      match_case; eauto; simpl; try reflexivity.
    Qed.
    Ltac simpl_rewrite H:=
      let HH:=fresh in
                pose proof H as HH;
                simpl in HH; erewrite HH.


    Lemma lift_c_lockRes:
          forall st b ofs,
            OrdinalPool.lockRes (lift_c_state st) (b, intval ofs) =
            OrdinalPool.lockRes st (b, intval ofs).
        Proof.
          intros.
          destruct st. simpl.
          unfold OrdinalPool.lockRes, OrdinalPool.lockGuts;
            reflexivity.
        Qed.
    Lemma sync_step_lift_c_state:
      forall st tid m st' m' ev
        (Hcnt: OrdinalPool.containsThread st tid)
        (Hcmpt: @HybridMachineSig.HybridMachineSig.mem_compatible
                  _ _ _
                  (@DryHybridMachineSig _ OrdinalPool.OrdinalThreadPool)
                  st m),
        @HybridMachineSig.HybridMachineSig.syncStep
          _ _ _ (@DryHybridMachineSig _ OrdinalPool.OrdinalThreadPool)
          true tid st m  Hcnt Hcmpt st' m' ev ->
        forall (Hcnt': OrdinalPool.containsThread (lift_c_state st) tid)
          (Hcmpt': @HybridMachineSig.HybridMachineSig.mem_compatible
                     _ _ _
                     (@DryHybridMachineSig (HybridSem _) _)
                     (lift_c_state st) m),
          @HybridMachineSig.HybridMachineSig.syncStep
            _ (HybridSem _) _ _ true tid 
            (lift_c_state st) m  Hcnt' Hcmpt' (lift_c_state st') m' ev.
    Proof.
      intros.
      inv H; simpl in *;
        [ econstructor 1|
          econstructor 2|
          econstructor 3|
          econstructor 4|
          econstructor 5|
          econstructor 6]; simpl; eauto.
      all: try (erewrite Compcert_lemmas.restre_equiv_eq; eauto;
            erewrite getR_lift_c_state; reflexivity).
      all: try now eapply invariant_lift_c_state; eauto.
      all: try solve[ exploit getC_lift_c_state; eauto].
      all: try (erewrite Compcert_lemmas.restre_equiv_eq; eauto;
            erewrite getR_lift_c_state; reflexivity).
      all: try (erewrite getR_lift_c_state; eassumption).
      all: try now rewrite lift_c_lockRes; eassumption.
      all: destruct st; simpl; eauto.
      - unfold OrdinalPool.updLockSet, OrdinalPool.updThread; simpl.
        f_equal; extensionality h;
          clean_proofs_goal; match_case; reflexivity.
      - unfold OrdinalPool.updLockSet, OrdinalPool.updThread; simpl.
        f_equal; extensionality h;
        clean_proofs_goal; match_case; reflexivity.
      - subst_set.
        unfold OrdinalPool.addThread, OrdinalPool.updThread; simpl.
        f_equal; extensionality h;
          clean_proofs_goal; repeat (match_case; try reflexivity).
      - unfold OrdinalPool.updLockSet, OrdinalPool.updThread; simpl.
        f_equal; extensionality h;
        clean_proofs_goal; match_case; reflexivity.
      - unfold OrdinalPool.remLockSet, OrdinalPool.updThread; simpl.
        f_equal; extensionality h;
          clean_proofs_goal; match_case; reflexivity.

        Unshelve.
        all: try (erewrite getR_lift_c_state; eassumption).
    Qed.
    
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
      
      inv H; try cat_find_and_replace_nil;
      try match goal with
        [H: ThreadPool.containsThread ?st ?tid |- _ ]=>
        try assert (OrdinalPool.containsThread (lift_c_state st) tid)
            by (eapply contains_lift_c_state; eauto)
      end.
        
      
      (* Here is the tactics for lifting all the easy subgoals *)
      Ltac lift_subgoals:=
        simpl;
        try solve[ eapply mem_compatible_lift_c_state; eauto];
        try solve[ eapply invariant_lift_c_state; eauto];
        try (match goal with
                |- install_perm _ _ _ _ _ _ =>
                solve [econstructor]
               end);
        try (unshelve simpl_rewrite updThread_lift; eauto; shelve_unifiable);
        (* solve the getThreadC goals*)
        try solve[match goal with [Hcode: ThreadPool.getThreadC _ = _  |- _ ]=>
                                  try eapply getC_lift_c_state in Hcode;
                                  apply Hcode
                  end].
        
      - (*START_THREAD*)
        unshelve econstructor 1; eauto.
        inv Htstep; unshelve econstructor;
            lift_subgoals; shelve_unifiable.
        2:{ unfold add_block.
            simpl; unfold OrdinalPool.updThread. simpl. 
            clean_proofs. 
            destruct st; simpl in *.
            clean_proofs. reflexivity. }
        + simpl; split.
          * !goal (~ (tid < 0)%nat).
            clear - ctn. intros HH.
            hnf in ctn; simpl in *.
            pose proof (@ssrnat.ltP (tid) (pos.n (OrdinalPool.num_threads st))).
            rewrite ctn in H; inv H.
            omega.
          * destruct Hinitial as [Hinitial  Hinitial_mem].
            econstructor; eauto. simpl.
            simpl in Hinitial.
            match goal with
              |- ?F ?m _ _ _ => replace m with m'
            end; eauto.
            { inv Hperm. clean_proofs.
              eapply restrPermMap_irr'.
              simpl. destruct st; simpl.
              clean_proofs. auto. }
      - (*RESUME_THREAD*)
        unshelve exploit getR_lift_c_state;
          eauto; intros Hsame_R.
        unshelve econstructor 2; eauto.
        inv Htstep; unshelve econstructor;
          lift_subgoals; shelve_unifiable; simpl in  *.
          (* * rewrite <- Hat_external. repeat f_equal.
            inv Hperm. eapply restrPermMap_irr'.
            erewrite getR_lift_c_state; reflexivity. *)
          * unfold state_sum_options.
            inv Hperm. simpl in *.
            clean_proofs.
            erewrite restrPermMap_irr'.
            rewrite Hafter_external; eauto.
            rewrite Hsame_R; reflexivity.
          * simpl; unfold OrdinalPool.updThreadC. simpl. 
            destruct st; f_equal; simpl.
            extensionality n; simpl.
            clean_proofs. 
            match_case; eauto.
      - (*SUSPEND_THREAD*)
        unshelve exploit getR_lift_c_state;
          eauto; intros Hsame_R.
        unshelve econstructor 3; eauto.
        inv Htstep; unshelve econstructor;
          lift_subgoals; shelve_unifiable; simpl in  *.
          * rewrite <- Hat_external. repeat f_equal.
            inv Hperm. eapply restrPermMap_irr'.
            erewrite getR_lift_c_state; reflexivity.
          * simpl; unfold OrdinalPool.updThreadC. simpl. 
            destruct st; f_equal; simpl.
            extensionality n; simpl.
            clean_proofs. 
            match_case; eauto.
      - (*Sync_THREAD*)
        unshelve exploit getR_lift_c_state;
          eauto; intros Hsame_R.
        unshelve econstructor 4; eauto.
        + eapply mem_compatible_lift_c_state; eauto.
        + clean_proofs_goal.
          eapply sync_step_lift_c_state; eauto.
      - (*schedfail*)
        unshelve econstructor 5; eauto.
        + destruct Htid; [left| right].
          * intros HH; eapply H. eapply contains_lift_c_state; eauto.
          * destruct H as (?&?&?&?&?).
            repeat (econstructor; eauto).
            eapply getC_lift_c_state in H.
            simpl in H. eauto.
            simpl; eauto.
        + eapply invariant_lift_c_state; eauto.
        + eapply mem_compatible_lift_c_state; eauto.

          Unshelve.
          eapply contains_lift_c_state; eauto.
    Qed. 
    
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
        unfold ctl_lifting in H.
        match_case in H.
        unshelve eapply HH; debug eauto.
      - unshelve eapply HH.
        + apply contains_lift_c_state; assumption.
        + apply SState, q.
        + eapply getC_lift_c_state in H; simpl in *.
          eauto.
    Qed.
    
    Inductive refl_match {st_t:Type}: unit -> meminj -> st_t -> mem -> st_t -> mem -> Prop :=
    | Build_refl_match:
        forall m st, refl_match tt (Mem.flat_inj (Mem.nextblock m)) st m st m.
    Definition lifted_refl_match :=
      fun cd j st1 m1 st2 m2 =>
         refl_match cd j (lift_c_state st1) m1 st2 m2.
    Lemma trivial_clight_simulation:
      (HybridMachine_simulation'
         (ClightMachine.DMS.ClightConcurSem
            (ge:=Clight_g)
            (Genv.init_mem (Ctypes.program_of_program C_program)))
         (HybConcSem (Some 0)%nat (Genv.init_mem (Ctypes.program_of_program C_program))))
        (@invariant _ (OrdinalPool.OrdinalThreadPool))
        (@invariant _ (OrdinalPool.OrdinalThreadPool))
        (@mem_compatible _ (OrdinalPool.OrdinalThreadPool))
        (@mem_compatible _ (OrdinalPool.OrdinalThreadPool)).
    Proof.
      intros.
      unshelve eapply Build_HybridMachine_simulation' with
          (match_state:=lifted_refl_match).
      - intros. hnf in H. inv H.
        eapply invariant_lift_c_state; eauto.
      - intros. hnf in H. inv H.
        eapply mem_compatible_lift_c_state; eauto.
      - { unshelve econstructor.
          - exact trivial_order.
          - exact trivial_order_wf.
          - (*initial_setup*)
            simpl; intros.
            exists (Mem.flat_inj (Mem.nextblock s_mem)), tt.
            unshelve eexists. eapply lift_c_state; eauto.
            exists s_mem, r1; split.
            2: { econstructor. }
            inv H0; econstructor; eauto.
            simpl in *.
        destruct r1; inv H2.
        econstructor; simpl in *.
        normal_hyp. split.
        2: { simpl. unfold lift_state.
             rewrite e; simpl.
             unfold  OrdinalPool.mkPool.
             f_equal. }
        simpl.
        econstructor ; simpl; auto.
        intros HH; omega.
        
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
        + simpl in H. inv H. inv Htstep. simpl in *.
          eapply flat_inj_lt.
          eapply ClightSemanticsForMachines.CLC_evsem_obligation_3,
          Clight_core.ev_elim_mem_step, mem_step_nextblock
            in Hcorestep.
          apply Hcorestep.
          
      - (*machine_diagram*)
        intros; unfold Clight_g; auto.
        unshelve (exploit machine_step_trace_C;
                  simpl in *; eauto); eauto; shelve_unifiable.
        eapply Some; assumption. 
        intros [tr_tail Htr].
        subst tr1'.
        exists (tr2 ++ tr_tail), (lift_c_state st1').
        normal. 
        + econstructor.
        + inv H2; simpl in H.
          eapply Forall_cat; auto.
          eapply inject_incr_trace; try eassumption.
          eapply flat_inj_lt, machine_step_nextblock; eauto.
          eapply external_step_event_injectable; eauto.
        + inv H2.
          eauto; simpl in *.
          eapply external_step_anytrace in H.
          eapply external_step_lift_c_state; eauto.
        + inv H2. 
          eapply flat_inj_lt, machine_step_nextblock; eassumption.
      - intros. revert H0.
        inv H. simpl.
        intros. exists v1. simpl in *.
        eapply halted__lift_c_state; auto.
      - intros; simpl. inv H. 
        apply unique_Krun_lift_c_state. } 
    Qed.
    Lemma trivial_asm_simulation:
      forall ap (Hsafe:Asm_core.safe_genv (@X86Context.the_ge ap)), 
        (HybridMachine_simulation'
         (HybConcSem None (Genv.init_mem ap))
         (X86Context.AsmConcurSem
            (the_program:=ap)
            (Hsafe:=Hsafe)
            (Genv.init_mem ap))
         (@invariant _ (OrdinalPool.OrdinalThreadPool))
         (@invariant _ (OrdinalPool.OrdinalThreadPool))
         (@mem_compatible _ (OrdinalPool.OrdinalThreadPool))
         (@mem_compatible _ (OrdinalPool.OrdinalThreadPool))).

    Proof.
      intros.
    (* This lemma follows just like the one above 
           [trivial_clight_simulation] , but for ASM. 
           will need to repeat many of the lemmas unfortunately.
     *)
    Admitted. (*Checked 1/16/20. adm its: 
                Yes. This should follow exactly like the lemma above for C, 
                any way to modularize the proofs?

               *)
    End TrivialSimulations.


    (* NOTE: This section could be moved to where the simulations are defined. *) 
    Section SimulationTransitivity.
      
          Lemma step_diagram_helper':
            forall{G TID SCH TR C M res inx : Type}
              Machine2 tge U st m st' m' (x1 x2:inx) ord,
              (machine_semantics_lemmas.thread_step_plus Machine2 tge U st m st' m' \/
              machine_semantics_lemmas.thread_step_star Machine2 tge U st m st' m' /\
               ord x1 x2) <->
              (@machine_semantics_lemmas.thread_step_plus
                 G TID SCH TR C M res
                 Machine2 tge U st m st' m' \/
               st = st' /\ m = m' /\ ord x1 x2).
          Proof.
            intros; split.
            - intros [|[]]; eauto.
              destruct H as [n H]. destruct n.
              + inv H; eauto.
              + left; econstructor; eauto.
            - intros [|]; eauto.
              normal; subst. right; split; eauto.
              exists 0%nat. econstructor.
          Qed.
      Lemma HBSimulation_transitivity:
        forall G1 G2 G3 TID SCH C1 C2 C3 res (ge2:G2),
        forall (Machine1 : @machine_semantics.ConcurSemantics G1 TID SCH _ C1 mem res)
               (Machine2 : @machine_semantics.ConcurSemantics G2 TID SCH _ C2 mem res)
               (Machine3 : @machine_semantics.ConcurSemantics G3 TID SCH _ C3 mem res)
        inv1 inv2 inv3 cmpt1 cmpt2 cmpt3,
          HybridMachine_simulation' Machine1 Machine2 inv1 inv2 cmpt1 cmpt2 -> 
          HybridMachine_simulation' Machine2 Machine3 inv2 inv3 cmpt2 cmpt3 ->
          HybridMachine_simulation' Machine1 Machine3 inv1 inv3 cmpt1 cmpt3.
      Proof.
        destruct 2 as [index1 match_state1 match_inv1 match_cmpt1 SIM1].
        destruct 1 as [index2 match_state2 match_inv2 match_cmpt2 SIM2].
        set (match_state := fun a j c1 m1 c3 m3 =>
                              exists j1 j2 c2 m2, j =
                                             compose_meminj j1 j2 /\
                                             match_state1 (snd a) j1 c1 m1 c2 m2 /\
                                             match_state2 (fst a) j2 c2 m2 c3 m3).
        eapply Build_HybridMachine_simulation' with
            (index := (index2 * index1)%type)
            (match_state := match_state).
        { subst match_state; simpl. intros; normal_hyp; eauto.  }
        { subst match_state; simpl. intros; normal_hyp; eauto. }
        
        { inversion SIM1; inversion SIM2; econstructor.
          - apply Coqlib.wf_lex_ord.
            eapply Transitive_Closure.wf_clos_trans; eauto.
            eauto.
        - subst match_state; simpl; intros.
          destruct (initial_setup _ _ _ _ _ _ H H0) as (? & ? & ? & ? & ? & H2 & ?).
          destruct (initial_setup0 _ _ _ _ _ _ H H2) as (? & ?  & ? & ? & ? & ? & ?).
          eexists; eexists (_, _); eauto 12.
        - intros.
          dup H0 as HH.
          unfold match_state in H0; simpl in H0.
          normal_hyp; subst.
          eapply thread_diagram in H; eauto.
          instantiate(1:=ge2) in H.
          normal_hyp.
          eapply step_diagram_helper' in H4. destruct H4 as [H4|(?&?&?)]; swap 1 2.
          + normal; subst.
            * subst match_state; simpl.
              do 4 eexists; repeat weak_split.
              -- reflexivity.
              -- instantiate (4:=(fst cd, x5)).
                 simpl; eauto.
              -- simpl; eauto.
            * eapply inject_incr_trace; try eapply H1.
              apply mem_lemmas.compose_meminj_inject_incr; eauto.
            * eapply step_diagram_helper'.
              right.
              repeat weak_split eauto.
              simpl.
              destruct cd; simpl.
              constructor 2; eauto.
            * apply mem_lemmas.compose_meminj_inject_incr; eauto.
          + destruct cd as (cd2&cd1).
            cut (exists (st2' : C3) (m2' : mem) (cd' : index2 ) (j2' : meminj),
                    match_state2 cd' j2' x3 x4 st2' m2' /\
                    (machine_semantics_lemmas.thread_step_plus Machine3 tge U st2 m2 st2' m2' \/
                     machine_semantics_lemmas.thread_step_star Machine3 tge U st2 m2 st2' m2' /\
                     Relation_Operators.clos_trans _ core_ord0 cd' (cd2)) /\ inject_incr x0 j2').
            { intros; normal.
              - hnf. do 4 eexists. repeat weak_split.
                reflexivity.
                instantiate (4:=(x9, x5)); eauto.
                eauto.
              - eapply inject_incr_trace; try eapply H1.
                apply mem_lemmas.compose_meminj_inject_incr; eauto.
              - destruct H7; normal_hyp; eauto. right; split; eauto.
                econstructor; eauto. 
              - apply mem_lemmas.compose_meminj_inject_incr; eauto. }

            destruct H4.
            revert H4.
            clear - H3 x7 thread_diagram0.
            exploit list_inject_mevent_interpolation; eauto.
            intros; normal_hyp.
            inv H.
            revert tge cd2 st2 m2 x1 x2 x0 x3 x4 H0 H3 H4.
            clear - x7 thread_diagram0.
            induction x7.
            * intros. simpl in H4; normal_hyp.
              inv H1.
              eapply thread_diagram0 in H; eauto.
              normal_hyp.
              normal; eauto.
              { destruct H2; eauto. right;normal_hyp.
                split; eauto. constructor; eauto. } 
            * intros. inv H4. normal_hyp.
              eapply thread_diagram0 in H; eauto.
              normal_hyp. 
              exploit IHx7; eauto.
              intros; normal_hyp.
              instantiate(1:=tge) in H4.
              unshelve eapply step_diagram_helper' in H4; eauto.
              unshelve eapply step_diagram_helper' in H7; eauto.
              normal; eauto.
              2:{ eapply inject_incr_trans; eauto. }
              
              eapply step_diagram_helper'.
              clear - H4 H7.
              destruct H4; destruct H7; normal_hyp; subst; eauto.
              -- left. eapply machine_semantics_lemmas.thread_step_plus_trans; eauto.
              -- right; normal; eauto. 
                 econstructor 2; eauto. constructor; eauto.
        - intros.
          subst match_state; simpl in *; normal_hyp.
          subst mu. apply list_inject_mevent_interpolation in H3.
          normal_hyp. eauto.
          eapply machine_diagram in H; eauto; normal_hyp.
          eapply machine_diagram0 in H7; eauto; normal_hyp.
          exists x9, x10, x11, (x12, x7), (compose_meminj x8 x13). 
          repeat weak_split eauto.
          + normal; eauto.
          + eapply forall_inject_mevent_compose; eauto.
          + apply mem_lemmas.compose_meminj_inject_incr; assumption.
        - intros ???????? (? & ? & ? & ? & ? & ? & ?) ?.
          edestruct thread_halted; eauto.
        - intros ?????? (? & ? & ? & ? & ? & ? & ?) ?.
          erewrite thread_running; eauto.

          Unshelve.
          all: eauto. }          
      Qed.
    End SimulationTransitivity.

  (* Lemma initial_memories_are_equal:
    forall (tp:Asm.program),
      CompCert_compiler C_program = Some tp ->
      Genv.init_mem tp = Genv.init_mem (Ctypes.program_of_program C_program ).
  Proof.
    intros **.
    eapply simpl_clight_semantic_preservation in H.
    inv H. clear - Injfsim_match_entry_pointsX.

    unfold Genv.init_mem; simpl.
    unfold Genv.globalenv; simpl.
    
    
    
    exploit Injfsim_match_entry_pointsX; simpl.
    
    simpl.
    econstructor; simpl; eauto.
    (* This can be a static check.
       Maybe you want to go to compcert and prove this directly, 
       it will break when remove globals is introduced...
     *)
  Admitted. *)
  
  Local Ltac subst_sig:=
    match goal with
      H': existT _ _ _ = existT _ _ _ |- _ =>
      eapply Eqdep.EqdepTheory.inj_pair2 in H'; subst
    end.
  Lemma ConcurrentCompilerCorrectness:
    forall (tp:Asm.program)
      (Hextern: single_thread_simulation_proof.Asm_externals_have_events Asm_g),
      CompCert_compiler C_program = Some tp ->
      forall (static_check_mems_eq: Genv.init_mem tp = Genv.init_mem (Ctypes.program_of_program C_program )),
      forall asm_genv_safety MSS MST,
        ConcurrentCompilerCorrectness_specification
          Clight_g tp asm_genv_safety
          (Genv.init_mem (Ctypes.program_of_program C_program)) (Genv.init_mem tp)
          MSS MST.
  Proof.
    unfold ConcurrentCompilerCorrectness_specification.
    intros.
    eapply HBSimulation_transitivity; swap 1 2.
    - eapply trivial_clight_simulation; eauto.
    - hnf. repeat (unshelve econstructor).
        all: intros *; try rewrite PTree.gleaf;
          try now intros; congruence.
        (* Its werid that I need a witness to the 
           gloabals, but it's never used.
           It must be a phantom of the ay the semantics is defined.
         *)

    - eapply HBSimulation_transitivity; swap 1 2; swap 2 3.
      + eapply compile_all_threads; eauto.
      + replace (Genv.init_mem (Ctypes.program_of_program C_program))
                with (Genv.init_mem tp) by
                  (eapply initial_memories_are_equal; eauto).
        pose proof trivial_asm_simulation.
        eapply trivial_asm_simulation; eauto.
      + hnf. repeat (unshelve econstructor).
        all: intros *; try rewrite PTree.gleaf;
          try now intros; congruence.

  Qed.
  
End Concurrent_correctness.
