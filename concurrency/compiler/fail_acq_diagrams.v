

Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.Compcert_lemmas.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.synchronisation_steps_semantics.


Require Import VST.concurrency.lib.Coqlib3.

Require Import VST.concurrency.memsem_lemmas.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.C_lemmas.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.Asm_lemmas.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.compiler.concur_match.
Require Import VST.concurrency.lib.Coqlib3.

Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import bounded_maps.

(* Many auxiliary lemmas and tactics are in *)
Require Import VST.concurrency.compiler.synchronisation_lemmas.





Section FailAcqDiagrams.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  (* this modules hosts lemmas that depend on the Hybrid machine setup.*)

  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  (* Module MySimulationTactics:= SimulationTactics CC_correct Args.
  Import MySimulationTactics.
  Import MyConcurMatch. *)
  
  Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).

  (*Lemmas about the calls: *)
  Notation vone:= (Vint Int.one).
  Notation vzero:= (Vint Int.zero).


  
  Section failAcq.
    Context (hb: nat).
    (*Instantiate definitions in Concur with the current hybridbound*)
    Notation concur_match:= (concur_match hb).
    Notation match_thread:= (match_thread hb).
    Notation match_thread_source:= (match_thread_source hb).
    Notation match_thread_target:= (match_thread_target hb).
    
    Notation memcompat2:= (memcompat2 hb).
    Notation memcompat1:= (memcompat1 hb).
    Notation contains12:= (contains12 hb).
    Notation mtch_target:= (mtch_target hb).
    Notation mtch_compiled:= (mtch_compiled hb).
    Notation mtch_source:= (mtch_source hb).


    
    Lemma acquire_fail_step_diagram_self Sem tid:
      let CoreSem:= sem_coresem Sem in
      forall (m1 m2: mem)
             (SelfSim: (self_simulation (@semC Sem) CoreSem))
             (st1 : mach_state hb) (st2 : mach_state (S hb))
             (mu : meminj) i b b' ofs delt
             (Hinj_b : mu b = Some (b', delt))
             cnt1 cnt2 (* Threads are contained *)
             (CMatch: concur_match i mu st1 m1 st2 m2)
             
             (* Thread states *)
             (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
             (HState1: coerce_state_type _ sum_state1 th_state1  
                                         (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
             (HState2: coerce_state_type (@semC Sem) sum_state2 th_state2
                                         (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
             (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
             (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
             
             (* angel,lock permissions and new thread permissions *)
             (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
             (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
             (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
             (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                            Some (LOCK, (Vptr b ofs :: nil)%list))
             (Hlock_lt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1)),
        let m1_locks:= restrPermMap Hlock_lt in
        forall (Hload: Mem.load AST.Mint32 m1_locks b (unsigned ofs) = Some vzero)
          (Hrange_perm: perm_interval m1_locks b (unsigned ofs) LKSIZE Cur Readable),
          let evnt1 := Events.failacq (b, unsigned ofs) in
          exists evnt2,
            inject_sync_event mu evnt1 evnt2 /\
            forall perm Hlt_perm,
              let m2_any:= @restrPermMap perm m2 Hlt_perm in
              forall (Hcmpt2: mem_compatible st2 m2_any),
                syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2 m2_any evnt2.
    Proof.
      
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      
      replace (m1_locks) with lk_mem1 in * by
          (subst m1_locks lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
      clear m1_locks Hlock_lt.
      
      assert (Hmem_equiv1: mem_equiv m1 th_mem1).
      { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2 th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      assert (Heq:unsigned (add ofs (repr delt)) = unsigned ofs + delt).
      { eapply Mem.address_inject; try apply Hinj_lock; eauto.
        unfold perm_interval in Hrange_perm.
        eapply perm_range_perm; eauto.
        move Hrange_perm at bottom.
        { clear. unfold Intv.In; simpl.
          pose proof LKSIZE_pos; omega. }
      }
      
      assert (Hinj: Mem.inject mu m1 m2).
      { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
      
      remember (Events.failacq (b', unsigned ofs + delt )) as evnt2. 
      
      (* Instantiate some of the existensials *)
      exists evnt2; split. (* 3 goal*)
      
      - !goal(inject_sync_event mu evnt1 evnt2).
        subst evnt1 evnt2; do 2 econstructor; auto. assumption.
        
      - intros; !goal (syncStep _ _ _ _ _ _).
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)
        subst evnt2; rewrite <- Heq.
        
        eapply (step_acqfail); eauto; try reflexivity; try solve[apply CMatch].
        
        (* 8 goals produced. *)
        + !goal (semantics.at_external _ _ _ = Some (LOCK, _)).
          
          pose proof (cur_equiv_restr_mem_equiv
                        _ _ (fst (ssrfun.pair_of_and (Hcmpt0 tid cnt2)))).
          erewrite <- coerse_state_atx; eauto.
          (* The following proof comes from acquire_step_diagram ...
               Should probably be turned into a lemm
           *)
          
          { clean_proofs.
            eapply ssim_preserves_atx in Hat_external.
            2: { inversion Amatch; constructor; eauto. }
            destruct Hat_external as (args' & Hat_external2 & val_inj).
            replace ( Vptr b' (add ofs (repr delt)) :: nil) with args'.
            
            simpl; unfold at_external_sum, sum_func.
            subst CoreSem; rewrite <- (restr_proof_irr (proj1 (Hcmpt0 tid cnt2))).
            rewrite <- Hat_external2; simpl.
            clear - Hthread_mem2 HState2 Hthread_mem1.
            
            inversion HState2; subst.
            - !goal ( Clight.at_external _ = _ _ m2).
              replace c with th_state2; auto.
              2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
              (* why can't I rewrite?*)
              
              eapply C_at_external_proper; auto.
              etransitivity.
              
              + symmetry; unshelve eapply restrPermMap_idempotent.
                rewrite Hthread_mem2; exact (cur_lt_max _).
              + rewrite RPM.
                eapply cur_equiv_restr_mem_equiv.
                eassumption.
            - !goal ( Asm.at_external _ _ = _ _ m2).
              replace c with th_state2; auto.
              2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
              simpl.
              (* why can't I rewrite?*)
              eapply Asm_at_external_proper; auto.
              etransitivity.
              
              + symmetry; unshelve eapply restrPermMap_idempotent.
                rewrite Hthread_mem2; exact (cur_lt_max _).
                
              + rewrite RPM.
                eapply cur_equiv_restr_mem_equiv.
                eassumption.
            - clear - val_inj Hinj_b.
              inversion val_inj; subst.
              inversion H3; f_equal.
              inversion H1; subst.
              rewrite Hinj_b in H4; inversion H4; subst.
              reflexivity. }
          
        + !goal(Mem.range_perm _ _ _ _ _ _).
          
          unshelve erewrite <- restrPermMap_idempotent_eq.
          { eapply Hcmpt2. }
          match goal with |- Mem.range_perm ?m _ ?ofs2 _ _ _ =>
                          replace m with lk_mem2;
                            replace ofs2 with (unsigned ofs + delt)
          end.
          replace (unsigned ofs + delt + LKSIZE)
            with (unsigned ofs + LKSIZE + delt) by omega.
          eapply Mem.range_perm_inj; eauto; eapply Hinj_lock.
          subst lk_mem2; simpl; repeat f_equal.
          eapply Axioms.proof_irr.
          

        + !context_goal Mem.load.
          unshelve erewrite <- restrPermMap_idempotent_eq.
          eapply Hcmpt2.
          eapply Mem.load_inject in Hload; eauto.
          destruct Hload as (?&Hload2&Hinj_v).
          inv Hinj_v.
          replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
          eassumption.
    Qed.  (* acquire_fail_step_diagram_self *)



    (** *Compiled diagram *)
    
    Lemma acquire_fail_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (m1 m1' : mem) (cd : compiler_index)
        mu st1 st2 (m2' : mem) Hcnt1 Hcnt2
        (Hsame_sch: same_cnt hb st1 st2 Hcnt1 Hcnt2)
        b1 ofs (code1 : semC)  (code2 : Asm.state)
        (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
        (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
        (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
        (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
        (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
        (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                         Some (LOCK, (Vptr b1 ofs :: nil)%list))
        (Hlock_lt: permMapLt (lock_perms _ _ Hcnt1) (getMaxPerm m1')),
        let m1_locks:= restrPermMap Hlock_lt in
        forall (Hload: Mem.load AST.Mint32 m1_locks b1 (unsigned ofs) = Some vzero)
          (Hrange_perm: perm_interval m1_locks b1 (unsigned ofs) LKSIZE Cur Readable)
          (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        exists evnt2,
        forall any_perm Hlt,
          let m2_any:= @restrPermMap any_perm m2' Hlt in
              forall (Hcmpt2: mem_compatible st2 m2_any),
          let evnt:= (Events.failacq (b1, unsigned ofs)) in
          concur_match (Some cd) mu st1 m1' st2 m2_any /\
          inject_sync_event mu evnt evnt2 /\
          forall (Hcmpt2: mem_compatible st2 m2_any),  
            syncStep(Sem:=HybridSem (Some (S hb)))
                    true Hcnt2 Hcmpt2 st2 m2_any evnt2.
    Proof.
      intros.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      clean_proofs.

      left_diagram.

      assert (Hmax_locks: Max_equiv m1_locks m1') by
           eapply restr_Max_equiv.
        
      remember (unsigned (add ofs (repr delta))) as ofs2.
      assert (Heq: ofs2 = unsigned ofs + delta ).
      { subst ofs2. solve_unsigned. }
        
      (* HERE *)
      econstructor; intros.
      repeat weak_split.
      - subst m2_any. eapply concur_match_perm_restrict2; eauto.
      - do 2 econstructor; eauto.
      - intros.
        !context_goal @syncStep.
        subst ofs2. 
        eapply step_acqfail; try reflexivity; eauto.
        + !goal (invariant st2).
          eapply CMatch.
        + simpl. rewrite <- Hat_external2'.
          simpl. repeat f_equal.
          clean_proofs. subst m2_any.
          erewrite <- restrPermMap_idempotent_eq.
          eapply self_restre_eq; assumption.
        + simpl.
          move Hrange_perm at bottom.
          clean_proofs. subst m2_any. 
          unfold unsigned in Heq.
          erewrite <- restrPermMap_idempotent_eq, Heq.
          replace (intval ofs + delta + LKSIZE) with (intval ofs + LKSIZE + delta) by
              omega.
          eapply Mem.range_perm_inject; eauto.
          subst m1_locks.
          eapply CMatch.
        + subst m2_any; simpl.
          unfold unsigned in Heq.
          unshelve erewrite <- restrPermMap_idempotent_eq, Heq; eauto.
          exploit Mem.load_inject; try eapply Hload; eauto.
          subst m1_locks; eapply CMatch.
          intros; normal_hyp; eauto.
          inv H0; eauto. rewrite <- H.
          simpl; f_equal; eauto.

      Unshelve.
      all: eauto.
    Qed.
    
    Lemma acquire_fail_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem(Some hb))) in 
      forall (m1 m2: mem) tid mu cd b ofs c
        (st1 : ThreadPool (Some hb)) cnt1
        (st2 : ThreadPool (Some (S hb))) cnt2
        (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        (Hat_external: semantics.at_external hybrid_sem c m1  =
                       Some (LOCK, (Vptr b ofs :: nil)%list))
        (Hlock_lt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1)),
        let m1_locks:= restrPermMap Hlock_lt in
        forall (Hload: Mem.load AST.Mint32 m1_locks b (unsigned ofs) = Some vzero)
          (Hrange_perm: perm_interval m1_locks b (unsigned ofs) LKSIZE Cur Readable)
          (Hcode: getThreadC cnt1 = Kblocked c),
        forall perm Hlt_perm,
          let any_mem:= @restrPermMap perm m2 Hlt_perm in
          exists evnt2,
            concur_match cd mu st1 m1 st2 any_mem /\
            let evnt:= (Events.failacq (b, unsigned ofs)) in
            inject_sync_event mu evnt evnt2 /\
            forall (Hcmpt2: mem_compatible st2 any_mem),  
              syncStep(Sem:=HybridSem (Some (S hb)))
                      true cnt2 Hcmpt2 st2 any_mem evnt2.
    Proof.
      intros; simpl in *.
      inv Hsame_sch.
      pose proof (memcompat1 CMatch) as Hcmpt1.
      get_mem_compatible.
      get_thread_mems.
      pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp thread_compat1) Hthread_mem1) as
          Hmem_equiv.
      
      (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
      destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].
      
      - (* (tid < hb) *)
        pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
          as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H3. (* Asm_match *)
        
        (*Destruct the values of the self simulation *)
        pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
        assert (Hinj':=Hinj).
        pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
        eapply sim_atx in Hinj'; eauto.
        2: { (*at_external*)
          erewrite restr_proof_irr.
          rewrite Hmem_equiv; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

        assert (Hth_lt1: permMapLt (thread_perms tid st1 cnt1) (getMaxPerm m1))
          by eapply CMatch.
        assert (Hth_lt2: permMapLt (thread_perms tid st2 cnt2) (getMaxPerm m2))
          by eapply CMatch.
        remember (restrPermMap Hth_lt1) as m1_thread.
        remember (restrPermMap Hth_lt2) as m2_thread.
        
        unshelve (edestruct (acquire_fail_step_diagram_self
                               AsmSem tid m1_thread m2_thread) as
                     (e' & Htrace_inj & external_step);
                  eauto; try eapply Hlock_lt;
                  first[ eassumption|
                         econstructor; eassumption|
                         solve[econstructor; eauto] |
                         eauto]); subst m1_thread m2_thread.
        1,2,3: shelve.
        + rewrite getMax_restr; assumption.
        + eapply concur_match_perm_restrict; eassumption.
        + rewrite getCur_restr; reflexivity.
        + rewrite getCur_restr; clean_proofs; reflexivity.
        + (* match_self*)
          inv H3; econstructor; eauto.
          clean_proofs; assumption.
        + simpl. !goal(Asm.at_external _ _ = _).
          instantiate(1:=ofs).
          pose proof (Asm_at_external_proper
                        Asm_g code1 _ eq_refl
                        (restrPermMap Hth_lt1) m1).
          unfold Asm_g in *. simpl in H; rewrite H; eauto.
          eapply cur_equiv_restr_mem_equiv; assumption.
        + rewrite <- restrPermMap_idempotent; eauto.
        + unfold perm_interval.
          rewrite <- restrPermMap_idempotent; eauto.
        + eexists.
          repeat (weak_split eauto).
          * rewrite (mem_is_restr_eq m1); subst any_mem.
            eapply concur_match_perm_restrict; eauto.
          * simpl in external_step.
            clean_proofs. simpl. subst any_mem.

            specialize (external_step perm ).
            unshelve (exploit external_step); intros.
            -- do 2 apply mem_compat_restrPermMap.
               eapply CMatch.
            -- rewrite getMax_restr. assumption.
            -- revert H; clear. clean_proofs.
               pose proof (restrPermMap_idempotent_eq _ Hlt_perm abs_proof0) as Heq.
               dependent_rewrite Heq.
               clean_proofs; auto.


      - (* tid = hb *)
        subst tid. 
        (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
        rename m1 into m1'.
        rename m2 into m2'.
        
        (* Retrieve the match relation for this thread *)
        pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                    (reflexivity)
                      cnt1 (contains12 CMatch cnt1)) as Hmatch.
        exploit_match ltac:(apply CMatch).
        
        rename H5 into Hinterference1.
        rename H7 into Hinterference2.
        rename H1 into Hcomp_match.
        rename H2 into Hstrict_evolution.
        
        rename cnt1 into Hcnt1.
        (*rename Hlt' into Hlt_setbBlock1. *)
        rename Hat_external into Hat_external1.
        rename b into b1.
        
        rename Hload into Hload1.
        
        symmetry in H0; clean_proofs.
        exploit (acquire_fail_step_diagram_compiled m1 m1' ) ;
          try eapply CMatch; eauto;
            try reflexivity.
        + econstructor; eassumption.
        + econstructor; eauto.
          * !goal(mem_interference m1 lev1 m1'). 
            rewrite self_restre_eq in Hinterference1; eauto.
          * !goal(mem_interference m2 lev2 m2').
            rewrite self_restre_eq in Hinterference2; eauto.
        + clear - CMatch Hcnt1.
          intros (?&?&?&?).
          { apply mem_compat_restrPermMap; apply CMatch. }
          
          eexists; eauto.
          (* repeat weak_split eauto.
          * rewrite (mem_is_restr_eq m1'); subst any_mem.
            eapply concur_match_perm_restrict; eauto. *)
            
      - (* hb < tid *)
        pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
          as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H3. (* Asm_match *)
        
        (*Destruct the values of the self simulation *)
        pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
        assert (Hinj':=Hinj).
        pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
        eapply sim_atx in Hinj'; eauto.
        2: { (*at_external*)
          erewrite restr_proof_irr.
          rewrite Hmem_equiv; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

        assert (Hth_lt1: permMapLt (thread_perms tid st1 cnt1) (getMaxPerm m1))
          by eapply CMatch.
        assert (Hth_lt2: permMapLt (thread_perms tid st2 cnt2) (getMaxPerm m2))
          by eapply CMatch.
        remember (restrPermMap Hth_lt1) as m1_thread.
        remember (restrPermMap Hth_lt2) as m2_thread.
        
        unshelve (edestruct (acquire_fail_step_diagram_self
                               CSem tid m1_thread m2_thread) as
                     (e' & Htrace_inj & external_step);
                  eauto; try eapply Hlock_lt;
                  first[ eassumption|
                         econstructor; eassumption|
                         solve[econstructor; eauto] |
                         eauto]); subst m1_thread m2_thread.
        1,2,3: shelve.
        + rewrite getMax_restr; assumption.
        + eapply concur_match_perm_restrict; eassumption.
        + rewrite getCur_restr; reflexivity.
        + rewrite getCur_restr; clean_proofs; reflexivity.
        + (* match_self*)
          inv H3; econstructor; eauto.
          clean_proofs; assumption.
          
        + simpl. !goal(Clight.at_external _ = _).
          instantiate(1:=ofs).
          pose proof (C_at_external_proper
                        Clight_g code1 _ eq_refl
                        (restrPermMap Hth_lt1) m1).
          unfold Clight_g in *. simpl in H; rewrite H; eauto.
          eapply cur_equiv_restr_mem_equiv; assumption.
        + rewrite <- restrPermMap_idempotent; eauto.
        + unfold perm_interval.
          rewrite <- restrPermMap_idempotent; eauto.
        + eexists.
          repeat (weak_split eauto).
          * rewrite (mem_is_restr_eq m1); subst any_mem.
            eapply concur_match_perm_restrict; eauto.
          * simpl in external_step.
            clean_proofs. simpl. subst any_mem.

            specialize (external_step perm ).
            unshelve (exploit external_step); intros.
            -- do 2 apply mem_compat_restrPermMap.
               eapply CMatch.
            -- rewrite getMax_restr. assumption.
            -- revert H; clear. clean_proofs.
               pose proof (restrPermMap_idempotent_eq _ Hlt_perm abs_proof0) as Heq.
               dependent_rewrite Heq.
               clean_proofs; auto.
               
               Unshelve.
               eapply CMatch.
               eapply CMatch. 
    Qed.    
   End failAcq.
End FailAcqDiagrams.