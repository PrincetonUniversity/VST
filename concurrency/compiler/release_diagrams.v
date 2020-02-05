

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





Section ReleaseDiagrams.
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
  
    Lemma at_external_sum_sem:
      forall Sem,
        let CoreSem := sem_coresem Sem in
        forall th_state2 sum_state2 m1 m2
               (st1:mach_state hb)
               (st2:mach_state (S hb)) tid cnt1 cnt2 args'
               (HState2 : coerce_state_type semC sum_state2 th_state2 
                                            (CSem, Clight.state) (AsmSem, Asm.state) 
                                            (Sem, semC))
               (Hthread_mem1 : access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
               (Hthread_mem2 : access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
               (thread_compat2 : thread_compat st2 tid cnt2 m2)
               (abs_proof : permMapLt (fst (getThreadR cnt2)) (getMaxPerm m2))
               (Hat_external2 : at_external CoreSem th_state2 m2 = Some (UNLOCK, args')), 
          at_external
            (sem_coresem (HybridSem (Some (S hb))))
            sum_state2 (restrPermMap abs_proof) = Some (UNLOCK, args').
    Proof.
      intros.
      
      simpl; unfold at_external_sum, sum_func.
      rewrite <- (restr_proof_irr (th_comp thread_compat2)).
      rewrite <- Hat_external2; simpl.
      
      inversion HState2; subst.
      - !goal ( Clight.at_external _ = _ _ m2).
        replace c with th_state2; auto.
        2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
        eapply C_at_external_proper; auto.
        eapply cur_equiv_restr_mem_equiv; auto.
      - !goal ( Asm.at_external _ _ = _ _ m2).
        replace c with th_state2; auto.
        2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
        simpl.
        (* why can't I rewrite?*)
        eapply Asm_at_external_proper; auto.
        eapply cur_equiv_restr_mem_equiv; auto.
    Qed.

    Lemma release_step_diagram_self Sem tid:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
        (st1 : mach_state hb) (st2 : mach_state (S hb))
        (m1 m1' m2 : mem) (mu : meminj) i b b' ofs delt
        (Htid_neq: tid <> hb)
        (Hinj_b : mu b = Some (b', delt))
        cnt1 cnt2 (* Threads are contained *)
        (CMatch: concur_match i mu st1 m1 st2 m2)

        (* Thread states *)
        (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
        (HState1: coerce_state_type _ sum_state1 th_state1  
                                    (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
        (HState2: coerce_state_type _ sum_state2 th_state2
                                    (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
        (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
        (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
        
        (* angel, lock permissions and new thread permissions *)
        (angel: virtue) empty_perms
        (Hempty_map: empty_doublemap empty_perms)
        (HisLock: lockRes st1 (b, Integers.Ptrofs.unsigned ofs) = Some empty_perms)
        (Hangel_bound: sub_map_virtue angel (getMaxPerm m1))
        (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2)),
        let Hcmpt2:= memcompat2 CMatch in
        let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
        forall (Hjoin_angel: permMapJoin_pair newThreadPerm1 (virtueLP angel) (getThreadR cnt1))
               (Hlock_update_mem_strict_load: lock_update_mem_strict_load b (unsigned ofs)
                                                                          (snd (getThreadR cnt1))
                                                                          m1 m1' vzero vone)
               (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
               (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                              Some (UNLOCK, (Vptr b ofs :: nil)%list)),
          let event1 := build_release_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
          exists event2 (m2' : mem),
            match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
            inject_sync_event mu event1 event2 /\
            let angel2:= inject_virtue m2 mu angel in
            let st2':= fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef)
                                      angel2 (b', unsigned (add ofs (repr delt))) in
            syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2 /\
            let st1':= fullThUpd_comp st1 tid cnt1 (Kresume sum_state1 Vundef)
                                      angel (b, unsigned ofs) in
            concur_match i mu st1' m1' st2' m2'.
    Proof.
      intros; simpl in *.

      
      (*Add all the memories and theeir relations *)
      
      get_mem_compatible.
      get_thread_mems.
      
      (* Build the new angel *)
      remember (inject_virtue m2 mu angel) as angel2.
      remember (virtueThread angel2) as angelThread2.
      remember (virtueLP angel2) as angelLP2.

      (* Inject the loads/stores/mem_range*)
      unshelve (exploit lock_update_mem_strict_load_inject;
                eauto; try (eapply CMatch; eauto)); eauto;
        intros (m2'&Hlock_update_mem_strict_load2&Hinj2).

      repeat pose_max_equiv.
      rename Hmax_eq0 into Hmax_equiv.
      rename Hmax_eq into Hmax_equiv2.
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      exploit address_inj_lock_update_load; eauto; intros Heq.
      
      remember (build_release_event (b', unsigned ofs + delt ) (fst (virtueThread angel2)) m2')
        as event2. 
      
      set (newThreadPerm2 := computeMap_pair (getThreadR cnt2) (virtueThread angel2)).

      assert (Hjoin_angel2: permMapJoin_pair newThreadPerm2
                                             (virtueLP angel2)
                                             (getThreadR cnt2)).
      { subst. eapply permMapJoin_pair_inject_rel; eauto;
                 try eapply full_injects_angel;
                 try eapply CMatch; assumption. }

      assert (Hlt11': permMapLt_pair (newThreadPerm1) (getMaxPerm m1')).
      { eapply permMapLt_pair_trans211.
        - eapply permMapJoin_lt_pair1; eapply Hjoin_angel.
        - eapply permMapLt_pair_trans211; eauto.
          + instantiate (1:= (getMaxPerm m1, getMaxPerm m1) ).
            split; simpl; eauto.
          + solve_pair. intros ??. rewrite Hmax_equiv. apply po_refl. }
      destruct Hlt11' as [Hlt11' Hlt12']. 
      
      assert (Hlt22': permMapLt_pair (newThreadPerm2) (getMaxPerm m2')).
      { eapply permMapLt_pair_trans211.
        - eapply permMapJoin_lt_pair1; eapply Hjoin_angel2.
        - eapply permMapLt_pair_trans211; eauto.
          + instantiate (1:= (getMaxPerm m2, getMaxPerm m2) ).
            split; simpl; eauto.
          + solve_pair. intros ??. rewrite Hmax_equiv2. apply po_refl. }
      destruct Hlt22' as [Hlt21' Hlt22'].

      try forward_state_cmpt_all; repeat forward_mem_cmpt_all.
      set (virtueLP1 :=   virtueLP angel).
      set (virtueLP2 :=   virtueLP_inject m2 mu virtueLP1).
      set (ofs2      :=   add ofs (repr delt)).
      set (st2':=(updLockSet
                    (updThread cnt2 (Kresume sum_state2 Vundef) newThreadPerm2)
                    (b', unsigned ofs2) virtueLP2)).
      remember (fullThUpd_comp
                  st1 tid cnt1 (Kresume sum_state1 Vundef) angel
                  (b, unsigned ofs)) as st1'.
      forward_state_cmpt_all.
      subst st1' st2' virtueLP1 virtueLP2 .


      assert (Hfull:Events.injection_full mu m1) by apply CMatch.
      assert (Hinj': Mem.inject mu m1 m2).
      { rewrite (mem_is_restr_eq m1), (mem_is_restr_eq m2).
        erewrite (restre_equiv_eq _ _ m1); try (symmetry; eauto).
        erewrite (restre_equiv_eq _ _ m2); try (symmetry; eauto).
        eapply CMatch. }
      
      assert (HHlock1:mi_memval_perm mu (fst newThreadPerm1)
                                     (Mem.mem_contents th_mem1)
                                     (Mem.mem_contents th_mem2)).
      { eapply mi_memval_perm_computeMap_Lt; auto.
        eapply mi_inj_mi_memval_perm, Hinj_th.
        subst th_mem1; simpl; rewrite getCur_restr.
        eapply permMapJoin_lt, Hjoin_angel. }
      assert (HHlock2:mi_memval_perm mu (snd newThreadPerm1)
                                     (Mem.mem_contents lk_mem1)
                                     (Mem.mem_contents lk_mem2)).
      { eapply mi_memval_perm_computeMap_Lt; auto.
        eapply mi_inj_mi_memval_perm, Hinj_lock.
        subst lk_mem1; simpl; rewrite getCur_restr.
        eapply permMapJoin_lt, Hjoin_angel. }
      
      assert (Hmemval2':
                mi_memval_perm mu (snd newThreadPerm1)
                               (Mem.mem_contents m1')
                               (Mem.mem_contents m2')).
      {
        inversion Hlock_update_mem_strict_load.
        inversion Hlock_update_mem_strict_load2.
        
        

        assert(Hmxeqv_lk1: Max_equiv lk_mem1 m1).
        { subst lk_mem1; simpl.
          apply restr_Max_equiv. }
        assert (Hwritable_lock1':=Hwritable_lock1).
        (*rewrite <- Hmxeqv_lk1 in Hwritable_lock1'. *)
        
        assert(Hmxeqv_lk2: Max_equiv lk_mem2 m2).
        { subst lk_mem2; simpl.
          eapply restr_Max_equiv. }
        assert (Hwritable_lock0':=Hwritable_lock0).
        (*rewrite <- Hmxeqv_lk2 in Hwritable_lock0'.*)
        

        eapply mi_memval_perm_store
          with (Hwritable_lock0:=Hwritable_lock0')
               (Hwritable_lock1:=Hwritable_lock1')
        ; try eapply Haccess;
          try eapply HHlock; eauto.
        1:{ eapply permMapLt_trans.
            destruct Hjoin_angel as [_ HHjoin2].
            simpl in HHjoin2. move HHjoin2 at bottom.
            eapply permMapJoin_lt; eauto.
            
            eassumption. }
        3:{ rewrite <- Hstore0. f_equal.
            subst m_writable_lock_0.
            apply restr_proof_irr. }
        2:{ rewrite <- Hstore. f_equal.
            subst m_writable_lock_1.
            apply restr_proof_irr. }
        2:{ replace (Mem.mem_contents m1) with
                (Mem.mem_contents lk_mem1) by
              (subst lk_mem1; reflexivity).
            replace (Mem.mem_contents m2) with
                (Mem.mem_contents lk_mem2) by
                (subst lk_mem2; reflexivity).
            eapply mi_memval_perm_computeMap_Lt.
            eapply mi_inj_mi_memval_perm, Hinj_lock.
            move Hjoin_angel at bottom.
            destruct Hjoin_angel as [HH1 HH2].
            subst lk_mem1; simpl.
            rewrite getCur_restr.
            eapply permMapJoin_lt in HH2.
            eauto. }
        apply restr_Max_equiv. }
      
      assert (Hmi_perm_perm1:
                mi_perm_perm mu (fst newThreadPerm1) (fst newThreadPerm2)).
      { unfold newThreadPerm1, newThreadPerm2; simpl.
        eapply computeMap_mi_perm_perm_perfect.
        - eapply maps_no_overlap_Lt; eauto.
          2: eapply Hangel_bound.
          eapply no_overlap_mem_perm.
          eapply Hinj'.
        - intros ? **. 
          exploit mi_inj_mi_perm_perm_Cur; try eapply Hinj_th; eauto.
          rewrite Heqth_mem1. unfold thread_mems; simpl.
          rewrite getCur_restr.
          eauto.
          rewrite Heqth_mem2. unfold thread_mems; simpl.
          rewrite getCur_restr; auto.
        - subst angel2;
            eapply inject_perm_perfect_image_dmap; eauto.
          + eapply sub_map_implication_dmap; eauto.
            eapply Hangel_bound.
          + eapply full_inject_dmap; eauto.
            -- eapply join_dmap_valid, Hangel_bound.
      }
      assert (Hmi_perm_perm2:
                mi_perm_perm mu (snd newThreadPerm1) (snd newThreadPerm2)).
      { unfold newThreadPerm1, newThreadPerm2; simpl.
        eapply computeMap_mi_perm_perm_perfect.
        - eapply maps_no_overlap_Lt; eauto.
          2: eapply Hangel_bound.
          eapply no_overlap_mem_perm.
          eapply Hinj'.
        - intros ? **. 
          exploit mi_inj_mi_perm_perm_Cur; try eapply Hinj_lock; eauto.
          rewrite Heqlk_mem1. unfold thread_mems; simpl.
          rewrite getCur_restr.
          eauto.
          rewrite Heqlk_mem2. unfold thread_mems; simpl.
          rewrite getCur_restr; auto.
        - subst angel2;
            eapply inject_perm_perfect_image_dmap; eauto.
          + eapply sub_map_implication_dmap; eauto.
            eapply Hangel_bound.
          + eapply full_inject_dmap; eauto.
            -- eapply join_dmap_valid, Hangel_bound.
      }
      
      
      assert (Hmemval1':
                mi_memval_perm mu (fst newThreadPerm1)
                               (Mem.mem_contents m1')
                               (Mem.mem_contents m2')).
      { inversion Hlock_update_mem_strict_load.
        inversion Hlock_update_mem_strict_load2.
        
        
        assert(Hmxeqv_th1: Max_equiv th_mem1 m1).
        { subst th_mem1; simpl.
          apply restr_Max_equiv. }
        assert (Hwritable_lock1':=Hwritable_lock1).
        (*rewrite <- Hmxeqv_lk1 in Hwritable_lock1'. *)
        
        assert(Hmxeqv_lk2: Max_equiv th_mem2 m2).
        { subst th_mem2; simpl.
          eapply restr_Max_equiv. }
        assert (Hwritable_lock0':=Hwritable_lock0).
        (*rewrite <- Hmxeqv_lk2 in Hwritable_lock0'.*)
        
        eapply mi_memval_perm_store
          with (Hwritable_lock0:=Hwritable_lock0')
               (Hwritable_lock1:=Hwritable_lock1')
        ; try eapply Haccess;
          try eapply HHlock; debug eauto.
        1:{ eapply permMapLt_trans.
            destruct Hjoin_angel as [HHjoin1 _].
            simpl in HHjoin1. move HHjoin1 at bottom.
            eapply permMapJoin_lt; eauto.
            eassumption.  }
        3:{ rewrite <- Hstore0. f_equal.
            subst m_writable_lock_0.
            apply restr_proof_irr. }
        2:{ rewrite <- Hstore. f_equal.
            subst m_writable_lock_1.
            apply restr_proof_irr. }
        2:{ replace (Mem.mem_contents m1) with
                (Mem.mem_contents th_mem1) by
              (subst th_mem1; reflexivity).
            replace (Mem.mem_contents m2) with
                (Mem.mem_contents th_mem2) by
                (subst th_mem2; reflexivity).
            eapply mi_memval_perm_computeMap_Lt.
            eapply mi_inj_mi_memval_perm, Hinj_th.
            move Hjoin_angel at bottom.
            destruct Hjoin_angel as [HH1 HH2].
            subst th_mem1; simpl.
            rewrite getCur_restr.
            eapply permMapJoin_lt in HH1.
            eauto. }
        apply restr_Max_equiv. }
      
      
      assert (Hmi_perm_inv_perm2: (mi_perm_inv_perm mu (snd newThreadPerm1)
                                                    (snd newThreadPerm2) m1')).
      {

        subst_set; simpl.
        subst angel2; simpl; erewrite tree_map_inject_restr.
        eapply mi_perm_inv_perm_compute with (m1:=lk_mem1).
        -- subst lk_mem1; simpl. symmetry; eapply getCur_restr.
        -- rewrite getCur_restr. reflexivity.
        -- replace (getMaxPerm lk_mem1) with (getMaxPerm m1).
           eapply Hangel_bound.
           subst lk_mem1; simpl. rewrite restr_Max_eq; reflexivity.
        -- subst lk_mem2. eapply Hinj_lock.
        -- subst lk_mem1; simpl. unfold lock_comp; simpl.
           etransitivity; eauto. eapply restr_Max_equiv.
      }
      
      assert (Hmi_perm_inv_perm1: (mi_perm_inv_perm mu (fst newThreadPerm1)
                                                    (fst newThreadPerm2) m1')).
      {

        subst_set; simpl.
        subst angel2; simpl; erewrite tree_map_inject_restr.
        eapply mi_perm_inv_perm_compute with (m1:=th_mem1).
        -- subst th_mem1; simpl. symmetry; eapply getCur_restr.
        -- rewrite getCur_restr. reflexivity.
        -- replace (getMaxPerm th_mem1) with (getMaxPerm m1).
           eapply Hangel_bound.
           subst th_mem1; simpl. rewrite restr_Max_eq; reflexivity.
        -- subst th_mem2. eapply Hinj_th.
        -- subst th_mem1; simpl. unfold lock_comp; simpl.
           etransitivity; eauto. eapply restr_Max_equiv.
      }
      assert (Hinj2': Mem.inject mu (restrPermMap Hlt12') (restrPermMap Hlt22'))
        by (apply inject_restr; eauto).
      assert (Hinj1': Mem.inject mu (restrPermMap Hlt11') (restrPermMap Hlt21'))
        by (apply inject_restr; debug eauto). 
      
      






      
      
      (** *Instantiate some of the existensials *)
      exists event2; exists m2'.
      repeat weak_split. (* 4 goal*)
      
      - !goal( match_self _ _ _ _ _ _). 
        inversion Amatch; constructor; eassumption.
        
      - !goal (inject_sync_event mu event1 event2).
        subst event2; do 2 econstructor; auto. assumption.
        
      - !goal (syncStep _ _ _ _ _ _).
        
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)

        subst event2 ; unfold build_release_event.
        rewrite <-  Heq.

        (*Prove that the new ThreadVirtue Joins in the right way:
                old_thread "+" delta_map = new_thread.
         *)
        
        rewrite <- Heq in Hlock_update_mem_strict_load2.
        inversion Hlock_update_mem_strict_load2 as [lock_mem_lt2'
                                                      vload vstore
                                                      Hwritable_lock2 
                                                      lock_mem2 m_writable_lock_2
                                                      lock_mem_lt2 
                                                      Hload2 
                                                      Hstore2];
          subst vload vstore.
        
        exploit INJ_lock_permissions_image; eauto;
          intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2).
        eapply step_release with
            (b0:= b')(m':=m2')
            (virtueThread:=(virtueThread angel2))
            (virtueLP:=angelLP2)
            (rmap:=pmap)
        ; eauto; try reflexivity.
        
        (* 9 goals produced. *)
        
        + subst angelThread2 angel2 lk_mem1 lk_mem2.
          eapply inject_virtue_sub_map_pair; eauto.
          * apply Hinj_lock.
          * apply Hangel_bound.
            
        + unfold HybridMachineSig.isCoarse,
          HybridMachineSig.HybridCoarseMachine.scheduler.
          destruct Hangel_bound as (?&(?&?&?&?)).
          subst; eapply (proj1 (Logic.and_assoc _ _ _)).
          split.
          * unfold virtueLP_inject,
            map_empty_def, inject_access_map; auto.
          * split; eapply inject_virtue_sub_map; eauto;
              try eapply Hinj_lock; eauto.
        + eapply CMatch.
        + !goal (semantics.at_external _ _ _ = Some (UNLOCK, _)).
          { eapply at_external_sum_sem; eauto.
            eapply ssim_preserves_atx in Hat_external.
            - destruct Hat_external as (args' & Hat_external2 & val_inj).
              subst CoreSem; rewrite Hat_external2; repeat f_equal.
              inversion val_inj; subst.
              inversion H3; inversion H1; subst.
              rewrite Hinj_b in H4; inversion H4; subst.
              reflexivity.
            - inversion Amatch. constructor; eauto. }
          
        + !goal (lockRes _ (b',_) = Some _).
          simpl in *; rewrite <- Hpmap; repeat f_equal.
          solve_unsigned.
        + (* new lock is empty *)
          intros *. rewrite <- Hpmap_equiv1, <- Hpmap_equiv2.
          eapply empty_map_useful.
          eapply inject_empty_maps; assumption.
          
        + (* Claims the transfered resources join in the appropriate way *)
          subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.
          
        + (* Claims the transfered resources join in the appropriate way *)
          subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.

        + subst; unfold fullThUpd_comp, fullThreadUpdate; auto.
          
      - !goal(concur_match _ _ _ _ _ _).
        clean_proofs.
        
        
        eapply concur_match_perm_restrict1,concur_match_perm_restrict2 in CMatch.
        simpl in Hlt12'.
        eapply concur_match_update_lock with
            (Hlt1:= Hlt11')(Hlt2:= Hlt21')
            (Hlt_lock1:=Hlt12')(Hlt_lock2:=Hlt22')
        ;
        try match goal with |- context[Forall2] => idtac | _ => eauto end.
        + !context_goal lock_update_mem.
          eapply lock_update_mem_strict_load_mem_update.
          * eapply lock_update_mem_strict_load_restr.
            eapply Hlock_update_mem_strict_load.
          * eapply getCur_restr.
        + !context_goal (lock_update_mem).
          eapply lock_update_mem_strict_load_mem_update.
          * eapply lock_update_mem_strict_load_restr.
            eapply Hlock_update_mem_strict_load2.
          * eapply getCur_restr.
        + !goal (@invariant (HybridSem _) _ _).
          (* simpl in Heqst1'. *) simpl.
          eapply invariant_update_join_rel; eauto.
          3: eapply CMatch.
          simpl; rewrite HisLock. constructor.
          reflexivity.
          
        + !goal (@invariant (HybridSem _ ) _ _).
          eapply invariant_update_join_rel; eauto.
          * edestruct INJ_lock_permissions_image as (?&?&?&?); eauto.
            simpl in *; rewrite H; eauto. constructor.
          * rewrite <- Heq; reflexivity.
          * eapply CMatch.
        + !goal (mem_compatible _ m2').
          unfold fullThUpd_comp,fullThreadUpdate; eauto; simpl in *.
          subst angel2 newThreadPerm2; simpl in *; eauto.
        + !goal(perm_surj mu _ _).
          subst newThreadPerm1 newThreadPerm2; simpl.
          eapply perm_surj_compute.
          ++ eapply CMatch.
          ++ subst angel2.
             cut (perm_perfect_image_dmap_pair
                    mu (virtueThread angel)
                    (virtueThread_inject m2 mu
                                         (virtueThread angel))).
             { subst_set. intros [? HH]; simpl in HH.
               simpl. unfold tree_map_inject_over_mem.
               apply HH. }
             eapply inject_virtue_perm_perfect_image_dmap; eauto.
             move Hangel_bound at bottom.
             eapply Hangel_bound.
             eapply full_inject_dmap_pair.
             ** !goal (Events.injection_full mu _ ).
                eapply CMatch.
             ** !goal (dmap_valid_pair _ _).
                apply join_dmap_valid_pair.
                move Hangel_bound at bottom.
                rewrite getMax_restr_eq.
                eapply Hangel_bound.
                
        +  (* Proof of match goes after the comment *)
          !context_goal one_thread_match. shelve.
        + !context_goal memval_inject.
          repeat econstructor.
        + first [reflexivity|
                 (* Remove this second part*)
                 unshelve eapply Equivalence_Reflexive;
                 apply access_map_equiv_pair_alence ].
        + !goal(lock_update _ st1 _ _ _ _ _).
          simpl. econstructor; simpl.
          subst newThreadPerm1;
            unfold fullThUpd_comp, fullThreadUpdate.
          simpl. 
          reflexivity.

          
        + !goal(lock_update _ st2 _ _ _ _ _).
          econstructor;
            subst newThreadPerm2 angel2;
            unfold fullThUpd_comp, fullThreadUpdate; simpl.
          erewrite virtueLP_inject_max_eq_exteny.
          repeat f_equal; eauto; simpl.
          eapply lock_update_mem_strict_load_Max_eq; eauto.
          
          

          Unshelve.
          all: eauto.
          { eapply permMapLt_trans. eapply mem_cur_lt_max.
            intros ??; rewrite Hmax_equiv. eapply po_refl. }
          { eapply permMapLt_trans. eapply mem_cur_lt_max.
            intros ??; rewrite Hmax_equiv2. eapply po_refl. }

          { !context_goal one_thread_match. (*shelved above.*)
            destruct (lt_eq_lt_dec tid hb) as [[Htid_neq'|Htid_neq']|Htid_neq'].
            - (* (tid < hb)%nat *)
              unshelve (eapply CMatch in Htid_neq' as Hthmatch); simpl;
                eauto.
              + rewrite getMax_restr; eauto.
              + rewrite getMax_restr; eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H3; simpl in *.
                
                econstructor 2; eauto. simpl.
                do 2 econstructor; eauto.
                (*worth writting this as a lemma, 
                then use it bellow
                 *)
                
                
                econstructor; debug eauto.
                * rewrite getCur_restr.
                  eapply perm_image_injects_map.
                  eapply full_inject_map; eauto.
                  -- eapply map_valid_Lt; eauto.
                     eapply map_valid_proper.
                     reflexivity.
                     symmetry; eapply Hmax_equiv.
                     eapply max_map_valid.
                * do 2 rewrite getCur_restr.
                  eapply perm_surj_compute.
                  -- exploit @mtch_target; eauto.
                     intros HH; inv HH; inv matchmem;
                       repeat rewrite getCur_restr in *;
                       eauto.
                  -- eapply inject_perm_perfect_image_dmap; eauto.
                     eapply sub_map_implication_dmap; eauto.
                     eapply Hangel_bound.
                     eapply full_inject_dmap; eauto.
                     eapply join_dmap_valid, Hangel_bound.
                     
            - subst tid; congruence.
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch); simpl;
                eauto.
              + rewrite getMax_restr; eauto.
              + rewrite getMax_restr; eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H3; simpl in *.

                econstructor 1; eauto.
                do 2 econstructor; eauto.

                
                econstructor; debug eauto.
                * rewrite getCur_restr.
                  eapply perm_image_injects_map.
                  eapply full_inject_map; eauto.
                  -- eapply map_valid_Lt; eauto.
                     eapply map_valid_proper.
                     reflexivity.
                     symmetry; eapply Hmax_equiv.
                     eapply max_map_valid.
                * do 2 rewrite getCur_restr.
                  eapply perm_surj_compute.
                  -- exploit @mtch_source; eauto.
                     intros HH; inv HH; inv matchmem;
                       repeat rewrite getCur_restr in *;
                       eauto.
                  -- eapply inject_perm_perfect_image_dmap; eauto.
                     eapply sub_map_implication_dmap; eauto.
                     eapply Hangel_bound.
                     eapply full_inject_dmap; eauto.
                     eapply join_dmap_valid, Hangel_bound.

                     Unshelve.
                     all: simpl;eauto.
                     all: rewrite getMax_restr; eauto. }
    Qed.   (* release_step_diagram_self *)


    
    (** *Compiled diagram*)

    Lemma release_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (angel: virtue) (cd : compiler_index) mu (*tr2*)
        st1 (m1 m1' m1'' : mem) Hcnt1 st2 (m2' : mem) Hcnt2
        (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
        b1 ofs lock_map (code1 : semC)  (code2 : Asm.state)
        (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
        (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
        (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
        (Hangel_bound: sub_map_virtue angel (getMaxPerm m1'))
        (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
        (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
        (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                         Some (UNLOCK, (Vptr b1 ofs :: nil)%list))
        (Hlock_update_mem_strict_load:
           lock_update_mem_strict_load b1 (unsigned ofs)  (snd (getThreadR Hcnt1))
                                       m1' m1'' vzero vone)
        (HisLock: lockRes st1 (b1, unsigned ofs) = Some lock_map)
        (Hrmap: empty_doublemap lock_map),
        let newThreadPerm1:= (computeMap_pair (getThreadR Hcnt1) (virtueThread angel)) in
        forall (Hjoin_angel: permMapJoin_pair newThreadPerm1 (virtueLP angel) (getThreadR Hcnt1))
          (Hlt1 : permMapLt (thread_perms _ _ Hcnt1) (getMaxPerm m1'))
          (Hlt2 : permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2'))
          (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        exists evnt2 (st2' : t) (m2'' : mem),
          let evnt:= build_release_event
                       (b1, unsigned ofs) (fst (virtueThread angel)) m1'' in 
          let st1':= fullThUpd_comp
                       st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                       angel (b1, unsigned ofs)  in
          concur_match (Some cd) mu st1' m1'' st2' m2'' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:= memcompat2 CMatch in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true Hcnt2 Hcmpt2 st2' m2'' evnt2.
    Proof.
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      clean_proofs. rename abs_proof into Hcmpt2.

      (* NOTE: this proof has three diagrams:
               - Left Diagram:      Generated by interference by other threads 
               - Middle Diagram:    The compiler diagram
               - Right Diagram:     Generated by interference by other threads

              m1 -lev1-> m1' -dpm-> m1'' -lev1'-> m1'''
              |          |          |             |
              |   Left   |          |    Right    |
              |          |          |             |
              m2 -lev2-> m2' -dpm-> m2'' -lev2'-> m2'''
              !          !          !             !     
              m2 -lev2-> m21'-dpm-> m21''-lev2'-> m21'''

              TODO: the last layer might not be needed?
       *)
      
      (** * 0. Stablish facts about m2' *)

      
      (** * 1. Set all the at_externals for LEFT diagram m1 m1' m2 m2' *)
      left_diagram.
      set (virtueThread1:= virtueThread angel).
      set (virtueLP1 :=   virtueLP angel   ).
      set (virtueThread2  :=   virtueThread_inject m2' mu  virtueThread1).
      set (virtueLP2 :=   virtueLP_inject m2'' mu virtueLP1).
      set (ofs2      :=   add ofs (repr delta)).
      set (new_cur2:=(computeMap (fst (getThreadR Hcnt2)) (fst virtueThread2),
                      computeMap (snd (getThreadR Hcnt2)) (snd virtueThread2))).
      set (st2':=(updLockSet
                    (updThread Hcnt2 (Kresume (TST code2) Vundef) new_cur2)
                    (b2, unsigned ofs2) virtueLP2)).
      remember (fullThUpd_comp
                  st1 hb Hcnt1 (Kresume (SST code1) Vundef) angel
                  (b1, unsigned ofs)) as st1'.
      
      assert (Hjoin_angel2: permMapJoin_pair new_cur2 virtueLP2 (getThreadR Hcnt2)).
      { subst new_cur2.
        replace virtueLP2 with (virtueLP (inject_virtue m2' mu angel)).
        2:{ subst virtueLP2 virtueLP1; simpl.
            erewrite virtueLP_inject_max_eq_exteny; try reflexivity.
            (* this is a bit stronger than equivalence *)
            inv Hlock_update_mem_strict_load2.
            erewrite <- getMax_restr_eq.
            eapply store_max_eq; eauto. }
        
        match goal with
          |- permMapJoin_pair ?P _ _ =>
          replace P with (computeMap_pair
                            (getThreadR Hcnt2)
                            virtueThread2) by reflexivity
        end.
        
        pose proof permMapJoin_pair_inject_rel.
        simpl in H. subst virtueThread2.
        unfold virtueThread1.

        eapply permMapJoin_pair_inject_rel; eauto; 
          try eapply full_injects_angel;
          try eapply CMatch; assumption.  }
      repeat pose_max_equiv.
      forward_cmpt_all.
      rename Hcmpt_mem_fwd into Hcmpt2'.
      rename Hcmpt_mem_fwd0 into Hcmpt1'.
      
      

      (** * 4. Finally we proceed with the goal: existentials. *)
      
      eexists.
      exists st2', m2''.
      split; [|split]. 
      
      - assert (Hlt11 : permMapLt (fst newThreadPerm1) (getMaxPerm m1'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq0; solve_permMapLt. }
        assert (Hlt12 : permMapLt (snd newThreadPerm1) (getMaxPerm m1'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq0; solve_permMapLt. }
        assert (Hlt21 : permMapLt (fst new_cur2) (getMaxPerm m2'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq; solve_permMapLt. }
        assert (Hlt22 : permMapLt (snd new_cur2) (getMaxPerm m2'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq; solve_permMapLt. }
        
        cut (concur_match (Some cd) mu st1' m1'' st2' m2''); [subst st1'; auto|].
        eapply concur_match_perm_restrict1,concur_match_perm_restrict2 in CMatch.

        assert (Heq: unsigned ofs2 = unsigned ofs + delta).
        { subst ofs2. solve_unsigned. }
        
        eapply concur_match_update_lock;
          try match goal with |- context[Forall2] => idtac | _ => eauto end.
        + !context_goal lock_update_mem.
          eapply lock_update_mem_strict_load_mem_update.
          * eapply lock_update_mem_strict_load_restr.
            eapply Hlock_update_mem_strict_load1.
          * eapply getCur_restr.
        + !context_goal (lock_update_mem).
          eapply lock_update_mem_strict_load_mem_update.
          * eapply lock_update_mem_strict_load_restr.
            eapply Hlock_update_mem_strict_load2.
          * eapply getCur_restr.
        + !context_goal Mem.inject.
          rewrite RPM. 
          instantiate(2:=fst new_cur2);
            instantiate(3:=fst newThreadPerm1).
          (* . *)
          apply inject_restr; auto.
          * !goal (mi_perm_perm mu (fst newThreadPerm1) (fst new_cur2)).
            subst newThreadPerm1 new_cur2; simpl.
            
            
            eapply computeMap_mi_perm_perm_perfect.
            -- eapply maps_no_overlap_Lt; eauto.
               2: eapply Hangel_bound.
               eapply no_overlap_mem_perm.
               eapply Hinj'.
            -- unshelve eapply (mi_perm_perm_threads). 4: eauto.
               
            -- eapply inject_perm_perfect_image_dmap; eauto.
               eapply sub_map_implication_dmap.
               eapply Hangel_bound.
               eapply full_inject_dmap.
               eapply concur_match_perm_restrict'; eapply CMatch.
               eapply join_dmap_valid, Hangel_bound.
               
          * !goal (mi_memval_perm mu (fst newThreadPerm1)
                                  (Mem.mem_contents m1'')
                                  (Mem.mem_contents m2'')).
            eapply mi_memval_perm_computeMap_Lt.
            2:{ eapply permMapJoin_lt. eapply Hjoin_angel. }
            
            
            inv Hlock_update_mem_strict_load1.
            inv Hlock_update_mem_strict_load2.
            eapply mi_memval_perm_store; eauto.
            -- !goal(Max_equiv _ _).
               subst lock_mem; apply restr_Max_equiv.
            -- rewrite Hthread_mem1. apply mi_inj_mi_memval_perm. eapply Hinj'0. 
          * subst_set; simpl.
            forget (thread_perms hb st1 Hcnt1) as perm1.
            forget (thread_perms hb st2 Hcnt2) as perm2.
            clear - Hthread_mem1 Hthread_mem2 m1' Hangel_bound Hmax_eq0 Hinj'
                                 Hangel_bound m2' Hinj'0.
            
            eapply mi_perm_inv_perm_compute; eauto. apply Hangel_bound.
            
        + !goal (@invariant (HybridSem _) _ st1').
          simpl in Heqst1'.
          eapply invariant_update_join_rel; eauto.
          2: eapply CMatch.
          simpl; rewrite HisLock. constructor.
          
        + !goal (@invariant (HybridSem _ ) _ st2').
          eapply invariant_update_join_rel; eauto.
          * edestruct INJ_lock_permissions_image as (?&?&?&?); eauto.
            simpl in *; rewrite H; eauto. constructor.
          * rewrite <- Heq; reflexivity.
          * eapply CMatch.
        + !goal(perm_surj mu _ _).
          instantiate(1:=snd new_cur2); instantiate (1:=snd newThreadPerm1).
          subst newThreadPerm1 new_cur2; simpl.
          eapply perm_surj_compute.
          ++ eapply CMatch.
          ++ subst virtueThread2.
             cut (perm_perfect_image_dmap_pair
                    mu virtueThread1 (virtueThread_inject m2' mu virtueThread1)).
             { subst_set. intros [? HH]; simpl in HH.
               unfold tree_map_inject_over_mem.
               apply HH. }
             subst virtueThread1.
             eapply inject_virtue_perm_perfect_image_dmap; eauto.
             move Hangel_bound at bottom.
             eapply Hangel_bound.
             eapply full_inject_dmap_pair.
             ** !goal (Events.injection_full mu _ ).
                eapply CMatch.
             ** !goal (dmap_valid_pair _ _).
                apply join_dmap_valid_pair.
                move Hangel_bound at bottom.
                rewrite getMax_restr_eq.
                eapply Hangel_bound.
        + !goal (Mem.inject mu _ _). 
          apply inject_restr; auto.
          * !goal (mi_perm_perm mu (snd newThreadPerm1) (snd new_cur2)).
            { unfold newThreadPerm1, new_cur2; simpl.
              eapply computeMap_mi_perm_perm_perfect.
              - eapply maps_no_overlap_Lt; eauto.
                2: eapply Hangel_bound.
                eapply no_overlap_mem_perm.
                eapply Hinj'.
              - intros ? **. 
                exploit mi_inj_mi_perm_perm_Cur; try eapply Hinj_lock; eauto.
                rewrite Heqlk_mem1. unfold thread_mems; simpl.
                rewrite getCur_restr.
                eauto.
                rewrite Heqlk_mem2. unfold thread_mems; simpl.
                rewrite getCur_restr; auto.
              - eapply inject_perm_perfect_image_dmap; eauto.
                + eapply sub_map_implication_dmap; eauto.
                  eapply Hangel_bound.
                + eapply full_inject_dmap.
                  eapply CMatch.
                  eapply join_dmap_valid.
                  rewrite restr_Max_eq.
                  eapply Hangel_bound. }
          * !goal (mi_memval_perm mu (snd newThreadPerm1)
                                  (Mem.mem_contents m1'')
                                  (Mem.mem_contents m2'')).
            
            inversion Hlock_update_mem_strict_load1.
            inversion Hlock_update_mem_strict_load2.
            
            assert (HHlock:mi_memval_perm mu (snd newThreadPerm1)
                                          (Mem.mem_contents lk_mem1)
                                          (Mem.mem_contents lk_mem2)).
            { eapply mi_memval_perm_computeMap_Lt; auto.
              eapply mi_inj_mi_memval_perm, Hinj_lock.
              subst lk_mem1; simpl; rewrite getCur_restr.
              eapply permMapJoin_lt, Hjoin_angel. }
            
            (*
              eapply mi_memval_perm_computeMap_Lt.
              2:{ eapply permMapJoin_lt. eapply Hjoin_angel. } *)

            assert(Hmxeqv_lk1: Max_equiv lk_mem1 m1').
            { subst lk_mem1; simpl.
              eapply restr_Max_equiv. }
            assert (Hwritable_lock1':=Hwritable_lock1).
            (*rewrite <- Hmxeqv_lk1 in Hwritable_lock1'. *)
            
            assert(Hmxeqv_lk2: Max_equiv lk_mem2 m2').
            { subst lk_mem2; simpl.
              eapply restr_Max_equiv. }
            assert (Hwritable_lock0':=Hwritable_lock0).
            (*rewrite <- Hmxeqv_lk2 in Hwritable_lock0'.*)
            

            eapply mi_memval_perm_store
              with (Hwritable_lock0:=Hwritable_lock0')
                   (Hwritable_lock1:=Hwritable_lock1')
            ; try eapply Haccess;
              try eapply HHlock; eauto.
            1:{ eapply permMapLt_trans.
                destruct Hjoin_angel as [_ HHjoin2].
                simpl in HHjoin2. move HHjoin2 at bottom.
                eapply permMapJoin_lt; eauto.
                
                eassumption. }
            3:{ rewrite <- Hstore0. f_equal.
                subst m_writable_lock_0.
                apply restr_proof_irr. }
            2:{ rewrite <- Hstore. f_equal.
                subst m_writable_lock_1.
                apply restr_proof_irr. }
            2:{ replace (Mem.mem_contents m1') with
                    (Mem.mem_contents lk_mem1) by
                  (subst lk_mem1; reflexivity).
                replace (Mem.mem_contents m2') with
                    (Mem.mem_contents lk_mem2) by
                    (subst lk_mem2; reflexivity).
                eapply mi_memval_perm_computeMap_Lt.
                eapply mi_inj_mi_memval_perm, Hinj_lock.
                move Hjoin_angel at bottom.
                destruct Hjoin_angel as [HH1 HH2].
                subst lk_mem1; simpl.
                rewrite getCur_restr.
                eapply permMapJoin_lt in HH2.
                eauto. }
            apply restr_Max_equiv.
            
          * !goal (mi_perm_inv_perm mu (snd newThreadPerm1) (snd new_cur2) m1'').
            subst_set; simpl.
            erewrite tree_map_inject_restr.
            eapply mi_perm_inv_perm_compute with (m1:=lk_mem1).
            -- subst lk_mem1; simpl. symmetry; eapply getCur_restr.
            -- rewrite getCur_restr. reflexivity.
            -- replace (getMaxPerm lk_mem1) with (getMaxPerm m1').
               eapply Hangel_bound.
               subst lk_mem1; simpl. rewrite restr_Max_eq; reflexivity.
            -- subst lk_mem2. eapply Hinj_lock.
            -- subst lk_mem1; simpl. unfold lock_comp; simpl.
               etransitivity; eauto. eapply restr_Max_equiv.
        +  (* Proof of match goes after the comment *)
          { !context_goal one_thread_match.
            eapply build_match_compiled; auto.
            instantiate(1:= Hlt21).
            instantiate(1:=(Kresume (TST code2) Vundef)).
            instantiate(1:= Hlt11).
            instantiate(1:=(Kresume (SST code1) Vundef)).
            subst st1' st2'.
            clean_proofs.
            eapply CThread_Resume.
            intros j'' s1' m1''' m2''' lev1' lev2'.
            intros Hstrict_evolution' (*Hincr'*) Hinterference1' Hinterference2'
                   Hafter_ext.
            remember (fst virtueThread1) as dpm1.
            remember (Events.Event_acq_rel lev1 dpm1 lev1' :: nil) as rel_trace.
            Tactic Notation "dont" tactic(t):= idtac. 
            


            (** *0 . Simplifications to do outside the l emma*)

            assert (Hext_rel1': extcall_release
                                  (Genv.globalenv (Ctypes.program_of_program C_program)) 
                                  (Vptr b1 ofs :: nil) m1
                                  (Events.Event_acq_rel lev1 (fst virtueThread1) lev1' :: nil)
                                  Vundef m1''').
            { inversion Hlock_update_mem_strict_load1; subst vload vstore.
              subst rel_trace; econstructor; try eassumption.
              econstructor; eauto.
              rewrite RPM.
              subst virtueThread1.
              subst newThreadPerm1; simpl.
              unfold delta_map.
              eapply restrPermMap_access_equiv.
              erewrite Hthread_mem1. reflexivity.
            } 
            assert (Hext_rel1: Events.external_call UNLOCK
                                                    (Clight.genv_genv Clight_g)
                                                    (Vptr b1 ofs :: nil)
                                                    m1 rel_trace Vundef m1''').
            { simpl; rewrite ReleaseExists.
              subst rel_trace dpm1; eauto. }
            clear Hext_rel1'.
            
            assert (Hext_rel2: extcall_release
                                 Asm_g (Vptr b2 ofs2 :: nil) m2
                                 (Events.Event_acq_rel lev2 (fst virtueThread2) lev2' :: nil)
                                 Vundef m2''').
            { inversion Hlock_update_mem_strict_load2; subst vload vstore.
              econstructor; eauto.
              subst m_writable_lock_1; econstructor.
              2: reflexivity.
              - rewrite <- Hstore; f_equal.
                subst ofs2. 
                exploit address_inj_lock_update_load; eauto; intros Heq.
              - subst new_cur2; simpl.
                eapply restrPermMap_access_equiv.
                intros ?. extensionality ofs0.
                do 2 rewrite computeMap_get.
                match_case; auto.
                rewrite Hthread_mem2; auto.
            }
            
            assert (Hnb_eq': Mem.nextblock (restrPermMap Hlt21) =
                             Mem.nextblock m2').
            { symmetry; etransitivity; eauto. }
            
            subst rel_trace.
            eapply large_external_diagram; try reflexivity; eauto.
            - exact release_is_consec.
            - exact unlock_doesnt_return.
            - reflexivity.
            - !goal(EventsAux.inject_delta_map _ _ _ ).
              instantiate(1:=fst virtueThread2).
              subst dpm1.
              subst virtueThread2 virtueThread1; simpl.
              remember (fst (virtueThread angel)) as virt.
              eapply virtue_inject_bounded; eauto.
              + eapply Hinj'0.
              + eapply full_inject_dmap.
                * eapply CMatch.
                * eapply join_dmap_valid.
                  rewrite restr_Max_eq.
                  subst virt.
                  eapply Hangel_bound.
              + subst virt; eapply Hangel_bound.
              + eapply Hinj'0.
              + eapply Hinj'0.
            - simpl; rewrite ReleaseExists; eauto.
            - exploit (interference_consecutive_until _ _ _ Hinterference2).
              rewrite <- Hnb_eq'; simpl; auto.
            - exploit (interference_consecutive_until _ _ _ Hinterference2').
              simpl; auto.
          }
        + !context_goal memval_inject.
          repeat econstructor.
        + first [reflexivity|
                 (* Remove this second part*)
                 unshelve eapply Equivalence_Reflexive;
                 apply access_map_equiv_pair_alence ].
        + !goal(lock_update _ st1 _ _ _ _ st1').
          econstructor;
            subst st1' newThreadPerm1 virtueThread1;
            unfold fullThUpd_comp, fullThreadUpdate.
          reflexivity.
        + !goal(lock_update _ st2 _ _ _ _ st2').
          econstructor;
            subst st2' new_cur2 virtueLP2  ofs2 virtueLP1;
            unfold fullThUpd_comp, fullThreadUpdate.
          repeat f_equal.
          * f_equal.
            !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta).
            { solve_unsigned. } 
            
      - econstructor.
        + econstructor; eauto.
        + instantiate (1:= Some (build_delta_content (fst virtueThread2) m2'')).
          simpl.
          constructor. (*Notice: this is a place-holder until we define
                        delta map injections correctly.
                        *)
      (* injection of the event*)
      (* Should be obvious by construction *)
      - (* HybridMachineSig.external_step *)
        assert (Hofs2: intval ofs2 = unsigned ofs + delta).
        { subst ofs2; solve_unsigned. }
        intros.
        rewrite <- Hofs2.

        
        exploit INJ_lock_permissions_image; eauto;
          intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2).
        
        eapply step_release with
            (b:= b2)
            (virtueThread:=virtueThread2)
            (virtueLP:=virtueLP2);
          eauto; try reflexivity;
            try unfold HybridMachineSig.isCoarse,
            HybridMachineSig.HybridCoarseMachine.scheduler.
        rename m2' into MMM.
        rename m2 into MMM2.
        
        + (* sub_map *)
          
          subst virtueThread2.
          unfold virtueThread_inject.
          destruct (virtueThread angel) as (virtue11, virtue12)
                                             eqn:HeqvirtueThread1.
          cbv iota beta delta[fst] in *.
          destruct Hangel_bound as [Hbounded HboundedLP].
          destruct Hbounded as [Hbound1 Hbound2].
          split.
          -- eapply inject_virtue_sub_map.
             eapply CMatch.
             inversion HeqvirtueThread1.
             destruct angel; simpl in H0.
             subst virtueThread.
             eassumption.
          -- eapply inject_virtue_sub_map.
             eapply CMatch.
             inversion HeqvirtueThread1.
             destruct angel; simpl in H0.
             subst virtueThread.
             eassumption.
             
        + (* sub_map *)
          
          destruct Hangel_bound as [Hbounded HboundedLP].
          destruct HboundedLP as (?&?&Hbound).
          move Hbound at bottom.
          subst virtueLP2; simpl.
          
          
          eapply (proj1 (Logic.and_assoc _ _ _)).
          split.

          (*Easy ones: the default is trivial:
                  map_empty_def
           *)
          unfold virtueLP_inject,
          map_empty_def, inject_access_map;
            simpl; auto.

          assert (HboundedLP':
                    sub_map (snd (fst virtueLP1)) (snd (getMaxPerm m1')) /\
                    sub_map (snd (snd virtueLP1)) (snd (getMaxPerm m1'))
                 ) by (subst virtueLP1; eassumption).
          
          destruct virtueLP1 as (virtueLP_fst, virtueLP_snd).
          revert HboundedLP'.
          unfold virtueLP_inject, inject_access_map.
          simpl (fst _).
          simpl (snd _) at 3 6 9.
          

          (* eapply self_simulation.minject in matchmem. *)

          (* strong version of preserving max
               Not only preserves max, but also preserves the structure!
           *)
          
          (* replace m2'' with m2'*)
          inversion Hlock_update_mem_strict_load2; subst vload vstore.
          eapply store_max_eq in Hstore.
          move Hstore at bottom.
          subst m_writable_lock_1.
          unfold tree_map_inject_over_mem.
          repeat rewrite <- Hstore.
          repeat erewrite restr_Max_eq.
          
          intros (Hl & Hr); split;
            eapply inject_virtue_sub_map;
            try eapply CMatch; eauto.
          
        + (*invariant st2 *)
          eapply CMatch.
          
        + (* at_external for code 4. *)
          pose proof Asm_at_external_proper.
          simpl in *.
          rewrite H; eauto.
          apply cur_equiv_restr_mem_equiv; auto.
          
        + (* Mem.range_perm *)
          (* Can read the lock *)
          !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Readable).
          simpl.
          rewrite RPM.
          eapply permMapLt_range_mem.
          inv Hlock_update_mem_strict_load2.
          replace (intval ofs2) with (unsigned ofs + delta).
          intros ? ?.
          exploit Haccess; eauto. simpl. unfold Mem.perm.
          rewrite <- po_oo. simpl in lock_mem_lt.
          pose proof (getCurPerm_correct lock_mem b2 ofs0) as HH.
          unfold permission_at in HH.
          rewrite <- HH. subst lock_mem.
          rewrite getCur_restr. simpl. eauto.

        + (* The load. *)
          inversion Hlock_update_mem_strict_load2; subst vload vstore.
          !goal ( Mem.load AST.Mint32 _ _ _ = Some _ ).
          rewrite <- Hload; f_equal; try assumption.
          * subst lock_mem; f_equal.
            clear; clean_proofs; reflexivity.
        + (* the store *)
          inversion Hlock_update_mem_strict_load2; subst vload vstore.
          !goal ( Mem.store AST.Mint32 _ _ _ _ = Some _ ).
          rewrite <- Hstore.
          f_equal; auto.
          * subst m_writable_lock_1.
            eapply restr_proof_irr'; auto; f_equal; auto.
        + (* content of lockres*)
          (* ThreadPool.lockRes st4 (b4', ofs4') *)
          (* NOTE: why is it rmap? It should be an injection of rmap 
                   ANSWER: the 'RMAP' is empty, so its injection is also empty... 
           *)
          !goal (ThreadPool.lockRes _ _ = Some _).
          simpl in *; rewrite <- Hpmap; repeat f_equal; auto.
        + intros *. rewrite <- Hpmap_equiv1, <- Hpmap_equiv2.
          eapply empty_map_useful.
          eapply inject_empty_maps; assumption.
        + (* permissions join FST*)
          !goal(permMapJoin _ _ _ ).
          subst new_cur2.
          clear - Hjoin_angel2.
          clean_proofs; apply Hjoin_angel2.
          
        + (* permissions join SND *)
          !goal(permMapJoin _ _ _ ).
          subst new_cur2.
          clear - Hjoin_angel2.
          clean_proofs; apply Hjoin_angel2.
          
          Unshelve.
          all: eauto.

          { unfold Max_equiv in Hmax_eq0.
            rewrite Hmax_eq0.
            apply mem_cur_lt_max. }

          { unfold Max_equiv in Hmax_eq.
            rewrite Hmax_eq.
            apply mem_cur_lt_max. }

          { subst_set.
            clear - Hjoin_angel Hthread_mem1 Hmax_eq0.
            unfold Max_equiv in Hmax_eq0.
            rewrite <- Hmax_eq0. clear Hmax_eq0.
            destruct Hjoin_angel as [Hfst _]; simpl in *.
            eapply permMapJoin_lt in Hfst.
            eapply permMapLt_trans; try apply mem_cur_lt_max.
            rewrite <- Hthread_mem1; auto. }

          { subst_set.
            clear - Hjoin_angel2 Hthread_mem2 Hmax_eq.
            unfold Max_equiv in Hmax_eq.
            rewrite <- Hmax_eq. clear Hmax_eq.
            destruct Hjoin_angel2 as [Hfst _]; simpl in *.
            eapply permMapJoin_lt in Hfst.
            eapply permMapLt_trans; try apply mem_cur_lt_max.
            rewrite <- Hthread_mem2; auto. }

          
          { rewrite Hofs2.
            clear - Hlock_update_mem_strict_load2;
              inv Hlock_update_mem_strict_load2; eauto. }
    Qed. (* release_step_diagram_compiled END *)
    (** *Full Machine diagrams *)
    Lemma release_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (angel: virtue) (m1 m1' : mem) (tid : nat) cd mu
        (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb))) (m2 : mem)
        (cnt1 : containsThread(Sem:=HybridSem _) st1 tid)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
        (c : semC) (b : block) (ofs : int)
        (rmap : lock_info)
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        (Hangel_bound: sub_map_virtue angel (getMaxPerm m1))
        (Hcode: getThreadC cnt1 = Kblocked c)
        (Hat_external: semantics.at_external hybrid_sem c m1 =
                       Some (UNLOCK, (Vptr b ofs :: nil)%list))
        (Hlock_update_mem_strict_load:
           lock_update_mem_strict_load
             b (unsigned ofs) (snd (getThreadR cnt1)) m1 m1' vzero vone)
        (HisLock: lockRes st1 (b, unsigned ofs) = Some rmap)
        (Hrmap: empty_doublemap rmap),
        let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
        forall (Hjoin_angel: permMapJoin_pair newThreadPerm1 (virtueLP angel) (getThreadR cnt1)),
        exists ev2 (st2' : t) (m2' : mem),
          let evnt:= build_release_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
          let st1':= fullThUpd_comp
                       st1 tid cnt1 (Kresume c Vundef) angel (b, unsigned ofs) in
          concur_match cd mu st1' m1' st2' m2' /\
          inject_sync_event mu evnt ev2 /\
          let Hcmpt2:= memcompat2 CMatch in
          syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' ev2.
    Proof.
      intros; simpl in *.
      pose proof (memcompat1 CMatch) as Hcmpt1.
      get_mem_compatible.
      get_thread_mems.
      clean_proofs.
      pose proof (cur_equiv_restr_mem_equiv
                    _ _ (th_comp thread_compat1) Hthread_mem1) as
          Hmem_equiv.
      inversion Hlock_update_mem_strict_load. subst vload vstore.
      
      (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
      destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].
      
      (** * tid < hb *)
      
      - rename m1 into MM1.
        pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1
                                (contains12 CMatch cnt1)) as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H3. (* Asm_match *)
        
        (*Destruct the values of the self simulation *)
        pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
        assert (Hinj':=Hinj).
        pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
        eapply sim_atx in Hinj'; eauto.
        2: { (*at_external*)
          idtac.
          erewrite restr_proof_irr.
          rewrite Hmem_equiv; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
        
        (edestruct (release_step_diagram_self AsmSem tid) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step & HCMatch');
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + omega.
        + clean_proofs; eassumption.
        (* + (*at external *)
            unfold thread_mems.
            rewrite Hmem_equiv; simpl; assumption.*)
        + (*match_self*)
          econstructor.
          * eapply H3.
          * simpl. move matchmem at bottom.
            eapply match_mem_proper; try eapply matchmem; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
               clean_proofs; eauto.
        + exists e'. eexists. exists m2'.
          split ; [|split].
          * (* reestablish concur *)
            eapply HCMatch'.
          * clear - Htrace_inj. 
            unfold build_release_event in *. (*subst virtueThread0; *) eauto.
          * clean_proofs; eauto.
            
      (** *tid = hb*)
      - subst tid. 
        (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
        rename m1' into m1''.
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
        remember (virtueThread angel) as virtueThread1.
        remember (virtueLP angel) as virtueLP1.
        rename Hat_external into Hat_external1.
        rename b into b1.
        rename Hstore into Hstore1.
        
        (* to remove until 'end to remove'*)
        rename rmap into lock_map.
        (* end to remove *)
        



        rewrite RPM in Hinterference1.
        symmetry in H0.
        clean_proofs.
        exploit release_step_diagram_compiled;
          try eapply Hthread_mem1;
          try eapply Hthread_mem2;
          try eapply CMatch;
          eauto;
          try reflexivity.
        
        + econstructor; eauto.
        + subst newThreadPerm1 virtueThread1 virtueLP1; eassumption.
        + econstructor; eauto.
          * !goal(mem_interference m1 lev1 m1').
            rewrite self_restre_eq in Hinterference1; eauto.
          * !goal(mem_interference m2 lev2 m2').
            rewrite self_restre_eq in Hinterference2; eauto.
        + subst virtueThread1; simpl; clean_proofs.
          intros; normal; eauto.
      - (* hb < tid *)
        pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1)) as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H3.
        
        (*Destruct the values of the self simulation *)
        pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
        assert (Hinj':=Hinj).
        pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
        eapply sim_atx in Hinj'; eauto.
        2: { erewrite restr_proof_irr.
             rewrite Hmem_equiv; simpl; eassumption.
             
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

        
        (edestruct (release_step_diagram_self CSem tid)
          as
            (e' & m2' & Hthread_match & Htrace_inj & external_step & CMatch');
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + omega.
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.

          * eapply H3.
          * simpl.
            eapply match_mem_proper; try eapply matchmem;
              eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
               clean_proofs; eauto.
        + exists e'. eexists. exists m2'.
          split ; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (fullThUpd_comp _ _ _ _ _ _ ) _ _ _).
            eapply CMatch'.
            
          * clear - Htrace_inj. 
            unfold build_release_event in *. (*subst virtueThread0; *) eauto.
          * clean_proofs; eauto.


            (** *Shelve *)
            Unshelve.
            all: eauto.
            all: try econstructor; eauto.
            all: try apply CMatch.
    Qed. (* release_step_diagram *)
End ReleaseDiagrams.