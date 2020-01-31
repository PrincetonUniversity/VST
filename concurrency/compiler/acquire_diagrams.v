

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
Require Import VST.concurrency.compiler.mem_equiv.
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





Module AcquireDiagrams
       (CC_correct: CompCert_correctness)(Args: ThreadSimulationArguments CC_correct).
  (* this modules hosts lemmas that depend on the Hybrid machine setup.*)

  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Module MySimulationTactics:= SimulationTactics CC_correct Args.
  Import MySimulationTactics.
  Import MyConcurMatch.
  
  (*Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)). *)


  

  

  (*Lemmas about the calls: *)
  Notation vone:= (Vint Int.one).
  Notation vzero:= (Vint Int.zero).


  Section acquire.
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
    


  

    
    (* 4490 *)
    Lemma acquire_step_diagram_self Sem:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
             (st1 : mach_state hb) (st2 : mach_state (S hb))
             (m1 m1' m2 : mem) (mu : meminj) tid i b b' ofs delt
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
             
             (* angel,lock permissions and new thread permissions *)
             (angel: virtue) lock_perm
             (HisLock: lockRes st1 (b, unsigned ofs) = Some lock_perm)
             (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1)*)
             (Hangel_bound:
                pair21_prop sub_map (virtueThread angel) (snd (getMaxPerm m1)))
             (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
             (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2)),
        let Hcmpt2:= memcompat2 CMatch in
        let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
        forall (Hjoin_angel: permMapJoin_pair lock_perm (getThreadR cnt1) newThreadPerm1)
          (Hlt_new: permMapLt_pair newThreadPerm1 (getMaxPerm m1))
          (Hlock_update_mem_strict_load:
             lock_update_mem_strict_load b (unsigned ofs)  (snd (getThreadR cnt1))
                                         m1 m1' vone vzero)
          (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
          (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                         Some (LOCK, (Vptr b ofs :: nil)%list)),
          let event1 := build_acquire_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
          exists event2 (m2' : mem),
            match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
            inject_sync_event mu event1 event2 /\
            let angel2:= inject_virtue m2 mu angel in
            let new_perms2:= Build_virtue (virtueThread angel2) (empty_map, empty_map) in
            let st2':= fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef)
                                       new_perms2 (b', unsigned (add ofs (repr delt))) in
            syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2 /\
            let new_perms:= Build_virtue (virtueThread angel) (empty_map, empty_map) in
            let st1':= fullThUpd_comp st1 tid cnt1 (Kresume sum_state1 Vundef)
                                      new_perms (b, unsigned ofs) in
            concur_match i mu st1' m1' st2' m2'.
    Proof.
      (*  4535 - 4490 = 45 *)
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      
      (*inversion Amatch; clear Amatch. *)

      (* Build the new angel *)
      remember (inject_virtue m2 mu angel) as angel2.
      remember (virtueThread angel2) as angelThread2.
      remember (virtueLP angel2) as angelLP2.

      (* Inject the loads/stores/mem_range*)
      unshelve( exploit lock_update_mem_strict_load_inject;
                eauto; try (eapply CMatch; eauto)); eauto;
        intros (m2'&Hlock_update_mem_strict_load2&Hinj2).

      repeat pose_max_equiv.
      rename Hmax_eq0 into Hmax_equiv.
      rename Hmax_eq into Hmax_equiv2.
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      exploit address_inj_lock_update_load; eauto; intros Heq.
      
      remember (build_acquire_event (b', unsigned ofs + delt ) (fst angelThread2) m2')
        as event2. 

      
      set (newThreadPerm2 := computeMap_pair (getThreadR cnt2) (virtueThread angel2)).

      assert (Hfull:Events.injection_full mu m1) by apply CMatch.
      assert (Hinj': Mem.inject mu m1 m2).
      { rewrite (mem_is_restr_eq m1), (mem_is_restr_eq m2).
        erewrite (restre_equiv_eq _ _ m1); try (symmetry; eauto).
        erewrite (restre_equiv_eq _ _ m2); try (symmetry; eauto).
        eapply CMatch. }
      assert (Hjoin_angel2: permMapJoin_pair
                              (virtueLP_inject m2 mu lock_perm)
                              (getThreadR cnt2)
                              newThreadPerm2).
      { clear -CMatch Hangel_bound Heqangel2
                      Hmax_equiv Hinj2 thread_compat1 Hjoin_angel HisLock.
        (* exploit full_injects_angel; eauto; try apply CMatch. intros Hinject_angel.
            subst newThreadPerm2; simpl. *)

          (* Look at how its done on release *)
          !goal(permMapJoin_pair _ _ _).
          assert (permMapLt_pair lock_perm (getMaxPerm m1)) by
              (eapply CMatch; eauto).
          subst newThreadPerm2; subst.
          eapply permMapJoin_pair_inject_acq; try eassumption; eauto;
            try eapply Hangel_bound;
            try eapply CMatch; eauto.

          !goal (injects_angel _ _).
          split; simpl.
          - eapply Lt_inject_map_pair; eauto.
            eapply full_inject_map; try eapply CMatch.
            eapply max_map_valid.
          - eapply full_inject_dmap_pair.
            eapply CMatch.
            eapply join_dmap_valid_pair; eauto. }
      
      assert (Hlt11': permMapLt_pair (newThreadPerm1) (getMaxPerm m1')).
      { unfold Max_equiv in *.
        split; simpl; rewrite <- Hmax_equiv; eapply Hlt_new. }
      destruct Hlt11' as [Hlt11' Hlt12']. 
      
      assert (Hlt_new2: permMapLt_pair newThreadPerm2 (getMaxPerm m2)).
      { subst newThreadPerm2.
        exploit (permMapLt_computeMap_pair (getMaxPerm m2));
            try (intros HH; eapply HH).
          2:{ eapply Hcmpt2. }
          subst angel2. simpl.
          eapply deltaMapLt2_inject_pair.
          * eapply CMatch.
          * eapply permMapLt_computeMap_pair'.
            eapply Hlt_new. }
      assert (Hlt22': permMapLt_pair (newThreadPerm2) (getMaxPerm m2')).
      { unfold Max_equiv in *.
        split; simpl; rewrite <- Hmax_equiv2; eapply Hlt_new2. }
      destruct Hlt22' as [Hlt21' Hlt22'].
      
      repeat forward_mem_cmpt_all.
      set (virtueLP1 :=   virtueLP angel).
      set (virtueLP2 :=   virtueLP_inject m2 mu virtueLP1).
      set (ofs2      :=   add ofs (repr delt)).
      set (new_perms2:= Build_virtue (virtueThread angel2) (empty_map, empty_map)).
      set (st2':= fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef)
                                 new_perms2 (b', unsigned (add ofs (repr delt)))).
      set (new_perms:= Build_virtue (virtueThread angel) (empty_map, empty_map)).
      remember (fullThUpd_comp st1 tid cnt1 (Kresume sum_state1 Vundef)
                                      new_perms (b, unsigned ofs)) as st1'.
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
        1:{ apply Hlt_new. }
        3:{ rewrite <- Hstore0. f_equal.
            subst m_writable_lock_0.
            apply restr_proof_irr. }
        2:{ rewrite <- Hstore. f_equal.
            subst m_writable_lock_1.
            apply restr_proof_irr. }
        2:{ subst newThreadPerm1; simpl.
            eapply mi_memval_perm_join.
            - eapply Hjoin_angel.
            - eapply INJ_lock_content'; eauto.
            - pose proof (mi_inj_mi_memval_perm mu m1 m2).
              rewrite Hthread_mem1.
              eapply H3.
              eapply Hinj'. }
        apply restr_Max_equiv. }
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
        1:{ apply Hlt_new. }
        3:{ rewrite <- Hstore0. f_equal.
            subst m_writable_lock_0.
            apply restr_proof_irr. }
        2:{ rewrite <- Hstore. f_equal.
            subst m_writable_lock_1.
            apply restr_proof_irr. }
        2:{ subst newThreadPerm1; simpl.
            eapply mi_memval_perm_join.
            - eapply Hjoin_angel.
            - eapply INJ_lock_content''; eauto.
            - replace (Mem.mem_contents m1) with
                  (Mem.mem_contents lk_mem1) by
                  (subst lk_mem1; reflexivity).
              replace (Mem.mem_contents m2) with
                  (Mem.mem_contents lk_mem2) by
                  (subst lk_mem2; reflexivity).
              pose proof (mi_inj_mi_memval_perm mu lk_mem1 lk_mem2).
              subst lk_mem1 lk_mem2; simpl in *.
              rewrite getCur_restr in H3.
              eapply H3.
              eapply CMatch. }
        apply restr_Max_equiv. }
      
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
      assert (Hinj2': Mem.inject mu (restrPermMap Hlt12') (restrPermMap Hlt22'))
        by (apply inject_restr; eauto).
      assert (Hinj1': Mem.inject mu (restrPermMap Hlt11') (restrPermMap Hlt21')) by
      (apply inject_restr; eauto). 
      
      
      simpl in *.
      (*assert (HH: st2' = fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef) new_perms2
                                     (b', unsigned (add ofs (repr delt)))) by reflexivity.*)
      forward_state_cmpt_all.
      subst st1' st2' virtueLP1 virtueLP2 .

      exploit INJ_lock_permissions_image; eauto;
        intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2).
      simpl in *.
      
      (* Instantiate some of the existensials *)
      exists event2; exists m2'.
      repeat weak_split. (* 4 goal*)
      
      - !goal( match_self _ _ _ _ _ _). 
        inversion Amatch.
        constructor; eassumption.
        
      - !goal (inject_sync_event mu event1 event2).
        (*Goal: Inject the trace*)
        subst event1 event2.
        do 2 econstructor; auto. assumption.
        
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
        subst angelThread2.
        eapply step_acquire with
            (b0:= b')(m':=m2')
            (virtueThread:=(virtueThread angel2))
            (pmap0:= pmap)
        ; eauto; try reflexivity.
        
        (* 10 goals produced. *)
        
        + subst  angel2 lk_mem1 lk_mem2.
          eapply inject_virtue_sub_map_pair; eauto.
        + apply CMatch. 
        + !goal (semantics.at_external _ _ _ = Some (LOCK, _)).
          { clean_proofs.
            eapply ssim_preserves_atx in Hat_external.
            2: { inversion Amatch; constructor; eauto. }
            destruct Hat_external as (args' & Hat_external2 & val_inj).
            replace ( Vptr b' (add ofs (repr delt)) :: nil) with args'.
            
            simpl; unfold at_external_sum, sum_func.
            subst CoreSem. 
            rewrite <- (restr_proof_irr (th_comp _ thread_compat2)).
            rewrite <- Hat_external2; simpl.
            clear - Hthread_mem2 HState2.
            
            inversion HState2; subst.
            - !goal ( Clight.at_external _ = _ _ m2).
              replace c with th_state2; auto.
              2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
              (* why can't I rewrite?*)
              eapply C_at_external_proper; auto.
              eapply cur_equiv_restr_mem_equiv; auto.
            - !goal ( Asm.at_external _ _ = _ _ m2).
              replace c with th_state2; auto.
              2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
              simpl.
              (* why can't I rewrite?*)
              eapply Asm_at_external_proper; auto.
              eapply cur_equiv_restr_mem_equiv; auto.
            - clear - val_inj Hinj_b.
              inversion val_inj; subst.
              inversion H3; f_equal.
              inversion H1; subst.
              rewrite Hinj_b in H4; inversion H4; subst.
              reflexivity. }
        + !goal (lockRes _ (b',_) = Some _).
          simpl in *; rewrite <- Hpmap; repeat f_equal.
          solve_unsigned.
        + (* Claims the transfered resources join in the appropriate way *)
          simpl in *; rewrite <- Hpmap_equiv1.
          subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.
        + (* Claims the transfered resources join in the appropriate way *)
          simpl in *; rewrite <- Hpmap_equiv2.
          subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.
        + subst angel2; unfold fullThUpd_comp, fullThreadUpdate; simpl.
          repeat (f_equal; simpl).

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
          eapply invariant_update_join_acq; eauto.
          2: eapply CMatch.
          unfold fullThUpd_comp, fullThreadUpdate; simpl.
          reflexivity. 
        + !goal (@invariant (HybridSem _ ) _ _).
          subst newThreadPerm2 angel2.
          eapply invariant_update_join_acq; try reflexivity.
          * simpl in *; rewrite <- Hpmap; repeat f_equal.
            subst ofs2; assumption.
          * apply CMatch.
          * simpl. eauto.
            simpl in *. split; simpl.
            rewrite <- Hpmap_equiv1; eauto; apply Hjoin_angel2.
            rewrite <- Hpmap_equiv2; eauto; apply Hjoin_angel2.
       (* + !goal (mem_compatible _ m1').
          unfold fullThUpd_comp,fullThreadUpdate; eauto; simpl in *.
          subst angel2 newThreadPerm2; simpl in *; eauto.
           *)
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
             ** eapply full_inject_dmap_pair.
                --- !goal (Events.injection_full mu _ ).
                    eapply CMatch.
                --- !goal (dmap_valid_pair _ _).
                apply join_dmap_valid_pair.
                move Hangel_bound at bottom.
                rewrite getMax_restr_eq.
                eapply Hangel_bound.
        +  (* Proof of match goes after the comment *)
          !context_goal one_thread_match. shelve.
        + !context_goal memval_inject.
          repeat econstructor.
        + eapply empty_map_is_empty_pair.
          eapply inject_empty_maps.
          eapply empty_is_empty_pair.
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
          repeat f_equal; eauto; simpl.
          
          Unshelve.
          all: eauto.
          all: try eapply CMatch.
          { hnf in Hmax_equiv. intros ? ?.
            move Hmax_equiv at bottom.
            rewrite Hmax_equiv.
            eapply mem_cur_lt_max. }
          { hnf in Hmax_equiv2. intros ? ?.
            move Hmax_equiv2 at bottom.
            rewrite Hmax_equiv2.
            eapply mem_cur_lt_max. }
          
          { !context_goal one_thread_match. (*shelved above.*)
            destruct (lt_eq_lt_dec tid hb) as [[Htid_neq'|Htid_neq']|Htid_neq'].
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch);
              simpl; eauto.
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
                
                
                econstructor; eauto.
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
                  -- exploit MyConcurMatch.mtch_target; eauto.
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

                
                econstructor; eauto.
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
                  -- exploit MyConcurMatch.mtch_source; eauto.
                     intros HH; inv HH; inv matchmem;
                       repeat rewrite getCur_restr in *;
                       eauto.
                  -- eapply inject_perm_perfect_image_dmap; eauto.
                     eapply sub_map_implication_dmap; eauto.
                     eapply Hangel_bound.
                     eapply full_inject_dmap; eauto.
                     eapply join_dmap_valid, Hangel_bound.
             }

          Unshelve.      
          all: simpl;eauto.
          all: rewrite getMax_restr; eauto.
    Qed. (* END acquire_step_diagram_self *)
    
    
    Lemma acquire_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (angel: virtue) (cd : compiler_index)
        mu (*tr2*)
        st1 (m1 m1' m1'' : mem) Hcnt1 
        st2 (m2' : mem) Hcnt2
        (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
        b1 ofs lock_perms (code1 : semC)  (code2 : Asm.state)
        (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
        (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
        (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
        (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
        (Hangel_bound: pair21_prop sub_map (virtueThread angel)
                                   (snd (getMaxPerm m1')))
        (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
        (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
        (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                         Some (LOCK, (Vptr b1 ofs :: nil)%list))
        (Hlock_update_mem_strict_load:
           lock_update_mem_strict_load b1 (unsigned ofs)  (snd (getThreadR Hcnt1))
                                       m1' m1'' vone vzero)
        (HisLock: lockRes st1 (b1, unsigned ofs) = Some lock_perms)
        (Hvirtue_locks: virtueLP angel= lock_perms),
        let newThreadPerm1:= (computeMap_pair (getThreadR Hcnt1) (virtueThread angel)) in
        let new_perms:= Build_virtue (virtueThread angel) (empty_map, empty_map) in
        forall (Hjoin_angel: permMapJoin_pair lock_perms (getThreadR Hcnt1) newThreadPerm1)
          (Hlt_new: permMapLt_pair newThreadPerm1 (getMaxPerm m1'))
          (Hlt1 : permMapLt (thread_perms _ _ Hcnt1) (getMaxPerm m1'))
          (Hlt2 : permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2'))
          (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        exists evnt2 (st2' : t) (m2'' : mem),
          let evnt:= build_acquire_event (b1, unsigned ofs) (fst (virtueThread angel)) m1'' in 
          let st1':= fullThUpd_comp st1 hb Hcnt1 (Kresume (SST code1) Vundef) new_perms (b1, unsigned ofs)  in
          concur_match (Some cd) mu st1' m1'' st2' m2'' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:= memcompat2 CMatch in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true Hcnt2 Hcmpt2 st2' m2'' evnt2.
    Proof.
      
      intros.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      clean_proofs. rename abs_proof into Hcmpt2.

      
      remember (virtueThread angel) as virtueThread1.
      (*remember (virtueLP angel) as virtueLP1. *)
      
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

      exploit INJ_lock_permissions_image; eauto;
        intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2); simpl in *.
      set (virtueThread2:= virtueThread_inject m2' mu virtueThread1).
      (*set (virtueLP2:=virtueLP_inject m2'' mu lock_perms). *)
      set (virtueLP2:=pmap).
      set (ofs2:= add ofs (repr delta)).
      set (new_cur2:= (computeMap_pair (getThreadR Hcnt2) virtueThread2)).
      set (st2':= (updLockSet
                     (updThread Hcnt2 (Kresume (TST code2) Vundef) new_cur2)
                     (b2, unsigned ofs2) (pair0 empty_map))).
      remember (fullThUpd_comp st1 hb Hcnt1 (Kresume (SST code1) Vundef) new_perms
                               (b1, unsigned ofs)) as st1'.

      
      (* assert (Hofs2: unsigned ofs2 = unsigned ofs + delta).
      { subst ofs2; solve_unsigned. } *)
      
      assert (H: ThreadPool (Some (S hb)) =
                 @t dryResources (HybridSem (@Some nat (S hb)))).
      { reflexivity. }
      dependent rewrite <- H in st2'. clear H.

      assert (Hjoin_angel2: permMapJoin_pair virtueLP2 (getThreadR Hcnt2)  new_cur2).
      { subst new_cur2.
        subst virtueLP2.
        cut
          (permMapJoin_pair (virtueLP (inject_virtue m2' mu angel)) (getThreadR Hcnt2)
                            (computeMap_pair (getThreadR Hcnt2) virtueThread2)
          ).
        { intros [HH1 HH2]; simpl in *; subst lock_perms.
          split; simpl; first [rewrite <- Hpmap_equiv1 | rewrite <- Hpmap_equiv2];
            eassumption. }
        
        (* replace virtueLP2 with (virtueLP (inject_virtue m2' mu angel)).
        2:{ subst virtueLP2; simpl. subst lock_perms.
            erewrite virtueLP_inject_max_eq_exteny; try reflexivity.
            (* this is a bit stronger than equivalence *)
            inv Hlock_update_mem_strict_load2.
            erewrite <- getMax_restr_eq.
            eapply store_max_eq; eauto. } *)
        
        assert (HH:permMapLt_pair lock_perms (getMaxPerm m1')) by
            (eapply CMatch; eauto).
        subst lock_perms newThreadPerm1 virtueThread1.

        eapply permMapJoin_pair_inject_acq; try eassumption; eauto;
          try eapply Hangel_bound;
          try eapply CMatch; eauto.

        !goal (injects_angel _ _).
        split; simpl.
        - eapply Lt_inject_map_pair; eauto. 
          eapply full_inject_map; try eapply CMatch.
          eapply max_map_valid.
        - eapply full_inject_dmap_pair.
          eapply CMatch.
          eapply join_dmap_valid_pair; eauto. }
      repeat pose_max_equiv.
      
      (*
    let Hcmpt_fwd:= fresh "Hcmpt_update" in
      repeat unfold_state_forward.
      (* Find the states and the mems.*)
      match goal with
      |[ H: ?st' = updLockSet (@updThread _ _ _ ?st _ _ _) _ _ |- _ ] =>
       let M:= fresh in mark M st';
                          
                        (let Hcmpt_update_state := fresh "Hcmpt_update" in
  eapply (mem_compatible_fullThreadUpdate _ (TP _)) in H as Hcmpt_update_state;
   try reflexivity; simpl;
   [  | eassumption | idtac | idtac | solve_valid_block ];
   idtac);
                        
                        try forward_state_cmpt_all;
                        clear M
      end;
      repeat forward_mem_cmpt_all; swap 1 3.
      try eassumption; subst_set; try subst;
          (first
             [ solve_permMapLt_easy
             | eapply permMapLt_pair_trans211;
               [ solve_permMapLt_easy | solve_permMapLt_cmpt ]
             | solve_permMapLt_set_new_perms
             (*| solve
                 [ apply_permMapLt_compute_inject_pair ]*)
             | idtac "permMapLt_pair cant be solved:"; print_goal ]).
      try eassumption; subst_set; try subst;
          (first
             [ solve_permMapLt_easy
             | eapply permMapLt_pair_trans211;
               [ solve_permMapLt_easy | solve_permMapLt_cmpt ]
             | solve_permMapLt_set_new_perms
             (*| solve
                 [ apply_permMapLt_compute_inject_pair ]*)
             | idtac "permMapLt_pair cant be solved:"; print_goal ]). *)
      

      forward_cmpt_all. 
      rename Hcmpt_mem_fwd into Hcmpt2'.
      rename Hcmpt_mem_fwd0 into Hcmpt1'.
      
      (** * 4. Finally we proceed with the goal: existentials. *)
      
      eexists.
      exists st2', m2''.
      split; [|split].
      
      - assert (Hlt11 : permMapLt (fst newThreadPerm1) (getMaxPerm m1'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq0; solve_permMapLt. }

        assert (Hlt21 : permMapLt (fst new_cur2) (getMaxPerm m2'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq.
          let H := fresh in
          match goal with
          | |- permMapLt (fst ?a) ?b => assert (H : permMapLt_pair a b)
          | |- permMapLt (snd ?a) ?b => assert (H : permMapLt_pair a b)
          end; try now apply H.
          eapply permMapLt_compute_inject_pair_useful; eauto. 
        (* HERE!: I commented out one case on the solve (*says HERE! *) 
               because it broke the QED.
               how can I better apply it?
         *) }
        assert (H : permMapLt_pair new_cur2 (getMaxPerm m2')).
        { eapply permMapLt_compute_inject_pair_useful; eauto.  }
        assert (Hlt22 : permMapLt (snd new_cur2) (getMaxPerm m2'')).
        { unfold Max_equiv in *; rewrite <- Hmax_eq.
          eapply permMapLt_compute_inject_pair_useful; eauto. }

        
        unshelve eapply (concur_match_perm_restrict' (getCurPerm m1') (getCurPerm m2')).
        (*1,2: apply mem_cur_lt_max. *)
        1,2: unfold Max_equiv in *; first [rewrite <- Hmax_eq0|rewrite <- Hmax_eq];
          apply mem_cur_lt_max. 
        clean_proofs_goal.
        
        eapply concur_match_update_lock; 
          try match goal with |- context[Forall2] => idtac
                         | _ => 
                           eauto; try solve[subst st1'; eauto] end.
        + !context_goal lock_update_mem.
          eapply lock_update_mem_strict_load_mem_update_restr; eauto.
        + !context_goal (lock_update_mem).
          eapply lock_update_mem_strict_load_mem_update_restr; eauto.
        + !context_goal Mem.inject.
          do 2 erewrite <- restrPermMap_idempotent_eq.
          instantiate(2:=fst new_cur2);
            instantiate(3:=fst newThreadPerm1).
          apply inject_restr; auto.
          * !goal (mi_perm_perm mu (fst newThreadPerm1) (fst new_cur2)).
            { 
              subst newThreadPerm1 new_cur2; simpl.
              
              eapply computeMap_mi_perm_perm_perfect.
              -- eapply maps_no_overlap_Lt; eauto.
                 2: eapply Hangel_bound.
                 eapply no_overlap_mem_perm.
                 eapply Hinj'0.
              -- unshelve eapply (mi_perm_perm_threads). 4: eauto.
                 
              -- eapply inject_perm_perfect_image_dmap; eauto.
                 eapply sub_map_implication_dmap.
                 eapply Hangel_bound.
                 eapply full_inject_dmap; swap 1 2.
                 eapply join_dmap_valid, Hangel_bound.
                 eapply CMatch.  }
          * !goal (mi_memval_perm mu (fst newThreadPerm1)
                                  (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
            {
              
              inversion Hlock_update_mem_strict_load1.
              inversion Hlock_update_mem_strict_load2. subst vload vstore vload0 vstore0.
              
              assert (Hwritable_lock1':=Hwritable_lock1).
              assert (Hwritable_lock0':=Hwritable_lock0).
              (*rewrite <- Hmxeqv_lk2 in Hwritable_lock0'.*)
              

              eapply mi_memval_perm_store
                with (Hwritable_lock0:=Hwritable_lock0')
                     (Hwritable_lock1:=Hwritable_lock1')
              ; try eapply Haccess;
                try eapply HHlock; eauto.
              1:{ apply Hlt_new. }
              3:{ rewrite <- Hstore0. f_equal.
                  subst m_writable_lock_0.
                  apply restr_proof_irr. }
              2:{ rewrite <- Hstore. f_equal.
                  subst m_writable_lock_1.
                  apply restr_proof_irr. }
              1:{ apply restr_Max_equiv. }
              1:{ 
                eapply mi_memval_perm_join; try apply Hjoin_angel; swap 1 2.
                - rewrite Hthread_mem1.
                  eapply mi_inj_mi_memval_perm, Hinj'0.
                - revert HisLock.
                  
                  
                  eapply INJ_lock_content'; eauto.
              }
            }
          * !goal (mi_perm_inv_perm mu (fst newThreadPerm1) (fst new_cur2) m1'').
            { subst_set; simpl.
              erewrite tree_map_inject_restr.
              rewrite <- tree_map_inject_restr.
              eapply mi_perm_inv_perm_compute with (m1:=m1'); eauto.
              -- eapply Hangel_bound. }
            
        + !goal (@invariant (HybridSem _) _ _).
          
          simpl in Heqst1'.
          eapply invariant_update_join_acq; eauto; simpl; try reflexivity.
          eapply CMatch.
          
        + !goal (invariant st2'). 
          eapply invariant_update_join_acq.
          4: eassumption.
          2: reflexivity.
          2: apply CMatch.
          subst virtueLP2. simpl in *; rewrite <- Hpmap.
          repeat f_equal.
          subst ofs2.
          solve_unsigned.
          
        + !goal (mem_compatible _ _ ).
          subst st1'; apply mem_compat_restrPermMap; auto.
        + !goal (mem_compatible _ _ ). apply mem_compat_restrPermMap; auto.
        + !goal(perm_surj mu _ _).
          instantiate(1:=snd new_cur2); instantiate (1:=snd newThreadPerm1).
          subst newThreadPerm1 new_cur2; simpl.
          eapply perm_surj_compute.
          ++ eapply CMatch. 
          ++ subst virtueThread2.
             cut (perm_perfect_image_dmap_pair
                    mu virtueThread1 (virtueThread_inject m2' mu virtueThread1)).
             { intros HH; apply HH. }
             subst virtueThread1.
             eapply inject_virtue_perm_perfect_image_dmap; eauto.
             eapply full_inject_dmap_pair.
             ** !goal (Events.injection_full mu _ ).
                eapply CMatch.
             ** !goal (dmap_valid_pair _ _).
                apply join_dmap_valid_pair.
                eapply Hangel_bound.
        + !goal (Mem.inject mu _ _).
          do 2 erewrite <- restrPermMap_idempotent_eq.
          apply inject_restr; auto.
          * !goal (mi_perm_perm mu (snd newThreadPerm1) (snd new_cur2)).
            { unfold newThreadPerm1, new_cur2; simpl.
              eapply computeMap_mi_perm_perm_perfect.
              - eapply maps_no_overlap_Lt; eauto.
                2: eapply Hangel_bound.
                eapply no_overlap_mem_perm.
                eapply Hinj'0.
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
                  eapply Hangel_bound. }
          * !goal (mi_memval_perm mu (snd newThreadPerm1)
                                  (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
            
            inversion Hlock_update_mem_strict_load1.
            inversion Hlock_update_mem_strict_load2.

            assert(Hmxeqv_lk1: Max_equiv lk_mem1 m1').
            { subst lk_mem1; simpl.
              eapply restr_Max_equiv. }
            assert (Hwritable_lock1':=Hwritable_lock1).
            
            assert(Hmxeqv_lk2: Max_equiv lk_mem2 m2').
            { subst lk_mem2; simpl.
              eapply restr_Max_equiv. }
            assert (Hwritable_lock0':=Hwritable_lock0).
            

            eapply mi_memval_perm_store
              with (Hwritable_lock0:=Hwritable_lock0')
                   (Hwritable_lock1:=Hwritable_lock1')
            ; try eapply Haccess;
              try eapply HHlock; eauto.
            1:{ apply Hlt_new. }
            3:{ rewrite <- Hstore0. f_equal.
                subst m_writable_lock_0.
                apply restr_proof_irr. }
            2:{ rewrite <- Hstore. f_equal.
                subst m_writable_lock_1.
                apply restr_proof_irr. }
            2:{  eapply mi_memval_perm_join; try apply Hjoin_angel; swap 1 2.
                 - replace (Mem.mem_contents m1') with
                       (Mem.mem_contents lk_mem1) by
                       (subst lk_mem1; reflexivity).
                   replace (Mem.mem_contents m2') with
                       (Mem.mem_contents lk_mem2) by
                       (subst lk_mem2; reflexivity).
                   assert (HH:access_map_equiv
                                (MySimulationTactics.lock_perms hb st1 Hcnt1)
                                (getCurPerm lk_mem1)).
                   { subst lk_mem1; unfold MySimulationTactics.lock_perms.
                     unfold thread_mems.
                     rewrite getCur_restr; simpl. reflexivity. }
                   rewrite HH.
                   eapply mi_inj_mi_memval_perm, Hinj_lock.
                 - eapply INJ_lock_content''; eauto. }
            1:{ eauto. subst lock_mem. apply restr_Max_equiv. }
            
          * !goal (mi_perm_inv_perm mu (snd newThreadPerm1) (snd new_cur2) _).
            
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
          
          (* LINE: 6135 *) 
          { !context_goal one_thread_match.
            do 2 erewrite <- restrPermMap_idempotent_eq.
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
            
            


            (** *0 . Simplifications to do outside the l emma*)
            
            assert (Hext_acq1': extcall_acquire
                                  (Genv.globalenv (Ctypes.program_of_program C_program)) 
                                  (Vptr b1 ofs :: nil) m1
                                  (Events.Event_acq_rel lev1 (fst virtueThread1) lev1' :: nil)
                                  Vundef m1''').
            { inversion Hlock_update_mem_strict_load1; subst vload vstore.
              subst rel_trace; econstructor; try eassumption.
              econstructor; eauto.
              eapply restrPermMap_access_equiv; subst newThreadPerm1; simpl.
              rewrite Hthread_mem1; reflexivity.
            } 
            assert (Hext_acq1: Events.external_call LOCK
                                                    (Clight.genv_genv Clight_g)
                                                    (Vptr b1 ofs :: nil)
                                                    m1 rel_trace Vundef m1''').
            { simpl; rewrite AcquireExists.
              subst rel_trace dpm1; eauto. }
            clear Hext_acq1'.
            
            assert (Hext_acq2: extcall_acquire
                                 Asm_g (Vptr b2 ofs2 :: nil) m2
                                 (Events.Event_acq_rel lev2 (fst virtueThread2)
                                                       lev2' :: nil)
                                 Vundef m2''').
            { inversion Hlock_update_mem_strict_load2; subst vload vstore.
              econstructor; eauto.
              subst m_writable_lock_1; econstructor.
              3: { eapply restrPermMap_access_equiv; subst new_cur2; simpl.
                   rewrite Hthread_mem2; reflexivity. }
              - clear - Hstore.
                move Hstore at bottom.
                replace (unsigned ofs2) with (unsigned ofs + delta) by
                    (subst ofs2; solve_unsigned).
                eassumption.
              - subst new_cur2; simpl.
                !goal (computeMap _ _ = computeMap _ _).
                reflexivity.
            }

            
            assert (Hnb_eq': Mem.nextblock (restrPermMap Hlt21) = Mem.nextblock m2')
              by auto.
            

            subst rel_trace.
            eapply large_external_diagram; try reflexivity; eauto.
            - exact acquire_is_consec.
            - exact lock_doesnt_return.
            - reflexivity.
            - !goal(EventsAux.inject_delta_map _ _ _ ).
              instantiate(1:=fst virtueThread2).
              subst dpm1.
              subst virtueThread2 virtueThread1; simpl.
              remember (fst (virtueThread angel)) as virt.
              eapply virtue_inject_bounded; eauto.
              + apply Hinj'0.
              + eapply full_inject_dmap.
                * eapply CMatch.
                * eapply join_dmap_valid.
                  subst virt.
                  eapply Hangel_bound.
              + subst virt; eapply Hangel_bound.
              + eapply Hinj'0.
              + eapply Hinj'0.
            - simpl; rewrite AcquireExists; eauto.
            - exploit (interference_consecutive_until _ _ _ Hinterference2).
              rewrite <- Hnb_eq; simpl; auto.
            - exploit (interference_consecutive_until _ _ _  Hinterference2').
              simpl; auto.
          }
          
        + !context_goal memval_inject.
          repeat econstructor.
        + !goal (access_map_equiv_pair _ _ ).
          instantiate(1:= pair0 empty_map).
          
          eapply empty_map_is_empty_pair, inject_empty_maps.
          instantiate(1:= pair0 empty_map).
          eapply empty_is_empty_pair.

        + !goal(lock_update _ st1 _ _ _ _ _).
          econstructor;
            subst st1' newThreadPerm1 virtueThread1;
            unfold fullThUpd_comp, fullThreadUpdate.
          reflexivity.

        + !goal(lock_update _ st2 _ _ _ _ st2'). simpl.
          econstructor;
            subst st2' new_cur2 virtueLP2  ofs2;
            unfold fullThUpd_comp, fullThreadUpdate.
          repeat f_equal.
          * f_equal.
            !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta).
            solve_unsigned.
      - econstructor.
        + econstructor; eauto.
        + instantiate (1:= Some (build_delta_content (fst virtueThread2) m2'')).
          simpl.
          constructor.
      (* adm it. (*TODO define inject_delta_content *)
       *)
      (* injection of the event*)
      (* Should be obvious by construction *)
      - (* HybridMachineSig.external_step *)
        assert (Hofs2: intval ofs2 = unsigned ofs + delta).
        { subst ofs2; solve_unsigned. }
        rewrite <- Hofs2.
        
        eapply step_acquire;
          eauto; try reflexivity;
            try unfold HybridMachineSig.isCoarse,
            HybridMachineSig.HybridCoarseMachine.scheduler.
        
        + (* sub_map *)
          subst virtueThread2.
          unfold virtueThread_inject.
          destruct virtueThread1 as (virtue11, virtue12).
          cbv iota beta delta[fst] in *.
          destruct Hangel_bound as [Hbound1 Hbound2].
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
             
        + (*invariant st4 *)
          !goal (@invariant (HybridSem _) _ st2).
          eapply CMatch.
          
        + (* at_external for code 4. *)
          move Hat_external2' at bottom.
          match goal with
            |- context [restrPermMap ?Hlt]=>
            pose proof (cur_equiv_restr_mem_equiv _ _ Hlt Hthread_mem2)
          end.
          pose proof (Asm_at_external_proper Asm_g code2 _ eq_refl _ _ H).
          simpl in H0; simpl. unfold Asm_g in H0.
          rewrite H0. eauto.
          
        + (* Mem.range_perm *)
          (* Can read the lock *)
          !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Readable).
          inversion Hlock_update_mem_strict_load2; subst vload vstore.
          rewrite Hofs2.
          eapply range_perm_mem_equiv_Cur; try apply eq_refl; eauto.
          * subst lock_mem.
            eapply Cur_equiv_restr; simpl; reflexivity.
            
        + (* The load. *)
          inversion Hlock_update_mem_strict_load1; subst vload vstore.
          !goal ( Mem.load AST.Mint32 _ _ _ = Some _ ).
          
          replace (intval ofs2) with (unsigned ofs + delta) by assumption.
          eapply (load_inject' mu); eauto; try congruence.
          unfold thread_mems; simpl.
          unshelve eapply INJ_locks; eauto.
          
        + !goal(permMapLt _ _ /\ permMapLt _ _ ).
          change (permMapLt_pair
                    (computeMap_pair (getThreadR Hcnt2) (virtueThread2))
                    (getMaxPerm m2')).
          eapply permMapLt_computeMap_pair; eauto.
          2: split; eauto.
          eapply deltaMapLt2_inject_pair; eauto.
          -- repeat rewrite <- mem_is_restr_eq; eauto.
          -- eapply permMapLt_computeMap_pair'; eassumption.
             
        + (* the store *)
          inversion Hlock_update_mem_strict_load2; subst vload vstore.
          
          !goal ( Mem.store AST.Mint32 _ _ _ _ = Some _ ).
          rewrite <- Hstore.
          
          subst m_writable_lock_1.
          f_equal; eauto.
          * eapply restr_proof_irr'; auto; f_equal; auto.
            
        + (* content of lockres*)
          (* ThreadPool.lockRes st4 (b4', ofs4') *)
          (* NOTE: why is it rmap? It should be an injection of rmap 
                   ANSWER: the 'RMAP' is empty, so its injection is also empty... 
           *)
          !goal (ThreadPool.lockRes _ _ = Some _).
          rewrite Hofs2; eauto.
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
            rewrite getMax_restr, <- Hmax_eq0.
            eapply Hlt_new.  }

          { rewrite getMax_restr; auto. }

          { unfold Max_equiv in Hmax_eq0.
            rewrite getMax_restr, <- Hmax_eq0.
            eapply Hlt_new.  }
          
          { rewrite getMax_restr; auto. }

          { unfold Max_equiv in Hmax_eq0.
            rewrite <- Hmax_eq0.
            eapply Hlt_new.  }

          { subst_set.
            move Hlt11 at bottom. simpl in Hlt11.
            rewrite <- Hthread_mem1; eauto. }

          { unfold Max_equiv in Hmax_eq.
            rewrite <- Hmax_eq.
            eapply permMapLt_computeMap; eauto.
            eapply deltaMapLt2_inject; eauto.
            -- repeat rewrite <- mem_is_restr_eq; eauto.
            -- eapply permMapLt_computeMap_pair'; eassumption.
            -- eapply cur_lt_max.
          }

          { rewrite Hofs2.
            clear - Hlock_update_mem_strict_load2;
              inv Hlock_update_mem_strict_load2; eauto. }

          
          
    Qed. (*acquire_step_diagram_compiled END*)         
    
    Lemma acquire_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (angel: virtue) (m1 m1' : mem) (tid : nat) cd
        (mu : meminj) (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb))) (m2 : mem)
        (cnt1 : containsThread(Sem:=HybridSem _) st1 tid)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
        (c : semC) (b : block) (ofs : int) lock_perms
        (Hangel_lock_perms: virtueLP angel = lock_perms)
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1)*)
        (Hangel_bound: pair21_prop sub_map (virtueThread angel)
                                   (snd (getMaxPerm m1)))
        (Hcode: getThreadC cnt1 = Kblocked c)
        (Hat_external: semantics.at_external hybrid_sem c m1 =
                       Some (LOCK, (Vptr b ofs :: nil)%list))
        (Hlock_update_mem_strict_load:
           lock_update_mem_strict_load b (unsigned ofs)
                                       (snd (getThreadR cnt1))
                                       m1 m1' vone vzero )
        (HisLock: lockRes st1 (b, unsigned ofs) = Some lock_perms),
        let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
        let new_perms:= Build_virtue (virtueThread angel) (empty_map, empty_map) in
        forall (Hjoin_angel: permMapJoin_pair lock_perms (getThreadR cnt1) newThreadPerm1)
          (Hlt_new: permMapLt_pair newThreadPerm1 (getMaxPerm m1)),
        exists evnt2 (st2' : t) (m2' : mem),
          let evnt:= build_acquire_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
          let st1':= fullThUpd_comp st1 tid cnt1 (Kresume c Vundef) new_perms (b, unsigned ofs) in
          concur_match cd mu st1' m1' st2' m2' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:=  (memcompat2 CMatch) in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true cnt2 Hcmpt2 st2' m2' evnt2.
    Proof.
      intros; simpl in *.
      pose proof (memcompat1 CMatch) as Hcmpt1.
      get_mem_compatible.
      get_thread_mems.
      pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp _ thread_compat1) Hthread_mem1) as
          Hmem_equiv1.
      inversion Hlock_update_mem_strict_load. subst vload vstore.

      (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
      destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].

      (* tid < hb *)
      - pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1)) as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H3. (* Asm_match *)
        
        (*Destruct the values of the self simulation *)
        pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
        assert (Hinj':=Hinj).
        pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
        eapply sim_atx in Hinj'; eauto.
        2: { (*at_external*)
          erewrite restr_proof_irr.
          rewrite Hmem_equiv1; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

        (edestruct (acquire_step_diagram_self AsmSem)
           with (tid:=tid) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step & CMatch');
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + omega.
        + eassumption.
        + clean_proofs; eauto.
        + (*match_self*)
          econstructor.
          * eapply H3.
          * symmetry in Hmem_equiv1.
            assert (Hmem_equiv2: mem_equiv m2 (restrPermMap Hlt2)).
            { symmetry; eapply cur_equiv_restr_mem_equiv.
              clean_proofs; auto. }
            (* why can't you rewrite here? *)
            eapply proper_match_mem;
              try eassumption.
            -- reflexivity.
            -- erewrite <- (restr_proof_irr Hlt1).
               assumption.
        + exists e'. eexists. exists m2'.
          split ; [|split]; eauto.
          * clean_proofs; eauto.
            
      (* tid = hb *)
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
        (* remember (virtueLP angel) as virtueLP1. *) 
        rename Hat_external into Hat_external1.
        rename b into b1.
        rename Hstore into Hstore1.
        
        rewrite RPM in Hinterference1.
        symmetry in H0.
        clean_proofs.
        exploit acquire_step_diagram_compiled;
          try eapply Hthread_mem1;
          try eapply Hthread_mem2;
          try solve[eapply CMatch; eauto; try reflexivity];
          eauto; try reflexivity.
        + econstructor; eassumption.
        + subst virtueThread1; eassumption.
        + subst newThreadPerm1 virtueThread1; eassumption.
        + subst newThreadPerm1 virtueThread1; eassumption.
        + econstructor; eauto; simpl.
          * !goal(mem_interference m1 lev1 m1').
            rewrite self_restre_eq in Hinterference1; eauto.
          * !goal(mem_interference m2 lev2 m2'). 
            rewrite self_restre_eq in Hinterference2; eauto.
        + subst virtueThread1.  
          intros (?&?&?&?&?&?).
          do 3 eexists; repeat weak_split eauto.
          clear - H2.
          clean_proofs; eauto.
          
      (* tid > hb *)
      - pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
          as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H3. (* Clight_match *)
        
        (*Destruct the values of the self simulation *)
        pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
        assert (Hinj':=Hinj).
        pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
        eapply sim_atx in Hinj'; eauto.
        2: { (*at_external*)
          erewrite restr_proof_irr.
          rewrite Hmem_equiv1; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
        
        (edestruct (acquire_step_diagram_self CSem)
           with (tid:=tid) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step & CMatch');
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + omega.
        + eassumption.
        + instantiate(1:=m2); clear - Hthread_mem2.
          clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply H3.
          * symmetry in Hmem_equiv1.
            assert (Hmem_equiv2: mem_equiv m2 (restrPermMap Hlt2)).
            { symmetry; eapply cur_equiv_restr_mem_equiv.
              clean_proofs; auto. }
            (* why can't you rewrite here? *)
            eapply proper_match_mem;
              try eassumption.
            -- reflexivity.
            -- erewrite <- (restr_proof_irr Hlt1).
               assumption.
        + exists e'. eexists. exists m2'.
          simpl in *.
          split ; [|split]; eauto.
          * instantiate(1:= CMatch) in external_step.
            clear - external_step.
            clean_proofs; eauto.

            Unshelve.
            all: eauto.
    Qed. (* acquire_step_diagram *)
    
  End acquire.
End AcquireDiagrams.