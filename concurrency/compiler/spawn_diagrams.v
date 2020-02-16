

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





Section SpawnDiagrams.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  (* this modules hosts lemmas that depend on the Hybrid machine setup.*)

  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  (*Module MySimulationTactics:= SimulationTactics CC_correct Args.
  Import MySimulationTactics.
  Import MyConcurMatch.*)
  
  (*Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)). *)

  (*Lemmas about the calls: *)
  Notation vone:= (Vint Int.one).
  Notation vzero:= (Vint Int.zero).


  Section spawn.
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

    
    

    
    (* probably go to advanced permissions *)
    
   
    (* end of advanced_permissions's lemmas*)

    
    (*synchronisation_steps_semantics*)
    Lemma spawn_step_diagram_self Sem tid m1 m2:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
        virtue1 virtue_new1  cd
        (mu : meminj) (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb)))
        (cnt1 : ThreadPool.containsThread(Sem:=HybridSem _) st1 tid)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
        (b1 b2 : block) (ofs : int) delt arg
        (Hneq: tid <> hb )
        (Hinj_b : mu b1 = Some (b2, delt))
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        (Hvalid_pointer: Mem.perm m1 b1 (unsigned ofs) Max Nonempty)
        (Hnot_undef_arg: arg <> Vundef)
        
        (* Thread states *)
        (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
        (HState1: coerce_state_type _ sum_state1 th_state1  
                                    (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
        (HState2: coerce_state_type _ sum_state2 th_state2
                                    (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
        (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
        (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
        (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)

        
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        
        (Harg : val_inject (Mem.flat_inj (Mem.nextblock m1)) arg arg),
        let ThreadPerm1:= (computeMap_pair (getThreadR cnt1) virtue1) in
        let newThreadPerm1:= (computeMap_pair (pair0 empty_map) virtue_new1) in

        let st1':= (ThreadPool.updThread cnt1 (Kresume sum_state1 Vundef) ThreadPerm1) in
        let st1'':= (ThreadPool.addThread st1' (Vptr b1 ofs) arg newThreadPerm1) in
        forall (Hcmpt : mem_compatible  st1'' m1)
               (Hinv' : invariant st1'')
               (Hangel_bound: sub_map_pair virtue1 (snd (getMaxPerm m1)))
               (Hangel_bound_new : sub_map_pair virtue_new1 (snd (getMaxPerm m1)))
               (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
               (Hmatch_mem: match_mem mu m1 m2)
               (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                              Some (CREATE, (Vptr b1 ofs :: arg :: nil)%list))
               (Hjoin_angel: permMapJoin_pair newThreadPerm1 ThreadPerm1 (getThreadR cnt1)),

        exists evnt2 (st2'' : t) m2',
          let evnt:= build_spwan_event (b1, unsigned ofs)
                                       (fst virtue1)
                                       (fst virtue_new1)
                                       m1 in 
          concur_match cd mu st1'' m1 st2'' m2' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:=  (memcompat2 CMatch) in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true cnt2 Hcmpt2 st2'' m2' evnt2.
    Proof.
      
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      
      assert (Hmem_equiv1: mem_equiv m1 th_mem1).
      { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2 th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      
      set (ofs2      :=   add ofs (repr delt)).
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      assert (Heq:unsigned (add ofs (repr delt)) = unsigned ofs + delt).
      { eapply address_inject_max; eauto.
        simpl in Hat_external.
        instantiate(1:=Nonempty).
        rewrite <- Hmem_equiv1; auto. } 

      
      assert (Hinj: Mem.inject mu m1 m2).
      { rewrite Hmem_equiv1, Hmem_equiv2; auto. }

      eapply ssim_preserves_atx in Hat_external as 
          (arg2 & Hat_external2 & Hinj_args).
      2:{  inversion Amatch. constructor; eauto. }
      inv Hinj_args. inv H1. inv H3. inv H5.
      rename v' into arg2. unify_injection. rename b3 into b2.
      
      set (virtue2:=virtueThread_inject m2 mu virtue1).
      set (virtue_new2:=virtueThread_inject m2 mu virtue_new1).
      set (ThreadPerm2:= (computeMap_pair (getThreadR cnt2) virtue2)).
      set (newThreadPerm2:= (computeMap_pair (pair0 empty_map) virtue_new2)).
      
      set (st2' := updThread cnt2 (Kresume sum_state2 Vundef) ThreadPerm2).
      set (st2'' := addThread st2' (Vptr b2 ofs2) arg2 newThreadPerm2).


      remember (build_spwan_event (b2, unsigned ofs2)
                                  (fst virtue2)
                                  (fst virtue_new2)
                                  m2) as event2. 
      
      (* Instantiate some of the existensials *)

      assert (Hjoin_angel2: permMapJoin_pair
                              newThreadPerm2
                              ThreadPerm2
                              (getThreadR cnt2)).
      { eapply permMapJoin_pair_inject_spawn. 
        3:{ subst newThreadPerm1 ThreadPerm1; simpl; eauto. }
        - eapply Hangel_bound.
        - eapply Hangel_bound_new.
        - apply Hinj_th.
        - apply Hinj_lock.
        - eapply full_inject_dmap_pair.
          + apply CMatch.
          + apply join_dmap_valid_pair.
            eapply Hangel_bound.
        - eapply full_inject_dmap_pair.
          + apply CMatch.
          + apply join_dmap_valid_pair.
            eapply Hangel_bound_new. }


      forward_state_cmpt_all.
      rename Hcmpt_update into Hcmpt2'.
      rename Hcmpt_update0 into Hcmpt1'.

      assert (Hlt1': permMapLt_pair (ThreadPerm1) (getMaxPerm m1)) by
          solve_permMapLt_pair.
      destruct Hlt1' as [Hlt1' Hlt1_lk']. 
      assert (Hlt2': permMapLt_pair (ThreadPerm2) (getMaxPerm m2)) by
          solve_permMapLt_pair.
      destruct Hlt2' as [Hlt2' Hlt2_lk'].
      assert (Hlt1_new: permMapLt_pair (newThreadPerm1) (getMaxPerm m1)) by
          solve_permMapLt_pair.
      destruct Hlt1_new as [Hlt1_new Hlt1_lk_new]. 
      assert (Hlt2_new: permMapLt_pair (newThreadPerm2) (getMaxPerm m2)) by
          solve_permMapLt_pair.
      destruct Hlt2_new as [Hlt2_new Hlt2_lk_new].
      simpl in *.

      assert (Hmi_perm_perm_new: mi_perm_perm_pair mu newThreadPerm1 newThreadPerm2).
      { eapply computeMap_mi_perm_perm_perfect_pair.
        - eapply maps_no_overlap_Lt_pair; eauto.
          + eapply no_overlap_mem_perm, Hinj.
          + exact (empty_LT_pair _).
          + eapply Hangel_bound_new.
        - exact (mi_perm_perm_empty_pair _).
        - eapply inject_perm_perfect_image_dmap_pair; eauto.
          + eapply sub_map_implication_dmap_pair; eauto.
          + eapply full_inject_dmap_pair; eauto.
            eapply CMatch.
            eapply join_dmap_valid_pair, Hangel_bound_new. }
      
      assert (Hmi_perm_perm: mi_perm_perm_pair mu ThreadPerm1 ThreadPerm2).
      { eapply computeMap_mi_perm_perm_perfect_pair.
        - eapply maps_no_overlap_Lt_pair; eauto.
          + eapply no_overlap_mem_perm, Hinj.
          + eapply CMatch.
          + eapply Hangel_bound.
        - split; eapply mi_inj_mi_perm_perm_Cur_backwards;
            eauto.
          + apply Hinj_th.
          + apply Hinj_lock.
        - eapply inject_perm_perfect_image_dmap_pair; eauto.
          + eapply sub_map_implication_dmap_pair; eauto.
          + eapply full_inject_dmap_pair; eauto.
            eapply CMatch.
            eapply join_dmap_valid_pair, Hangel_bound. }

      
      assert (Hmemval:
                mi_memval_perm_pair mu ThreadPerm1
                                    (Mem.mem_contents m1) (Mem.mem_contents m2)).
      { eapply mi_memval_perm_computeMap_Lt_pair.
        - split; eapply mi_inj_mi_memval_perm_backwards.
          + eapply Hinj_th.
          + eapply Hinj_lock.  
        - eapply permMapJoin_lt_pair2; eauto. }
      
      assert (Hmemval_new:
                mi_memval_perm_pair mu newThreadPerm1
                                    (Mem.mem_contents m1) (Mem.mem_contents m2)).
      { eapply mi_memval_perm_computeMap_Lt_pair.
        - split; eapply mi_inj_mi_memval_perm_backwards.
          + eapply Hinj_th.
          + eapply Hinj_lock.  
        - eapply permMapJoin_lt_pair2, permMapJoin_pair_comm; eauto. }

      assert (Hmi_perm_inv_perm: (mi_perm_inv_perm_pair
                                    mu ThreadPerm1
                                    ThreadPerm2 m1)) by
          (eapply mi_perm_inv_perm_compute_pair; eauto).
      
      assert (Hmi_perm_inv_perm_new: (mi_perm_inv_perm_pair
                                        mu newThreadPerm1
                                        newThreadPerm2 m1)).
      { eapply mi_perm_inv_perm_compute_pair; eauto;
          eapply inject_empty; eauto. }

      assert (Hinj': Mem.inject mu (restrPermMap Hlt1') (restrPermMap Hlt2')).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm.
        - apply Hmemval.
        - apply Hmi_perm_inv_perm. }
      
      assert (Hinj1_lk': Mem.inject mu (restrPermMap Hlt1_lk') (restrPermMap Hlt2_lk')).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm.
        - apply Hmemval.
        - apply Hmi_perm_inv_perm. }

      assert (Hinj_new': Mem.inject mu (restrPermMap Hlt1_new) (restrPermMap Hlt2_new)).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm_new.
        - apply Hmemval_new.
        - apply Hmi_perm_inv_perm_new. }
      
      assert (Hinj_new_lk': Mem.inject mu (restrPermMap Hlt1_lk_new) (restrPermMap Hlt2_lk_new)).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm_new.
        - apply Hmemval_new.
        - apply Hmi_perm_inv_perm_new. } 

      
      exists event2, st2'', m2.  
      repeat weak_split. (* 4 goal*)
      - !goal(concur_match _ _ _ _ _ _ ).
        
        unshelve eapply (concur_match_add_thread hb tid mu cd st1)
          with (Hlt1:=Hlt1')
               (Hlt2:=Hlt2')
               (Hlt1_lk:=Hlt1_lk')
               (Hlt2_lk:=Hlt2_lk')
               (Hlt1_new:=Hlt1_new)
               (Hlt2_new:=Hlt2_new)
               (Hlt1_lk_new:=Hlt1_lk_new)
               (Hlt2_lk_new:=Hlt2_lk_new); eauto;
          subst ThreadPerm1 ThreadPerm2; simpl.
        + !goal(perm_surj _ _ _).
          eapply perm_surj_compute.
          * eapply CMatch.
          * eapply inject_perm_perfect_image_dmap; eauto.
            -- eapply sub_map_implication_dmap; eapply Hangel_bound.
            -- eapply full_inject_dmap.
               ++ eapply CMatch.
               ++ eapply join_dmap_valid; eapply Hangel_bound.
        + !goal(perm_surj _ _ _).
          eapply perm_surj_compute.
          * simpl. 
            exact (perm_surj_empty _).
          * eapply inject_perm_perfect_image_dmap; eauto.
            -- eapply sub_map_implication_dmap; eapply Hangel_bound_new.
            -- eapply full_inject_dmap.
               ++ eapply CMatch.
               ++ eapply join_dmap_valid; eapply Hangel_bound_new.
        + !goal(invariant _).
          eapply invariant_add_thread; eauto.
          reflexivity.
          apply CMatch.
        + !context_goal one_thread_match. shelve.
          
      - subst event2. repeat econstructor; eauto.
      - !goal (syncStep _ _ _ _ _ _).
        
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)

        (* set the event in the right shape *)
        match goal with
          |- syncStep _ _ _ _ _ ?ev =>
          match type of ev with
            ?T => evar (ev_new: T);
                    replace ev with ev_new; unfold ev_new
          end
        end.

        eapply step_create;
          match goal with
            |- val_inject _ _ _ => idtac
          | |- _ => eauto; try reflexivity
          end.
        + eapply inject_virtue_sub_map_pair'; eauto. (*
                                                      * apply Hinj_lock.
                                                      * apply Hangel_bound. *)
        + eapply inject_virtue_sub_map_pair'; eauto. (*
                                                      * apply Hinj_lock.
                                                      * apply Hangel_bound_new. *)
        + eapply CMatch.
        + !goal (semantics.at_external _ _ _ = Some (CREATE, _)).
          { eapply at_external_sum_sem; eauto. }
        + !goal(val_inject  _ arg2 arg2).
          eapply val_inject_mem_inject; eauto.
        + { simpl. subst ThreadPerm2 newThreadPerm2 virtue2 virtue_new2.
            eapply Hjoin_angel2. }
        + { simpl. subst ThreadPerm2 newThreadPerm2 virtue2 virtue_new2.
            eapply Hjoin_angel2. }
        + subst event2 virtue2 virtue_new2. unfold build_spwan_event.
          reflexivity.

          Unshelve.
          all: try apply empty_LT.
          
          { !context_goal one_thread_match. (*shelved above.*)
            
            destruct (lt_eq_lt_dec tid hb) as [[Htid_neq'|Htid_neq']|Htid_neq'].
            - (* (tid < hb)%nat *)
              
              unshelve (eapply CMatch in Htid_neq' as Hthmatch); simpl;
                eauto.
              (*  + rewrite getMax_restr; eauto.
              + rewrite getMax_restr; eauto.*)
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H5; simpl in *.
                
                econstructor 2; eauto. simpl.
                do 2 econstructor; eauto.
                
                
                econstructor; eauto.
                * rewrite getCur_restr.
                  eapply perm_image_injects_map.
                  eapply full_inject_map; eauto.
                  eapply CMatch.
                  -- eapply map_valid_Lt; eauto.
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
                     eapply CMatch.
                     eapply join_dmap_valid, Hangel_bound.
                     
            - subst tid; congruence.
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch); simpl;
                eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H5; simpl in *.

                econstructor 1; eauto.
                do 2 econstructor; eauto.

                
                econstructor; eauto.
                * rewrite getCur_restr.
                  eapply perm_image_injects_map.
                  eapply full_inject_map; eauto.
                  -- apply CMatch.
                  -- eapply map_valid_Lt; eauto.
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
                     apply CMatch.
                     eapply join_dmap_valid, Hangel_bound.

                     Unshelve.
                     all: simpl;eauto. }
          
    Qed.
    
    Lemma spawn_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in
      forall m1 m2 m10 virtue1 virtue_new1  cd
        (mu : meminj) (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb)))
        (cnt1 : ThreadPool.containsThread(Sem:=HybridSem _) st1 hb)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 hb)
        (b1 : block) (ofs : int) arg
        Hcnt1 Hcnt2 code1 code2
        (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
        (CMatch: concur_match (Some cd) mu st1 m1 st2 m2)
        (Hvalid_pointer: Mem.perm m1 b1 (unsigned ofs) Max Nonempty)
        (Hnot_undef_arg: arg <> Vundef)
        
        (* Thread states *)
        (Hget_th_state1: @getThreadC _ _ hb st1 cnt1 = Kblocked (SST code1))
        (Hget_th_state2: @getThreadC _ _ hb st2 cnt2 = Kblocked (TST code2))

        
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        
        (Harg : val_inject (Mem.flat_inj (Mem.nextblock m1)) arg arg),
        let ThreadPerm1:= (computeMap_pair (getThreadR cnt1) virtue1) in
        let newThreadPerm1:= (computeMap_pair (pair0 empty_map) virtue_new1) in

        let st1':= (ThreadPool.updThread cnt1 (Kresume (SST code1) Vundef) ThreadPerm1) in
        let st1'':= (ThreadPool.addThread st1' (Vptr b1 ofs) arg newThreadPerm1) in
        forall (Hcmpt : mem_compatible  st1'' m1)
          (Hinv' : invariant st1'')
          (Hangel_bound: pair21_prop sub_map virtue1 (snd (getMaxPerm m1)))
          (Hangel_bound_new : pair21_prop sub_map virtue_new1 (snd (getMaxPerm m1)))
          (Hat_external: semantics.at_external hybrid_sem (SST code1) m1 =
                         Some (CREATE, (Vptr b1 ofs :: arg :: nil)%list))
          (Hjoin_angel: permMapJoin_pair newThreadPerm1 ThreadPerm1 (getThreadR cnt1))
          (Hstrict: strict_evolution_diagram cd mu code1 m10 m1 code2 m2),

        exists evnt2 (st2'' : t) m2',
          let evnt:= build_spwan_event (b1, unsigned ofs)
                                       (fst virtue1)
                                       (fst virtue_new1)
                                       m1 in 
          concur_match (Some cd) mu st1'' m1 st2'' m2' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:=  (memcompat2 CMatch) in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true cnt2 Hcmpt2 st2'' m2' evnt2.
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
      
      
      
      (** * 1. Set all the at_externals for LEFT diagram m1 m1' m2 m2' *)
      left_diagram.
      
      set (virtue2:=virtueThread_inject m2 mu virtue1).
      set (virtue_new2:=virtueThread_inject m2 mu virtue_new1).
      set (ThreadPerm2:= (computeMap_pair (getThreadR Hcnt2) virtue2)).
      set (newThreadPerm2:= (computeMap_pair (pair0 empty_map) virtue_new2)).
      set (ofs2:= (add ofs (repr delta))).
      set (st2' := updThread Hcnt2 (Kresume (TST code2) Vundef) ThreadPerm2).
      set (st2'' := addThread st2' (Vptr b2 ofs2) arg0 newThreadPerm2).
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      assert (Heq:unsigned (add ofs (repr delta)) = unsigned ofs + delta).
      { eapply address_inject_max; eauto. } 

      
      
      remember (build_spwan_event (b2, unsigned ofs2)
                                  (fst virtue2)
                                  (fst virtue_new2)
                                  m2) as event2. 
      
      assert (Hjoin_angel2: permMapJoin_pair
                              newThreadPerm2
                              ThreadPerm2
                              (getThreadR Hcnt2)).
      {
        eapply permMapJoin_pair_inject_spawn. 
        3:{ subst newThreadPerm1 ThreadPerm1; simpl; eauto. }
        - eapply Hangel_bound.
        - eapply Hangel_bound_new.
        - subst; apply Hinj_th.
        - subst; apply Hinj_lock.
        - eapply full_inject_dmap_pair.
          + apply CMatch.
          + apply join_dmap_valid_pair.
            eapply Hangel_bound.
        - eapply full_inject_dmap_pair.
          + apply CMatch.
          + apply join_dmap_valid_pair.
            eapply Hangel_bound_new. }
      
      forward_state_cmpt_all.
      rename Hcmpt_update into Hcmpt2'.
      rename Hcmpt_update0 into Hcmpt1'.

      assert (Hlt1': permMapLt_pair (ThreadPerm1) (getMaxPerm m1)) by
          solve_permMapLt_pair.
      destruct Hlt1' as [Hlt1' Hlt1_lk']. 
      assert (Hlt2': permMapLt_pair (ThreadPerm2) (getMaxPerm m2)) by
          solve_permMapLt_pair.
      destruct Hlt2' as [Hlt2' Hlt2_lk'].
      assert (Hlt1_new: permMapLt_pair (newThreadPerm1) (getMaxPerm m1)) by
          solve_permMapLt_pair.
      destruct Hlt1_new as [Hlt1_new Hlt1_lk_new]. 
      assert (Hlt2_new: permMapLt_pair (newThreadPerm2) (getMaxPerm m2)) by
          solve_permMapLt_pair.
      destruct Hlt2_new as [Hlt2_new Hlt2_lk_new].
      simpl in *.

      assert (Hmi_perm_perm_new: mi_perm_perm_pair mu newThreadPerm1 newThreadPerm2).
      { eapply computeMap_mi_perm_perm_perfect_pair.
        - eapply maps_no_overlap_Lt_pair; eauto.
          + eapply no_overlap_mem_perm, Hinj'.
          + exact (empty_LT_pair _).
          + eapply Hangel_bound_new.
        - exact (mi_perm_perm_empty_pair _).
        - eapply inject_perm_perfect_image_dmap_pair; eauto.
          + eapply sub_map_implication_dmap_pair; eauto.
          + eapply full_inject_dmap_pair; eauto.
            eapply CMatch.
            eapply join_dmap_valid_pair, Hangel_bound_new. }
      
      assert (Hmi_perm_perm: mi_perm_perm_pair mu ThreadPerm1 ThreadPerm2).
      { eapply computeMap_mi_perm_perm_perfect_pair.
        - eapply maps_no_overlap_Lt_pair; eauto.
          + eapply no_overlap_mem_perm, Hinj'.
          + eapply CMatch.
          + eapply Hangel_bound.
        - split; eapply mi_inj_mi_perm_perm_Cur_backwards;
            eauto.
          + subst; apply Hinj_th.
          + subst; apply Hinj_lock.
        - eapply inject_perm_perfect_image_dmap_pair; eauto.
          + eapply sub_map_implication_dmap_pair; eauto.
          + eapply full_inject_dmap_pair; eauto.
            eapply CMatch.
            eapply join_dmap_valid_pair, Hangel_bound. }

      
      assert (Hmemval:
                mi_memval_perm_pair
                  mu ThreadPerm1
                  (Mem.mem_contents m1) (Mem.mem_contents m2)).
      { eapply mi_memval_perm_computeMap_Lt_pair.
        - split; eapply mi_inj_mi_memval_perm_backwards.
          + subst; eapply Hinj_th.
          + subst; eapply Hinj_lock.  
        - eapply permMapJoin_lt_pair2; eauto. }
      
      assert (Hmemval_new:
                mi_memval_perm_pair mu newThreadPerm1
                                    (Mem.mem_contents m1) (Mem.mem_contents m2)).
      { eapply mi_memval_perm_computeMap_Lt_pair.
        - split; eapply mi_inj_mi_memval_perm_backwards.
          + subst; eapply Hinj_th.
          + subst; eapply Hinj_lock.  
        - eapply permMapJoin_lt_pair2, permMapJoin_pair_comm; eauto. }

      assert (Hmi_perm_inv_perm: (mi_perm_inv_perm_pair
                                    mu ThreadPerm1
                                    ThreadPerm2 m1)) by
          (eapply mi_perm_inv_perm_compute_pair; subst; eauto).
      
      assert (Hmi_perm_inv_perm_new: (mi_perm_inv_perm_pair
                                        mu newThreadPerm1
                                        newThreadPerm2 m1)).
      { eapply mi_perm_inv_perm_compute_pair; subst; eauto;
          eapply inject_empty; eauto. }

      assert (Hinj'': Mem.inject mu
                                 (restrPermMap Hlt1')
                                 (restrPermMap Hlt2')).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm.
        - apply Hmemval.
        - apply Hmi_perm_inv_perm. }
      
      assert (Hinj1_lk': Mem.inject mu (restrPermMap Hlt1_lk') (restrPermMap Hlt2_lk')).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm.
        - apply Hmemval.
        - apply Hmi_perm_inv_perm. }

      assert (Hinj_new': Mem.inject mu (restrPermMap Hlt1_new) (restrPermMap Hlt2_new)).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm_new.
        - apply Hmemval_new.
        - apply Hmi_perm_inv_perm_new. }
      
      assert (Hinj_new_lk': Mem.inject mu (restrPermMap Hlt1_lk_new) (restrPermMap Hlt2_lk_new)).
      { apply inject_restr; simpl; eauto.
        - apply Hmi_perm_perm_new.
        - apply Hmemval_new.
        - apply Hmi_perm_inv_perm_new. } 
      
      
      
      (** * 4. Finally we proceed with the goal: existentials. *)
      
      exists event2, st2'', m2.  
      repeat weak_split. (* 4 goal*)
      - !goal(concur_match _ _ _ _ _ _ ).
        
        unshelve eapply (concur_match_add_thread hb hb mu _ st1)
          with (Hlt1:=Hlt1')
               (Hlt2:=Hlt2')
               (Hlt1_lk:=Hlt1_lk')
               (Hlt2_lk:=Hlt2_lk')
               (Hlt1_new0:=Hlt1_new)
               (Hlt2_new0:=Hlt2_new)
               (Hlt1_lk_new0:=Hlt1_lk_new)
               (Hlt2_lk_new0:=Hlt2_lk_new); eauto;
          subst ThreadPerm1 ThreadPerm2; simpl.
        + !goal(perm_surj _ _ _).
          eapply perm_surj_compute.
          * eapply CMatch.
          * eapply inject_perm_perfect_image_dmap; eauto.
            -- eapply sub_map_implication_dmap; eapply Hangel_bound.
            -- eapply full_inject_dmap.
               ++ eapply CMatch.
               ++ eapply join_dmap_valid; eapply Hangel_bound.
        + !goal(perm_surj _ _ _).
          eapply perm_surj_compute.
          * simpl. 
            exact (perm_surj_empty _).
          * eapply inject_perm_perfect_image_dmap; eauto.
            -- eapply sub_map_implication_dmap; eapply Hangel_bound_new.
            -- eapply full_inject_dmap.
               ++ eapply CMatch.
               ++ eapply join_dmap_valid; eapply Hangel_bound_new.
        + !goal(invariant _).
          eapply invariant_add_thread; eauto.
          reflexivity.
          apply CMatch.
        + !context_goal one_thread_match. shelve.
        + eauto.
          eapply val_inject_incr.
          eapply evolution_inject_incr; eauto.
          eauto.
      - subst event2. repeat econstructor; eauto.
      - !goal (syncStep _ _ _ _ _ _).
        
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)

        subst event2 ; unfold build_release_event.

        (* set the event in the right shape *)
        match goal with
          |- syncStep _ _ _ _ _ ?ev =>
          match type of ev with
            ?T => evar (ev_new: T);
                   replace ev with ev_new; unfold ev_new
          end
        end.
        
        eapply step_create;
          match goal with
            |- val_inject _ _ _ => idtac
          | |- _ => eauto; try reflexivity
          end.
        + eapply inject_virtue_sub_map_pair'; eauto.
        + eapply inject_virtue_sub_map_pair'; eauto.
        + eapply CMatch.
        + !goal (semantics.at_external _ _ _ = Some (CREATE, _)).
          { simpl. subst ofs2.
            rewrite self_restre_eq; eauto. }
        + !goal(val_inject  _ arg0 arg0).
          eapply val_inject_mem_inject; eauto.
          eapply val_inject_incr.
          eapply evolution_inject_incr; eauto.
          assumption.
        + { simpl. subst ThreadPerm2 newThreadPerm2 virtue2 virtue_new2.
            eapply Hjoin_angel2. }
        + { simpl. subst ThreadPerm2 newThreadPerm2 virtue2 virtue_new2.
            eapply Hjoin_angel2. }
        + subst virtue2 virtue_new2. unfold build_spwan_event.
          reflexivity.

          Unshelve.
          all: eauto.
          all: try apply empty_LT.
          
          { (*Shelved above*)
            !context_goal one_thread_match.
            

            (** *0 . Simplifications to do outside the l emma*)

            set (ThreadPerm1:=computeMap_pair (getThreadR Hcnt1) virtue1).

            
            (* assert (Hext_rel1': extcall_spawn
                                  (Genv.globalenv (Ctypes.program_of_program C_program)) 
                                  (Vptr b1 ofs :: nil) m10
                                  (Events.Event_acq_rel lev1 (fst virtue1) lev1' :: nil)
                                  Vundef m1''').
            { econstructor; try eassumption.
              econstructor; eauto.
            } 
            assert (Hext_rel1: Events.external_call CREATE
                                                    (Clight.genv_genv Clight_g)
                                                    (Vptr b1 ofs :: nil)
                                                    m1 rel_trace Vundef m1''').
            { simpl; rewrite ReleaseExists.
              subst rel_trace dpm1; eauto. } *)
            
            eapply build_match_compiled; auto.
            subst st1' st2' st1'' st2''.
            clean_proofs.
            
            eapply CThread_Resume.
            intros j'' s1' m1''' m2''' lev1' lev2'.
            intros Hstrict_evolution' (*Hincr'*) Hinterference1' Hinterference2'
                   Hafter_ext.
            
            eapply large_external_diagram; try reflexivity; eauto;
              swap 4 5.
            - exact spawn_is_consec.
            - exact spawn_doesnt_return.
            - reflexivity.
            - simpl.
              rewrite SpawnExists.
              econstructor; try eassumption.
              (*HERE CHANGED SPAWN*)
              
              unshelve erewrite restre_equiv_eq by (
              rewrite Hthread_mem1; reflexivity).
              rewrite <- Hthread_mem1; auto.
              simpl. econstructor; eauto.
            - eapply virtue_inject_bounded.
              + eapply Hinj'0.
              + eapply full_inject_dmap; eauto.
                eapply CMatch.
                apply join_dmap_valid, Hangel_bound.
              + apply Hangel_bound.
              + apply Hinj'0.
              + eapply Hinj'0.
            - simpl.
              rewrite SpawnExists.
              econstructor; try eassumption.
              (*HERE CHANGED SPAWN*)
              
              unshelve erewrite restre_equiv_eq by (
              rewrite Hthread_mem2; reflexivity).
              rewrite <- Hthread_mem2; auto.
              simpl. econstructor; eauto.
            - apply (interference_consecutive_until _ _ _  Hinterference2).
            - apply (interference_consecutive_until _ _ _ Hinterference2').
              
          }
    Qed.
    
    Lemma spawn_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall virtue1 virtue_new1 (m1 m2 : mem) (tid : nat) cd
        (mu : meminj) (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb)))
        (cnt1 : ThreadPool.containsThread(Sem:=HybridSem _) st1 tid)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
        (c : semC) (b : block) (ofs : int) arg
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        (Hvalid_pointer: Mem.perm m1 b (unsigned ofs) Max Nonempty)
        (Hnot_undef_arg: arg <> Vundef)
        (Hcode: getThreadC cnt1 = Kblocked c)
        (Harg : val_inject (Mem.flat_inj (Mem.nextblock m1)) arg arg),
        let ThreadPerm1:= (computeMap_pair (getThreadR cnt1) virtue1) in
        let newThreadPerm1:= (computeMap_pair (pair0 empty_map) virtue_new1) in

        let st1':= (ThreadPool.updThread cnt1 (Kresume c Vundef) ThreadPerm1) in
        let st1'':= (ThreadPool.addThread st1' (Vptr b ofs) arg newThreadPerm1) in
        forall (Hcmpt : mem_compatible  st1'' m1)
          (Hinv' : invariant st1'')
          (Hangel_bound: pair21_prop sub_map virtue1 (snd (getMaxPerm m1)))
          (Hangel_bound_new : pair21_prop sub_map virtue_new1 (snd (getMaxPerm m1)))
          (Hat_external: semantics.at_external hybrid_sem c m1 =
                         Some (CREATE, Vptr b ofs :: arg :: nil))
          (Hjoin_angel: permMapJoin_pair newThreadPerm1 ThreadPerm1 (getThreadR cnt1)),

        exists evnt2 (st2'' : t) m2',
          let evnt:= build_spwan_event (b, unsigned ofs)
                                       (fst virtue1)
                                       (fst virtue_new1)
                                       m1 in 
          concur_match cd mu st1'' m1 st2'' m2' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:=  (memcompat2 CMatch) in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true cnt2 Hcmpt2 st2'' m2' evnt2.
    Proof.
      intros; simpl in *.
      get_mem_compatible.
      get_thread_mems.
      clean_proofs.

      pose proof (cur_equiv_restr_mem_equiv
                    _ _ (th_comp thread_compat1) Hthread_mem1) as
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
          simpl. replace (restrPermMap Hlt1) with m1; eauto.
          rewrite self_restre_eq; eauto.
        } clear sim_atx.
        destruct Hinj' as (args2 & Hinj_b & Hat_external2); eauto.
        inversion Hinj_b as [| ? ? ? ? AA BB CC]; subst; clear Hinj_b.
        inversion AA as [ | | | | ? ? ? ? ? Hinj_b  | ]; subst.
        inversion BB as [| ? ? ? ? Hargs_inj _ CC]; subst; clear BB.

        clean_proofs.
        do 2 rewrite self_restre_eq in * by eassumption.
        
        (edestruct (spawn_step_diagram_self AsmSem tid m1 m2) as
            (e' & st2' & m2' &
             CMatch' & Htrace_inj & external_step); eauto;
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + omega.
        + exists e'; eexists; exists m2'.
          subst_set.
          repeat weak_split eauto.
          clean_proofs; eauto.
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
        rename Hat_external into Hat_external1.
        rename b into b1.
        (* rename Hstore into Hstore1. *)
        
        symmetry in H0.
        clean_proofs.
        
        exploit (spawn_step_diagram_compiled m1' m2');
          (* try eapply CMatch; *)
          eauto; try reflexivity.
        + econstructor; eassumption.
        + econstructor; eauto.
          * !goal(mem_interference m1 lev1 m1').
            rewrite self_restre_eq in Hinterference1; eauto.
          * !goal(mem_interference m2 lev2 m2').
            rewrite self_restre_eq in Hinterference2; eauto.
        + simpl; clean_proofs.
          normal; eauto.
          
      - (* (hb < tid) *)
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
          simpl. replace (restrPermMap Hlt1) with m1; eauto.
          rewrite self_restre_eq; eauto.
        } clear sim_atx.
        destruct Hinj' as (args2 & Hinj_b & Hat_external2); eauto.
        inversion Hinj_b as [| ? ? ? ? AA BB CC]; subst; clear Hinj_b.
        inversion AA as [ | | | | ? ? ? ? ? Hinj_b  | ]; subst.
        inversion BB as [| ? ? ? ? Hargs_inj _ CC]; subst; clear BB.

        clean_proofs.
        do 2 rewrite self_restre_eq in * by eassumption.
        
        (edestruct (spawn_step_diagram_self CSem tid m1 m2) as
            (e' & st2' & m2' &
             CMatch' & Htrace_inj & external_step); eauto;
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + omega.
        + exists e'; eexists; exists m2'.
          subst_set.
          repeat weak_split eauto.
          clean_proofs; eauto.


          Unshelve.
          all: eauto.
          
    Qed.

    (** * Here be dragons  *)

    
  End spawn.
End SpawnDiagrams.