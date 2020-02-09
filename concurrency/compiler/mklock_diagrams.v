

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





Section MklockDiagrams.
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
  
  Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).

  (*Lemmas about the calls: *)
  Notation vone:= (Vint Int.one).
  Notation vzero:= (Vint Int.zero).


  
  Section mklock.
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

    Lemma make_step_diagram_self Sem tid: (*5336*) 
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
        (st1 : mach_state hb) (st2 : mach_state (S hb))
        (m1 m1' m2 : mem) (mu : meminj) i b1 b2 ofs delt
        (Htid_neq: tid <> hb)
        (Hinj_b : mu b1 = Some (b2, delt)) new_perms1 new_perms2
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

        (* The following two things are not needed *)
        (HH1: set_new_mems b1 (unsigned ofs) (getThreadR cnt1) LKSIZE_nat new_perms1)
        (HH1: set_new_mems b2 (unsigned ofs+delt) (getThreadR cnt2) LKSIZE_nat new_perms2)
        
        (* angel, lock permissions and new thread permissions *)
        (HisLock: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = None )
        (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2)),
        let Hcmpt2:= memcompat2 CMatch in
        forall (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
          (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                         Some (MKLOCK, (Vptr b1 ofs :: nil)%list))
          (Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1 m1' vzero),
          let evnt1:= Events.mklock (b1, unsigned ofs) in
          exists event2 (m2' : mem),
            let st2':= fullThreadUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                        (new_perms2, pair0 empty_map) (b2, unsigned ofs + delt) in
            match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
            inject_sync_event mu evnt1 event2 /\
            syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2 /\
            let st1':= fullThreadUpdate st1 tid cnt1 (Kresume sum_state1 Vundef)
                                        (new_perms1, pair0 empty_map) (b1, unsigned ofs) in
            concur_match i mu st1' m1' st2' m2'.
    Proof. (* 5374 - 5336 = 38 *)
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.

      assert (Hmem_equiv1: mem_equiv m1 th_mem1).
      { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2 th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      
      (* Inject the loads/stores/mem_range*)
      unshelve (exploit lock_update_mem_strict_inject;
                try apply Hlock_update_mem_strict;
                eauto; try (eapply CMatch; eauto)); eauto.
      rewrite Hmem_equiv1; assumption.
      intros (m2'&Hlock_update_mem_strict2&Hinj2).
      
      assert (Hmax_equiv: Max_equiv m1 m1')
        by (eapply lock_update_mem_strict_Max_equiv; eassumption).
      assert (Hmax_equiv2: Max_equiv m2 m2').
      { etransitivity; swap 1 2. 
        eapply lock_update_mem_strict_Max_equiv; eassumption.
        subst th_mem2; simpl.
        symmetry. eapply restr_Max_equiv. }

      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      exploit address_inj_lock_update;
        try apply Hlock_update_mem_strict; eauto; intros Heq.
      
      assert (Hinj: Mem.inject mu m1 m2).
      { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
      
      remember (Events.mklock (b2, unsigned ofs + delt ))
        as event2. 

      
      assert (ThreadPool.lockRes st2 (b2, unsigned ofs + delt) = None).
      { destruct_lhs; eauto.
        eapply INJ_lock_permissions_preimage in Heqo; eauto. normal_hyp.
        destruct (peq x0 b1).
        - subst; unify_injection.  move HisLock at bottom.
          assert (x1 = unsigned ofs) by omega.
          subst x1. rewrite HisLock in H0. congruence.
        - eapply writable_locks in H0; eauto.
          exploit Mem.mi_no_overlap; try eapply n;
            swap 1 5; first [exact H|exact Hinj_b|idtac].
          + eapply lock_update_mem_permMapLt_range_Max in Hlock_update_mem_strict.
            eapply perm_order_trans211.
            move Hlock_update_mem_strict at bottom.
            rewrite_getPerm.
            eapply Hlock_update_mem_strict.
            instantiate(1:=unsigned ofs).
            pose proof LKSIZE_pos; omega.
            constructor.
          + eapply Mem.perm_implies; eauto.
            constructor.
          + eauto.
          + intros [? | ?]; congruence. }

      
      assert (Hlt1': permMapLt_pair (new_perms1) (getMaxPerm m1')).
      { inv Hlock_update_mem_strict.
        unfold Max_equiv in *. rewrite <- Hmax_equiv.
        eapply permMapLt_pair_trans211 with (pb:=(getCurPerm m1,getCurPerm m1)).
        - split; simpl.
          + eapply set_new_mems_LT1; eauto. symmetry; eauto.
          + eapply set_new_mems_LT2; eauto. symmetry; eauto.
        - split; apply mem_cur_lt_max. }
      destruct Hlt1' as [Hlt11' Hlt12'].
      assert (Hlt2: permMapLt_pair new_perms2 (getMaxPerm m2)).
      { inv Hlock_update_mem_strict2; simpl in Haccess.
        rewrite self_restre_eq in Haccess; eauto.
        eapply permMapLt_pair_trans211 with (pb:=(getCurPerm m2,getCurPerm m2)).
        - split; simpl.
          + eapply set_new_mems_LT1; eauto. symmetry; eauto.
          + eapply set_new_mems_LT2; eauto. symmetry; eauto.
        - split; apply mem_cur_lt_max. }
      assert (Hlt2': permMapLt_pair (new_perms2) (getMaxPerm m2'))
        by (unfold Max_equiv in *; rewrite <- Hmax_equiv2; eauto ).
      destruct Hlt2' as [Hlt21' Hlt22'].
      set (st1':=(fullThreadUpdate st1 tid cnt1 (Kresume sum_state1 Vundef)
                                   (new_perms1, pair0 empty_map) (b1, unsigned ofs))).
      set (st2':=(fullThreadUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                   (new_perms2, pair0 empty_map) (b2, unsigned ofs + delt))).
      
      assert (Mem.nextblock m1 = Mem.nextblock m1').
      { inv Hlock_update_mem_strict.
        symmetry; eapply Mem.nextblock_store; eauto. }
      assert (Hm2_eq: th_mem2 = m2).
      { subst th_mem2. simpl; rewrite self_restre_eq; eauto.  }
      assert (Mem.nextblock m2 = Mem.nextblock m2').
      { inv Hlock_update_mem_strict2.
        symmetry; eapply Mem.nextblock_store; eauto.
        rewrite <- Hm2_eq; eauto. }
      
      assert (Hinj1': Mem.inject mu (restrPermMap Hlt11') (restrPermMap Hlt21')).
      { destruct new_perms1,new_perms2; simpl in *.
        inv Hlock_update_mem_strict; inv Hlock_update_mem_strict2.
        eapply set_new_mems_inject1; eauto.
        - eapply store_inject_other_perm; eauto.
          rewrite <- mem_is_restr_eq; eauto.
        - eapply store_inject_other_perm; eauto.
          rewrite <- mem_is_restr_eq; eauto. }
      assert (Hinj2': Mem.inject mu (restrPermMap Hlt12') (restrPermMap Hlt22')).
      { destruct new_perms1,new_perms2; simpl in *.
        inv Hlock_update_mem_strict; inv Hlock_update_mem_strict2.
        eapply set_new_mems_inject; eauto.
        - eapply store_inject_other_perm; eauto.
          rewrite <- mem_is_restr_eq; eauto.
        - eapply store_inject_other_perm; eauto.
          rewrite <- mem_is_restr_eq; eauto. }
      forward_cmpt_all.
      
      (* Instantiate some of the existensials *)
      exists event2; exists m2'.  
      repeat weak_split. (* 4 goal*)
      
      - !goal(match_self _ _ _ _ _ _).
        inversion Amatch. constructor; eassumption.
        
      - !goal(inject_sync_event mu evnt1 event2).
        subst event2; do 2 econstructor; auto. assumption.
        
      - !goal (syncStep _ _ _ _ _ _).
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)
        subst event2.
        rewrite <-  Heq.

        (*Prove that the new ThreadVirtue Joins in the right way:
                old_thread "+" delta_map = new_thread.
         *)
        inversion Hlock_update_mem_strict2 as [vstore
                                                 lock_mem_lt2 
                                                 Hstore2];
          subst vstore.

        (* exploit INJ_lock_permissions_image; eauto.
          intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2). *)
        subst st2'.
        eapply (step_mklock _ _ _ _ _ )
          with (pmap_tid':= new_perms2);
          eauto; try reflexivity; try solve[apply CMatch].
        
        (* 8 goals produced. *)
        + !goal (semantics.at_external _ _ _ = Some (MKLOCK, _)).
          abstract_proofs; unify_proofs.
          erewrite (Sum_at_external_proper' (S hb));
            try eapply (cur_equiv_restr_mem_equiv m2 _ abs_proof Hthread_mem2);
            try reflexivity.
          erewrite <- coerse_state_atx; eauto.
          eapply atx_injection; eauto.

        + !goal(Mem.range_perm _ _ _ _ _ _).
          inversion Hlock_update_mem_strict2; subst th_mem2.
          replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
          eauto.
        + move Hstore2 at bottom.
          match goal with |- Mem.store _ ?m' _ _ _ = _ => (replace m' with th_mem2) end.
          replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
          assumption.
          * subst th_mem2.
            simpl; f_equal.
            apply Axioms.proof_irr.
        + inv HH0; simpl.
          f_equal; eauto.
        + inv HH0; simpl.
          f_equal; eauto.
        + !goal (lockRes _ (b2,_) = None).
          replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
          eapply INJ_lock_permissions_None; eauto.
          apply Hinj.
          eapply Mem.perm_implies. 
          inv Hlock_update_mem_strict.
          eapply Haccess.
          pose proof LKSIZE_pos; omega.
          constructor.
        + simpl. repeat f_equal; eauto.
      - !goal(concur_match _ _ _ _ _ _).
        clean_proofs.

        destruct new_perms1 as (new_perms11 & new_perms12).
        destruct new_perms2 as (new_perms21 & new_perms22).
        simpl in *.
        assert (Hsurj:perm_surj mu new_perms12 new_perms22).
        { inv HH1; inv HH0.
          inv Hset_block. inv Hset_block0.
          eapply perm_surj_setPermBlock; eauto.
          eapply CMatch; eauto. }
        
        eapply concur_match_update_lock  with
            (Hlt1:= Hlt11')(Hlt3:= Hlt21')
            (Hlt_lock1:=Hlt12')(Hlt_lock2:=Hlt22'); 
          try match goal with |- context[Forall2] => idtac | _ => eauto end.
        + !context_goal lock_update_mem.
          eapply lock_update_mem_strict_mem_update; eauto.
        + !context_goal lock_update_mem.
          subst th_mem2. simpl in Hlock_update_mem_strict2.
          rewrite self_restre_eq in Hlock_update_mem_strict2; eauto.
          eapply lock_update_mem_strict_mem_update; eauto.          
        + !goal (invariant _). unfold fullThreadUpdate; simpl.
          eapply invariant_update_mk; eauto.
          reflexivity.
          eapply CMatch.
        + !goal (@invariant (HybridSem _ ) _ _).
          eapply invariant_update_mk; eauto.
          * reflexivity.
          * eapply CMatch.
        + shelve.
        + !context_goal memval_inject.
          repeat econstructor.
        + !goal (access_map_equiv_pair _ (pair0 empty_map)).
          eapply empty_map_is_empty_pair, inject_empty_maps, empty_is_empty_pair.
        + !context_goal @lock_update.
             econstructor. unfold fullThreadUpdate; simpl.
             reflexivity. 
        + !context_goal @lock_update.
             econstructor. unfold fullThreadUpdate; simpl.
             reflexivity. 

          Unshelve.
          all: try (unfold Max_equiv in *;
                    first [rewrite <- Hmax_equiv|
                           rewrite <- Hmax_equiv2]; eauto).

          { !context_goal one_thread_match.
            (* Shelved above*)
            destruct (lt_eq_lt_dec tid hb) as [[Htid_neq'|Htid_neq']|Htid_neq'].
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch);
              simpl; eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H6; simpl in *.
                
                econstructor 2; eauto. simpl.
                do 2 econstructor; eauto.
                (*worth writting this as a lemma, 
                then use it bellow
                 *)
                
                econstructor; eauto.
                * rewrite getCur_restr.
                  eapply perm_image_injects_map.
                  eapply full_inject_map; eauto.
                  -- eapply CMatch.
                  -- eapply map_valid_Lt; eauto.
                     eapply map_valid_proper.
                     reflexivity.
                     symmetry; eapply Hmax_equiv.
                     eapply max_map_valid.
                     
                * do 2 rewrite getCur_restr; eauto.
                  { inv HH1; inv HH0.
                    inv Hset_block. inv Hset_block0.
                    eapply perm_surj_setPermBlock_Nonempty; eauto.
                    unshelve exploit @mtch_target; eauto.
                    intros HH; inv HH; inv matchmem;
                       repeat rewrite getCur_restr in *;
                       eauto.
                  }
            - subst tid; congruence.
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch);
              simpl; eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H6; simpl in *.
                
                econstructor 1; eauto. simpl.
                do 2 econstructor; eauto.
                (*worth writting this as a lemma, 
                then use it bellow
                 *)
                
                
                econstructor; eauto.
                * rewrite getCur_restr.
                  eapply perm_image_injects_map.
                  eapply full_inject_map; eauto.
                  -- eapply CMatch.
                  -- eapply map_valid_Lt; eauto.
                     eapply map_valid_proper.
                     reflexivity.
                     symmetry; eapply Hmax_equiv.
                     eapply max_map_valid.
                * do 2 rewrite getCur_restr; eauto.
                  { inv HH1; inv HH0.
                    inv Hset_block. inv Hset_block0.
                    eapply perm_surj_setPermBlock_Nonempty; eauto.
                  exploit @mtch_source; eauto.
                     intros HH; inv HH; inv matchmem;
                       repeat rewrite getCur_restr in *;
                       eauto. }
                  
                  Unshelve.
                  all: simpl; eauto. }
    Qed. (* make_step_diagram_self *)


    
    Lemma make_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (U : list nat) (cd : compiler_index) (mu:meminj) (*tr2*) 
        (st1 : ThreadPool (Some hb)) (m1 m1' m1'' : mem) new_perms1
        (st2 : ThreadPool (Some (S hb))) (m2' : mem) Hcnt1 Hcnt2
        (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
        b1 ofs (code1 : semC)  (code2 : Asm.state)
        (*Hinj_b : mu b1 = Some (b2, delt)*)
        (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
        (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
        (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
        (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
        (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
        (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
        
        (HH1: set_new_mems b1 (unsigned ofs) (getThreadR Hcnt1) LKSIZE_nat new_perms1)
        (*HH2: set_new_mems b2 (unsigned ofs+delt) (getThreadR Hcnt2) LKSIZE_nat new_perms2*)
        
        (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                         Some (MKLOCK, (Vptr b1 ofs :: nil)%list))
        (Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1' m1'' vzero)
        (HisLock: lockRes st1 (b1, unsigned ofs) = None)
        (Hlt1 : permMapLt (thread_perms _ _ Hcnt1) (getMaxPerm m1'))
        (Hlt2 : permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2'))
        (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
      exists evnt2 (st2' : t) (m2'' : mem),
        let evnt:= Events.mklock (b1, unsigned ofs) in 
        let st1':= fullThreadUpdate
                     st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                     (new_perms1, pair0 empty_map) (b1, unsigned ofs)  in
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
      clean_proofs.
      
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
      set (ofs2:= add ofs (repr delta)).
      
      assert (Hofs2: unsigned ofs2 = unsigned ofs + delta).
      { subst ofs2. solve_unsigned. }
      
      assert (HH2:exists new_perms2,
                 set_new_mems b2 (unsigned ofs + delta)
                              (getThreadR Hcnt2) LKSIZE_nat new_perms2).
      { exists (setPermBlock_pair b2 (unsigned ofs + delta)
                             (Some Nonempty, Some Writable)
                             (getThreadR Hcnt2)
                             (pair0 LKSIZE_nat)).
        econstructor; reflexivity. }
      destruct HH2 as [new_perms2 HH2].
      set (st2':= fullThreadUpdate st2 hb Hcnt2 (Kresume (TST code2) Vundef)
                                   (new_perms2, pair0 empty_map) (b2, unsigned ofs2)).
      remember (fullThreadUpdate st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                                 (new_perms1, pair0 empty_map)
                                 (b1, unsigned ofs)) as st1'.

      assert (H: ThreadPool (Some (S hb)) =
                 @t dryResources (HybridSem (@Some nat (S hb)))).
      { reflexivity. }
      dependent rewrite <- H in st2'. clear H.
      
      repeat pose_max_equiv.
      forward_cmpt_all.
      rename Hcmpt_mem_fwd into Hcmpt2'.
      rename Hcmpt_mem_fwd0 into Hcmpt1'.

      assert (Hlt1:permMapLt_pair (new_perms1) (getMaxPerm m1'')).
      { assert (Hcnt1': containsThread st1' hb).
        { subst st1'. eapply cntUpdateL, cntUpdate; eauto. }
        match goal with
          |- permMapLt_pair ?X _ =>
          assert ((@getThreadR _ _ hb st1' Hcnt1') = X)
        end.
        { subst st1'; erewrite gLockSetRes, gssThreadRes; reflexivity. }
        erewrite <- H.
        eapply @compat_th with (cnt:=Hcnt1') in Hcmpt1'.
        assumption. }
      destruct Hlt1 as [Hlt11 Hlt12]; simpl in Hlt11, Hlt12.
      
      assert (Hlt2:permMapLt_pair (new_perms2) (getMaxPerm m2'')).
      { assert (Hcnt2': containsThread st2' hb).
        { subst st2'. eapply cntUpdateL, cntUpdate; eauto. }
        match goal with
          |- permMapLt_pair ?X _ =>
          assert ((@getThreadR _ _ hb st2' Hcnt2') = X)
        end.
        { subst st2'; erewrite gLockSetRes, gssThreadRes; reflexivity. }
        erewrite <- H.
        eapply @compat_th with (cnt:=Hcnt2') in Hcmpt2'.
        assumption. }
      destruct Hlt2 as [Hlt21 Hlt22]; simpl in Hlt21, Hlt22.
      

      
      
      (** * 4. Finally we proceed with the goal: existentials. *)
      set (evnt2:= (Events.mklock (b2, unsigned ofs2))).
      
      exists evnt2, st2', m2''.
      split; [|split].
      - eapply concur_match_update_lock; 
          match goal with |- context[Forall2] => idtac
                     | _ => eauto; try solve[subst st1'; eauto] end.
        + !context_goal lock_update_mem.
          eapply lock_update_mem_strict_mem_update.
          eapply Hlock_update_mem_strict1.
        + !context_goal (lock_update_mem).
          eapply lock_update_mem_strict_mem_update.
          eapply Hlock_update_mem_strict2.
        + !context_goal Mem.inject.
          rewrite RPM.
          instantiate(2:=fst new_perms2);
            instantiate(3:=fst new_perms1).
          apply inject_restr; auto.
          * !goal (mi_perm_perm mu _ _).
            { repeat match goal with
                     | [ H: set_new_mems _ _ _ _ _  |- _ ] =>
                       inv H
                     end; simpl in *.
              eapply mi_perm_perm_setPermBlock; eauto;
                try now econstructor.
              - rewrite <- Hmax_eq0.
                eapply Mem.mi_no_overlap.
                eapply  Hinj'.
              - rewrite Hthread_mem1, Hthread_mem2.
                eapply mi_inj_mi_perm_perm_Cur; eapply Hinj'. }
          * !goal (mi_memval_perm mu _ _ _).
            eapply mi_memval_perm_computeMap_Lt with (p:=fst (getThreadR Hcnt1)).
            rewrite Hthread_mem1.
            inv Hlock_update_mem_strict1;
              inv Hlock_update_mem_strict2.
            eapply mi_memval_perm_store_easy; eauto;
              try apply mi_inj_mi_memval_perm;
              apply Hinj'0.
            rewrite Hthread_mem1.
            inv Hlock_update_mem_strict1.
            eapply set_new_mems_LT1; eauto.
            symmetry; eauto.  
          * !goal (mi_perm_inv_perm mu _ _ _).
            rewrite <- Hmax_eq0.
            inv Hlock_update_mem_strict1.
            eapply mi_perm_inv_perm_setPerm1; eauto.
            rewrite Hthread_mem1, Hthread_mem2.
            eapply inject_mi_perm_inv_perm_Cur; eauto.
            apply Hinj'0.
        + !goal (@invariant (HybridSem _) _ _).
          assert (Haccess': forall ofs0 : Z,
                     unsigned ofs <= ofs0 < unsigned ofs + LKSIZE ->
                     Mem.perm_order' ((thread_perms hb st1 Hcnt1) !! b1 ofs0) Writable).
          { intros; rewrite Hthread_mem1.
            inv Hlock_update_mem_strict1.
            exploit Haccess. instantiate(1:= ofs0). omega.  
            unfold Mem.perm.
            rewrite_getPerm_goal; eauto. }
          
          simpl in Heqst1'.
          eapply invariant_empty_updLockSet;
            try eapply Heqst1'.
          * pose proof (invariant_makelock hb hb) as HH. 
            eapply HH; eauto; eapply CMatch.
          * inv Hlock_update_mem_strict1.
            intros. simpl; rewrite gsoThreadLPool.
            eapply writable_is_not_lock; eauto.
            eapply perm_order_trans101; try (eapply Haccess'; omega).
            constructor.
          * simpl; intros; rewrite gsoThreadLPool.
            destruct_lhs; eauto.
            eapply lockSet_is_not_readable in Heqo as [HH3 _]; eauto.
            exploit Haccess'.  instantiate(1:= unsigned ofs); omega.
            exploit HH3. instantiate(1:= unsigned ofs). omega.
            intros ->. intros HH; inv HH.
        + !goal (invariant st2').
          assert (Haccess2': forall ofs0 : Z,
                     unsigned ofs + delta <= ofs0 < unsigned ofs + delta + LKSIZE ->
                     Mem.perm_order' ((thread_perms hb st2 Hcnt2) !! b2 ofs0) Writable).
          { intros; rewrite Hthread_mem2.
            inv Hlock_update_mem_strict2.
            exploit Haccess. instantiate(1:= ofs0). omega.  
            unfold Mem.perm.
            rewrite_getPerm_goal; eauto. }
          
          assert (Haccess1': forall ofs0 : Z,
                     unsigned ofs <= ofs0 < unsigned ofs + LKSIZE ->
                     Mem.perm_order' ((thread_perms hb st1 Hcnt1) !! b1 ofs0) Writable).
          { intros; rewrite Hthread_mem1.
            inv Hlock_update_mem_strict1.
            exploit Haccess. instantiate(1:= ofs0). omega.  
            unfold Mem.perm.
            rewrite_getPerm_goal; eauto. }
          simpl in st2'.
          eapply invariant_empty_updLockSet; try reflexivity.
          * pose proof (invariant_makelock hb (S hb)) as HH. 
            eapply HH; eauto. eapply CMatch.
            
            
          * inv Hlock_update_mem_strict2.
            intros. simpl; rewrite gsoThreadLPool.
            replace ofs0 with ((ofs0 - delta) + delta) by omega.
            remember (ofs0 - delta) as OFS.
            assert (unsigned ofs <= OFS < unsigned ofs + LKSIZE).
            { subst OFS ofs2.  
              replace (unsigned (add ofs (repr delta))) with (unsigned ofs + delta) in H.
              clear - H; omega.
            }
            
            eapply INJ_lock_permissions_None; eauto.
            eapply Hinj'0.
            eapply Mem.perm_implies.
            unfold Mem.perm.
            move Haccess1' at bottom.
            rewrite_getPerm_goal; eauto.
            rewrite <- Hthread_mem1; eapply Haccess1'; eauto.
            constructor.

            
            !goal (lockRes st1 (b1, OFS) = None).
            { (* Just like it was proven above *)
              eapply writable_is_not_lock; eauto.
              eapply perm_order_trans101; try (eapply Haccess1'; omega).
              constructor.  }
          * simpl. intros; rewrite gsoThreadLPool.
            (*by contradiction*)
            destruct_lhs; eauto; exfalso.

            (* First we show b1 maps to b2
               and there is a lockRes b1 ofs = Some _ 
             *)
            exploit INJ_lock_permissions_preimage; eauto.
            intros; normal_hyp.
            assert (Hunsign: unsigned ofs2 = unsigned ofs + delta).
            { subst ofs2. solve_unsigned. }
            
            
            exploit @no_overlapp_iff'.
            intros [HH _].
            specialize (HH ltac:(eapply no_overlap_mem_perm; eauto; eapply Hinj2)).
            exploit HH. apply H0. apply Hinj_b'.
            1, 2: erewrite at_least_perm_order.
            -- eapply perm_order_trans211; swap 1 2.
               instantiate(1:=Some Nonempty); econstructor.
               eapply lockSet_is_not_readable in H2 as [HH' _];eauto.
               exploit HH'. instantiate(1:= (unsigned ofs + delta) - x2).
               rewrite Hunsign in *.
               subst; clear - H1 H. omega. intros <-.
               rewrite <- Hmax_eq0. eapply Hlt_th1.
            -- inv HH1; simpl in *.
               exploit setPermBlock_range_perm; eauto.
               split; try reflexivity. pose proof LKSIZE_nat_pos'; omega.
               unfold Mem.perm; rewrite_getPerm; eauto.
            -- omega.
            -- intros; normal_hyp.
               move HisLock at bottom.
               subst. unify_injection.
               rewrite Hunsign in *.
               
               eapply lockSet_is_not_readable in H2 as [H2 _]; eauto.
               exploit H2. instantiate(1:=unsigned ofs); omega.

               inv Hlock_update_mem_strict1.
               rewrite Hthread_mem1. intros contra.
               exploit Haccess. split; try reflexivity; omega.
               unfold Mem.perm. rewrite_getPerm. rewrite contra.
               intros contra'; inversion contra'.
        + !goal(perm_surj mu _ _).
          instantiate(1:=snd new_perms2); instantiate(1:=snd new_perms1).
          inv HH1; inv HH2; simpl.
          eapply perm_surj_setPermBlock; eauto.
          eapply CMatch.
        + !goal (Mem.inject mu _ _).
          apply inject_restr; auto.
          * !goal (mi_perm_perm mu (snd new_perms1) (snd new_perms2)).
            
            { repeat match goal with
                     | [ H: set_new_mems _ _ _ _ _  |- _ ] =>
                       inv H
                     end; simpl in *.
              eapply mi_perm_perm_setPermBlock; eauto;
                try now econstructor.
              - rewrite <- Hmax_eq0.
                eapply Mem.mi_no_overlap.
                eapply Hinj'.
                
              (*  - match type of Hcmpt1' with
                    mem_compatible ?st1'_ _ =>
                    remember st1'_ as st1'
                  end.
                  assert (Hcnt1': containsThread st1' hb).
                  { subst st1'. eapply cntUpdateL, cntUpdate; eauto. }
                  match goal with
                    |- permMapLt ?X _ =>
                  assert (snd (@getThreadR _ _ hb st1' Hcnt1') = X)
                  end.
                  { subst st1'; erewrite gLockSetRes, gssThreadRes; reflexivity. }
                  erewrite <- H.
                  eapply @compat_th with (cnt:=Hcnt1') in Hcmpt1'
                  as [HH1 HH2].
                  unfold Max_equiv in Hmax_eq0;
                    rewrite Hmax_eq0.
                  assumption. *)
              - erewrite <- getCur_restr.
                erewrite <- (getCur_restr (lock_perms hb st2 Hcnt2)).
                eapply mi_inj_mi_perm_perm_Cur; eapply Hinj_lock. }
          * !goal (mi_memval_perm mu (snd new_perms1)
                                  (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
            { 
              eapply mi_memval_perm_computeMap_Lt with (p:=fst (getThreadR Hcnt1)).
              rewrite Hthread_mem1.
              inv Hlock_update_mem_strict1;
                inv Hlock_update_mem_strict2.
              eapply mi_memval_perm_store_easy; eauto;
                try apply mi_inj_mi_memval_perm;
                apply Hinj'0.
              rewrite Hthread_mem1.
              inv Hlock_update_mem_strict1.
              eapply set_new_mems_LT2; eauto.
              symmetry; eauto.   }
          * !goal (mi_perm_inv_perm mu (snd new_perms1) (snd new_perms2) m1'').
            { rewrite <- Hmax_eq0.
              inv Hlock_update_mem_strict1.
              eapply mi_perm_inv_perm_setPerm2; eauto.
              2: apply Hinj'0.
              erewrite <- getCur_restr.
              erewrite <- (getCur_restr (lock_perms hb st2 Hcnt2)).
              eapply inject_mi_perm_inv_perm_Cur in Hinj_lock; eauto.
              revert Hinj_lock.
              match goal with
              | [  |- mi_perm_inv_perm _ _ _ ?m -> mi_perm_inv_perm _ _ _ ?m' ] =>
                assert (HH:Max_equiv m m') by apply restr_Max_equiv
              end.
              intros; rewrite <- HH; eauto; eapply Hinj_lock. }
        +  (* Proof of match goes after the comment *)
          !context_goal one_thread_match.
          { eapply build_match_compiled; auto.
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
            
            eapply large_external_diagram; try reflexivity; eauto.
            - eapply makelock_is_consec.
            - eapply mklock_doesnt_return.
            - reflexivity.
            - eapply inject_delta_map_empty.
            - simpl. rewrite MakeLockExists.
              inv HH1. econstructor; swap 1 2.
              econstructor; eauto.
              eauto.
              erewrite restre_equiv_eq; eauto.
              simpl.
              eapply setPermBlock_access_map_equiv; try reflexivity.
              symmetry; etransitivity; eauto.
              eapply lock_update_mem_strict_cur; eauto.
              constructor; auto.
            - simpl; rewrite MakeLockExists.
              inv HH2. econstructor; eauto.
              econstructor; eauto.
              move Hlock_update_mem_strict2 at bottom.
              subst ofs2; rewrite Hofs2; eauto.
              erewrite restre_equiv_eq; eauto; simpl.
              subst ofs2; rewrite Hofs2; eauto.
              eapply setPermBlock_access_map_equiv; try reflexivity.
              etransitivity; eauto.
              eapply lock_update_mem_strict_cur; eauto.
              constructor; auto.
            - exploit (interference_consecutive_until _ _ _  Hinterference2).
              rewrite <- Hnb_eq; simpl; auto.
            - exploit (interference_consecutive_until _ _ _ Hinterference2').
              simpl; auto. }
        + !context_goal Forall2.
          simpl. unfold encode_int; simpl.
          repeat econstructor.
        + !goal (access_map_equiv_pair _ _ ).
          instantiate(1:= pair0 empty_map).
          eapply empty_map_is_empty_pair, inject_empty_maps.
          instantiate(1:= pair0 empty_map).
          eapply empty_is_empty_pair.
        + !context_goal (@lock_update _ _ (@Some nat hb)).
          subst st1'. econstructor.
          destruct new_perms1; eauto.
        + !context_goal (@lock_update _ _ (@Some nat (S hb))).
          simpl in *. econstructor.
          subst st2' ofs2; destruct new_perms2. repeat f_equal.
          eauto.
      - subst evnt2. replace (unsigned ofs2) with (unsigned ofs + delta).
        repeat econstructor; eassumption.
      - simpl.
        rewrite <- Hofs2 in *.
        eapply step_mklock;
          eauto; try reflexivity;
            try unfold HybridMachineSig.isCoarse,
            HybridMachineSig.HybridCoarseMachine.scheduler.
        + !goal (@invariant (HybridSem _) _ st2).
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
          (* Can write the lock *) simpl.
          !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Writable).
          inversion Hlock_update_mem_strict2; subst vstore.
          unfold unsigned in *. rewrite Hofs2.
          eapply range_perm_mem_equiv_Cur; try apply eq_refl; eauto.
          2:{ repeat rewrite Hofs2 in Haccess; eauto. }
          intros ?.
          rewrite getCur_restr; eauto.
        + (* the store *)
          inversion Hlock_update_mem_strict2; subst vstore.
          rewrite (mem_is_restr_eq m2') in Hstore.
          erewrite restrPermMap_equiv_eq; eauto.
        + simpl; inv HH2; auto.
        + simpl; inv HH2; auto.
        + !goal (lockRes _ (b2,_) = None).
          { unfold unsigned in *. rewrite Hofs2.
            eapply INJ_lock_permissions_None; eauto.
            eapply Hinj'0.
            eapply Mem.perm_implies.
            hnf. rewrite_getPerm.
            eapply lock_update_mem_permMapLt_range_Cur;
              try apply Hlock_update_mem_strict1; eauto.
            { pose proof LKSIZE_pos; omega. }
            constructor.
          } 
          Unshelve.
          all: eauto.

          { simpl in *.
            pose proof (lock_update_mem_strict_cur
                          _ _ _ _ _ Hlock_update_mem_strict1) as HH.
            unfold Cur_equiv in HH.
            rewrite <- HH, <- Hthread_mem1; eauto. }

          { subst ofs2; rewrite Hofs2.
            pose proof (lock_update_mem_strict_cur
                          _ _ _ _ _ Hlock_update_mem_strict2) as HH.
            unfold Cur_equiv in HH.
            rewrite <- HH, <- Hthread_mem2; eauto. }
          
    Qed. (* make_step_diagram_compiled*)

    (** *Full Machine diagrams *)






    






    






    
    

    Lemma make_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (m1 m1' m2 : mem) (tid : nat) cd (mu : meminj)
             (st1 : ThreadPool (Some hb)) cnt1
             (st2 : ThreadPool (Some (S hb))) cnt2
             (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
             (c : semC) (b : block) (ofs : int) new_perms
             (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
             (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
             (CMatch: concur_match cd mu st1 m1 st2 m2)
             (Hcode: getThreadC cnt1 = Kblocked c)
             (Hat_external: semantics.at_external hybrid_sem c m1 =
                            Some (MKLOCK, (Vptr b ofs :: nil)%list))
             (Hset_block: set_new_mems b (unsigned ofs) (getThreadR cnt1) LKSIZE_nat new_perms)
             (Hlock_update_mem_strict: lock_update_mem_strict b (unsigned ofs) m1 m1' vzero),
        lockRes st1 (b, unsigned ofs) = None ->
        exists evnt2 (st2' : t) (m2' : mem),
          let evnt:= Events.mklock (b, unsigned ofs) in
          let st1':= fullThreadUpdate st1 tid cnt1 (Kresume c Vundef)
                                      (new_perms, pair0 empty_map) (b, unsigned ofs) in
          concur_match cd mu st1' m1' st2' m2' /\
          inject_sync_event mu evnt evnt2 /\
          
          let Hcmpt2:= memcompat2 CMatch in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true cnt2 Hcmpt2 st2' m2' evnt2.
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
        (* 6883*) 
        
        pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
          as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H4. (* Asm_match *)
        
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
        destruct Hinj' as (args2 & Hinj_b & Hat_external2); eauto.
        inversion Hinj_b as [| ? ? ? ? AA _ CC]; subst; clear Hinj_b.
        inversion AA as [ | | | | ? ? ? ? ? Hinj_b  | ]; subst.
        
        (edestruct (make_step_diagram_self AsmSem tid) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step & CMatch')); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + omega.
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl. move matchmem at bottom.
            eapply match_mem_proper; try eapply matchmem; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
               clean_proofs; eauto.
        + exists e'. eexists. exists m2'.
          split ; [|split]; eauto.
          * clean_proofs; eauto.
      - (* (tid = hb) *)
        subst tid. 
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
        
        rename H8 into Hinterference2.
        rename H6 into Hinterference1.
        rename H2 into Hcomp_match.
        rename H3 into Hstrict_evolution.
        
        rename cnt1 into Hcnt1.
        rename Hat_external into Hat_external1.
        rename b into b1.
        (* rename Hstore into Hstore1. *)
        
        rewrite RPM in Hinterference1.
        symmetry in H1.
        clean_proofs.
        exploit make_step_diagram_compiled;
          try reflexivity;
          try solve[eapply CMatch]; eauto.
        + econstructor; eassumption.
        + !goal (same_cnt _ _ _ _ _). constructor.
        + !goal (strict_evolution_diagram _ _ _ _ _ _ _).
          econstructor; eauto; simpl.
          * !goal(mem_interference m1 lev1 m1'). 
            rewrite self_restre_eq in Hinterference1; eauto.
          * !goal(mem_interference m2 lev2 m2'). 
            rewrite self_restre_eq in Hinterference2; eauto.
        + intros (?&?&?&?&?&?).
          do 3 eexists; repeat weak_split eauto.
          clean_proofs; eauto.
          
      - (* tid > hb  *)
        pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
          as match_thread.
        simpl in Hcode; exploit_match ltac:(apply CMatch).
        inversion H4. (* Clight_match *)
        
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
        destruct Hinj' as (args2 & Hinj_b & Hat_external2); eauto.
        inversion Hinj_b as [| ? ? ? ? AA _ CC]; subst; clear Hinj_b.
        inversion AA as [ | | | | ? ? ? ? ? Hinj_b  | ]; subst.
        
        (edestruct (make_step_diagram_self CSem tid) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step & CMatch')); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + omega.
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl. move matchmem at bottom.
            eapply match_mem_proper; try eapply matchmem; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
               clean_proofs; eauto.
        + exists e'. eexists. exists m2'.
          split ; [|split]; eauto.
          * clean_proofs; eauto.


            Unshelve.
            all: eauto.

    Qed. (* make_step_diagram*)


  End mklock. 
End MklockDiagrams.