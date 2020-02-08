

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


    Definition build_spwan_event addr dmap1 dmap2 m:=
      Events.spawn addr (Some (build_delta_content dmap1 m))
                   (Some (build_delta_content dmap2 m)).

    Lemma perm_perfect_image_computeMap:
      forall mu A B A' B'
        (Hno_overlapAB: maps_no_overlap mu A (fun _=> None, B)),
        perm_perfect_image mu A A' ->
        perm_perfect_image_dmap mu  B B' ->
        perm_perfect_image mu (computeMap A B) (computeMap A' B').
    Proof.
      intros.
      econstructor;
        intros ? **; unfold at_least_Some in *;
        simpl in *.
      - match_case in H1; clear H1.
        rewrite computeMap_get in Heqo.
        match_case in Heqo.
        + exploit @p_image_dmap; eauto.
          { rewrite Heqo0; constructor. }
          intros HH; normal; eauto.
          rewrite computeMap_get.
          rewrite <- H2, Heqo0; auto.
        + exploit @p_image; eauto.
          { rewrite Heqo; constructor. }
          intros HH; normal; eauto.
          rewrite computeMap_get.
          rewrite <- H2, Heqo.
          match_case; auto.
          exploit @ppre_perfect_image_dmap; eauto.
          { rewrite Heqo1; constructor. }
          intros HH; normal.
          rewrite Heqo1 in H5; symmetry in H5.
          destruct (peq b1 x1).
          * subst; unify_injection.
            replace x2 with ofs in H5 by omega.
            rewrite H5 in Heqo0; congruence.
          * (* NO OVERLAP *)
            clear - Heqo0 Hno_overlapAB n Heqo H5 H4 H1 H3.
            exploit Hno_overlapAB; try exact n; eauto;
              try (rewrite Heqo; constructor);
              try rewrite computeMap_get.
            -- unfold dmap_get in H5.
               instantiate(1:=x2).
               unfold delta_map in *.
               rewrite H5. constructor.
            -- intros [ | ]; congruence.
      - match_case in H1; clear H1.
        rewrite computeMap_get in Heqo.
        match_case in Heqo.
        + exploit @ppre_perfect_image_dmap; eauto.
          { rewrite Heqo0; constructor. }
          intros HH; normal; eauto.
          rewrite computeMap_get.
          rewrite <- H3, Heqo0; auto.
        + exploit @ppre_perfect_image; eauto.
          { rewrite Heqo; constructor. }
          intros HH; normal; eauto.
          rewrite computeMap_get.
          rewrite <- H3, Heqo.
          match_case; auto.
          exploit @p_image_dmap; eauto.
          { rewrite Heqo1; constructor. }
          intros HH; normal.
          unify_injection. subst.
          rewrite <- H5,Heqo1 in Heqo0. congruence.

    Qed.
    Lemma maps_no_overlap_option_impl:
      forall {A B1 B2} mu m p1 p2,
        map_no_overlap mu m ->
        (forall b ofs, @option_implication B1 A (p1 !! b ofs) (m !! b ofs)) ->
        (forall b ofs, @option_implication B2 A (p2 !! b ofs) (m !! b ofs)) ->
        maps_no_overlap mu p1 p2.
    Proof.
      intros ** ? **; eapply H; eauto.
      - unfold at_least_Some in *; simpl in *.
        specialize (H0 b1 ofs1).
        match_case in H5.
      - unfold at_least_Some in *; simpl in *.
        specialize (H1 b2 ofs2).
        match_case in H6.
    Qed.
    Lemma perm_perfect_imageempty_map:
      forall mu, perm_perfect_image mu empty_map empty_map.
    Proof.
    Admitted.
    
    Lemma val_inject_mem_inject:
      forall mu m1 m2 arg1 arg2,
        val_inject (Mem.flat_inj (Mem.nextblock m1)) arg1 arg1 ->
        arg1 <> Vundef ->
        Mem.inject mu m1 m2 ->
        val_inject mu arg1 arg2 ->
        val_inject (Mem.flat_inj (Mem.nextblock m2)) arg2 arg2.
    Proof.
      intros. inv H; inv H2; try solve[econstructor]; swap 1 2.
      - contradict H0; eauto.
      - intros; econstructor. 
        + unfold Mem.flat_inj. match_case.
          * reflexivity.
          * clear Heqs.
            contradict n. eapply Mem.mi_mappedblocks; eauto.
        + rewrite add_zero; auto.
    Qed.
    Lemma permMapJoin_pair_inject_spawn:
          forall virtue1 virtue_new1 m1
            m2 mu  th_perms1 th_perms2,
            sub_map_pair virtue1 (snd (getMaxPerm m1)) ->
            sub_map_pair virtue_new1 (snd (getMaxPerm m1)) ->
            let ThreadPerm1 := computeMap_pair th_perms1 virtue1 in
            let newThreadPerm1 := computeMap_pair (pair0 empty_map) virtue_new1 in
            permMapJoin_pair newThreadPerm1 ThreadPerm1 th_perms1 ->
            forall 
              (Hlt_th1 : permMapLt (fst th_perms1) (getMaxPerm m1))
              (Hlt_th2 : permMapLt (fst th_perms2) (getMaxPerm m2))
              (Hlt_lk1 : permMapLt (snd th_perms1) (getMaxPerm m1))
              (Hlt_lk2 : permMapLt (snd th_perms2) (getMaxPerm m2)),
              Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
              Mem.inject mu (restrPermMap Hlt_lk1) (restrPermMap Hlt_lk2) ->
              injects_dmap_pair mu virtue1   ->
              injects_dmap_pair mu virtue_new1   ->
              let virtue2 := virtueThread_inject m2 mu virtue1 in
              let virtue_new2 := virtueThread_inject m2 mu virtue_new1 in
              let ThreadPerm2 :=  computeMap_pair th_perms2 virtue2 in
              let newThreadPerm2 := computeMap_pair (pair0 empty_map) virtue_new2 in
              permMapJoin_pair newThreadPerm2 ThreadPerm2 th_perms2.
        Proof.
          (*Move to synchronization_lemmas next to
            permMapJoin_pair_inject_rel               
           the rpoof should be similar.*)
        Admitted.
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
      
      assert (Hcmpt2': mem_compatible(tpool:=OrdinalThreadPool) st2'' m2).
      { (* Make a Lemma *) 

        admit.  }
      
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

      exists event2, st2'', m2.  
      repeat weak_split. (* 4 goal*)
      - !goal(concur_match _ _ _ _ _ _ ).
        admit. (* Lemma concur_spawn*)
      - subst event2. repeat econstructor; eauto.
      - !goal (syncStep _ _ _ _ _ _).
        
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)

        subst event2 ; unfold build_release_event.
        
        eapply step_create;
          match goal with
            |- val_inject _ _ _ => idtac
          | |- _ => eauto; try reflexivity
          end.
        + eapply inject_virtue_sub_map_pair'; eauto.
          * apply Hinj_lock.
          * apply Hangel_bound.
        + eapply inject_virtue_sub_map_pair'; eauto.
          * apply Hinj_lock.
          * apply Hangel_bound_new.
        + eapply CMatch.
        + !goal (semantics.at_external _ _ _ = Some (CREATE, _)).
          { eapply at_external_sum_sem; eauto. }
        + !goal(val_inject  _ arg2 arg2).
          eapply val_inject_mem_inject; eauto.
        + { simpl. subst ThreadPerm2 newThreadPerm2 virtue2 virtue_new2.
            eapply Hjoin_angel2. }
        + { simpl. subst ThreadPerm2 newThreadPerm2 virtue2 virtue_new2.
            eapply Hjoin_angel2. }
    Admitted.

    Lemma spawn_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in
      forall m1 m2 m10 virtue1 virtue_new1  cd
        (mu : meminj) (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb)))
        (cnt1 : ThreadPool.containsThread(Sem:=HybridSem _) st1 hb)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 hb)
        (c : semC) (b1 : block) (ofs : int) arg
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

        let st1':= (ThreadPool.updThread cnt1 (Kresume c Vundef) ThreadPerm1) in
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

      
      assert (Hcmpt2': mem_compatible(tpool:=OrdinalThreadPool) st2'' m2).
      { (* Make a Lemma *) 

        admit.  }

      
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

      
      (** * 4. Finally we proceed with the goal: existentials. *)
      
      exists event2, st2'', m2.  
      repeat weak_split. (* 4 goal*)
      - !goal(concur_match _ _ _ _ _ _ ).
        admit. (* Lemma concur_spawn*)
      - subst event2. repeat econstructor; eauto.
      - !goal (syncStep _ _ _ _ _ _).
        
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)

        subst event2 ; unfold build_release_event.
        
        eapply step_create;
          match goal with
            |- val_inject _ _ _ => idtac
          | |- _ => eauto; try reflexivity
          end.
        + eapply inject_virtue_sub_map_pair'; eauto.
          * subst; apply Hinj_th.
          * apply Hangel_bound.
        + eapply inject_virtue_sub_map_pair'; eauto.
          * subst; apply Hinj_lock.
          * apply Hangel_bound_new.
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

          Unshelve.
          all: auto.
      
      
    Admitted.

    
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