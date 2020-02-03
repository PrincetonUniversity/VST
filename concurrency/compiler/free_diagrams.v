

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





Section FreeDiagrams.
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


  Section freelock.
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


    
    Lemma free_step_diagram_self Sem tid:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
        (st1 : mach_state hb) (st2 : mach_state (S hb))
        (m1 m2 : mem) (mu : meminj) i b1 b2 ofs delt
        lock_data pdata
        (Hinj_b : mu b1 = Some (b2, delt))
        cnt1 cnt2 (* Threads are contained *)
        (CMatch: concur_match i mu st1 m1 st2 m2)

        (* We can assume invariant and compatible:
           because the second step is assumed to be safe -> 
           satisfies both 
         *)
        
        (* Thread states *)
        (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
        (HState1: coerce_state_type _ sum_state1 th_state1  
                                    (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
        (HState2: coerce_state_type _ sum_state2 th_state2
                                    (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
        (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
        (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
        
        (* angel, lock permissions and new thread permissions *)
        (Hnone_beyond : bounded_nat_func' pdata LKSIZE_nat)
        (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
        (Hlock_map: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = Some lock_data)
        (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
        (HlocksLt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1) )
        (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                    b1 (unsigned ofs) LKSIZE Cur Writable)
        (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                  Mem.perm_order'' (pdata (S i)) (Some Writable))
        (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
        (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                       Some (FREE_LOCK, (Vptr b1 ofs :: nil)%list)),
        let ofs2:=  unsigned ofs + delt in
        let new_perms1:=
            setPermBlock_var_pair b1 (unsigned ofs) LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR cnt1) in
        let new_perms2:=
            setPermBlock_var_pair b2 ofs2 LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR cnt2) in
        let evnt1:= Events.freelock (b1, unsigned ofs) in
        exists event2,
          let Hcmpt2:= memcompat2 CMatch in
          let st1':= remLockfFullUpdate st1 tid cnt1 (Kresume sum_state1 Vundef)
                                        new_perms1 (b1, unsigned ofs) in
          let st2':= remLockfFullUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                        new_perms2 (b2, unsigned ofs + delt) in
          match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
          concur_match i mu st1' m1 st2' m2 /\
          inject_sync_event mu evnt1 event2 /\
          syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2 event2.
    Proof.
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.

      replace (restrPermMap HlocksLt) with lk_mem1 in * by
          (subst lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
      clear HlocksLt.
      
      assert (Hmem_equiv1: mem_equiv m1 th_mem1).
      { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2 th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      assert (Heq:unsigned (add ofs (repr delt)) = unsigned ofs + delt).
      { eapply Mem.address_inject; try apply Hinj_lock. 2: eauto.
        unfold perm_interval in Hrange_perm.
        eapply perm_range_perm; eauto.
        { clear. unfold Intv.In; simpl.
          pose proof LKSIZE_pos; omega. }
      }
      
      
      assert (Hinj: Mem.inject mu m1 m2).
      { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
      
      remember (Events.freelock (b2, unsigned ofs + delt )) as event2. 
      
      (* Instantiate some of the existensials *)
      
      exists event2.  
      repeat weak_split. (* 4 goal*)
      
      - !goal(match_self _ _ _ _ _ _).
        inversion Amatch. constructor; eassumption.
      - !goal(concur_match _ _ _ _ _ _ ).
        Lemma concur_match_free_lock:
          forall hb f ocd st1 m1 st2 m2,
            concur_match.concur_match hb ocd f st1 m1 st2 m2 ->
            forall st1' m1' st2' m2' b_lock1 b_lock2 ofs_lock delta
              th_perms1 th_perms2 c1 c2 tid,
            forall (Hlt1 : permMapLt th_perms1 (getMaxPerm m1'))
              (Hlt2 : permMapLt th_perms2 (getMaxPerm m2')),
              Mem.inject f (restrPermMap Hlt1) (restrPermMap Hlt2) ->
              invariant(tpool:=OrdinalThreadPool) st1' ->
              invariant(tpool:=OrdinalThreadPool) st2' ->
              mem_compatible(Sem:=HybridSem (Some hb)) st1' m1 ->
              mem_compatible(Sem:=HybridSem (Some (S hb))) st2' m2 ->
              forall (th_lock_perms1 th_lock_perms2 : access_map)
                (Hlt_lock1 : permMapLt th_lock_perms1 (getMaxPerm m1'))
                (Hlt_lock2 : permMapLt th_lock_perms2 (getMaxPerm m2'))
                cnt1 cnt2,
                Mem.inject f (restrPermMap Hlt_lock1) (restrPermMap Hlt_lock2) ->
                perm_surj f th_lock_perms1 th_lock_perms2 ->
                let st1':=
                    (remLockfFullUpdate
                       st1 tid cnt1 c1 (th_perms1, th_lock_perms1)
                       (b_lock1, ofs_lock)) in
                let st2':=
                    (remLockfFullUpdate
                       st2 tid cnt2 c2 (th_perms2, th_lock_perms2)
                       (b_lock2, ofs_lock + delta)) in
                f b_lock1 = Some (b_lock2, delta) ->
                one_thread_match hb hb tid ocd f c1 (restrPermMap Hlt1) c2
                                 (restrPermMap Hlt2) ->
       concur_match.concur_match hb ocd f st1' m1' st2' m2'.
        Admitted.
        
        admit.
      - !goal(inject_sync_event mu evnt1 event2).
        subst event2; do 2 econstructor; auto. assumption.
        
      - !goal (syncStep _ _ _ _ _ _).
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)
        subst event2. rewrite <-  Heq.

        
        exploit INJ_lock_permissions_image; eauto;
          intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2).
        eapply (step_freelock _ _ _ _ _ )
          with (b:=b2)
               (pmap_tid':= new_perms2);
          eauto; try reflexivity; try solve[apply CMatch].
        
        (* 8 goals produced. *)
        + !goal (semantics.at_external _ _ _ = Some (FREE_LOCK, _)).
          erewrite (Sum_at_external_proper' (S hb));
            try eapply (cur_equiv_restr_mem_equiv _ _ _ Hthread_mem2);
            try reflexivity.
          erewrite <- coerse_state_atx; eauto.
          eapply atx_injection; eauto.
        + !goal (lockRes _ (b2,_) = Some _).
          simpl in *; rewrite <- Hpmap; repeat f_equal; auto.
        + clear - Hempty_lock Hpmap_equiv1 Hpmap_equiv2.
          
          assert (empty_doublemap lock_data).
          { unfold empty_doublemap.
            repeat autounfold with pair in *; simpl in *.
            split; simpl; intros b ofs;
              specialize (Hempty_lock b ofs);
              inv Hempty_lock; auto.
          }
          intros *. rewrite <- Hpmap_equiv1, <- Hpmap_equiv2.
          eapply empty_map_useful.
          eapply inject_empty_maps; assumption.
          
          
        + !goal(Mem.range_perm _ _ _ _ _ _).
          match goal with |- Mem.range_perm ?m _ ?ofs2 _ _ _ =>
                          replace m with lk_mem2;
                            replace ofs2 with (unsigned ofs + delt)
          end.
          replace (unsigned ofs + delt + LKSIZE)
            with (unsigned ofs + LKSIZE + delt) by omega.
          eapply Mem.range_perm_inj; eauto; eapply Hinj_lock.
          subst lk_mem2; simpl; f_equal; apply Axioms.proof_irr.
          
        + !goal(setPermBlock _ _ _ _ _ = _).
          subst new_perms2; simpl.
          rewrite setPermBlock_setPermBlock_var.
          f_equal. subst ofs2; auto.

        + !goal(setPermBlock_var _ _ _ _ _ = _).
          simpl; f_equal.
          subst ofs2. eauto.

    Admitted. (* free_step_diagram_self *)


    
    
    
    (** *Compiled diagrams*)


    Lemma free_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (m1 m1' m1'': mem) (cd : compiler_index) mu pdata
        (st1 : ThreadPool (Some hb))  new_perms1
        (st2 : ThreadPool (Some (S hb))) (m2' : mem) Hcnt1 Hcnt2
        (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
        b1 ofs (code1 : semC)  (code2 : Asm.state) lock_data
        (Hnone_beyond: bounded_nat_func' pdata LKSIZE_nat)
        (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
        (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
        (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
        (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
        (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
        (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
        (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                         Some (FREE_LOCK, (Vptr b1 ofs :: nil)%list))
        (*Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1' m1'' vzero *)
        (Hlock_map: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = Some lock_data)
        (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
        (HlocksLt: permMapLt (lock_perms _ _ Hcnt1) (getMaxPerm m1') )
        (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                    b1 (unsigned ofs) LKSIZE Cur Writable)
        (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                  Mem.perm_order'' (pdata (S i)) (Some Writable))
        (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        exists evnt2 (st2' : t) (m2'' : mem),
          let evnt:= (Events.freelock (b1, unsigned ofs)) in
          let st1':= remLockfFullUpdate st1 hb Hcnt1
                                        (Kresume (SST code1) Vundef) new_perms1
                                        (b1, unsigned ofs) in
          concur_match (Some cd) mu st1' m1' st2' m2'' /\
          inject_sync_event mu evnt evnt2 /\
          let Hcmpt2:= memcompat2 CMatch in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true Hcnt2 Hcmpt2 st2' m2'' evnt2.
    Proof.
      
      intros.
      
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.

      replace (restrPermMap HlocksLt) with lk_mem1 in * by
          (subst lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
      clear HlocksLt.
      
      (* assert (Hmem_equiv1: mem_equiv m1 th_mem1).
      { subst th_mem1; symmetry. eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2 th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. } *)
      
      
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
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      
      
      set (ofs2:= add ofs (repr delta)).
      assert (unsigned ofs2 = unsigned ofs + delta).
      { subst ofs2.
        eapply perm_range_perm with (ofs':=unsigned ofs) in Hrange_perm.
        eapply address_inject_max; swap 1 2.
        eapply Mem.perm_cur_max; eassumption.
        eauto. eauto. pose LKSIZE_pos; hnf; simpl; omega. }

      set (new_perms2:=
             setPermBlock_var_pair b2 (unsigned ofs2) LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR Hcnt2)).
      set (st2':= remLockfFullUpdate st2 hb Hcnt2
                                     (Kresume (TST code2) Vundef) new_perms2
                                     (b2, unsigned ofs2)).
      remember (remLockfFullUpdate st1 hb Hcnt1
                                   (Kresume (SST code1) Vundef) new_perms1
                                   (b1, unsigned ofs)) as st1'.
      (* forward_cmpt_all.
         rename Hcmpt_update into Hcmpt2'.
         rename Hcmpt_update0 into Hcmpt1'. *)
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      assert (Heq:unsigned ofs2 = unsigned ofs + delta).
      { subst ofs2.
        eapply Mem.address_inject; try apply Hinj_lock. 2: eauto.
        unfold perm_interval in Hrange_perm.
        eapply perm_range_perm; eauto.
        { clear. unfold Intv.In; simpl.
          pose proof LKSIZE_pos; omega. }
      }
      
      
      (** * 4. Finally we proceed with the goal: existentials. *)
      
      set (evnt2:= (Events.freelock (b2, unsigned ofs2))).
      
      clean_proofs.
      exists evnt2, st2', m2'; simpl.
      repeat weak_split.
      
      - !context_goal concur_match. admit.
      - subst evnt2. replace (unsigned ofs2) with (unsigned ofs + delta).
        repeat econstructor; eassumption.
      - !goal (syncStep _ _ _ _ _ _).
        simpl in *. 
        
        exploit INJ_lock_permissions_image; eauto;
          intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2); simpl in *.
        eapply (step_freelock _ _ _ _ _ )
          with (b:=b2)
               (pmap_tid':= new_perms2);
          eauto; try reflexivity; try solve[apply CMatch].
        +  !goal (semantics.at_external _ _ _ = Some (FREE_LOCK, _)).
           subst ofs2.
           erewrite (Sum_at_external_proper' (S hb));
            try eapply (cur_equiv_restr_mem_equiv _ _ _ Hthread_mem2);
            try reflexivity. assumption.
        + !goal (lockRes _ (b2,_) = Some _).
          simpl in *; rewrite <- Hpmap; repeat f_equal; auto.
        + clear - Hempty_lock Hpmap_equiv1 Hpmap_equiv2.
          
          assert (empty_doublemap lock_data).
          { unfold empty_doublemap.
            repeat autounfold with pair in *; simpl in *.
            split; simpl; intros b ofs;
              specialize (Hempty_lock b ofs);
              inv Hempty_lock; auto.
          }
          intros *. rewrite <- Hpmap_equiv1, <- Hpmap_equiv2.
          exploit empty_map_useful; intros [HH _].
          exploit HH.
          { eapply inject_empty_maps; eassumption. }
          simpl; eauto.
          
          
        + !goal(Mem.range_perm _ _ _ _ _ _).
          match goal with |- Mem.range_perm ?m _ ?ofs2 _ _ _ =>
                          replace m with lk_mem2;
                            replace ofs2 with (unsigned ofs + delta)
          end.
          replace (unsigned ofs + delta + LKSIZE)
            with (unsigned ofs + LKSIZE + delta) by omega.
          eapply Mem.range_perm_inj; eauto; eapply Hinj_lock.
          subst lk_mem2; simpl; f_equal; apply Axioms.proof_irr.

          Unshelve.
          all: assumption.

    Admitted. (* free_step_diagram_compiled *)
    
    Lemma free_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem(Some hb))) in 
      forall (m1 m2: mem) tid cd (mu : meminj)
        (st1 : ThreadPool (Some hb)) cnt1
        (st2 : ThreadPool (Some (S hb))) cnt2
        (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
        (c : semC) (b : block) (ofs : int)
        (new_perms : Pair access_map)
        (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
        (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        (pdata : nat -> option permission) (lock_data : lock_info)
        (Hnone_beyond: bounded_nat_func' pdata LKSIZE_nat)
        (Hcode: getThreadC cnt1 = Kblocked c)
        (Hat_external: semantics.at_external hybrid_sem c m1  =
                       Some (FREE_LOCK, (Vptr b ofs :: nil)%list))
        (Hlock_map: lockRes st1 (b, Integers.Ptrofs.unsigned ofs) = Some lock_data)
        (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
        (HlocksLt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1) )
        (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                    b (unsigned ofs) LKSIZE Cur Writable)
        (HsetPerms:
           setPermBlock_var_pair b (unsigned ofs) LKSIZE_nat
                                 (pdata, fun _:nat => None) (getThreadR cnt1) = new_perms)
        (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                       Mem.perm_order'' (pdata (S i)) (Some Writable)),
      exists evnt2 (st2' : t) (m2' : mem),
        let evnt:= (Events.freelock (b, unsigned ofs)) in
        let st1':= remLockfFullUpdate st1 tid cnt1
                                      (Kresume c Vundef) new_perms (b, unsigned ofs) in
        concur_match cd mu st1' m1 st2' m2' /\
        inject_sync_event mu evnt evnt2 /\
        let Hcmpt2:= memcompat2 CMatch in
        syncStep(Sem:=HybridSem (Some (S hb)))
                true cnt2 Hcmpt2 st2' m2' evnt2.
    Proof.
      
      intros; simpl in *.
      inv Hsame_sch.
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
          erewrite restr_proof_irr.
          rewrite Hmem_equiv; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
        (* bounded_nat_func' pdata LKSIZE_nat *)
        (edestruct (free_step_diagram_self AsmSem) as
            (e' & Hthread_match & CMatch' & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + !goal (access_map_equiv _ _). clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl. move matchmem at bottom.
            eapply match_mem_proper; try eapply matchmem; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
               clean_proofs; eauto.
        + exists e'; eexists; exists m2.
          repeat weak_split eauto.
         (* * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (remLockfFullUpdate _ _ _ _ _ _ ) _ _ _).
            simpl; eauto.
          * clear - Htrace_inj; auto.*)
          * clean_proofs; eauto.
            
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
        
        rewrite RPM in Hinterference1.
        symmetry in H0.
        clean_proofs.
        exploit (free_step_diagram_compiled m1 m1');
          try eapply CMatch;
          eauto; try reflexivity.
        + econstructor; eassumption.
        + !goal (strict_evolution_diagram _ _ _ _ _ _ _).
          econstructor; eauto; simpl.
          * !goal(mem_interference m1 lev1 m1'). 
            rewrite self_restre_eq in Hinterference1; eauto.
          * !goal(mem_interference m2 lev2 m2'). 
            rewrite self_restre_eq in Hinterference2; eauto.
        + simpl; clean_proofs.
          normal; eauto.
          
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
        
        (edestruct (free_step_diagram_self CSem) as
            (e' & Hthread_match & CMatch' & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl. move matchmem at bottom.
            eapply match_mem_proper; try eapply matchmem; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
            -- symmetry; eapply cur_equiv_restr_mem_equiv; eauto.
               clean_proofs; eauto.
        + exists e'; eexists; exists m2.
          repeat weak_split eauto.
          (*
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (remLockfFullUpdate _ _ _ _ _ _ ) _ _ _).
            adm it.
          * clear - Htrace_inj; auto. *)
          * clean_proofs; eauto.

            Unshelve.
            all: eauto.
    Qed.

    (*TODO move to Mem_equiv*)
    
  End freelock. 
End FreeDiagrams.