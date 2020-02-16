

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
        (Hneq: tid <> hb )
        lock_data pdata
        (Hinj_b : mu b1 = Some (b2, delt))
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
        (* We can assume invariant and compatible:
           because the second step is assumed to be safe -> 
           satisfies both 
         *)
        let new_perms1:=
            setPermBlock_var_pair b1 (unsigned ofs) LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR cnt1) in
        let st1':= remLockfFullUpdate st1 tid cnt1 (Kresume sum_state1 Vundef)
                                      new_perms1 (b1, unsigned ofs) in
        forall (Hinv1': invariant(tpool:=OrdinalThreadPool) st1')
          (Hcmpt1': mem_compatible(tpool:=OrdinalThreadPool) st1' m1),
          let ofs2:=  unsigned ofs + delt in
          let new_perms2:=
              setPermBlock_var_pair b2 ofs2 LKSIZE_nat
                                    (pdata, fun _:nat => None) (getThreadR cnt2) in
          let evnt1:= Events.freelock (b1, unsigned ofs) in
          exists event2,
            let Hcmpt2:= memcompat2 CMatch in
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
      
      assert ( Hdatalt1: permMapLt_pair
                           (setPermBlock_var_pair
                              b1 (unsigned ofs)  LKSIZE_nat
                              (pdata, fun _ => None)
                              (getThreadR cnt1))
                           (getMaxPerm m1)).
      { assert (Hcnt1': containsThread st1' tid) by eauto.
        assert (HHnew: (getThreadR Hcnt1') =  (new_perms1)).
        { unfold remLockfFullUpdate in *; subst st1'.
          erewrite gRemLockSetRes,gssThreadRes. reflexivity. }
        assert (HHnew11: thread_perms _ _ Hcnt1' = fst (new_perms1)).
        { rewrite HHnew; eauto. }
        assert (HHnew12: lock_perms _ _ Hcnt1' = snd (new_perms1)).
        { rewrite HHnew; eauto. }

        split; simpl.
        - match goal with |- permMapLt ?X _ => replace X with
              (thread_perms tid st1' Hcnt1') end.
          eapply (compat_th _ _ Hcmpt1' Hcnt1'). 
        - match goal with |- permMapLt ?X _ => replace X with
              (lock_perms tid st1' Hcnt1') end.
          eapply (compat_th _ _ Hcmpt1' Hcnt1'). }

      
      set (st2':= remLockfFullUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                     new_perms2 (b2, unsigned ofs + delt) ).
      
      
      assert (Hcmpt2': mem_compatible(tpool:=OrdinalThreadPool) st2' m2).
      { eapply mem_compat_remLockSet.
        eapply mem_compatible_updthread; eauto; swap 1 2.
        reflexivity.
        subst new_perms2; split; simpl; swap 1 2.
        - intros ??.
          rewrite <- setPermBlock_setPermBlock_var'.
          destruct (peq b b2); swap 1 2.
          + rewrite setPermBlock_other_2; eauto.
          + subst.
            destruct (Intv.In_dec ofs0 (ofs2, ofs2 + Z.of_nat LKSIZE_nat)).  
            * rewrite setPermBlock_same; eauto.
              eapply event_semantics.po_None.
            * rewrite setPermBlock_other_1; eauto.
              -- eapply Intv.range_notin in n; simpl in *. eauto.
                 simpl. clear.
                 pose proof LKSIZE_nat_pos. omega.
        - intros ??.
          destruct (peq b b2); swap 1 2.
          + rewrite setPermBlock_var_other_2; eauto.
          + subst.
            destruct (Intv.In_dec ofs0 (ofs2, ofs2 + Z.of_nat LKSIZE_nat)); swap 1 2.
            * rewrite setPermBlock_var_other_1; eauto.
              -- eapply Intv.range_notin in n; simpl in *. eauto.
                 simpl. clear.
                 pose proof LKSIZE_nat_pos. omega.
            * rewrite setPermBlock_var_same; eauto.
              remember (ofs0 - delt) as ofs0'.
              assert (ofs0 = ofs0' + delt) by omega.
              subst ofs0; remember ofs0' as ofs0.
              eapply perm_order''_trans. 
              -- eapply perm_order_perm_impl.
                 intros p; eapply Hinj; eauto.
              -- destruct Hdatalt1 as [Hdatalt _]; simpl in *.
                 specialize (( Hdatalt) b1 ofs0).
                 rewrite setPermBlock_var_same in Hdatalt; eauto.
                 move Hdatalt at bottom.
                 subst ofs2.
                 replace (ofs0 + delt - (unsigned ofs + delt) + 1)
                   with (ofs0 - unsigned ofs + 1) by omega.
                 eapply Hdatalt.
                 subst ofs2.
                 clear - i0. hnf in i0; simpl in *. 
                 omega. }
      assert ( Hdatalt2: permMapLt_pair
                           (setPermBlock_var_pair
                              b2 ofs2  LKSIZE_nat
                              (pdata, fun _ => None)
                              (getThreadR cnt2))
                           (getMaxPerm m2)).
      { assert (Hcnt2': containsThread st2' tid) by eauto.
        assert (HHnew: (getThreadR Hcnt2') =  (new_perms2)).
        { unfold remLockfFullUpdate in *; subst st2'.
          erewrite gRemLockSetRes,gssThreadRes. reflexivity. }
        assert (HHnew11: thread_perms _ _ Hcnt2' = fst (new_perms2)).
        { rewrite HHnew; eauto. }
        assert (HHnew22: lock_perms _ _ Hcnt2' = snd (new_perms2)).
        { rewrite HHnew; eauto. }

        split; simpl.
        - match goal with |- permMapLt ?X _ => replace X with
              (thread_perms tid st2' Hcnt2') end.
          eapply (compat_th _ _ Hcmpt2' Hcnt2'). 
        - match goal with |- permMapLt ?X _ => replace X with
              (lock_perms tid st2' Hcnt2') end.
          eapply (compat_th _ _ Hcmpt2' Hcnt2'). }
      
      remember (Events.freelock (b2, unsigned ofs + delt )) as event2. 
      
      (* Instantiate some of the existensials *)

      destruct Hdatalt1 as [Hdatalt11 Hdatalt12].
      destruct Hdatalt2 as [Hdatalt21 Hdatalt22]. simpl in *.
      
      assert (Hin1:Mem.inject mu (restrPermMap Hdatalt11) (restrPermMap Hdatalt21)).
      {  eapply inject_restr; eauto.
        - eapply mi_perm_perm_setPermBlock_var; eauto.
         (* + intros; eapply perm_order_trans101. eapply HH; eauto.
            constructor. *)
          + eapply Hinj.
          + rewrite Hthread_mem1, Hthread_mem2.
            eapply mi_inj_mi_perm_perm_Cur. eapply Hinj.
        - eapply mi_memval_perm_setPermBlock_var; eauto.
          + rewrite Hthread_mem1.
            eapply mi_inj_mi_memval_perm. eapply Hinj.
          + intros. exploit INJ_lock_content; eauto.    
            unfold inject_lock,inject_lock'.
            intros HH'. normal_hyp.
            unify_injection. 
            eapply H1.  eauto.
        - unfold ofs2.
          rewrite Hthread_mem1, Hthread_mem2.
          eapply mi_perm_inv_perm_setPermBlock_var; eauto.
          eapply inject_mi_perm_inv_perm_Cur; eauto.
          eapply Hinj. }
        assert (Hlock_mem1: access_map_equiv
                               (lock_perms tid st1 cnt1) (getCurPerm lk_mem1)).
         { subst lk_mem1; symmetry; eapply getCur_restr. }
         assert (Hlock_mem2: access_map_equiv
                               (lock_perms tid st2 cnt2) (getCurPerm lk_mem2)).  
         { subst lk_mem2; symmetry; eapply getCur_restr. }

         assert (Hin2:Mem.inject mu (restrPermMap Hdatalt12) (restrPermMap Hdatalt22)).
      { 
         
         eapply inject_restr; eauto.
        - eapply mi_perm_perm_setPermBlock_var; eauto.
          + eapply Hinj.
          + erewrite Hlock_mem1, Hlock_mem2.
            eapply mi_inj_mi_perm_perm_Cur, Hinj_lock.
        - erewrite Hlock_mem1.
          eapply mi_memval_perm_setPermBlock_var; eauto.
          + replace (Mem.mem_contents m1) with
                (Mem.mem_contents lk_mem1).
            replace (Mem.mem_contents m2) with
                (Mem.mem_contents lk_mem2).
            * eapply mi_inj_mi_memval_perm. eapply Hinj_lock.
            * subst lk_mem2; reflexivity.
            * subst lk_mem1; reflexivity.
          + intros. exploit INJ_lock_content; eauto.    
            unfold inject_lock,inject_lock'.
            intros HH'. normal_hyp.
            unify_injection. 
            eapply H1.  eauto.
        - unfold ofs2.
          rewrite Hlock_mem1, Hlock_mem2.
          assert (HMaxlk:Max_equiv m1 lk_mem1) by
              (subst lk_mem1; symmetry; eapply restr_Max_equiv). 
          rewrite HMaxlk.
          eapply mi_perm_inv_perm_setPermBlock_var; eauto.
          eapply inject_mi_perm_inv_perm_Cur; eauto.
          eapply Hinj_lock. }


        
          exists event2.  
      repeat weak_split. (* 4 goal*)
      
      - !goal(match_self _ _ _ _ _ _).
        inversion Amatch. constructor; eassumption.
      - !goal(concur_match _ _ _ _ _ _ ).
        
        { eapply INJ_lock_permissions_image in Hlock_map; eauto.
          normal_hyp.
          unshelve (eapply (concur_match_free_lock CC_correct Args i); eauto);
            simpl; try eassumption.
          + !goal (invariant _ ).
            move Hrange_perm at bottom.
            unfold perm_interval in Hrange_perm.
            eapply invariant_update_free; eauto.
            * intros ? **.
              cut (Mem.perm lk_mem2 b2 ofs0 Cur (Writable)).
              
              unfold Mem.perm.
              rewrite_getPerm.
              rewrite <- Hlock_mem2. eauto.

              replace (ofs0) with ((ofs0 - delt) + delt) by omega.
              eapply Hinj_lock; eauto.
              eapply Hrange_perm; eauto.
              subst ofs2. clear - H1. unfold LKSIZE_nat in *.
              erewrite Z2Nat.id in H1. omega.
              pose LKSIZE_pos. omega.
            * reflexivity.
            * eapply CMatch.
          + eapply perm_surj_setPermBlock_var_all; eauto.
            eapply CMatch.
        + !context_goal one_thread_match.
          { destruct (lt_eq_lt_dec tid hb) as [[Htid_neq'|Htid_neq']|Htid_neq'].
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch);
                simpl; eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H5; simpl in *.
                
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
                     eapply max_map_valid.
                     
                * do 2 rewrite getCur_restr; eauto.
                  eapply perm_surj_setPermBlock_var_all; eauto.
                  eapply ppreimage in matchmem.
                  do 2 rewrite getCur_restr in matchmem; eauto.
            - subst tid; congruence.
            - unshelve (eapply CMatch in Htid_neq' as Hthmatch);
                simpl; eauto.
              + rewrite Hget_th_state1, Hget_th_state2 in Hthmatch.
                unshelve (repeat erewrite <- restrPermMap_idempotent_eq in Hthmatch);
                  eauto.
                inv Hthmatch. inv H5; simpl in *.
                
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
                     eapply max_map_valid.
                     
                * do 2 rewrite getCur_restr; eauto.
                  eapply perm_surj_setPermBlock_var_all; eauto.
                  eapply ppreimage in matchmem.
                  do 2 rewrite getCur_restr in matchmem; eauto. }
                  
                  Unshelve.
                  all: simpl; eauto. }
          
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

        + unfold unsigned in Heq. rewrite Heq.
          subst_set. simpl. unfold remLockfFullUpdate; simpl.
          reflexivity.
    Qed. (* free_step_diagram_self *)


    
    
    
    (** *Compiled diagrams*)

    Lemma free_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (m1 m1': mem) (cd : compiler_index) mu pdata
        (st1 : ThreadPool (Some hb))
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
        let new_perms1:=
            setPermBlock_var_pair b1 (unsigned ofs) LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR Hcnt1) in
        let st1':= remLockfFullUpdate st1 hb Hcnt1
                                      (Kresume (SST code1) Vundef) new_perms1
                                      (b1, unsigned ofs) in
         forall (Hinv1': invariant(tpool:=OrdinalThreadPool) st1')
          (Hcmpt1': mem_compatible(tpool:=OrdinalThreadPool) st1' m1'),

      exists evnt2 (st2' : t) (m2'' : mem),
        let evnt:= (Events.freelock (b1, unsigned ofs)) in
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
      left_diagram.

      replace (restrPermMap HlocksLt) with lk_mem1 in * by
          (subst lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
      clear HlocksLt.
      
      assert (Hmem_equiv1: mem_equiv m1' th_mem1).
      { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2' th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      set (ofs2:= unsigned (add ofs (repr delta))).
      assert (Heq: ofs2 = unsigned ofs + delta).
      { subst ofs2; eapply Mem.address_inject; try apply Hinj_lock. 2: eauto.
        unfold perm_interval in Hrange_perm.
        eapply perm_range_perm; eauto.
        { clear. unfold Intv.In; simpl.
          pose proof LKSIZE_pos; omega. }
      } 

      assert ( Hdatalt1: permMapLt_pair
                           (setPermBlock_var_pair
                              b1 (unsigned ofs)  LKSIZE_nat
                              (pdata, fun _ => None)
                              (getThreadR Hcnt1))
                           (getMaxPerm m1')).
      { assert (Hcnt1': containsThread st1' hb) by eauto.
        assert (HHnew: (getThreadR Hcnt1') =  (new_perms1)).
        { unfold remLockfFullUpdate in *; subst st1'.
          erewrite gRemLockSetRes,gssThreadRes. reflexivity. }
        assert (HHnew11: thread_perms _ _ Hcnt1' = fst (new_perms1)).
        { rewrite HHnew; eauto. }
        assert (HHnew12: lock_perms _ _ Hcnt1' = snd (new_perms1)).
        { rewrite HHnew; eauto. }
        split; simpl.
        - match goal with |- permMapLt ?X _ => replace X with
              (thread_perms hb st1' Hcnt1') end.
          eapply (compat_th _ _ Hcmpt1' Hcnt1'). 
        - match goal with |- permMapLt ?X _ => replace X with
              (lock_perms hb st1' Hcnt1') end.
          eapply (compat_th _ _ Hcmpt1' Hcnt1'). }

      
      set (new_perms2:=
              setPermBlock_var_pair b2 ofs2 LKSIZE_nat
                                    (pdata, fun _:nat => None) (getThreadR Hcnt2)).
      set (st2':= remLockfFullUpdate st2 hb Hcnt2 (Kresume (TST code2) Vundef)
                                     new_perms2 (b2, unsigned ofs + delta) ).
      
      assert (Hcmpt2': mem_compatible(tpool:=OrdinalThreadPool) st2' m2').
      { eapply mem_compat_remLockSet.
        eapply mem_compatible_updthread; eauto; swap 1 2.
        reflexivity.
        subst new_perms2; split; simpl; swap 1 2.
        - intros ??.
          rewrite <- setPermBlock_setPermBlock_var'.
          destruct (peq b b2); swap 1 2.
          + rewrite setPermBlock_other_2; eauto.
          + subst.
            destruct (Intv.In_dec ofs0 (ofs2, ofs2 + Z.of_nat LKSIZE_nat)).  
            * rewrite setPermBlock_same; eauto.
              eapply event_semantics.po_None.
            * rewrite setPermBlock_other_1; eauto.
              -- eapply Intv.range_notin in n; simpl in *. eauto.
                 simpl. clear.
                 pose proof LKSIZE_nat_pos. omega.
        - intros ??.
          destruct (peq b b2); swap 1 2.
          + rewrite setPermBlock_var_other_2; eauto.
          + subst.
            destruct (Intv.In_dec ofs0 (ofs2, ofs2 + Z.of_nat LKSIZE_nat)); swap 1 2.
            * rewrite setPermBlock_var_other_1; eauto.
              -- eapply Intv.range_notin in n; simpl in *. eauto.
                 simpl. clear.
                 pose proof LKSIZE_nat_pos. omega.
            * rewrite setPermBlock_var_same; eauto.
              remember (ofs0 - delta) as ofs0'.
              assert (ofs0 = ofs0' + delta) by omega.
              subst ofs0; remember ofs0' as ofs0.
              eapply perm_order''_trans. 
              -- eapply perm_order_perm_impl.
                 intros p; eapply Hinj'; eauto.
              -- destruct Hdatalt1 as [Hdatalt _]; simpl in *.
                 specialize (( Hdatalt) b1 ofs0).
                 rewrite setPermBlock_var_same in Hdatalt; eauto.
                 move Hdatalt at bottom.
                 subst ofs2.
                 rewrite Heq.
                 replace (ofs0 + delta - (unsigned ofs + delta) + 1)
                   with (ofs0 - unsigned ofs + 1) by omega.
                 eapply Hdatalt.
                 subst ofs2.
                 rewrite Heq in i.
                 clear - i. hnf in i; simpl in *. 
                 omega. }
      assert ( Hdatalt2: permMapLt_pair
                           (setPermBlock_var_pair
                              b2 ofs2  LKSIZE_nat
                              (pdata, fun _ => None)
                              (getThreadR Hcnt2))
                           (getMaxPerm m2')).
      { assert (Hcnt2': containsThread st2' hb) by eauto.
        assert (HHnew: (getThreadR Hcnt2') =  (new_perms2)).
        { unfold remLockfFullUpdate in *; subst st2'.
          erewrite gRemLockSetRes,gssThreadRes. reflexivity. }
        assert (HHnew11: thread_perms _ _ Hcnt2' = fst (new_perms2)).
        { rewrite HHnew; eauto. }
        assert (HHnew22: lock_perms _ _ Hcnt2' = snd (new_perms2)).
        { rewrite HHnew; eauto. }

        split; simpl.
        - match goal with |- permMapLt ?X _ => replace X with
              (thread_perms hb st2' Hcnt2') end.
          eapply (compat_th _ _ Hcmpt2' Hcnt2'). 
        - match goal with |- permMapLt ?X _ => replace X with
              (lock_perms hb st2' Hcnt2') end.
          eapply (compat_th _ _ Hcmpt2' Hcnt2'). }
      
      remember (Events.freelock (b2, unsigned ofs + delta )) as event2. 
      
      (* Instantiate some of the existensials *)

      destruct Hdatalt1 as [Hdatalt11 Hdatalt12].
      destruct Hdatalt2 as [Hdatalt21 Hdatalt22]. simpl in *.

      
      assert (Hin1:Mem.inject mu (restrPermMap Hdatalt11) (restrPermMap Hdatalt21)).
      { subst ofs2; rewrite Heq in *.
        eapply inject_restr; eauto.
        - rewrite Heq.
          eapply mi_perm_perm_setPermBlock_var; eauto.
         (* + intros; eapply perm_order_trans101. eapply HH; eauto.
            constructor. *)
          + eapply Hinj'.
          + rewrite Hthread_mem1, Hthread_mem2.
            eapply mi_inj_mi_perm_perm_Cur. eapply Hinj'.
        - eapply mi_memval_perm_setPermBlock_var; eauto.
          + rewrite Hthread_mem1.
            eapply mi_inj_mi_memval_perm. eapply Hinj'.
          + intros. exploit INJ_lock_content; eauto.    
            unfold inject_lock,inject_lock'.
            intros HH'. normal_hyp.
            unify_injection. 
            eapply H1.  eauto.
        - rewrite Heq.
          rewrite Hthread_mem1, Hthread_mem2.
          eapply mi_perm_inv_perm_setPermBlock_var; eauto.
          eapply inject_mi_perm_inv_perm_Cur; eauto.
          eapply Hinj'. }
        assert (Hlock_mem1: access_map_equiv
                               (lock_perms hb st1 Hcnt1) (getCurPerm lk_mem1)).
         { subst lk_mem1; symmetry; eapply getCur_restr. }
         assert (Hlock_mem2: access_map_equiv
                               (lock_perms hb st2 Hcnt2) (getCurPerm lk_mem2)).  
         { subst lk_mem2; symmetry; eapply getCur_restr. }

         assert (Hin2:Mem.inject mu (restrPermMap Hdatalt12) (restrPermMap Hdatalt22)).
      { subst ofs2.
        eapply inject_restr; eauto.
        - rewrite Heq. eapply mi_perm_perm_setPermBlock_var; eauto.
          + eapply Hinj'.
          + erewrite Hlock_mem1, Hlock_mem2.
            eapply mi_inj_mi_perm_perm_Cur, Hinj_lock.
        - erewrite Hlock_mem1.
          eapply mi_memval_perm_setPermBlock_var; eauto.
          + replace (Mem.mem_contents m1') with
                (Mem.mem_contents lk_mem1).
            replace (Mem.mem_contents m2') with
                (Mem.mem_contents lk_mem2).
            * eapply mi_inj_mi_memval_perm. eapply Hinj_lock.
            * subst lk_mem2; reflexivity.
            * subst lk_mem1; reflexivity.
          + intros. exploit INJ_lock_content; eauto.    
            unfold inject_lock,inject_lock'.
            intros HH'. normal_hyp.
            unify_injection. 
            eapply H1.  eauto.
        - rewrite Heq.
          rewrite Hlock_mem1, Hlock_mem2.
          assert (HMaxlk:Max_equiv m1' lk_mem1) by
              (subst lk_mem1; symmetry; eapply restr_Max_equiv). 
          rewrite HMaxlk.
          eapply mi_perm_inv_perm_setPermBlock_var; eauto.
          eapply inject_mi_perm_inv_perm_Cur; eauto.
          eapply Hinj_lock. }


      
      
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
      
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      
      
      (** * 4. Finally we proceed with the goal: existentials. *)
      
      set (evnt2:= (Events.freelock (b2, ofs2))).
      
      clean_proofs.
      exists evnt2, st2', m2'; simpl.
      repeat weak_split.
      
      - !context_goal concur_match.

        !goal(concur_match _ _ _ _ _ _ ).
        
        { eapply INJ_lock_permissions_image in Hlock_map; eauto.
          normal_hyp.
          subst st1' st2' ofs2.
          (* destruct new_perms1 as [new_perms11 new_perms12];
            destruct new_perms2 as [new_perms21 new_perms22]. *)
          unshelve (eapply (concur_match_free_lock CC_correct Args (Some cd)); eauto);
            simpl; try eassumption.
          + eapply CMatch.
(*          
          + !goal (invariant _ ).
            move Hrange_perm at bottom.
            unfold perm_interval in Hrange_perm.
            eapply invariant_update_free; eauto.
            * intros ? **.
              cut (Mem.perm lk_mem2 b2 ofs0 Cur (Writable)).
              
              unfold Mem.perm.
              rewrite_getPerm.
              rewrite <- Hlock_mem2. eauto.

              replace (ofs0) with ((ofs0 - delta) + delta) by omega.
              eapply Hinj_lock; eauto.
              eapply Hrange_perm; eauto.
              clear - H2. unfold LKSIZE_nat in *.
              erewrite Z2Nat.id in H2. omega.
              pose LKSIZE_pos. omega.
            * reflexivity.
            * eapply CMatch.*)
          + rewrite Heq. eapply perm_surj_setPermBlock_var_all; eauto.
            eapply CMatch.
        + !context_goal one_thread_match.
          { eapply build_match_compiled; auto.
            clean_proofs.
            
            eapply CThread_Resume.
            intros j'' s1' m1''' m2''' lev1' lev2'.
            intros Hstrict_evolution' (*Hincr'*) Hinterference1' Hinterference2'
                   Hafter_ext.

            eapply large_external_diagram; try reflexivity; eauto.
            - eapply freelock_is_consec.
            - eapply freelock_doesnt_return.
            - reflexivity.
            - eapply inject_delta_map_empty.
            - simpl.
              rewrite FreeLockExists.
              econstructor; swap 1 2.
              + econstructor; eauto.
              + eauto.
              + erewrite restre_equiv_eq; eauto.
                simpl; rewrite Hthread_mem1; reflexivity.
            - simpl; rewrite FreeLockExists.
              econstructor; eauto.
              econstructor; eauto.
              erewrite restre_equiv_eq; eauto; simpl.
              simpl; rewrite Hthread_mem2; reflexivity.
            - exploit (interference_consecutive_until _ _ _  Hinterference2).
              eauto.
            - exploit (interference_consecutive_until _ _ _ Hinterference2').
              simpl; auto. } }
      - subst evnt2. subst ofs2; rewrite Heq.
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
          all: try assumption.
          { rewrite <- Hthread_mem1; eauto. }
          { rewrite <- Hthread_mem2; eauto. }

        + subst ofs2 st2'. unfold remLockfFullUpdate. simpl.
          unfold unsigned in Heq; rewrite Heq. 
          reflexivity.
    Qed. (* free_step_diagram_compiled *)
    
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
        let st1':= remLockfFullUpdate st1 tid cnt1
                                      (Kresume c Vundef) new_perms (b, unsigned ofs) in
        forall (Hinv1': invariant(tpool:=OrdinalThreadPool) st1')
        (Hcmpt1': mem_compatible(tpool:=OrdinalThreadPool) st1' m1),
      exists evnt2 (st2' : t) (m2' : mem),
        let evnt:= (Events.freelock (b, unsigned ofs)) in
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
        destruct Hinj' as (args2 & Hinj_b & Hat_external2); eauto.
        inversion Hinj_b as [| ? ? ? ? AA _ CC]; subst; clear Hinj_b.
        inversion AA as [ | | | | ? ? ? ? ? Hinj_b  | ]; subst.

        (* bounded_nat_func' pdata LKSIZE_nat *)
        (edestruct (free_step_diagram_self AsmSem tid) as
            (e' & Hthread_match & CMatch' & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + omega.
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
        destruct Hinj' as (args2 & Hinj_b & Hat_external2); eauto.
        inversion Hinj_b as [| ? ? ? ? AA _ CC]; subst; clear Hinj_b.
        inversion AA as [ | | | | ? ? ? ? ? Hinj_b  | ]; subst.
        
        (edestruct (free_step_diagram_self CSem tid) as
            (e' & Hthread_match & CMatch' & Htrace_inj & external_step)); eauto;
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
        + exists e'; eexists; exists m2.
          repeat weak_split eauto.
          (*  *)
          * clean_proofs; eauto.

            Unshelve.
            all: eauto.
    Qed.

    (*TODO move to Mem_equiv*)
    
  End freelock. 
End FreeDiagrams.