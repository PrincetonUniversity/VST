
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
Require Import VST.concurrency.compiler.release_diagrams.
Require Import VST.concurrency.compiler.acquire_diagrams.
Require Import VST.concurrency.compiler.mklock_diagrams.
Require Import VST.concurrency.compiler.free_diagrams.
Require Import VST.concurrency.compiler.fail_acq_diagrams.
Require Import VST.concurrency.compiler.spawn_diagrams.


Section SyncSimulation.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  (* Module MySimulationTactics:= SimulationTactics CC_correct Args.
  Import MySimulationTactics.

  (* We import the proofs for each call *)
  Module MyReleaseDiagrams:= ReleaseDiagrams CC_correct Args.
  Import MyReleaseDiagrams.
  Module MyAcquireDiagrams:= AcquireDiagrams CC_correct Args.
  Import MyAcquireDiagrams.
  Module MyMklockDiagrams:= MklockDiagrams CC_correct Args.
  Import MyMklockDiagrams.
  Module MyFreeDiagrams:= FreeDiagrams CC_correct Args.
  Import MyFreeDiagrams.
  Module MyFailAcqDiagrams:= FailAcqDiagrams CC_correct Args.
  Import MyFailAcqDiagrams.
  Module MySpawnDiagrams:= SpawnDiagrams CC_correct Args.
  Import MySpawnDiagrams.
  Import MyConcurMatch. *)
  
  Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).


  Notation vone:= (Vint Int.one).
  Notation vzero:= (Vint Int.zero).

  
  

  (** * The following lemmas prove the injection 
                  of memories unfer setPermBlock.
   *)

  (** *step_diagram_Self*)

  (* TODO: move the tactics to a "sectoin for tactics" *)
  
  Section SyncCallsDiagrams.
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
    Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
    Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).


    Existing Instance HybridSem.
    Existing Instance dryResources.
    Existing Instance DryHybridMachineSig.
    
    




    


    
    
    Instance at_ext_sum_Proper:
      Proper (Logic.eq ==> mem_equiv ==> Logic.eq )
             (at_external_sum Clight.state Asm.state mem
                              (fun s m => Clight.at_external (Clight.set_mem s m))
                              (fun s m => Asm.at_external (Genv.globalenv Asm_program)
                                                       (Asm.set_mem s m))).
    Proof.
      intros ??? ???; subst.
      change
        (at_external (sem_coresem (HybridSem (Some hb))) y x0 =
         at_external (sem_coresem (HybridSem (Some hb))) y y0).
      eapply Sum_at_external_proper'; try assumption; reflexivity.
    Qed.
    
    
    Lemma external_step_diagram:
      forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
        (st1 : ThreadPool.t) 
        (m1 : mem)
        (st1' : ThreadPool.t)
        (m1' : mem) (tid : nat) (ev : Events.sync_event),
      forall (cd : option compiler_index) (st2 : ThreadPool.t) (mu : meminj) (m2 : mem),
        concur_match cd mu st1 m1 st2 m2 ->
        List.Forall2 (inject_mevent mu) tr1 tr2 ->
        forall (cnt1 : ThreadPool.containsThread st1 tid) (Hcmpt : mem_compatible st1 m1),
          HybridMachineSig.schedPeek U = Some tid ->
          syncStep true cnt1 Hcmpt st1' m1' ev ->
          forall (Hinv':invariant st1') (Hcmpt':mem_compatible st1' m1'),
          exists ev' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
            (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') (tr1 ++ (Events.external tid ev :: nil))
                         (tr2 ++ (Events.external tid ev' :: nil)) /\
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2 (HybridMachineSig.schedSkip U)
              (seq.cat tr2 (Events.external tid ev' :: nil)) st2' m2'.
    Proof.
      intros.
      match goal with
        |- exists (a:?A) (b:?B) (c:?C) (d:?D) (e:?E),
          ?H1 /\
          (Forall2 (inject_mevent e) (_ ++ (?ev1::nil)) (_ ++ (?ev1'::nil))) /\
          ?H3 =>
        cut (exists (a:A) (b:B) (c:C) (d:D) (e:E),
                H1 /\ 
                inject_incr mu e /\
                (inject_mevent e ev1 ev1') /\
                H3)
      end.
      { intros (a&b&c&d&e&(HH1 & HH2 & HH3 & HH4)).
        exists a, b, c, d, e; repeat weak_split (try assumption).
        eapply List.Forall2_app; auto.
        eapply inject_incr_trace; eauto. }
      
      assert (thread_compat1:thread_compat _ _ cnt1 m1) by
          (apply mem_compatible_thread_compat; assumption).
      assert (cnt2: ThreadPool.containsThread st2 tid) by
          (eapply contains12; eauto).
      assert (thread_compat2:thread_compat _ _ cnt2 m2) by
          (apply mem_compatible_thread_compat; eapply H).
      inversion H2; subst.
      - (*Acquire*)
        rename m1 into m1_base.
        remember (fst (thread_mems thread_compat1)) as m1.
        rename m2 into m2_base.
        remember (fst (thread_mems thread_compat2)) as m2.
        assert (Hmax_equiv1: Max_equiv m1_base m1).
        { subst. symmetry.  eapply restr_Max_equiv. }
        assert (Hnb1: Mem.nextblock m1_base = Mem.nextblock m1).
        { subst;reflexivity. }
        assert (Hmem_compat: mem_compatible st1 m1).
        { eapply mem_compat_Max; try eapply Hcmpt; eauto. }

        remember (Build_virtue virtueThread pmap) as angel'.
        unshelve edestruct (acquire_step_diagram hb angel' m1 m1') as
            (?&?&?&?&?&?); subst angel'; simpl in *; eauto;
          try rewrite (restr_proof_irr _ (proj1 (Hcmpt tid cnt1))).
        + hnf.
          !goal(concur_match _ _ _ _ _ _).
          eapply concur_match_perm_restrict in H.
          do 2 rewrite <- mem_is_restr_eq in H.
          subst m1 m2; apply concur_match_perm_restrict.
          assumption. 
        + !goal(access_map_equiv _ (_ m1) ).
          subst. symmetry; apply getCur_restr.
        + !goal(access_map_equiv _ (_ m2) ).
          subst. symmetry; apply getCur_restr.
        (* + !goal(concur_match _ _ _ _ _ _).
            eapply concur_match_perm_restrist in H.
            instantiate (1:= mu).
            instantiate (1:= cd).
            subst m1 m2. eapply H.*)
        + !goal(pair21_prop sub_map _ _).
          move Hbounded at bottom.
          change (sub_map (fst virtueThread) (snd (getMaxPerm m1)) /\
                  sub_map (snd virtueThread) (snd (getMaxPerm m1))).
          unfold Max_equiv in *.
          replace (getMaxPerm m1) with (getMaxPerm m1_base); auto.
          subst m1.
          symmetry; apply restr_Max_eq.
        + !goal(at_external_sum _ _ _ _ _ _ _ = _).
          subst m1; rewrite restr_proof_irr_equiv; eauto.
        + !context_goal lock_update_mem_strict_load.
          assert (Hlock_update_mem_strict_load:
                    lock_update_mem_strict_load
                      b (unsigned ofs) (lock_perms _ _ cnt1)
                      m1_base m1' vone vzero).
          { econstructor; eauto. }
          subst m1; eapply lock_update_mem_strict_load_restr; eauto.
        + econstructor; eauto.
        + unfold Max_equiv in *.
          rewrite <- Hmax_equiv1.
          eapply Hlt_new.
        + unfold fullThUpd_comp, fullThreadUpdate in *.
          subst newThreadPerm.
          simpl in H3.
          assert (Hlt2': permMapLt (getCurPerm m2_base) (getMaxPerm m2)).
          { subst. rewrite getMax_restr. apply mem_cur_lt_max. }
          clean_proofs.
          apply syncStep_restr with (Hlt:=Hlt2') in H5.
          destruct H5 as (?&?&Hstep).
          do 5 econstructor; repeat (weak_split idtac);
            try eapply Hstep.
          * eapply concur_match_perm_restrict2; eauto.
          * apply inject_incr_refl.
          * econstructor; eauto.
          * replace m2_base with (@restrPermMap (getCurPerm m2_base) m2 Hlt2').
            econstructor; eauto; simpl.
            symmetry; subst.
            erewrite <- restrPermMap_idempotent_eq.
            eapply mem_is_restr_eq.
            
            
      - (*Release*)
        (*Shifting to the threads cur.*)
        rename m1 into m1_base.
        remember (fst (thread_mems thread_compat1)) as m1.
        rename m2 into m2_base.
        remember (fst (thread_mems thread_compat2)) as m2.
        remember (Build_virtue virtueThread virtueLP) as angel'.
        assert (Hmax_equiv1: Max_equiv m1_base m1).
        { subst. symmetry.  eapply restr_Max_equiv. }
        assert (Hnb1: Mem.nextblock m1_base = Mem.nextblock m1).
        { subst;reflexivity. }
        assert (Hmem_compat: mem_compatible st1 m1).
        { eapply mem_compat_Max; try eapply Hcmpt; eauto. }
        
        unshelve edestruct (release_step_diagram hb angel' m1 m1') as
            (?&?&?&?&?&?); subst angel';
          try apply HisLock; simpl in *; eauto.
        + !goal(concur_match _ _ _ _ _ _).
          eapply concur_match_perm_restrict in H.
          do 2 rewrite <- mem_is_restr_eq in H.
          subst m1 m2; apply concur_match_perm_restrict.
          assumption.
        + !goal(access_map_equiv _ (_ m1) ).
          subst. symmetry. apply getCur_restr.
        + !goal(access_map_equiv _ (_ m2) ).
          subst. symmetry; apply getCur_restr.
        + !goal(sub_map_virtue _ _).
          replace (getMaxPerm m1) with  (getMaxPerm m1_base).
          constructor; eauto.
          subst m1. symmetry; apply getMax_restr_eq. 
        + !context_goal(at_external_sum).
          simpl. subst m1; simpl.
          rewrite <- Hat_external.
          repeat f_equal; eapply Axioms.proof_irr.
        + (* instantiate(1:= m1'). *)
          assert (Hlock_update_mem_strict_load:
                    lock_update_mem_strict_load
                      b (unsigned ofs) (lock_perms _ _ cnt1)
                      m1_base m1' vzero vone).
          { econstructor; eauto. }
          subst m1; eapply lock_update_mem_strict_load_restr; auto.
        + eapply empty_map_useful; auto.
        + econstructor; eauto.
        + clean_proofs.
          unfold fullThUpd_comp, fullThreadUpdate in *.
          subst newThreadPerm; simpl in H3.
          
          assert (Hlt2': permMapLt (getCurPerm m2_base) (getMaxPerm m2)).
          { subst. rewrite getMax_restr. apply mem_cur_lt_max. }

          apply syncStep_restr with (Hlt:=Hlt2') in H5.
          destruct H5 as (?&?&Hstep).
          do 5 econstructor; repeat (weak_split idtac).
          * eapply concur_match_perm_restrict2; eauto.
          * apply inject_incr_refl.
          * econstructor; eauto.
          * replace m2_base with (@restrPermMap (getCurPerm m2_base) m2 Hlt2').
            econstructor; eauto; simpl.
            symmetry; subst.
            erewrite <- restrPermMap_idempotent_eq.
            eapply mem_is_restr_eq.
            
      - (*Create/Spawn*)
        simpl in *.

        admit.
      - (*Make Lock*)
        pose proof (memcompat2 H) as Hcmpt2.
        rename m1 into m1_base.
        rename m2 into m2_base.
        simpl in *.
        remember (restrPermMap (proj1 (Hcmpt2 tid cnt2))) as m2.
        remember (restrPermMap (proj1 (Hcmpt tid cnt1))) as m1.
        clean_proofs.

        assert (HH:set_new_mems b (unsigned ofs) (getThreadR cnt1) LKSIZE_nat pmap_tid').
        { econstructor; destruct pmap_tid'; simpl in *; subst a a0; reflexivity. }
        
        unshelve edestruct (make_step_diagram hb m1 m1' m2) as (?&?&?&?&?&?);
          eauto; simpl; try solve[subst; eauto].
        + subst; eapply concur_match_perm_restrict; assumption.
        + econstructor; eauto.
        + subst. symmetry; apply getCur_restr.
        + subst. symmetry; apply getCur_restr.
        + econstructor; subst; eauto.
        + clean_proofs.
          unfold fullThUpd_comp, fullThreadUpdate in *.
          
          assert (Hlt2': permMapLt (getCurPerm m2_base) (getMaxPerm m2)).
          { subst. rewrite getMax_restr. apply mem_cur_lt_max. }

          simpl in *.
          apply syncStep_restr with (Hlt:=Hlt2') in H5.
          destruct H5 as (?&?&?).
          clean_proofs.
          
          do 5 econstructor; repeat (weak_split idtac).
          * eapply concur_match_perm_restrict2; eauto.
          * apply inject_incr_refl.
          * econstructor; eauto.
          * replace m2_base with (@restrPermMap (getCurPerm m2_base) m2 Hlt2').
            econstructor; eauto; simpl.
            symmetry; subst.
            erewrite <- restrPermMap_idempotent_eq.
            eapply mem_is_restr_eq.
            
      - (*Free Lock*)
        simpl in Hlock_perm.
        simpl in Hfreeable.
        pose proof (memcompat2 H) as Hcmpt2.
        rename m1' into m1_base.
        rename m2 into m2_base.
        simpl in *.
        remember (restrPermMap (proj1 (Hcmpt2 tid cnt2))) as m2.
        remember (restrPermMap (proj1 (Hcmpt tid cnt1))) as m1.
        clean_proofs.

        unshelve edestruct (free_step_diagram hb m1 m2)
          with (new_perms:=pmap_tid') as (?&?&?&?&?&?);
          eauto; simpl; try solve[subst; eauto]; simpl in *;
            try eassumption.
        + subst m1 m2. eapply concur_match_perm_restrict; eauto.
        + subst m1. rewrite getMax_restr; eapply Hcmpt.
        + constructor; eassumption.
        + subst m1; symmetry; eapply getCur_restr.
        + symmetry; subst m2; eapply getCur_restr.
        + intros b0 ofs0. destruct rmap as (a1 & a2).
          destruct (Hrmap b0 ofs0); simpl in *.
          autounfold with pair; unfold pair_appl, compose; simpl.
          f_equal; eauto.
        + simpl. clean_proofs. unfold perm_interval.
          simpl in *; subst m1.
          assert (Hcur_equiv: Cur_equiv
                                (restrPermMap abs_proof1) (restrPermMap abs_proof2) ).
          { eapply Cur_equiv_restr. reflexivity. }
          rewrite <- Hcur_equiv; eauto.
          
        + destruct pmap_tid' as (a&a0); simpl in *; subst a a0.
          reflexivity.
        + unfold remLockfFullUpdate.
          subst m1; eapply mem_compat_restrPermMap; eauto.
        + clean_proofs.
          unfold fullThUpd_comp, fullThreadUpdate in *.
          
          assert (Hlt2': permMapLt (getCurPerm m2_base) (getMaxPerm m2)).
          { subst. rewrite getMax_restr. apply mem_cur_lt_max. }
          
          assert (Hlt1': permMapLt (getCurPerm m1_base) (getMaxPerm m1)).
          { subst. rewrite getMax_restr. apply mem_cur_lt_max. }
          
          apply syncStep_restr with (Hlt:=Hlt2') in H5.
          destruct H5 as (?&?&Hstep).
          do 5 econstructor; repeat (weak_split idtac).
          * replace m1_base with (@restrPermMap (getCurPerm m1_base) m1 Hlt1').
            eapply concur_match_perm_restrict; eauto.
            { subst m1.
              rewrite mem_is_restr_eq.
              symmetry. eapply restrPermMap_idempotent_eq. }
            
          * apply inject_incr_refl.
          * econstructor; eauto.
          * replace m2_base with (@restrPermMap (getCurPerm m2_base) m2 Hlt2').
            econstructor; eauto; simpl.
            symmetry; subst.
            erewrite <- restrPermMap_idempotent_eq.
            eapply mem_is_restr_eq.

      - (*AcquireFail*)
        remember (memcompat2 H) as Hcmpt2.
        set (m1_restr:= restrPermMap (proj1 (Hcmpt tid cnt1))).
        set (m2_restr:= restrPermMap (proj1 (Hcmpt2 tid cnt2))).
        
        unshelve edestruct (acquire_fail_step_diagram hb m1_restr m2_restr) as (?&?&?&?);
          eauto; simpl; try solve[subst; eauto]; simpl in *;
            try eassumption.
        + subst m1_restr; rewrite restr_Max_eq. apply Hcmpt.
        + exact (getCurPerm m2).
        + subst m2_restr; rewrite restr_Max_eq. apply cur_lt_max.
        + econstructor; eauto.
        + eapply concur_match_perm_restrict; eauto.
        + subst m1_restr; symmetry.
          eapply getCur_restr.
        + symmetry; eapply getCur_restr.
        + subst m1_restr.
          rewrite <- restrPermMap_idempotent; eauto.
        + subst m1_restr. unfold perm_interval.
          rewrite <- restrPermMap_idempotent; eauto.
        + clean_proofs.
          match type of H5 with
            forall Hcmpt2, syncStep _ _ _ ?st2' ?m2' ?ev2 =>
            exists ev2, st2', m2', cd, mu
          end; repeat (weak_split eauto).
          * subst m1_restr.
            clean_proofs.
            rewrite (mem_is_restr_eq m1').
            eapply concur_match_perm_restrict; eauto.
            rewrite (mem_is_restr_eq m1').
            eapply concur_match_perm_restrict; eauto.
          * econstructor; eauto.
          * unshelve econstructor; eauto.
            clean_proofs; simpl.
            unshelve exploit H5. 
            subst  m2_restr; do 2 eapply compat_restr; eauto.
            clean_proofs; simpl in *.
            subst m2_restr.
            intros Hstep.
            assert (HH:(@restrPermMap (getCurPerm m2) (@restrPermMap (thread_perms tid st2 cnt2) m2 abs_proof0)
                                      abs_proof) = m2) .
            { unshelve erewrite <- (restrPermMap_idempotent_eq abs_proof0). 
              apply cur_lt_max.
              symmetry. eapply mem_is_restr_eq. }
            rewrite HH in *.
            dependent_rewrite HH. auto.
            
            Unshelve.
            
    Admitted.

    
  End SyncCallsDiagrams.
  
End SyncSimulation.
