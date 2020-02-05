

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

    
    Lemma spawn_step_diagram_self Sem tid:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
        virtue1 virtue_new1 (m1 m2 : mem) cd
        (mu : meminj) (st1 : ThreadPool (Some hb)) 
        (st2 : ThreadPool (Some (S hb)))
        (cnt1 : ThreadPool.containsThread(Sem:=HybridSem _) st1 tid)
        (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
        (c : semC) (b1 b2 : block) (ofs : int) delt arg
        (Hneq: tid <> hb )
        (Hinj_b : mu b1 = Some (b2, delt))
        (CMatch: concur_match cd mu st1 m1 st2 m2)
        
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

        let st1':= (ThreadPool.updThread cnt1 (Kresume c Vundef) ThreadPerm1) in
        let st1'':= (ThreadPool.addThread st1' (Vptr b1 ofs) arg newThreadPerm1) in
        forall (Hcmpt : mem_compatible  st1'' m1)
          (Hinv' : invariant st1'')
          (Hangel_bound: pair21_prop sub_map virtue1 (snd (getMaxPerm m1)))
          (Hangel_bound_new : pair21_prop sub_map virtue_new1 (snd (getMaxPerm m1)))
          (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
          (Hmatch_mem: match_mem mu m1 m2)
          (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                         Some (FREE_LOCK, (Vptr b1 ofs :: nil)%list))
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
          simpl. replace (restrPermMap Hlt1) with m1.
          2:{  rewrite self_restre_eq; eauto. }
          move Hat_external at bottom.
          eauto.
          
               rewrite Hthread_mem1.
            
          erewrite restr_proof_irr.
          rewrite Hmem_equiv; simpl; eassumption.
        }
        clear sim_atx.
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
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
            
            
            

            
            
    Admitted.

    (** * Here be dragons  *)

    
  End spawn.
End SpawnDiagrams.