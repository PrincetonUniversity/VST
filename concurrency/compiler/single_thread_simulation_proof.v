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
Require Import VST.concurrency.compiler.Asm_lemmas.
Require Import VST.concurrency.compiler.synchronisation_symulations.



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
Require Import VST.concurrency.compiler.Asm_self_simulation.
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


(* migration: MOVE TO OTHER FILES: *)

      (* Propers for Clight and Asm *)

(* End MIGRATION! *)


Ltac subst_sig:=
  match goal with
    H': existT _ _ _ = existT _ _ _ |- _ =>
    eapply Eqdep.EqdepTheory.inj_pair2 in H'; subst
  end.




Section ThreadedSimulation.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  
  (*Module MySyncSimulation:= SyncSimulation CC_correct Args.
  Import MySyncSimulation.*)
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  (* Module MyConcurMatch := ConcurMatch CC_correct Args.*)

  

  
  Section ThreadedSimulation.
    (*Import MySimulationTactics.MyConcurMatch.*)
    
    
    
    Section CompileOneThread.
      Import OrdinalPool.
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
      

      Definition cast_t {Sem}:
        @OrdinalPool.t _ Sem -> @ThreadPool.t _ Sem (@OrdinalThreadPool dryResources _):=
        fun X => X.

      Lemma free_perms:
        forall m b0 lo hi m', Mem.free m b0 lo hi = Some m' ->
                         forall b ofs,
                           (getCurPerm m') !! b ofs =
                           (getCurPerm m) !! b ofs /\
                           (getMaxPerm m') !! b ofs =
                           (getMaxPerm m) !! b ofs
                           \/
                           (getCurPerm m) !! b ofs = Some Freeable.
      Proof.
        intros.
        repeat rewrite getCurPerm_correct, getMaxPerm_correct.
        unfold permission_at.
        pose proof (juicy_mem.free_not_freeable_eq m b0 lo hi m' b ofs H).
        unfold Memory.access_at in *; simpl in *.
        eapply Mem.free_result in H as HH.
        unfold Mem.unchecked_free in H; subst m'; simpl in *.
        clear H0.
        destruct (peq b b0); subst.
        - rewrite PMap.gss. 
          match_case; eauto.
          right. eapply Mem.free_range_perm in H. 
          exploit (H ofs).
          + eapply andb_prop in Heqb; normal_hyp.
            simpl in *.
            destruct (zle lo ofs); simpl in *; try congruence.
            destruct (zlt ofs hi); simpl in *; try congruence.
            omega.
          + unfold Mem.perm.
            destruct ((Mem.mem_access m) !! b0 ofs Cur);
              intros HH; inv HH; eauto.
        - rewrite PMap.gso; auto.
      Qed.
      Lemma mem_step_perms_max:
        forall m m', mem_step m m' ->
                forall b ofs,
                  (getCurPerm m') !! b ofs = (getCurPerm m) !! b ofs /\
                  (getMaxPerm m') !! b ofs = (getMaxPerm m) !! b ofs \/
                  (getMaxPerm m) !! b ofs = None \/
                  (getCurPerm m) !! b ofs = Some Freeable.
      Proof.
        intros. induction H.
        - left. split; symmetry;
                  try eapply memory_lemmas.MemoryLemmas.mem_storebytes_cur; eauto.
          do 2 erewrite getMaxPerm_correct; unfold permission_at.
          symmetry; erewrite Mem.storebytes_access; eauto.
        - destruct (peq b b').
          + subst; right; left.
            apply Mem.alloc_result in H.
            pose proof (Mem.nextblock_noaccess m b' ofs Max).
            rewrite_getPerm; apply H0.
            subst; apply Plt_strict.
          + left. 
            pose proof (Memory.alloc_access_other m lo hi m' b' H b ofs).
            pose proof (H0 Cur ltac:(left; eauto)).
            pose proof (H0 Max ltac:(left; eauto)).
            unfold Memory.access_at in *. repeat rewrite_getPerm.
            simpl in *; eauto.
        - revert  m m' H b ofs.
          induction l.
          + simpl; intros. inv H; eauto.
          + intros. simpl in H.
            destruct a as (p0, hi); destruct p0 as (b0, lo).
            match_case in H.
            exploit free_perms; eauto. intros HH.
            destruct HH as [ [HH1 HH2] |]; eauto.
            repeat rewrite <- HH1; rewrite <- HH2.
            clear HH1 HH2.
            eapply IHl; eauto.
        - destruct IHmem_step1 as [[HH1 HH2]|[?|?]]; eauto.
          repeat rewrite <- HH1, <- HH2; eauto.
      Qed.
      
      Lemma mem_step_perms:
        forall m m', mem_step m m' ->
                forall b ofs,
                  (getCurPerm m') !! b ofs = (getCurPerm m) !! b ofs \/
                  (getMaxPerm m) !! b ofs = None \/
                  (getCurPerm m) !! b ofs = Some Freeable.
      Proof.
        intros; exploit mem_step_perms_max; eauto;
          intros [[]|[?|?]]; eauto.
      Qed.
      
      Lemma perms_permMapsDisjoint:
        forall A A' M B,
          (forall b ofs, A' !! b ofs = A !! b ofs \/
                    M !! b ofs = None \/
                    A !! b ofs = Some Freeable) ->
          permMapLt B M ->
          permMapsDisjoint A B ->
          permMapsDisjoint A'  B.
      Proof.
        intros * HH Hlt Hdisj b ofs.
        specialize (HH b ofs).
        destruct HH as [?|[? | ?]].
        - rewrite H; eapply Hdisj.
        - specialize (Hlt b ofs).
          rewrite H in Hlt; simpl in Hlt.
          match_case in Hlt.
          unfold perm_union. econstructor; simpl.
          match_case; eauto.
        - specialize (Hdisj b ofs);
            destruct Hdisj. rewrite H in H0.
          simpl in H0. match_case in H0.
          unfold perm_union. econstructor; simpl.
          match_case; eauto.
      Qed.
      
      Lemma perms_permMapCoherence:
        forall A A' M B,
          (forall b ofs, A' !! b ofs = A !! b ofs \/
                    M !! b ofs = None \/
                    A !! b ofs = Some Freeable) ->
          permMapLt B M ->
          permMapCoherence A B ->
          permMapCoherence A'  B.
      Proof.
        intros * HH Hlt Hdisj b ofs.
        specialize (HH b ofs).
        destruct HH as [?|[? | ?]].
        - rewrite H; eapply Hdisj.
        - specialize (Hlt b ofs).
          rewrite H in Hlt; simpl in Hlt.
          match_case in Hlt.
          unfold perm_coh. 
          repeat match_case; eauto.
        - specialize (Hdisj b ofs); hnf in Hdisj.
          rewrite H in Hdisj; match_case in Hdisj.
          unfold perm_coh. repeat match_case; eauto.
      Qed.
      Instance permMapCoherence_Proper:
        Proper (access_map_equiv ==> access_map_equiv ==> iff) permMapCoherence.
      Proof.
        setoid_help.proper_iff; setoid_help.proper_intros.
        intros b ofs; unfold permMapCoherence in *.
        rewrite <- H, <- H0. apply H1.
      Qed.
      
      Lemma mem_step_preserves_invariant:
        forall hb (st st': @t dryResources (HybridSem (@Some nat hb)))
          i cnt m m' c
          (Hcur: access_map_equiv (getCurPerm m) (thread_perms i st cnt)),
          @mem_compatible (HybridSem _) _ st m ->
          @invariant  (HybridSem _) _ st ->
          mem_step m m' ->
          st' = updThread cnt c (getCurPerm m', snd (@getThreadR dryResources _ i st cnt)) ->
          @invariant (HybridSem _) _ st'.
      Proof.
        intros.
        rename H into Hcmpt.
        rename H0 into Hinv.

        pose proof (mem_step_perms _ _ H1) as Hperms; clear H1.
        
        eapply synchronisation_lemmas.invariant_update_thread; simpl; eauto.
        - intros. assert (Hneq: i <> j) by eauto; clear H.
          unshelve exploit @no_race_thr; try eapply Hneq; simpl; eauto.
          intros [? ?]; split; simpl in *; eauto.
          
          eapply perms_permMapsDisjoint; eauto.
          + eapply Hcmpt.
          + eapply permMapsDisjoint_Proper; try eapply Hcur; try eassumption; try reflexivity.
            
        - intros. 
          unshelve exploit @no_race; simpl; eauto.
          intros [? ?]; split; simpl in *; eauto.
          
          eapply perms_permMapsDisjoint; eauto.
          + eapply Hcmpt; eauto.
          + eapply permMapsDisjoint_Proper; try eapply Hcur; try eassumption; reflexivity.
        - simpl. eapply perms_permMapCoherence; eauto.
          + eapply Hcmpt; eauto.
          + rewrite Hcur. exploit @thread_data_lock_coh; eauto.
            intros [? ?]. eapply H.
        - simpl; intros.
          split.
          + exploit @thread_data_lock_coh; eauto. intros [? _].
            eapply perms_permMapCoherence; eauto.
            * eapply Hcmpt; eauto.
            * rewrite Hcur. exploit @thread_data_lock_coh; eauto.
              intros [? ?]. simpl in *. eapply H1.
          + exploit @thread_data_lock_coh; eauto. intros [? _].
            simpl in *; eapply H0.
        - simpl; intros. split.
    + eapply Hinv; eauto.
    + exploit @locks_data_lock_coh; eauto. intros [? _].
      eapply perms_permMapCoherence; eauto.
      * eapply Hcmpt; eauto.
      * rewrite Hcur. apply H0.

        Unshelve.
        all: simpl; eauto.
      Qed.

        
    Lemma Asm_preserves_invariant:
  forall hb g i (st: @t dryResources (HybridSem (@Some nat hb)))
    cnt st' (th_st: Smallstep.state (Asm.part_semantics g)) c2 m Hlt t0
    (Hgenv:Asm_core.safe_genv Asm_g),
    @mem_compatible (HybridSem _) _ st m ->
    @invariant  (HybridSem _) _ st ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    forall (Hext:Asm.at_external Asm_g (Asm.set_mem c2 th_m) = None),
    Asm.step Asm_g (Asm.set_mem c2 th_m) t0 th_st ->
    st' = updThread cnt (Krun (TST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    @invariant (HybridSem _) _ st'.
Proof.
  intros.
  rename H into Hcmpt.
  rename H0 into Hinv.

  eapply (mem_step_preserves_invariant _ _ _ _ _ th_m); eauto.
  - subst_set. eapply getCur_restr.
  - subst_set; eapply synchronisation_lemmas.compat_restr; eauto.
  - exploit Asm_core.asm_mem_step.
    + simpl; econstructor; simpl; eauto. 
    + assumption. 
    + auto.
Qed.
Lemma Clight_preserves_invariant:
  forall hb g i (st: @t dryResources (HybridSem (@Some nat hb)))
    cnt st' (th_st: Smallstep.state (Clight.part_semantics2 g)) c2 m Hlt t0,
    @mem_compatible (HybridSem _) _ st m ->
    @invariant  (HybridSem _) _ st ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    forall (Hext:Clight.at_external (Clight.set_mem c2 th_m) = None),
    Clight.step2 g (Clight.set_mem c2 th_m) t0 th_st ->
    st' = updThread cnt (Krun (SST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    @invariant (HybridSem _) _ st'.
Proof.
  intros.
  rename H into Hcmpt.
  rename H0 into Hinv.

  eapply (mem_step_preserves_invariant _ _ _ _ _ th_m); eauto.
  - subst_set. eapply getCur_restr.
  - subst_set; eapply synchronisation_lemmas.compat_restr; eauto.
  - eapply Clightcore_coop.CLC_corestep_mem; simpl.
    econstructor; eauto.
Qed.

Definition cmpt_valid_blocks (Sem : Semantics) (tpool : ThreadPool.ThreadPool)
       (tp : ThreadPool.t) (m : mem):=
  forall (l : address) (rmap : lock_info),
                     ThreadPool.lockRes tp l = Some rmap ->
                     Mem.valid_block m (fst l).
Record factored_compt(Sem : Semantics) (tpool : ThreadPool.ThreadPool)
       (tp : ThreadPool.t) (m : mem) b ofs : Prop :=
  { compat_th : forall (tid : nat) (cnt : ThreadPool.containsThread tp tid),
      Mem.perm_order'' ((getMaxPerm m)!! b ofs)
                       ((fst (ThreadPool.getThreadR cnt)) !! b ofs)  /\
      Mem.perm_order'' ((getMaxPerm m)!! b ofs)
                       ((snd (ThreadPool.getThreadR cnt)) !! b ofs);
    compat_lp : forall (l : address) (pmaps : lock_info),
        ThreadPool.lockRes tp l = Some pmaps ->
        Mem.perm_order'' ((getMaxPerm m)!! b ofs)
                         ((fst pmaps) !! b ofs)  /\
        Mem.perm_order'' ((getMaxPerm m)!! b ofs)
                         ((snd pmaps) !! b ofs)}.


Lemma factor_compt:
  forall Sem tpool tp m,
    (@mem_compatible Sem tpool tp m) <->
    (cmpt_valid_blocks Sem tpool tp m /\
      forall b ofs, @factored_compt Sem tpool tp m b ofs).
Proof.
  intros; split; intros * HH.
  - inv HH; econstructor; intros; eauto.
    econstructor; intros; eauto.
    + split; eapply compat_th0.
    + split; eapply compat_lp0; eauto.
  - econstructor; intros; eauto.
    + split; intros ??; eapply HH.
    + split; intros ??; eapply HH; eauto.
    + eapply HH; eauto. 
Qed.
Lemma useful_disjoint:
  forall A B X b ofs,
    permMapsDisjoint A B ->
    B !! b ofs = Some Freeable ->
    Mem.perm_order'' X (A !! b ofs).
Proof.
  intros.
  specialize (H b ofs); rewrite H0 in H.
  inv H. unfold perm_union in H1; repeat match_case in H1.
  apply event_semantics.po_None.
Qed.
Lemma useful_coherence:
  forall A B X b ofs,
    permMapCoherence B A ->
    B !! b ofs = Some Freeable ->
    Mem.perm_order'' X (A !! b ofs).
Proof.
  intros.
  specialize (H b ofs); rewrite H0 in H.
  simpl in H. repeat match_case in H.
  apply event_semantics.po_None.
Qed.
Lemma mem_step_preserves_compat:
  forall hb i (st: @t dryResources (HybridSem (@Some nat hb)))
    cnt st' m m' c
    (Hcur: access_map_equiv (getCurPerm m) (thread_perms i st cnt)),
    @invariant (HybridSem _) _ st -> 
    @mem_compatible (HybridSem _) _ st m ->
    mem_step m m' ->
    st' = updThread cnt c
                    (getCurPerm m',
                     snd (getThreadR cnt)) ->
      @mem_compatible (HybridSem _) _ st' m'.
Proof.
    intros.
    rename H0 into Hcmpt.
    rename H into Hinv.
    pose proof (mem_step_perms_max _ _ H1) as Hperms.

    eapply factor_compt in Hcmpt as [Hlock_valid Hcmpt].
  
    eapply factor_compt; split.
    {!goal(cmpt_valid_blocks _ _ _ _ ).
     eapply mem_step_nextblock' in H1.
     hnf; intros. unfold Mem.valid_block.
     
     subst st'; simpl in *; rewrite gsoThreadLPool in H.
     eapply Hlock_valid in H; eauto. unfold Mem.valid_block in H.
     eapply Plt_Ple_trans; try eassumption. }

    
    intros b ofs. specialize (Hcmpt b ofs).
    
  specialize (Hperms b ofs);
    destruct Hperms as [?|[?|?]]; normal_hyp; swap 1 2.
    -  inv Hcmpt. rewrite H in *.
     econstructor.
     + intros tid cnt'.
       destruct (Nat.eq_dec i tid).
       * subst; unshelve exploit @gssThreadRes; try eapply cnt'.
         simpl; intros HH; rewrite HH; simpl.
         split.
         -- simpl. eapply cur_lt_max.
         -- simpl; eapply perm_order''_trans; eauto.
            apply event_semantics.po_None.
            eapply compat_th0.
       * assert (cnt0:containsThread st tid) by eauto.
         exploit (gsoThreadRes cnt0 n cnt'); simpl;
           intros HH; rewrite HH; clear HH.
         split; simpl; eapply perm_order''_trans; eauto;
         try eapply event_semantics.po_None;
         eapply compat_th0.
     + simpl. intros. rewrite gsoThreadLPool in H0.
         split; simpl; eapply perm_order''_trans; eauto;
         try eapply event_semantics.po_None;
         eapply compat_lp0; eauto.
  - inv Hcmpt. rewrite <- H0 in *. 
    econstructor.
    + intros tid cnt'.
       destruct (Nat.eq_dec i tid).
       * subst; unshelve exploit @gssThreadRes; try eapply cnt'.
         simpl; intros HH; rewrite HH; simpl.
         split.
         -- simpl. eapply cur_lt_max.
         -- eapply compat_th0.
      * assert (cnt0:containsThread st tid) by eauto.
         exploit (gsoThreadRes cnt0 n cnt'); simpl;
           intros HH; rewrite HH; clear HH.
         eapply compat_th0.
    + simpl. intros. rewrite gsoThreadLPool in H2.
      eapply compat_lp0; eauto.
  - econstructor.
    + intros tid cnt'.
       rewrite Hcur in H.
       destruct (Nat.eq_dec i tid).
       * subst; unshelve exploit @gssThreadRes; try eapply cnt'.
         simpl; intros HH; rewrite HH; simpl.
         split.
         -- simpl. eapply cur_lt_max.
         -- eapply useful_coherence; eauto.
            inv Hinv.
            specialize (thread_data_lock_coh0 _ cnt) as (? & _).
            eapply H0.
       * subst st'; assert (cnt0:containsThread st tid).
         { simpl in cnt'. eapply cntUpdate'; eauto . }
         exploit (gsoThreadRes cnt0 n cnt'); simpl;
           intros HH; rewrite HH; clear HH.
         split; [eapply useful_disjoint| eapply useful_coherence]; try eassumption.
         -- apply permMapsDisjoint_comm.
            eapply Hinv; auto.
         -- inv Hinv; simpl in *.
            specialize (thread_data_lock_coh0 _ cnt0) as (? & _).
            eapply H0.
    + rewrite Hcur in H.
      subst; simpl. intros. rewrite gsoThreadLPool in H0.
      split; [eapply useful_disjoint| eapply useful_coherence]; try eassumption.
      * apply permMapsDisjoint_comm.
        inv Hinv. eapply no_race0; eauto.
      * inv Hinv; simpl in *.
        specialize (locks_data_lock_coh0 _ _ H0) as (? & _).
        eapply H2.
  Qed.

  Lemma Asm_preserves_compat:
  forall hb g i (st: @t dryResources (HybridSem (@Some nat hb)))
    cnt st' (th_st: Smallstep.state (Asm.part_semantics g)) c2 m Hlt t0
    (Hgenv:Asm_core.safe_genv Asm_g),
    @invariant (HybridSem _) _ st -> 
    @mem_compatible (HybridSem _) _ st m ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    forall (Hext:Asm.at_external Asm_g (Asm.set_mem c2 th_m) = None),
    Asm.step Asm_g (Asm.set_mem c2 th_m) t0 th_st ->
    st' = updThread cnt (Krun (TST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    @mem_compatible (HybridSem _) _ st' (Asm.get_mem th_st).
  Proof.
  
  intros.
  rename H into Hinv.
  rename H0 into Hcmpt.
  simpl in H1.
  exploit Asm_core.asm_mem_step.
  { simpl; econstructor; simpl; eauto. }
  { assumption. }
  intros HH.

  eapply mem_step_preserves_compat; try eapply HH; eauto.
  - subst_set. apply getCur_restr.
  - subst_set; apply mem_compat_restrPermMap; assumption.
  Qed.

    Lemma Asm_plus_preserves_invariant_cmpt:
  forall hb g i (st: @t dryResources (HybridSem (@Some nat hb)))
    cnt st' (th_st: Smallstep.state (Asm.part_semantics g)) c2 m Hlt
    (Hgenv:Asm_core.safe_genv Asm_g),
    @mem_compatible (HybridSem _) _ st m ->
    @invariant  (HybridSem _) _ st ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    corestep_plus (Asm_core.Asm_core_sem Asm_g) c2 
                  th_m th_st (Smallstep.get_mem th_st) ->
    st' = updThread cnt (Krun (TST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    @invariant (HybridSem _) _ st' /\
    @mem_compatible (HybridSem _) _ st' (Smallstep.get_mem th_st).
Proof.
  intros.
  rename H into Hcmpt.
  rename H0 into Hinv.

  destruct H1.  revert st th_st m Hcmpt Hinv cnt Hlt th_perm th_m c2 st' H2 H .
  induction x.
  - intros. simpl in H. destruct H as (?&?&?&HH); inv HH.
    inv H; simpl in *. split.
    + eapply Asm_preserves_invariant; eauto.
    + eapply Asm_preserves_compat; eauto.
  - intros. simpl in H. destruct H as (?&?&H&Hsteps).
    inv H; simpl in *.
    eapply Asm_preserves_invariant in H0 as Hinv'; eauto.
    eapply Asm_preserves_compat in H0 as Hcmpt'; eauto.
    eapply IHx; eauto.
    + rewrite updThread_twice, gssThreadRes; auto.
    + erewrite restrPermMap_rewrite, <- mem_is_restr_eq; eauto.
      rewrite gssThreadRes; reflexivity.

      Unshelve.
      all: eauto.
      rewrite gssThreadRes; simpl.
      apply cur_lt_max.
Qed.


  
  Lemma Clight_preserves_compat:
    
  forall hb g i (st: @t dryResources (HybridSem (@Some nat hb)))
    cnt st' (th_st: Smallstep.state (Clight.part_semantics2 g)) c2 m Hlt t0,
    @mem_compatible (HybridSem _) _ st m ->
    @invariant  (HybridSem _) _ st ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    forall (Hext:Clight.at_external (Clight.set_mem c2 th_m) = None),
    Clight.step2 g (Clight.set_mem c2 th_m) t0 th_st ->
    st' = updThread cnt (Krun (SST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    @mem_compatible (HybridSem _) _ st' (Clight.get_mem th_st).
  Proof.
  
  intros.
  rename H into Hinv.
  rename H0 into Hcmpt.
  simpl in H1.
  exploit Clightcore_coop.CLC_corestep_mem; simpl.
  { simpl; econstructor; simpl; eauto. }
  intros HH.

  eapply mem_step_preserves_compat; try eapply HH; eauto.
  - subst_set. apply getCur_restr.
  - subst_set; apply mem_compat_restrPermMap; assumption.
  Qed.

Inductive sync_event: Events.event -> Prop:=
| sync_Event_acq_rel: forall e dmp e',
    sync_event (Events.Event_acq_rel e dmp e')
| sync_Event_spawn: forall b dmp1 dmp2,
    sync_event (Events.Event_spawn b dmp1 dmp2).
Definition not_sync_event (ev:Events.event):= ~ sync_event ev.
Definition not_sync_trace := Forall not_sync_event.


Definition Asm_externals_have_events {F V} (ge:Genv.t (AST.fundef F) V):=
  forall b f ef args res m t m',
    Genv.find_funct_ptr ge b = Some (AST.External f) ->
    Events.external_call ef Asm_g args m t res m' ->
    t <> nil.
Context (Hexterns_have_events: Asm_externals_have_events Asm_g)
        (Hrestricted_builtins: Asm_core.safe_genv Asm_g).

  Lemma step_nil_trace_not_atx:
  forall s1 s2,
    Asm.step Asm_g s1 nil s2 ->
    Asm.at_external Asm_g s1 = None.
Proof.
  intros. unfold Asm.at_external.
  inv H.
  - rewrite H0.
    match_case. rewrite H1; auto.
  - rewrite H0.
    match_case. rewrite H1; auto.
  - rewrite H0.
    match_case. rewrite H1; auto.
    eapply Asm.get_arguments_correct in H2.
    rewrite H2.
    eapply Hexterns_have_events in H3; eauto.
    congruence.
Qed.

      (* Where to move this:*)
      
      (*
        ConcurMatch used to be here. 
       *)

      
      (* The following tactics are also in permissions.v  
         but for some reason that one doesn't work...
       *)
      Ltac unfold_getCurPerm:=
        repeat rewrite getCurPerm_correct in *;
        unfold permission_at in *.
      Ltac unfold_getMaxPerm:=
        repeat rewrite getMaxPerm_correct in *;
        unfold permission_at in *.
      Ltac unfold_getPerm:=
        try unfold_getMaxPerm; try unfold_getMaxPerm.
      
      (** *Tactics
         These tactics are here becasue they must be outside a section.
         they also must be after concur_match definition.
       *)

      (*Do I have to reppeat the LTAC from the section? *)


      Inductive opt_rel' {A} (ord: A -> A -> Prop): option A -> option A -> Prop:=
      | Some_ord:
          forall x y, ord x y -> opt_rel' ord (Some x) (Some y).
      
      Lemma option_wf:
        forall A (ord: A -> A -> Prop),
          well_founded ord ->
          well_founded (opt_rel' ord).
      Proof.
        unfold well_founded.
        intros.
        destruct a.
        2: econstructor; intros; inversion H0.
        specialize (H a).
        induction H.
        econstructor; intros.
        inversion H1; subst.
        eapply H0; eauto.
      Qed.


      Lemma simulation_equivlanence:
        forall s3 t s2 cd cd0,
          (Smallstep.plus (Asm.step (Genv.globalenv Asm_program)) 
                          s3 t s2 \/
           Smallstep.star (Asm.step (Genv.globalenv Asm_program)) 
                          s3 t s2 /\ InjorderX compiler_sim cd cd0) ->
          Smallstep.plus (Asm.step (Genv.globalenv Asm_program)) 
                         s3 t s2 \/
          t = Events.E0 /\
          s2 = s3 /\
          InjorderX compiler_sim cd cd0.
      Proof.
        intros. destruct H; eauto.
        destruct H.
        inversion H; subst; eauto.
        left. econstructor; eauto.
      Qed.
      


      (*This lemma is used when the compiled thread steps*)
      
      Ltac exploit_match tac:=  
        unfold match_thread_target,match_thread_source in *;
        repeat match goal with
               | [ H: ThreadPool.getThreadC ?i = _ ?c |- _] => simpl in H
               end;
        match goal with
        | [ H: getThreadC ?i = _ ?c,
               H0: context[match_thread] |- _ ] =>
          match type of H0 with
          | forall (_: ?Hlt1Type) (_: ?Hlt2Type), _ =>
            assert (Hlt1:Hlt1Type); [
              first [eassumption | tac | idtac]|
              assert (Hlt2:Hlt2Type); [
                first [eassumption | tac | idtac]|
                specialize (H0 Hlt1 Hlt2);
                rewrite H in H0; inversion H0; subst; simpl in *; clear H0
            ]]
          end

        | [ H: getThreadC ?i = _ ?c,
               H0: context[match_thread_compiled] |- _ ] =>
          match type of H0 with
          | forall (_: ?Hlt1Type) (_: ?Hlt2Type), _ =>
            assert (Hlt1:Hlt1Type); [
              first [eassumption | tac | idtac]|
              assert (Hlt2:Hlt2Type); [
                first [eassumption | tac | idtac]|
                specialize (H0 Hlt1 Hlt2);
                rewrite H in H0; inversion H0; subst; simpl in *; clear H0
            ]]
          end
        end;
        fold match_thread_target in *;
        fold match_thread_source in *.

      (* Build the concur_match *)
      Ltac destroy_ev_step_sum:=
        match goal with
        | [ H: ev_step_sum _ _ _ _ _ _ _ |- _ ] => inversion H; clear H
        end.
      
      Lemma break_existensial_of_thread_stepN:
        forall G TID SCH TR C M res, 
        forall Sem ge U c1 m1 c2 m2 c3 m3,
        @machine_semantics.thread_step G TID SCH TR C M res Sem ge U c1 m1 c2 m2 ->
        (exists n : nat, machine_semantics_lemmas.thread_stepN Sem ge n U c2 m2 c3 m3) ->
        exists n : nat, machine_semantics_lemmas.thread_stepN Sem ge (S n) U c1 m1 c3 m3.
      Proof.
        intros; normal.
        repeat (econstructor; eauto).
      Qed.
      
      Lemma thread_step_plus_from_corestep':
        forall NN m tge U i st2 m2
          (Hinv: @invariant (HybridSem _) (@OrdinalThreadPool dryResources _) st2)
          (code2 : Asm.state)
          (s4' : Smallstep.state (Asm.part_semantics Asm_g))
          (cnt2: containsThread st2 i)
          (Hcmpt: mem_compatible st2 m2)
          (m4' : mem) m2_i Hlt2
          (Hm_eq: m2_i =  (@restrPermMap (fst (getThreadR cnt2)) m2 Hlt2)),
          corestepN (Asm_core.Asm_core_sem Asm_g) (S NN) code2 m2_i s4' m4' ->
          getThreadC cnt2 = Krun (TST code2) ->
            HybridMachineSig.schedPeek U = Some i ->
            machine_semantics_lemmas.thread_step_plus
              (HybConcSem (Some (S hb)) m) tge U st2
              m2 (updThread cnt2 (Krun (TState Clight.state Asm.state s4'))
                            (getCurPerm m4', snd (getThreadR cnt2))) m4'.
      Proof.
        simpl; induction NN; intros.
        - subst; destruct H as (c2 & m3 & STEP & Heq). inv Heq.
          simpl in STEP. inv STEP.
          exists O; simpl; do 2 eexists. split; try reflexivity.
          dilute_mem (Asm.get_mem s4').
          exploit Asm_event.asm_ev_ax2.
          econstructor; simpl in *; eassumption.
          intros (T&HH).
          econstructor; try eassumption; simpl.
          do 2 (econstructor; eauto); try reflexivity.
          + clean_proofs; eauto.
            
        - simpl in H; normal.
          simpl in H. inv H; simpl in *.
          eapply break_existensial_of_thread_stepN.
          + (* first step *)
            dilute_mem (Asm.get_mem s4').
            exploit Asm_event.asm_ev_ax2.
            { econstructor; simpl in *; eassumption. }
            intros (T&HH).
            do 2 (econstructor; eauto); try reflexivity.
            * constructor;clean_proofs; eauto.
          + (* The rest of the steps (inductively) *)
            match goal with
              |- exists x, machine_semantics_lemmas.thread_stepN _ _ _ _ ?upd_st2
                                                           _ _ _ =>
              remember upd_st2 as st2'
            end.
            assert (cnt2': containsThread st2' i).
            { subst. eapply cntUpdate; auto. }
            assert (HH:(thread_perms i st2' cnt2') = (getCurPerm (Asm.get_mem x))).
            { subst st2'; pose proof (@gssThreadRR dryResources _ i st2).
              simpl in *; rewrite H; auto. }
            assert (Hinv':invariant st2').
            { eapply Asm_preserves_invariant; eauto. }
            exploit IHNN.
            * apply Hinv'.
            * eapply Asm_preserves_compat; try eapply Hcmpt; eauto.
            * pose proof (mem_is_restr_eq (Asm.get_mem x)).
              clean_proofs.
              remember (getCurPerm (Asm.get_mem x))  as TEMP.
              rewrite <- HH in HeqTEMP; subst TEMP.
              erewrite restr_proof_irr.
              eapply H.
              
            * normal; [apply H2 | apply H3]. 
            * subst st2'.
              pose proof @gssThreadCC.
              specialize (H dryResources _ i st2 cnt2
                            (Krun (TState (@semC CSem) (@semC AsmSem) x)) cnt2').
              simpl in *; apply H.
            * eassumption.
            (* * erewrite (mem_is_restr_eq (Asm.get_mem x)).
              clean_proofs.
              remember ( getCurPerm (Asm.get_mem x))  as TEMP.
              rewrite <- HH in HeqTEMP; subst TEMP.
              unshelve (apply restr_proof_irr). *)
      
            * intros (n&c3&m3&one_step&many_steps).
            eexists (S n); simpl.
            exists c3, m3. split.
            -- eassumption.
            -- simpl in *.
              instantiate(1:= tge) in many_steps.
              instantiate(1:= m) in many_steps.
              match goal with
                [H: machine_semantics_lemmas.thread_stepN _ _ _ _ _ _ ?S _
                 |- machine_semantics_lemmas.thread_stepN _ _ _ _ _ _ ?S' _ ]=>
                replace S' with S; eauto
              end.
              subst st2'.
              rewrite updThread_twice.
              do 2 f_equal.
              unfold lock_perms.
              pose proof (@gssThreadRR dryResources _ i st2).
              simpl in *.
              rewrite H; reflexivity.

              Unshelve.
              apply Asm_genv_safe.
              assumption.
              apply Asm_genv_safe.
              assumption.

              { eapply tge. }
              { eapply tge. }
              { assert (HH:(thread_perms i st2' cnt2') = (getCurPerm (Asm.get_mem x))).
                { subst st2'; pose proof (@gssThreadRR dryResources _ i st2).
                  simpl in *; rewrite H; auto. }
                rewrite HH.
                eapply mem_cur_lt_max. }
      Qed.
              
      Lemma thread_step_plus_from_corestep:
        forall (m : option mem) (tge : ClightSemanticsForMachines.G * Asm.genv)
          i
          (U : list nat) (st1 : t) (m1 : mem) (Htid : containsThread st1 i) 
          (st2 : t) (mu : meminj) (m2 : mem) (cd0 : compiler_index)
          (CMatch : concur_match (Some cd0) mu st1 m1 st2 m2) (code2 : Asm.state)
          (s4' : Smallstep.state (Asm.part_semantics Asm_g)) 
          (m4' : mem) (cnt2 : containsThread st2 i),
          getThreadC cnt2 = Krun (TST code2) ->
          HybridMachineSig.schedPeek U = Some i ->
          corestep_plus (Asm_core.Asm_core_sem Asm_g) code2
                        (restrPermMap
                           (proj1 ((memcompat2 CMatch) i (contains12 CMatch Htid))))
                        s4' m4' ->
            machine_semantics_lemmas.thread_step_plus
              (HybConcSem (Some (S hb)) m) tge U st2
              m2 (updThread cnt2 (Krun (TState Clight.state Asm.state s4'))
                            (getCurPerm m4', snd (getThreadR cnt2))) m4'.
      Proof.
        (** NOTE: This might be missing that the corestep never reaches an at_external
                  If this is the case, we might need to thread that through the compiler...
                  although it should be easy, I would prefere if there is any other way...
         *)
        intros * HgetC Hschedule H.
        destruct H as (NN& H).
        clean_proofs.
        eapply thread_step_plus_from_corestep'; eauto; try apply CMatch.
      Qed.

      

      
          Lemma nil_eapp:
            forall t1 t2,
            Events.Eapp t1 t2 = nil ->
            t1 = nil /\ t2 = nil.
          Proof.
            intros t1 t2; destruct t1; destruct t2; simpl; intros;
              eauto; congruence. 
          Qed.
          
          (** *Need an extra fact about simulations*)
          Lemma step2corestep_star:
            forall (s1 s2: Smallstep.state (Asm.part_semantics Asm_g)),
              Smallstep.star
            (Asm.step (Genv.globalenv Asm_program))
            s1 nil s2 ->
              (corestep_star (Asm_core.Asm_core_sem Asm_g))
                s1 (Smallstep.get_mem s1) s2 (Smallstep.get_mem s2).
          Proof.
            intros * H. eapply Smallstep.star_starN in H as [n H].
            exists n.
            revert s1 s2 H. induction n.
            - intros. simpl; intros; inv H. 
              reflexivity.
            - intros; inv H.
              symmetry in H3; eapply nil_eapp in H3 as [? ?];subst.
              exploit IHn; eauto; intros Hsteps.
              do 2 eexists; split.
              + econstructor; eauto; simpl.
                rewrite asm_set_mem_get_mem; eauto.
                rewrite asm_set_mem_get_mem;
                  eapply step_nil_trace_not_atx; eauto.
              + eauto.
          Qed.
      Lemma step2corestep_plus:
        forall (s1 s2: Smallstep.state (Asm.part_semantics Asm_g)) m1,
          Smallstep.plus
            (Asm.step (Genv.globalenv Asm_program))
            (Smallstep.set_mem s1 m1) nil s2 ->
          (corestep_plus (Asm_core.Asm_core_sem Asm_g))
            s1 m1 s2 (Smallstep.get_mem s2).
      Proof.
        intros; inv H.
        symmetry in H2; eapply nil_eapp in H2 as [? ?]; subst.
        eapply corestep_plus_star_trans.
        - exists 0%nat; simpl.
          do 2 eexists; split; try reflexivity.
          econstructor; eauto.
          + eapply step_nil_trace_not_atx; eauto.
        - apply step2corestep_star in H1. simpl.
          destruct s3; eassumption.
      Qed.
          
      (* This in principle is not provable. We should get it somehow from the simulation.
              Possibly, by showing that the (internal) Clight step has no traces and allo
              external function calls have traces, so the "matching" Asm execution must be
              all internal steps (because otherwise the traces wouldn't match).
       *)
      
      
      
      (* When a thread takes an internal step (i.e. not changing the schedule) *)
      Lemma asm_get_mem_set_mem:
        forall s m, Asm.get_mem (Asm.set_mem s m) = m.
      Proof. intros st; destruct st; reflexivity. Qed.
      Lemma Clight_set_mem_get_mem
        : forall s, Clight.set_mem s (Clight.get_mem s) = s.
      Proof. intros st; destruct st; reflexivity. Qed.
      
      Lemma internal_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat) tr1
          (st1 : ThreadPool (Some hb)) m1 (st1' : ThreadPool (Some hb)) m1',
          machine_semantics.thread_step (HybConcSem (Some hb) m) sge U st1 m1 st1' m1' ->
          forall cd tr2 (st2 : ThreadPool (Some (S hb))) mu m2,
            concur_match cd mu st1 m1 st2 m2 ->
            forall (Hmatch_event : List.Forall2 (inject_mevent mu) tr1 tr2),
            exists (st2' : ThreadPool (Some (S hb))) m2' cd' mu',
              concur_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1 tr2 /\
              (machine_semantics_lemmas.thread_step_plus
                 (HybConcSem (Some (S hb)) m) tge U st2 m2 st2' m2' \/
               machine_semantics_lemmas.thread_step_star
                 (HybConcSem (Some (S hb)) m) tge U st2 m2 st2' m2' /\
               opt_rel' (InjorderX compiler_sim) cd' cd) /\
      inject_incr mu mu'.
      Proof.
        intros.
        inversion H; subst.
        inversion Htstep; subst.
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].  
        - (* tid < hb *)
          pose proof (mtch_target _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
          simpl in *.

          exploit_match ltac:(apply H0).
          destroy_ev_step_sum; subst; simpl in *; simpl.
          eapply Asm_event.asm_ev_ax1 in H2.
          instantiate (1:=Asm_genv_safe) in H2.
          
          eapply Aself_simulation in H5; eauto.
          destruct H5 as (c2' & f' & t' & m2' &
                          (CoreStep & MATCH & Hincr & is_ext & inj_trace)).
          

          eapply Asm_event.asm_ev_ax2 in CoreStep; try eapply Asm_genv_safe.
          destruct CoreStep as (?&?); eauto.
          
          (* contains.*)
          pose proof (@contains12  H0 _ Htid) as Htid'.

          (* Construct the new thread pool *)
          exists (updThread Htid' (Krun (TState Clight.state Asm.state c2'))
                       (getCurPerm m2', snd (getThreadR Htid'))).
          (* new memory is given by the self_simulation. *)
          exists m2', cd, f'.
          repeat weak_split.
          + (*Reestablish the concur_match *)
            simpl.
            move H0 at bottom.
            dup H0 as Hcmpt2.
            eapply memcompat2 in Hcmpt2.
            
            eapply concur_match_update1; eauto.
            { eapply semantics.corestep_mem in H2. eapply H2. }
            { instantiate(1:=Hcmpt2).
              eapply Asm_event.asm_ev_ax1 in H1.
              eapply semantics.corestep_mem.
              instantiate(1:=c2').
              instantiate(1:=code2).
              repeat abstract_proofs; unify_proofs; eauto.
            }
            
            { apply H0. }

            (*The compiler match*)
            econstructor 2; eauto.
            simpl in MATCH.
            unfold match_thread_target; simpl.
            constructor.
            exact MATCH.
            
          + (* Reestablish inject_mevent *)
            eapply inject_incr_trace; eauto.
          + left. (* Construct the step *)
            exists 0%nat; simpl.
            do 2 eexists; split; [|reflexivity].
            dilute_mem m2'.
            econstructor; eauto; simpl.
            econstructor; eauto.
            * simpl in *.
              eapply H0.
            * simpl; erewrite restr_proof_irr; econstructor; eauto.
            * simpl; repeat (f_equal; try eapply Axioms.proof_irr).
          + assumption.
          + erewrite restr_proof_irr; eassumption.
            
            
        - (*  tid = hb*)
          pose proof (mtch_compiled _ _ _ _ _ _ H0 _ e Htid (contains12 H0 Htid)) as HH.
          subst.
          simpl in *.
          
          exploit_match ltac:(apply H0).

          
          (* This takes three steps:
           1. Simulation of the Clight semantics  
           2. Simulation of the compiler (Clight and Asm) 
           3. Simulation of the Asm semantics 
           *)
          
          rename H6 into Compiler_Match; simpl in *.
          
          (* (1) Clight step *)
          destroy_ev_step_sum. subst m'0 t0 s.
          eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H2; eauto.
          
          (* (2) Compiler step/s *)
          rename H2 into CoreStep.
          simpl in CoreStep.
          inversion CoreStep. subst s1 m0 s2.
          
          eapply compiler_sim in H1 as HH; simpl in *; eauto.
          2: { erewrite restr_proof_irr; eassumption. }
          destruct HH as (cd' & s2' & j2' & t'' & step &
                          comp_match & Hincr2 & inj_event).
          assert (Ht0: t0 = nil).
          { eapply ClightSemanticsForMachines.Clight_step_nil_trace_not_atx;
            eauto.  }
          subst t0.
          assert (Ht'': t'' = nil).
          { inv inj_event; reflexivity. } subst t''.
          eapply simulation_equivlanence in step.
          assert ( HH: Asm.state =
                       Smallstep.state (Asm.part_semantics Asm_g)) by
              reflexivity.
          remember (@Smallstep.get_mem (Asm.part_semantics Asm_g) s2') as m2'.
          pose proof (contains12 H0 Htid) as Htid'.
          
          (*Invariant + compatible of the new source state (st1'): *)
          exploit Clight_preserves_invariant; eauto;
            intros Hinv1'.
          eapply Clight_preserves_compat in Hcmpt as Hcmpt1'; eauto.

          destruct step as [plus_step | (? & ? & ?)].
          +
            (*assert (@invariant
                      _ (TP (Some _))
                      (updThread Htid (Krun (SState Clight.state Asm.state s'))
                                 (getCurPerm (Clight.get_mem s'), lock_perms hb st1 Htid))).
            { *)

            
            exists (updThread Htid' (Krun (TState Clight.state Asm.state s2'))
                         (getCurPerm m2', snd (getThreadR Htid'))), m2', (Some cd'), j2'.
            repeat weak_split.
            * (*assert (CMatch := H0). inversion H0;*)
              rename H0 into CMatch.
              subst. simpl. intros.
              
              eapply (concur_match_thread_step _ st2 st1);
                try reflexivity; eauto; try now eapply compiler_sim; eauto.
              -- econstructor 3; auto. constructor; eauto.
                 unfold compiler_match.
                 simpl. rewrite asm_set_mem_get_mem,  Clight_set_mem_get_mem.
                 eauto.
              -- unshelve eapply Asm_plus_preserves_invariant_cmpt; try reflexivity;
                 try (eapply memcompat2; apply CMatch); shelve_unifiable; eauto.
                 apply CMatch.
                 clean_proofs_goal; simpl; match_case.
                 apply step2corestep_plus; simpl; eauto. revert plus_step.
                 clean_proofs_goal; simpl; eauto.
                 
              -- unshelve eapply Asm_plus_preserves_invariant_cmpt; try reflexivity;
                 try (eapply memcompat2; apply CMatch); shelve_unifiable; eauto.
                 eapply CMatch.
                 clean_proofs_goal; simpl; match_case.
                 apply step2corestep_plus; simpl; eauto. revert plus_step.
                 clean_proofs_goal; simpl; eauto.
                 
                 
            * eapply inject_incr_trace; try eassumption.
            * left.
              eapply thread_step_plus_from_corestep; eauto.
              -- symmetry; revert H4; clean_proofs_goal; eauto.
              -- subst m2'.
                 instantiate(1:=Htid).
                 instantiate (5:=H0).
                 erewrite restr_proof_irr; eauto.
                 instantiate(1:=Hlt2).
                 eapply step2corestep_plus; simpl in *. 
                 eauto.
            * assumption.
                 
          + exists st2, m2, (Some cd'), j2'.
            repeat weak_split.
            * (* assert (CMatch := H0). inversion H0;*)
              rename H0 into CMatch.
              pose proof (updThread_same Htid') as Hst2_eq.
              symmetry in Hst2_eq.
              replace (getThreadR Htid') with
                  (thread_perms _ _ Htid', lock_perms _ _ Htid') in Hst2_eq.
              2:{ destruct (getThreadR Htid'); reflexivity. }
              subst.
              eapply concur_match_perm_restrict'.
              rewrite <- mem_is_restr_eq.
              instantiate(1:= Hlt2).
              erewrite <- (asm_get_mem_set_mem _ (restrPermMap Hlt2)).
              eapply concur_match_thread_step;try eapply Hst2_eq;
                try reflexivity;
                       eauto; try now eapply compiler_sim; eauto.
              -- revert H4; clean_proofs_goal; intros <-.
                econstructor 3; auto. constructor; eauto.
                 unfold compiler_match.
                 simpl. rewrite Clight_set_mem_get_mem, asm_get_mem_set_mem.
                 eauto.
              -- apply CMatch.
              -- rewrite asm_get_mem_set_mem.
                 apply mem_compat_restrPermMap, CMatch.
              -- rewrite asm_get_mem_set_mem.
                 clean_proofs_goal; apply getCur_restr.
            * eapply inject_incr_trace; try eassumption.
            * right; split.
              { (*zero steps*)
                exists 0%nat; simpl; auto. }
              { (*order of the index*)
                constructor; auto.  }
            * assumption.
        - (* tid > hb *)
          pose proof (mtch_source _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
          simpl in *.
          exploit_match ltac:(apply H0).
          destroy_ev_step_sum; subst; simpl in *.
          simpl.
          eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H2; eauto.
          replace Hcmpt with (memcompat1 H0) in H2
            by eapply Axioms.proof_irr.
          
          eapply Cself_simulation in H5; eauto.
          destruct H5 as (c2' & f' & t' & m2' & (CoreStep & MATCH & Hincr & His_ext & Htrace)).
          
          eapply (event_semantics.ev_step_ax2 (@semSem CSem)) in CoreStep.
          destruct CoreStep as (?&?); eauto.
          
          (* contains.*)
          pose proof (contains12 H0 Htid) as Htid'.

          (* Construct the new thread pool *)
          exists (updThread Htid' (Krun (SState Clight.state Asm.state c2'))
                       (getCurPerm m2', snd (getThreadR Htid'))).
          (* new memory is given by the self_simulation. *)
          exists m2', cd, f'. repeat weak_split.
          
          + (*Reestablish the concur_match *)
            simpl.
            move H0 at bottom.
            eapply concur_match_update1; eauto.
            { eapply semantics.corestep_mem in H2.
              eapply H2. }
            { eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H1.
              eapply semantics.corestep_mem in H1.
              clean_proofs.
              erewrite restr_proof_irr.
              eassumption.
            }
            { apply H0. }
            
            econstructor 1; eauto.
            simpl in MATCH.
            unfold match_thread_source; simpl.
            constructor.
            exact MATCH.
          + eapply inject_incr_trace; try eassumption. 
          + (* Construct the step *)
            left; exists 0%nat; simpl.
            do 2 eexists; split; [|reflexivity].
            dilute_mem m2'.
            econstructor; eauto; simpl.
            econstructor; eauto.
            * simpl in *.
              eapply H0.
            * simpl. 
              erewrite restr_proof_irr.
              econstructor; eauto.
            * simpl; repeat (f_equal; try eapply Axioms.proof_irr).
          + assumption.
          + erewrite restr_proof_irr.
            eassumption.


            Unshelve. all: auto.
            (*This shouldn't be her e*) 
            all: try (exact nil).
            all: try (eapply H0).
            { !goal (Asm.genv).
              eapply  (Asm.part_semantics Asm_g). }
            { !goal (Asm.genv).
              eapply  (Asm.part_semantics Asm_g). }
      Qed.

      (** *Diagrams for machine steps*)
      
      
      (* What to do with this? *)
      Hint Resolve inject_incr_refl: core.
      Lemma asm_init_mem_step:
        forall g m st v args,
          Asm.entry_point g m st v args ->
          mem_step m (Asm.get_mem st).
      Proof.
        intros. inv H; simpl.
      Admitted.


      (* We can keep track of thread hb. 
         Before thread hb gets initialized, 
         all threads have same content and memories are equal.
         
         See if we can push that as a separate simulation proof 
         and merge them (don't want to change concur_match 
         an break perfectly nice proofs.

         Look at CPM_self_simulations and strengthen them      
         lemmas to inlcude not only [num_threads < hb]
         but also [getThreadC hb = Krun _] then we might be able to merge
         witht he present proofs.
       *)
      Lemma start_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (st1 : ThreadPool (Some hb)) 
               (m1 : mem) (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m' : mem)
               (cd : option compiler_index) (st2 : ThreadPool (Some (S hb)))
               (mu : meminj) (m2 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid),
          concur_match cd mu st1 m1 st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          HybridMachineSig.start_thread m1 Htid st1' m' ->
          invariant st1' ->
          mem_compatible st1' m' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' (HybridMachineSig.diluteMem m') st2'
                         m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step(HybConcSem (Some (S hb)) m) tge
                                          U tr2 st2 m2
                                          (HybridMachineSig.yield
                                             (Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                                             U) tr2 st2' m2'
      /\ inject_incr mu mu'.
      Proof.
        intros * CMatch Htrace Hsch Hstart.
        inversion Hstart; subst.
        inv Hperm.

        assert (cnt2:containsThread st2 tid).
        {eapply contains12; eauto. }
        
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].  
        - eapply CMatch in l as HH.
          simpl in Hcode; rewrite Hcode in HH; inv HH.
          hnf in Hinitial.
          match_case in Hinitial; normal_hyp.
          { contradict n; hnf. omega. }
          exploit (ssim_initial _ _ Aself_simulation);
            try eapply H4.
          + !goal(initial_core _ _ _ _ _ _ _).
            simpl in *; split; eauto; eapply i.
          + !goal (match_mem _ _ _). (* HERE *)
            econstructor; eauto.
            * unshelve eapply CMatch; simpl; eauto.
              -- eapply CMatch.
            * admit. (* maybe add to the match for Kinit *)
            * admit. (* maybe add to the match for Kinit *)
          + econstructor; eauto.
          + intros ?; normal_hyp.
            simpl; unfold add_block. 
            simpl in H. match_case in H.
            destruct H as (?&?).
            eexists; exists (HybridMachineSig.diluteMem x0), cd, x1;
              repeat weak_split eauto.
            * unfold add_block; simpl.
              assert (m' = Asm.get_mem c).
              { inversion i; subst m'; reflexivity. }
              eapply concur_match_thread_step;
                try eassumption; try reflexivity.
              -- econstructor 2; eauto.
                 subst m'; eauto.
                 econstructor; eauto.
              -- subst m'; apply H0. 
              -- !goal (invariant _). 
                 eapply mem_step_preserves_invariant;
                   try reflexivity.
                 ++ eapply getCur_restr.
                 ++ eapply mem_compat_restrPermMap, CMatch.
                 ++ eapply CMatch.
                 ++ subst x0; eapply asm_init_mem_step; eauto.
              -- !goal (mem_compatible _ _).
                 
                 eapply mem_step_preserves_compat;
                   try reflexivity.
                 ++ eapply getCur_restr.
                 ++ eapply CMatch.
                 ++ eapply mem_compat_restrPermMap, CMatch.
                 ++ subst x0; eapply asm_init_mem_step; eauto.
              -- subst m'; eapply is_ext_full; eauto.
                 apply full_inj_restr, CMatch.
            * eapply inject_incr_trace; eauto.
            * unshelve eapply @HybridMachineSig.start_state'; eauto.
              econstructor; simpl; try eassumption; eauto.
              -- reflexivity.
              -- simpl; hnf. simpl in *.
                 simpl;
                   repeat weak_split eauto.
                 clean_proofs_goal. eauto.  
              -- apply CMatch.
        - (* If the first "compiled" thread is being initialized, 
             then everything should be equal source and target,
             up to this point.
           *)

          eapply CMatch in e as HH.
          simpl in Hcode; rewrite Hcode in HH; inv HH.
          hnf in Hinitial.
          match_case in Hinitial; normal_hyp.
          2: { exfalso. contradict l; hnf. simpl; omega. }
          destruct i.
          exploit (Injfsim_match_entry_pointsX  compiler_sim); eauto.
          simpl. intros; normal_hyp.
          simpl; unfold add_block. simpl in H2.
          revert H2; clean_proofs_goal; intros H2.
          
          eexists; exists (HybridMachineSig.diluteMem (Asm.get_mem x1)),
                   (Some x), x0;
          repeat weak_split eauto.
          + !goal (concur_match _ _ _ _ _ _).
            assert (HH: mem_compatible st2 m2) by apply CMatch.
            unfold add_block; simpl.
            instantiate(1:=cnt2) in H3.

            unshelve (eapply concur_match_thread_step;
              try eassumption; try reflexivity); shelve_unifiable.
            * econstructor 3; eauto.
              econstructor. unfold compiler_match.
              subst m'; simpl.
              rewrite Clight_set_mem_get_mem,  asm_set_mem_get_mem.
              auto.
            * subst m'. eapply (Injfsim_match_meminjX compiler_sim); eauto.
            * admit. (* this is missing from the compiler simulation *)
            * !goal (invariant _). 
              eapply mem_step_preserves_invariant; try reflexivity.
              ++ unshelve eapply getCur_restr; eauto.
                 eapply HH.
              ++ eapply mem_compat_restrPermMap, CMatch.
              ++ eapply CMatch.
              ++ simpl.
                 admit. (* the memories are expected to be equal! *)
            * !goal (mem_compatible _ _). 
              eapply mem_step_preserves_compat; try reflexivity.
              ++ unshelve eapply getCur_restr; eauto.
                 eapply HH.
              ++ eapply CMatch.
              ++ eapply mem_compat_restrPermMap, CMatch.
              ++ simpl.
                 admit. (* the memories are expected to be equal! *)
            * subst m'; eapply (Injfsim_match_fullX compiler_sim); eauto.
          + eauto.
            eapply inject_incr_trace; try eassumption.
            admit. (* mu is expected to be trivial 
                      but it should exists (someone should carry it...
                    *)
          + econstructor; eauto.
            econstructor; eauto.
            * reflexivity.
            * hnf. instantiate(3:=TST x1); simpl.
              repeat weak_split eauto.
              admit. (* again, the memories are expected to be equal!*)
            * eapply CMatch.
            * simpl. reflexivity.
          + admit. (* mu is expected to be trivial 
                      but it should exists (someone should carry it...
                    *)
        - admit. (* just like the ASM case, easy*)
                
      Admitted. (* start_step_diagram *)
      
      Lemma Clight_get_mem_set_mem:
              forall (s : Clight.state) (m : mem),
                Clight.get_mem (Clight.set_mem s m) = m.
            Proof. intros st ?; destruct st; reflexivity. Qed.
            
      Lemma resume_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (st1 : ThreadPool (Some hb))
               (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem)
               (cd : option compiler_index) (st2 : ThreadPool (Some (S hb)))
               (mu : meminj) (m2 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid),
          concur_match cd mu st1 m1' st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          HybridMachineSig.resume_thread m1' Htid st1' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step
              (HybConcSem (Some (S hb)) m) tge
              U tr2 st2 m2
              (HybridMachineSig.yield
                 (Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                 U) tr2 st2' m2' /\
      inject_incr mu mu'.
      Proof.
        intros * Hconcur Htrace Hchs_peek Hresume.

        assert (Hcnt2: containsThread st2 tid).
        { eapply contains12; eauto. }
        
        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].
        - (* tid < hb *)
          intros. inv Hresume.
          hnf in Hperm; subst m'.

          (* get the match for this thread *)
          exploit @mtch_target; eauto.
          simpl in *; rewrite Hcode.
          intros HH.
          hnf in HH. inv HH; simpl in *.
          destruct H3 as  (Hasm_match & Hmem_match).

          (* get the first after_external*)
          revert Hafter_external.
          unfold after_external_sum,
          state_sum_optiont,
          sum_func_option,
          state_sum_options.
          match_case. intros HH; inv HH.

          (* get the second after_external, construct the new state*)
          assert (ssim_after_ext:
                    forall (f : meminj)
                      (c1 c1' : Smallstep.state (Asm.part_semantics Asm_g))
                      (m1 : mem)
                      (c2 : Smallstep.state (Asm.part_semantics Asm_g))
                      (m2 : mem),
                      match_self (code_inject _ _ Aself_simulation) f c1 m1 c2 m2 ->
                      Asm.after_external Asm_g None c1 m1 = Some c1' ->
                      exists (c2' : Smallstep.state (Asm.part_semantics Asm_g)),
                        Asm.after_external Asm_g None c2 m2 = Some c2' /\
                        match_self (code_inject _ _ Aself_simulation) f c1' m1 c2' m2).
          { eapply ssim_after_ext. }
          exploit ssim_after_ext; simpl.
          2:{ eauto. }
          { econstructor; eauto. }
          intros; normal_hyp. destruct H0 as (Hasm_match' & Hmem_match').

          (* get the second at_external*)
          (*destruct X as (FUN & args).
          exploit ssim_external; simpl; try exact Hasm_match;
            eauto.
          { eapply Hconcur. }
          { simpl; eauto. }
          intros ; normal_hyp. *)

                        
          
          intros; normal; eauto.
          + unshelve eapply concur_match_updateC; eauto; shelve_unifiable.
            hnf; simpl.

            econstructor 2; eauto.
            econstructor; econstructor; eauto.
            unfold Asm_code_inject; simpl.
            clean_proofs; eauto.
            unfold thmem_from_concur1, thmem_from_concur2.
            instantiate(1:= (th_comp
                               (mem_compatible_thread_compat st2 m2 tid Hcnt2
             (memcompat2 Hconcur)))) in Hmem_match'.
            revert Hmem_match'; clean_proofs_goal; eauto.
          + replace U with
                (@HybridMachineSig.yield HybridMachineSig.HybridCoarseMachine.scheduler U)
              by reflexivity.
            unshelve eapply HybridMachineSig.resume_step'; eauto.
            econstructor.
            * simpl. reflexivity.
            (* * simpl.; simpl. simpl in *; eauto. *)
            * simpl; eauto.
              unfold state_sum_optiont. simpl in H.
              instantiate(3:=TST code2).
              instantiate(2:= (memcompat2 Hconcur)).
              revert H; clean_proofs_goal.
              simpl. intros Hafter.
              unfold state_sum_optiont. 
              unfold Asm_g in *; rewrite Hafter.
              reflexivity.
            * simpl; eauto. 
            * eapply Hconcur.
            * simpl. eauto.
              
        - (* tid = hb *)
          subst.
          inversion Hresume; subst.
          inversion Hconcur. simpl in *.
          assert (m1_restr: permMapLt (thread_perms _ _ ctn) (getMaxPerm m1')) by
              eapply memcompat1.
          assert (m2_restr: permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2)) by
              eapply memcompat2.
          specialize (mtch_compiled hb ltac:(reflexivity) ctn Hcnt2
                                                          m1_restr
                                                          m2_restr).
          rewrite Hcode in mtch_compiled.
          inv mtch_compiled.
          
          (* TODO: Add the precondition of H10 to the concur match.
             that means: assert all the preconditions for the current state,
             and also have the precondition for all future states that satisfy the hyps.
             
             WAIT: Maybe not, I think you just need to instantiate it with the 
             current values. All the precontidions are refelxive.

           *)
          simpl in H4.
          inv Hafter_external.
          erewrite (restr_proof_irr m1_restr) in H4.
          destruct ((Clight.after_external None code1 m')) eqn:Hafter_x1; inv H0.
          rewrite Hperm in Hafter_x1.
          specialize (H4 mu s (restrPermMap _) (restrPermMap m2_restr) nil nil
                          ltac:(constructor)
                                 ltac:(constructor)
                                        ltac:(constructor)
                                               Hafter_x1
                     ).
          destruct H4 as (cd' & mu' & s2' & Hafter_x2 & INJ1 & Hcompiler_match).
          remember 
            (updThreadC Hcnt2 (Krun (TState Clight.state Asm.state s2'))) as st2'.

          (* We can probbaly do better than this. 
             (Without using full injection)
           *)
            assert (mu = mu').
            { (extensionality b).
              destruct (mu b) eqn:HH.
              - destruct p.
                eapply INJ1 in HH. eauto.
              - destruct (valid_block_dec m1' b).
                + eapply full_inj in v.
                  contradict v; eauto.
                + eapply Injfsim_match_meminjX in Hcompiler_match as
                      Hinj.
                  simpl in Hinj.
                  rewrite Clight_get_mem_set_mem,
                  asm_get_mem_set_mem
                    in Hinj.
                  erewrite Mem.mi_freeblocks; eauto.
            } subst mu'.
            
            exists st2',m2,(Some cd'), mu.

          
          
          repeat weak_split eauto.
          + !goal (concur_match _ mu _ _ _ _).

            
            subst st2'; unshelve eapply @concur_match_updateC; eauto;
              shelve_unifiable; swap 1 2.
            { unfold upd_cd; match_case; reflexivity. }
            eapply Injfsim_match_fullX in Hcompiler_match as
                Hfull'.
            simpl in Hfull'.
            rewrite Clight_get_mem_set_mem in Hfull'.
            
            eauto. simpl; unfold thmem_from_concur1.
            repeat (clean_proofs_goal; simpl).

            econstructor 3; eauto.
            econstructor.
            revert Hcompiler_match.
            unfold thmem_from_concur2; simpl; clean_proofs_goal; simpl; eauto.
          + (* Step *)
            !goal (HybridMachineSig.external_step _ _ _ _ _ _ _ _).
            assert (HH: U = (HybridMachineSig.yield
                               (Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler) U))
              by reflexivity.
            rewrite HH at 2.
            eapply HybridMachineSig.resume_step'; eauto.
            symmetry in Heqst2'.
            symmetry in H2.
            
            unshelve econstructor; simpl; try eapply memcompat2;
              shelve_unifiable;
              try eapply Heqst2'; try eapply H2; simpl.
            * reflexivity.
            * simpl in *.
              unfold state_sum_optiont.
              unfold Asm_g in *.
              move Hafter_x2 at bottom.
              clean_proofs_goal.
              rewrite Hafter_x2; reflexivity.
            * apply Hconcur.
            
        - (* hb < tid *)
          intros. inv Hresume.
          hnf in Hperm; subst m'.

          (* get the match for this thread *)
          exploit @mtch_source; eauto.
          simpl in *; rewrite Hcode.
          intros HH.
          hnf in HH. inv HH; simpl in *.
          destruct H3 as  (Hasm_match & Hmem_match).

          (* get the first after_external*)
          revert Hafter_external.
          unfold after_external_sum,
          state_sum_optiont,
          sum_func_option,
          state_sum_options.
          match_case. intros HH; inv HH.

          (* get the second after_external, construct the new state*)
          pose proof (ssim_after_ext _ _ Cself_simulation) as
              ssim_after_ext.
          exploit ssim_after_ext; simpl.
          2:{ eauto. }
          { econstructor; eauto. }
          intros; normal_hyp. destruct H0 as (Hasm_match' & Hmem_match').

          (* get the second at_external*)
          (*destruct X as (FUN & args).
          exploit ssim_external; simpl; try exact Hasm_match;
            eauto.
          { eapply Hconcur. }
          { simpl; eauto. }
          intros ; normal_hyp. *)

                        
          
          intros; normal; eauto.
          + unshelve eapply concur_match_updateC; eauto; shelve_unifiable.
            hnf; simpl.
            
            econstructor 1; eauto.
            econstructor; econstructor; eauto.
            simpl.
            clean_proofs; eauto.
            unfold thmem_from_concur1, thmem_from_concur2.
            instantiate(1:= (th_comp
                               (mem_compatible_thread_compat st2 m2 tid Hcnt2
             (memcompat2 Hconcur)))) in Hmem_match'.
            revert Hmem_match'; clean_proofs_goal; eauto.
          + replace U with
                (@HybridMachineSig.yield HybridMachineSig.HybridCoarseMachine.scheduler U)
              by reflexivity.
            unshelve eapply HybridMachineSig.resume_step'; eauto.
            econstructor.
            * simpl. reflexivity.
            (* * simpl.; simpl. simpl in *; eauto. *)
            * simpl; eauto.
              unfold state_sum_optiont. simpl in H.
              instantiate(3:=SST code2).
              instantiate(2:= (memcompat2 Hconcur)).
              revert H; clean_proofs_goal.
              simpl. intros Hafter.
              unfold state_sum_optiont. 
              rewrite Hafter.
              reflexivity.
            * simpl; eauto. 
            * eapply Hconcur.
            * simpl. eauto.
      Qed.
      
      
      
      Lemma suspend_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (st1 : ThreadPool (Some hb))
               (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem)
               (cd : option compiler_index) (st2 : ThreadPool (Some (S hb)))
               (mu : meminj) (m2 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid),
          concur_match cd mu st1 m1' st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          HybridMachineSig.suspend_thread m1' Htid st1' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge
                                           U tr2 st2 m2 (HybridMachineSig.schedSkip U) tr2 st2' m2'/\
      inject_incr mu mu'.
      Proof.
        intros * Hconcur Htrace Hchs_peek Hresume.

        assert (Hcnt2: containsThread st2 tid).
        { eapply contains12; eauto. }
        inv Hresume.

        exploit match_same_state_type; eauto.
        intros HH. rewrite Hcode in HH.
        simpl in HH. unfold get_state_type in HH. match_case in HH.
        clear HH.

        assert (Hmatch:individual_match
                  hb tid cd mu (Krun c)
                  (thmem_from_concur1 hb Hconcur ctn) (Krun s)
                  (thmem_from_concur2 hb Hconcur Hcnt2)).
        { unfold thmem_from_concur1, thmem_from_concur2;
              simpl; clean_proofs_goal.
            destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[HH|HH]|HH];
              unshelve eapply Hconcur in HH as Hmatch; eauto;
                simpl in *; rewrite Hcode in Hmatch; inv Hmatch;
                  [ econstructor 2 |
             econstructor 3 |
             econstructor 1 ]; eauto.
            * rewrite <- H1 in Heqc0; inv Heqc0.
              econstructor; eauto.
            * rewrite <- H2 in Heqc0; inv Heqc0.
              repeat (econstructor; eauto).
            * rewrite <- H1 in Heqc0; inv Heqc0.
              econstructor; eauto. }
        
        assert (Hmatch':individual_match
                  hb tid cd mu (Kblocked c)
                  (thmem_from_concur1 hb Hconcur ctn) (Kblocked s)
                  (thmem_from_concur2 hb Hconcur Hcnt2)).
        { unfold thmem_from_concur1, thmem_from_concur2;
            simpl; clean_proofs_goal.

          inv Hmatch.
          * revert H0;
            unfold thmem_from_concur1, thmem_from_concur2;
            clean_proofs_goal. intros Hmatch.
            inv Hmatch.  econstructor; eauto.
            econstructor; eauto.
          * revert H0;
            unfold thmem_from_concur1, thmem_from_concur2;
            clean_proofs_goal. intros Hmatch.
            inv Hmatch.  econstructor 2; eauto.
            econstructor; eauto.
          * revert H0;
            unfold thmem_from_concur1, thmem_from_concur2;
            clean_proofs_goal. intros Hmatch.
            inv Hmatch.  econstructor 3; eauto.
            repeat (econstructor; eauto). }
            
            
        eexists ; exists m2, cd, mu;
          repeat weak_split; eauto.
        - unshelve eapply concur_match_updateC; eauto.
          unfold upd_cd; match_case; reflexivity.
        - econstructor; simpl; eauto.
          simpl in *. inv Hperm.
          inv Hmatch. 
          + (* First get the at_external*)
            inv H0; simpl. destruct X.
            exploit (ssim_external _ _ Cself_simulation);
              eauto; try eapply H5; simpl.
            { unfold thmem_from_concur1.
              revert Hat_external.
              simpl; clean_proofs_goal; eauto. }
            unfold thmem_from_concur1, thmem_from_concur2 in *.
            clean_proofs_goal.
            intros;  normal_hyp.
            
            unshelve econstructor; try reflexivity; simpl;
              shelve_unifiable; eauto; swap 2 3. 
            * apply Hconcur.
            * erewrite <- H1. repeat f_equal.
              eapply Axioms.proof_irr.
          + (* First get the at_external*)
            inv H0; simpl. destruct X.
            exploit (ssim_external _ _ Aself_simulation);
              eauto; try eapply H5; simpl.
            { unfold thmem_from_concur1.
              revert Hat_external. unfold Asm_g.
              simpl; clean_proofs_goal; eauto. }
            unfold thmem_from_concur1, thmem_from_concur2 in *.
            clean_proofs_goal.
            intros;  normal_hyp.
            
            unshelve econstructor; try reflexivity; simpl;
              shelve_unifiable; eauto; swap 2 3. 
            * apply Hconcur.
            * erewrite <- H1. repeat f_equal.
              eapply Axioms.proof_irr.
          + (* First get the at_external*)
            inv H0; simpl. destruct X.
            exploit (Injsim_atxX compiler_sim). 
            * simpl. eapply H5.
            * { unfold thmem_from_concur1.
              revert Hat_external. 
              simpl; clean_proofs_goal; eauto. }

            * intros; normal_hyp.
              
              unshelve econstructor; try reflexivity; simpl;
                shelve_unifiable; eauto; swap 2 3. 
              -- apply Hconcur.
              -- erewrite <- H; simpl. unfold thmem_from_concur2.
                 repeat f_equal.
                 eapply Axioms.proof_irr.



                 Unshelve.
                 all: apply Hconcur.
      Qed.

      Lemma schedfail_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem)
               (st2 : ThreadPool (Some (S hb))) (m2 : mem) 
               (tid : nat) cd mu,
          concur_match cd mu st1' m1' st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          (~ ThreadPool.containsThread st1' tid \/
         (exists (cnt : ThreadPool.containsThread st1' tid) (c : semC) i,
             ThreadPool.getThreadC cnt = Krun c /\
             halted (sem_coresem (HybridSem (Some hb))) c i)) ->
          HybridMachineSig.invariant st1' ->
          HybridMachineSig.mem_compatible st1' m1' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge
                                           U tr2 st2 m2 U tr2 st2' m2'
      /\
      inject_incr mu mu'.
      Proof.
        intros * Hconcur Htrace Hsch HH Hinv Hcmpt.
        destruct HH as [HH | HH].
        - exists st2, m2, cd, mu.
          repeat weak_split eauto.
          hnf. econstructor 5; eauto;
                 try now apply Hconcur.
          left; intros ?. eapply HH.
          simpl. eapply contains21; eauto.
        - normal_hyp.
          exists st2, m2, cd, mu.
          repeat weak_split eauto.
          hnf. econstructor 5; eauto;
                 try now apply Hconcur.
          right.
          
          assert (cnt2: containsThread st2 tid).
          { eapply contains12; eauto. }
          
          unshelve econstructor; eauto.
          destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[HH|HH]|HH];
            unshelve eapply Hconcur in HH as Hmatch; eauto;
              simpl in *; try now apply Hconcur; simpl in *.
          + revert Hmatch. simpl; clean_proofs_goal.
            repeat match_case; clean_proofs_goal.
            intros. rewrite H in Hmatch; inv Hmatch.
            do 2 eexists; split; eauto.
            simpl.
            eapply Aself_simulation; try eapply H0; eauto.
          + revert Hmatch. simpl; clean_proofs_goal.
            repeat match_case; clean_proofs_goal.
            intros. rewrite H in Hmatch; inv Hmatch.
            do 2 eexists; split; eauto.
            simpl.
            Lemma Asm_final_mem:
              (* it would be more elegant to not need this.
                 SOLUTION: change the core_semantics, 
                 such that halted takes a memory (and sets it in the state)
                 just like the step and other things.
               *)
              forall st m ret,
                Asm.final_state (Asm.set_mem st m) ret <->
                Asm.final_state st ret.
            Proof. split; intros HH; destruct st; inv HH;
                   econstructor; eauto. Qed.
            Lemma Csm_final_mem:
              (* it would be more elegant to not need this.
                 SOLUTION: change the core_semantics, 
                 such that halted takes a memory (and sets it in the state)
                 just like the step and other things.
               *)
              forall st m ret,
                Clight.final_state (Clight.set_mem st m) ret <->
                Clight.final_state st ret.
            Proof. split; intros HH; destruct st; inv HH;
                   econstructor; eauto. Qed.
            eapply Asm_final_mem.
            exploit (Injfsim_match_final_statesX compiler_sim); simpl;
              try (eapply Csm_final_mem; eapply H0); eauto.
          + revert Hmatch. simpl; clean_proofs_goal.
            repeat match_case; clean_proofs_goal.
            intros. rewrite H in Hmatch; inv Hmatch.
            do 2 eexists; split; eauto.
            simpl.
            eapply Cself_simulation; try eapply H0; eauto.
      Qed.
      
      Lemma machine_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat)
               (tr1 : HybridMachineSig.event_trace) (st1 : ThreadPool (Some hb)) 
               (m1 : mem) (U' : list nat) (tr1' : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem),
          machine_semantics.machine_step (HybConcSem (Some hb) m) sge U tr1 st1 m1 U' tr1' st1' m1' ->
          forall (cd : option compiler_index) tr2 (st2 : ThreadPool (Some (S hb))) 
                 (mu : meminj) (m2 : mem)
                 (Hinv:invariant st1') (Hcmpt':mem_compatible st1' m1'),
            concur_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            exists
              tr2' (st2' : ThreadPool (Some (S hb))) (m2' : mem) (cd' : option compiler_index) 
              (mu' : meminj),
              concur_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1' tr2' /\
              machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge U tr2 st2 m2 U' tr2' st2'
                                             m2' /\
              inject_incr mu mu'.
      Proof.
        intros; simpl in H. 
        inversion H; subst.
        - (* Start thread. *)
          exists tr2; eapply start_step_diagram; eauto.
          
        - (* resume thread. *)
          exists tr2; eapply resume_step_diagram; eauto.
          
        - (* suspend thread. *)
          exists tr2; eapply suspend_step_diagram; eauto.
          
        - (* sync step. *)
          edestruct external_step_diagram as (? & ? & ? & ? & ? & ? & ? & ?); eauto 8.

        - (*schedfail. *) 
          exploit schedfail_step_diagram; eauto.

          
      Qed.


      Lemma getCurPerm_valid:
        forall m b1 ofs,
          at_least_Some ((getCurPerm m) !! b1 ofs) ->
          Mem.valid_block m b1.
      Proof.
        unfold at_least_Some in *; simpl in *.
        intros *; match_case; intros HH; try solve[inv HH].
        unfold Mem.valid_block, Plt.
        destruct (plt b1 (Mem.nextblock m)); eauto.
        eapply m in n.
        instantiate(1:=Cur) in n;
          instantiate(1:=ofs) in n.
        rewrite_getPerm. rewrite Heqo in n.
        congruence.
      Qed.
      
      Lemma initial_diagram:
        forall (m : option mem) (m0 s_mem : mem) (main : val) (main_args : list val)
          (s_mach_state : ThreadPool (Some hb)) (r1 : option res),
          Mem.mem_wd m0 ->
          machine_semantics.initial_machine (HybConcSem (Some hb) m) r1 m0 s_mach_state s_mem
                                            main main_args ->
          exists
            (j : meminj) (cd : option compiler_index) (t_mach_state : ThreadPool (Some (S hb))) 
            (t_mem : mem) (r2 : option res),
            machine_semantics.initial_machine
              (HybConcSem (Some (S hb)) m) r2 m0 t_mach_state
              t_mem main main_args /\ concur_match cd j s_mach_state s_mem t_mach_state t_mem.
      Proof.
        intros m.
        simpl; unfold HybridMachineSig.init_machine''.
        intros * Hwd (?&?).
        destruct r1; try solve[inversion H0].
        subst; simpl in *.
        destruct H0 as (init_thread&?&?); simpl in *.
        unfold initial_core_sum in *.
        (* destruct (Compare_dec.lt_eq_lt_dec 0 hb) as [[HH|HH]|HH].
         *)
        destruct init_thread; destruct H as (LT&H&Hm); simpl in LT.
        + assert (hb = 0%nat).
          { clear - LT; omega. }
          subst hb.

          exploit (Injfsim_match_entry_pointsX compiler_sim);
            eauto.
          intros ; normal_hyp.
          do 4 econstructor.
          exists (Some p); eauto;
            repeat weak_split eauto.
          * econstructor; repeat weak_split eauto.
            hnf. instantiate(3:= TST x1); simpl;
                   repeat weak_split eauto.
          * (* initial concur! *)
            instantiate(1:=x0).
            instantiate(1:=Some x).
            subst s_mach_state s_mem.
            eapply concur_match_initial; simpl; eauto.
            -- econstructor 3; eauto.
               econstructor. unfold compiler_match.
               simpl. rewrite Clight_set_mem_get_mem,
                      asm_set_mem_get_mem.
               eauto.
            -- eapply Injfsim_match_meminjX in H2; eauto.
            -- eapply Injfsim_match_fullX in H2; eauto.
        + (* 0 < hb *)
          exploit (ssim_initial _ _ Aself_simulation);
            simpl; eauto.
          * constructor.
            -- eapply Mem.mem_wd_inject; eauto.
            --  intros ? **.
                eapply getCurPerm_valid in H1.
                unfold Mem.flat_inj.
                match_case.
                do 2 eexists; eauto.
            -- intros ? * H1. 
                eapply getCurPerm_valid in H1.
                unfold Mem.flat_inj.
                exists b2, ofs_delt, 0.
                match_case. repeat weak_split eauto.
                omega.
          * simpl. instantiate(1:=main_args).
            admit. (* are we taking no argumetns ? 
                      if it does, they must be valid!
                      Check the soundness proof to see what they do
                    *)
          * instantiate(1:=main).
            admit. (* just like above, main has to be valid! *)

          * intros ? ; normal_hyp.

          exists x1, None.
          unshelve eexists.
          { eapply mkPool.
            + eapply Krun. eapply TState. exact x.
            + exact (getCurPerm (Asm.get_mem x), empty_map). }
          exists x0, (Some p).
          repeat weak_split eauto.
          -- subst x0; eexists; simpl; repeat weak_split eauto.
             hnf; repeat weak_split eauto.
             hnf; omega.
          -- simpl.
             (* initial match! *)
             eapply concur_match_initial; simpl; eauto.
            ++ econstructor 2; eauto.
               econstructor; eauto.
            ++ eapply H2.
            ++ eapply is_ext_full; eauto.
               apply Events.flat_injection_full.
            ++ subst x0;reflexivity.

               Unshelve.
               all: eauto. 
      Admitted.

      Lemma compile_one_thread:
        forall m ,
          simulation_properties_exposed
            (HybConcSem (Some hb) m)
            (HybConcSem (Some (S hb)) m)
            invariant
            mem_compatible
            (concur_match)
            (opt_rel' (InjorderX compiler_sim)).
      Proof.
        intros.
        unshelve econstructor;
          [econstructor| reflexivity].
        - eapply option_wf.
          eapply (Injfsim_order_wfX compiler_sim). (*well_founded order*)

        (*Initial Diagram*)
        - eapply initial_diagram.

        (* Internal Step diagram*)
        - eapply internal_step_diagram.

        (* Machine Step diagram *)
        - eapply machine_step_diagram.

        (* Halted *)
        - simpl; unfold HybridMachineSig.halted_machine; simpl; intros.
          destruct (HybridMachineSig.schedPeek U); inversion H0.
          eexists; reflexivity.

        (*Same running *)
        - eapply concur_match_same_running.
      Qed.
      
      
    End CompileOneThread.

  End ThreadedSimulation.
End ThreadedSimulation.
