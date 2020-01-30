
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

(* THINGS TO KEEP*)
Lemma LKSIZE_nat_pos': (0 < LKSIZE_nat)%nat.
Proof.
  replace 0%nat with (Z.to_nat 0)%Z by reflexivity.
  unfold LKSIZE_nat, LKSIZE.
  rewrite size_chunk_Mptr.
  destruct Archi.ptr64;
    eapply Z2Nat.inj_lt; eauto; try omega.
Qed.
Hint Resolve LKSIZE_nat_pos'.


(* MOVE this within the file. Probably add a section for update lemmas? *)
Lemma mem_compatible_updLock:
  forall Sem Tp m st st' l lock_info,
    permMapLt_pair lock_info (getMaxPerm m) ->
    Mem.valid_block m (fst l) ->
    st' = ThreadPool.updLockSet(resources:=dryResources) st l lock_info ->
    @mem_compatible Sem Tp st m ->
    @mem_compatible Sem Tp st' m.
Proof.
  intros * Hlt Hvalid HH Hcmpt.
  subst st'; constructor; intros.
  - erewrite ThreadPool.gLockSetRes. apply Hcmpt.
  - (*Two cases, one of which goes by Hlt*)
    destruct (addressFiniteMap.AMap.E.eq_dec l l0).
    + subst. rewrite ThreadPool.gsslockResUpdLock in H.
      inv H; auto.
    + subst. rewrite ThreadPool.gsolockResUpdLock in H; auto.
      eapply Hcmpt; eauto. 
  - (*Two cases, one of which goes by Hvalid*)
    destruct (addressFiniteMap.AMap.E.eq_dec l l0); subst; eauto.
    eapply Hcmpt.
    subst. rewrite ThreadPool.gsolockResUpdLock in H; eauto.

    Unshelve.
    eapply ThreadPool.cntUpdateL'; eauto.
Qed.
Lemma mem_compatible_updthread:
  forall Sem Tp m st st' i (cnt:ThreadPool.containsThread st i) c res,
    permMapLt_pair res (getMaxPerm m) ->
    st' = ThreadPool.updThread(resources:=dryResources) cnt c res ->
    @mem_compatible Sem Tp st m ->
    @mem_compatible Sem Tp st' m.
Proof.
  intros * Hlt HH Hcmpt.
  subst st'; constructor; intros.
  - (*Two cases, one of which goes by Hlt*)
    destruct (Nat.eq_dec i tid).
    + subst. rewrite ThreadPool.gssThreadRes; auto.
    + subst. unshelve erewrite ThreadPool.gsoThreadRes; auto.
      eapply ThreadPool.cntUpdate'; eauto.
      eapply Hcmpt.
  - rewrite ThreadPool.gsoThreadLPool in H.
    eapply Hcmpt; eassumption.
  -  rewrite ThreadPool.gsoThreadLPool in H.
     eapply Hcmpt; eassumption.
Qed.


Module SimulationTactics (CC_correct: CompCert_correctness)(Args: ThreadSimulationArguments).

  
  Module MyConcurMatch := ConcurMatch CC_correct Args.
  Import MyConcurMatch.
  
  Export MyThreadSimulationDefinitions.
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  
  Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).
  
    (*+ tactics to push 
         mem_compat
         forward (in diagrams) *)
    
    Lemma mem_compatible_fullThreadUpdate:
      forall Sem Tp m st st' st'' l lock_info
        i (cnt:ThreadPool.containsThread st i) c res,
        @mem_compatible Sem Tp st m ->
        permMapLt_pair res (getMaxPerm m) ->
        permMapLt_pair lock_info (getMaxPerm m) ->
        Mem.valid_block m (fst l) ->
        st'' = ThreadPool.updLockSet st' l lock_info ->
        st' = ThreadPool.updThread cnt c res ->
        @mem_compatible Sem Tp st'' m.
    Proof.
      intros.
      eapply mem_compatible_updLock; eauto. clear H1 H2 H3.
      eapply mem_compatible_updthread; eauto.
    Qed.
    Lemma mem_compatible_fullThreadUpdate_join1:
      forall {Sem Tp} st c m st' st'' b ofs th_perm lock_perm
        i (cnt:ThreadPool.containsThread st i) ,
        @mem_compatible Sem Tp st m ->
        permMapJoin_pair th_perm lock_perm (ThreadPool.getThreadR cnt) ->
        Mem.valid_block m b ->
        st'' = ThreadPool.updLockSet st' (b, ofs) lock_perm ->
        st' = ThreadPool.updThread cnt c th_perm ->
        @mem_compatible Sem Tp st'' m.
    Proof.
      intros. eapply mem_compatible_fullThreadUpdate; simpl; eauto.
      - apply (permMapLt_pair_trans211 _ (ThreadPool.getThreadR cnt)).
        * eapply permMapJoin_lt_pair1; eassumption.
        * eapply H.
      - apply (permMapLt_pair_trans211 _ (ThreadPool.getThreadR cnt)).
        * eapply permMapJoin_lt_pair2; eassumption.
        * eapply H.
      - simpl; auto.
    Qed.
    
  Definition fullThreadUpdate {sem} st i cnt th_st new_perms adr  :=
    (updLockSet
       (@updThread dryResources sem i st cnt th_st (fst new_perms)) adr (snd new_perms)).
  Definition fullThUpd_comp {sem} st i cnt th_st (angel: virtue) adr  :=
    @fullThreadUpdate
      sem st i cnt th_st
      (computeMap_pair (getThreadR cnt) (virtueThread angel), virtueLP angel) adr.
    
    Lemma store_cmpt:
      forall Sem Tp st chunk b ofs v m m' p Hlt ,
        Mem.store chunk (@restrPermMap p m Hlt ) b ofs v = Some m' ->
        @mem_compatible Sem Tp st m -> 
        @mem_compatible Sem Tp st m'.
    Proof.
      intros. 
      eapply mem_compat_Max in H0;
        try (symmetry; etransitivity).
      - eassumption.
      - symmetry; eapply store_max_equiv; eassumption.
      - apply restr_Max_equiv.
      - eapply Mem.nextblock_store; eassumption.
      - reflexivity.
    Qed.

    Ltac unfold_state_forward:=
      match goal with
      | H:?st' = fullThUpd_comp ?st _ _ _ _ (?b, ?ofs)
        |- _ => unfold fullThUpd_comp, fullThreadUpdate in H
      | H:= fullThUpd_comp ?st _ _ _ _ (?b, ?ofs)
            |- _ => unfold fullThUpd_comp, fullThreadUpdate in H
          | H:?st' = fullThreadUpdate ?st _ _ _ _ (?b, ?ofs)
            |- _ => unfold fullThreadUpdate in H
          | H:= fullThreadUpdate ?st _ _ _ _ (?b, ?ofs)
                |- _ => unfold fullThreadUpdate in H
      end.



    
    
    Ltac apply_permMapLt_compute_inject_pair:=
      match goal with
      | |- permMapLt_pair (computeMap_pair _ _) _ =>
        eapply permMapLt_compute_inject_pair_useful; eauto
      | |- permMapLt_pair (computeMap _ _ , computeMap _ _) _ =>
        eapply permMapLt_compute_inject_pair_useful; eauto
      end.
    

    (** *solve_permMapLt_easy
          for all those permMapLt_pair that can be solved "directly"
     *)
    Ltac solve_permMapLt_lock_update_mem:=
      first [eapply lock_update_mem_permMapLt_range_Cur; eassumption
            |eapply lock_update_mem_permMapLt_range_Max; eassumption].
    Ltac solve_permMapLt_cmpt:=
      match goal with
        [Hcmpt: mem_compatible ?st ?m
         |- permMapLt_pair (@getThreadR _ _ _ ?st _) (getMaxPerm ?m)] =>
        eapply Hcmpt
      |[Hcmpt: mem_compatible ?st ?m,
               Hlock_perm: ThreadPool.lockRes ?st _ = Some ?pmaps
        |- permMapLt_pair ?pmaps (getMaxPerm ?m)] =>
       eapply Hcmpt
      end.
    
    Ltac solve_permMapLt_join:=
      match goal with
      | H:permMapJoin_pair ?b _ _ |- permMapLt_pair2 ?b _ =>
        now apply (permMapJoin_lt_pair1 _ _ _ H)
      | H:permMapJoin_pair _ ?b _ |- permMapLt_pair2 ?b _ =>
        now apply (permMapJoin_lt_pair2 _ _ _ H)
      end.
    Ltac solve_permMapLt_empty_pair:=
      match goal with
      | |- permMapLt_pair (pair0 empty_map) _ =>
        eapply permMapLt_empty_pair
      | |- permMapLt_pair (empty_map,empty_map) _ =>
        eapply permMapLt_empty_pair
      end.
    Ltac solve_permMapLt_easy:=
      (* for those goals that can be solved directly*)
      first
        [ eassumption
        | solve_permMapLt_empty_pair
        | solve_permMapLt_lock_update_mem
        | solve_permMapLt_join
        (* slower :*)
        | solve_permMapLt_cmpt ].
    Ltac solve_permMapLt_set_new_perms:=
      match goal with
        [Hnp: set_new_mems _ _ _ _ ?new_perms
         |- permMapLt_pair ?new_perms (getMaxPerm _)] =>
        inv Hnp; eapply permMapLt_setPermBlock_pair;
        [ permMapLt_range_pair_simpl|];
        solve_permMapLt_easy
      end.
    Ltac solve_permMapLt_pair:=
      try eassumption;
      subst_set; try subst;
      first
        [ solve_permMapLt_easy
        | eapply permMapLt_pair_trans211;
          [solve_permMapLt_easy  
          |solve_permMapLt_cmpt]
        | solve_permMapLt_set_new_perms
        (* inject one sometimes gets stuck. *)
        | solve[apply_permMapLt_compute_inject_pair] (*HERE!*)
        | idtac "permMapLt_pair cant be solved:"; print_goal].
    (*We can use the previous to solve regular permMapLt *)
    Ltac solve_permMapLt:=
      let H:= fresh in
      match goal with
      | [ |- permMapLt (fst ?a) ?b] =>
        assert (H:permMapLt_pair a b) by solve_permMapLt_pair
      | [|- permMapLt (snd ?a) ?b] =>
        assert (H:permMapLt_pair a b) by solve_permMapLt_pair
      end; apply H.
    Ltac solve_valid_block:=
      subst_set; subst;
      match goal with
      |  |- Mem.valid_block ?m ?b =>
         solve[simpl; eapply Mem.valid_block_inject_1; eauto]
      (* destruct (mem_l emmas.valid_block_dec m b) as [n|n]; eauto;
            eapply Mem.mi_freeblocks in n; eauto;
            unify_injection *)
      | |- Mem.valid_block ?m ?b =>
        solve[simpl; eapply Mem.valid_block_inject_2; eauto]
      end.
    Ltac forward_cmpt' H:=
      let Hcmpt_update_state:= fresh "Hcmpt_update" in
      eapply (@mem_compatible_fullThreadUpdate _ (TP _)) in H
        as Hcmpt_update_state; try reflexivity; simpl;
      [ idtac
      | eassumption
      | solve_permMapLt_pair 
      | solve_permMapLt_pair
      | solve_valid_block ];
      idtac.
    
    Ltac forward_state_cmpt_all :=
      let Hcmpt_fwd:= fresh "Hcmpt_update" in
      repeat unfold_state_forward;
      (* Find the states and the mems.*)
      match goal with
      |[ H: ?st' = updLockSet (@updThread _ _ _ ?st _ _ _) _ _ |- _ ] =>
       let M:= fresh in mark M st';
                        forward_cmpt' H;
                        try forward_state_cmpt_all;
                        clear M
      |[ st':= updLockSet (@updThread _ _ _ ?st _ _ _) _ _ |- _ ] =>
       let M:= fresh in mark M st';
                        let H:= fresh in
                        match goal with
                          [st':= ?ST' |- _] => assert (H: st' = ST') by (subst st'; reflexivity)
                        end; forward_cmpt' H;
                        (try forward_state_cmpt_all);
                        clear M H
      end.

    (* TODO move this to the highest place possible (there the lmmas are defined?)*)
    Ltac solve_max_equiv:=
      (* solves the following cases:
               - reflexivity
               - just a restriction.
               - after a Mem.store.
               - a compbination of two of the previous ones. *)
      solve[ etransitivity;
             (* try Mem.store; *)
             first [(eapply store_max_equiv; eassumption)|
                    (symmetry; eapply store_max_equiv; eassumption)|
                    idtac];
             (*try straight restrictions*)
             first [(eapply restr_Max_equiv)|
                    (symmetry; eapply restr_Max_equiv)|
                    idtac];
             (*try restrictions of another hypothesis*)
             first [(eapply Max_equiv_restr; eassumption)|
                    (symmetry; eapply Max_equiv_restr; eassumption)|
                    idtac];
             (*finally, if there are goals left, reflexivity*)
             try reflexivity].
    Ltac solve_nextblock_eq:=
      (* solves the following cases:
               - reflexivity
               - just a restriction.
               - after a Mem.store.
               - a compbination of two of the previous ones. *)
      solve[ etransitivity;
             (* try Mem.store; *)
             first [(eapply Mem.nextblock_store; eassumption)|
                    (symmetry; eapply Mem.nextblock_store; eassumption)|
                    idtac];
             (*finally, if there are goals left, reflexivity*)
             try reflexivity].
    Ltac pose_max_equiv:=
      match goal with
        [H:lock_update_mem_strict_load _ _ _ ?m ?m' _ _ |- _] =>
        try match goal with [Hmax_eq: Max_equiv m m'|- _]=> fail 2 end;
        let Hmax_eq:= fresh "Hmax_eq" in
        let Hnb_eq:= fresh "Hnb_eq" in
        assert (Hmax_eq: Max_equiv m m') by (inv H; solve_max_equiv);
        assert (Hnb_eq: Mem.nextblock m = Mem.nextblock m')
          by (inv H; solve_nextblock_eq)
      | [H:lock_update_mem_strict _ _ ?m ?m' _ |- _] =>
        try match goal with [Hmax_eq: Max_equiv m m'|- _]=> fail 2 end;
        let Hmax_eq:= fresh "Hmax_eq" in
        let Hnb_eq:= fresh "Hnb_eq" in
        assert (Hmax_eq: Max_equiv m m') by (inv H; solve_max_equiv);
        assert (Hnb_eq: Mem.nextblock m = Mem.nextblock m')
          by (inv H; solve_nextblock_eq)
      end.
    Ltac forward_mem_cmpt_all :=
      match goal with
      |[ Hmax_equiv: Max_equiv ?m ?m',
                     Hnb_eq:  Mem.nextblock ?m =  Mem.nextblock ?m',
                              Hcmpt: mem_compatible ?st ?m |- _ ] =>
       try match goal with [H: mem_compatible st m' |- _ ] => fail 2 end;
       let Hcmpt_mem_fwd:= fresh "Hcmpt_mem_fwd" in 
       try eapply mem_compat_Max in Hcmpt as Hcmpt_mem_fwd;
       [| eassumption| eassumption]
      end.
    Ltac forward_cmpt_all:=
      forward_state_cmpt_all;
      repeat forward_mem_cmpt_all.
    (*+ End forward CMPT*)
  
End SimulationTactics.




Module SyncSimulation (CC_correct: CompCert_correctness)(Args: ThreadSimulationArguments).
  
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Module MySimulationTactics:= SimulationTactics CC_correct Args.
  Import MySimulationTactics.
  Import MyConcurMatch.
  
  Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).


  

  Definition sem_coresem Sem:=(@csem _ (@event_semantics.msem _ (@semSem Sem))).
  Instance Sum_at_external_proper shb (c_gen: Clight.genv):
    Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
           (semantics.at_external (sem_coresem (HybridSem shb))).
  Proof.
    intros ??? ???; subst; simpl.
    unfold at_external_sum, sum_func.
    destruct y.
    - eapply C_at_external_proper; auto.
    - eapply Asm_at_external_proper; auto.
      Unshelve.
      eassumption.
  Qed.
  Instance Sum_at_external_proper':
    forall hb,
      Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
             (semantics.at_external (sem_coresem (HybridSem (Some hb)))).
  Proof.
    intros ??? ???; subst; simpl.
    unfold at_external_sum, sum_func.
    destruct y.
    - eapply C_at_external_proper; auto.
    - eapply Asm_at_external_proper; auto.

      Unshelve.
      exact Clight_g.
  Qed.
  

  (*Lemmas about the calls: *)
  Notation vone:= (Vint Int.one).
  Notation vzero:= (Vint Int.zero).

  
  
  (** * Lemmas about invariant*)
  
    Ltac rewrite_getupd:=
      repeat match goal with
             | _ => erewrite ThreadPool.gLockSetRes
             | _ => rewrite ThreadPool.gsoThreadLPool
             | _ => rewrite ThreadPool.gssThreadRes
             | _ => erewrite ThreadPool.gssLockRes
             | _ => erewrite ThreadPool.gsoThreadRes by eauto
             | _ => erewrite ThreadPool.gsoLockRes by eauto 
             end.
    Lemma invariant_update:
      forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool) h laddr c lock_perm th_perm
             (Hcnt:ThreadPool.containsThread st h),
        st' =
        ThreadPool.updLockSet (ThreadPool.updThread Hcnt c th_perm) laddr lock_perm ->
        invariant st ->
        forall (no_race_thr0: forall j (cntj : ThreadPool.containsThread st j),
                   (j <> h) ->
                   permMapsDisjoint2 th_perm (ThreadPool.getThreadR cntj))
               (no_race_lr: forall (laddr': address) (rmap : lock_info),
                   laddr' <> laddr ->
                   ThreadPool.lockRes st laddr' = Some rmap -> permMapsDisjoint2 lock_perm rmap)
               (no_race1: permMapsDisjoint2 th_perm lock_perm)
               (no_race2: forall laddr0 rmap,
                   laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
                   permMapsDisjoint2 th_perm rmap)
               (no_race3: forall i (cnti : ThreadPool.containsThread st i),
                   i <> h ->
                   permMapsDisjoint2 (ThreadPool.getThreadR cnti) lock_perm)
               (thread_date_lock_coh1: permMapCoherence (fst th_perm) (snd th_perm))
               (thread_date_lock_coh2: permMapCoherence (fst lock_perm) (snd th_perm))
               (thread_date_lock_coh3: permMapCoherence (fst th_perm) (snd lock_perm))
               (thread_date_lock_coh4: forall i (cnti : ThreadPool.containsThread st i),
                   i <> h ->
                   permMapCoherence (fst th_perm) (snd (ThreadPool.getThreadR cnti)) /\
                   permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd th_perm))
               (thread_date_lock_coh5: forall i (cnti : ThreadPool.containsThread st i),
                   i <> h ->
                   permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd lock_perm) /\
                   permMapCoherence (fst lock_perm) (snd (ThreadPool.getThreadR cnti)))
               (thread_date_lock_coh6: forall laddr0 rmap,
                   laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
                   permMapCoherence (fst rmap) (snd th_perm) /\
                   permMapCoherence (fst th_perm) (snd rmap))
               (locks_data_lock_coh1: permMapCoherence (fst lock_perm) (snd lock_perm))
               (locks_data_lock_coh2: forall laddr0 rmap,
                   laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
                   permMapCoherence (fst rmap) (snd lock_perm) /\
                   permMapCoherence (fst lock_perm) (snd rmap))
               (lockRes_valid: coqlib4.isSome (ThreadPool.lockRes st laddr)),
          invariant st'.
    Proof.
      intros * ? Hinv **. constructor.
      - intros * ?.
        destruct (Nat.eq_dec i h);
          destruct (Nat.eq_dec j h); subst; rewrite_getupd.
        + contradict Hneq; reflexivity.
        + rewrite_getupd. auto.
        + apply permMapsDisjoint2_comm; auto.
        + eapply no_race_thr; eauto.
      - intros * ?.
        destruct (addressFiniteMap.AMap.E.eq_dec laddr1 laddr);
          destruct (addressFiniteMap.AMap.E.eq_dec laddr2 laddr); subst;
            rewrite_getupd; intros.
        + contradict Hneq; auto.
        + inv Hres1. eapply no_race_lr0; eauto.
        + inv Hres2. eapply permMapsDisjoint2_comm, no_race_lr0; eauto.
        + eapply no_race_lr; try apply Hneq; eauto.
      - intros *.
        destruct (Nat.eq_dec i h);
          destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
          subst; rewrite_getupd; intros.
        + inv Hres; assumption.
        + eauto.
        + inv Hres. eauto.
        + eapply no_race; eauto.
      - intros *; split; intros *.
        + destruct (Nat.eq_dec i h);
            destruct (Nat.eq_dec j h); subst; intros; rewrite_getupd.
          * assumption.
          * apply thread_date_lock_coh4; auto.
          * apply thread_date_lock_coh4; auto.
          * exploit thread_data_lock_coh; eauto. intros [HH ?].
            apply HH.
        + destruct (Nat.eq_dec i h);
            destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
            subst; rewrite_getupd; intros.
          * inv H; assumption.
          * eapply thread_date_lock_coh6; eauto.
          * symmetry in H; inv H. apply thread_date_lock_coh5; auto.
          * eapply Hinv; eauto.
      - intros *; split; intros *; revert Hres.
        + destruct (Nat.eq_dec j h);
            destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
            subst; rewrite_getupd; intros.
          * inv Hres; eauto.
          * eapply thread_date_lock_coh6; eauto.
          * inv Hres. eapply thread_date_lock_coh5; auto.
          * exploit locks_data_lock_coh; eauto. intros [HH ?].
            apply HH.
        + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
            destruct (addressFiniteMap.AMap.E.eq_dec laddr' laddr);
            subst; rewrite_getupd; intros.
          * inv Hres; inv H; eauto.
          * inv Hres; eapply locks_data_lock_coh2; eauto.
          * inv H; eapply locks_data_lock_coh2; eauto.
          * pose proof (locks_data_lock_coh _ Hinv _ _ Hres).
            destruct H0. specialize (H1 _ _ H). auto.
      - intros ??.
        destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs) laddr); subst.
        + rewrite ThreadPool.gsslockResUpdLock; intros.
          assert (ofs <> ofs0) by omega.
          rewrite ThreadPool.gsolockResUpdLock, ThreadPool.gsoThreadLPool.
          2: { intros HH; apply H0; inv HH; reflexivity. }
          exploit lockRes_valid; eauto.
          assert (coqlib4.isSome (ThreadPool.lockRes st (b, ofs))) by assumption.
          instantiate(2:=ofs); instantiate(2:=b).
          match_case; try inv H1; eauto.
        + rewrite ThreadPool.gsolockResUpdLock,
          ThreadPool.gsoThreadLPool; auto; intros.
          match_case; auto; intros.
          exploit lockRes_valid; eauto.
          instantiate(2:=ofs); instantiate(2:=b). rewrite Heqo.
          intros HH; apply HH in H.
          assert ((b, ofs0) <> laddr). {
            destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs0) laddr); auto.
            subst. rewrite H in lockRes_valid0; inv lockRes_valid0. }
          rewrite ThreadPool.gsolockResUpdLock, ThreadPool.gsoThreadLPool; auto.

          Unshelve.
          all: auto.
    Qed.
    
    Lemma invariant_updateLock:
      forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
             laddr lock_perm,
        st' =
        ThreadPool.updLockSet st laddr lock_perm ->
        invariant st ->
        forall (no_race_lr: forall (laddr': address) (rmap : lock_info),
                   laddr' <> laddr ->
                   ThreadPool.lockRes st laddr' = Some rmap -> permMapsDisjoint2 lock_perm rmap)
               (no_race3: forall i (cnti : ThreadPool.containsThread st i),
                   permMapsDisjoint2 (ThreadPool.getThreadR cnti) lock_perm)
               (thread_date_lock_coh5: forall i (cnti : ThreadPool.containsThread st i),
                   permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd lock_perm) /\
                   permMapCoherence (fst lock_perm) (snd (ThreadPool.getThreadR cnti)))
               (locks_data_lock_coh1: permMapCoherence (fst lock_perm) (snd lock_perm))
               (locks_data_lock_coh2: forall laddr0 rmap,
                   laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
                   permMapCoherence (fst rmap) (snd lock_perm) /\
                   permMapCoherence (fst lock_perm) (snd rmap))
               (lockRes_valid: forall ofs0 : Z, snd laddr < ofs0 < (snd laddr) + LKSIZE ->
                                           lockRes st (fst laddr, ofs0) = None)
               (lockRes_valid2: forall ofs0 : Z, ofs0 < snd laddr < ofs0 + LKSIZE ->
                                           lockRes st (fst laddr, ofs0) = None),
          invariant st'.
    Proof.
      intros * ? Hinv **. constructor.
      - intros * ?. subst; rewrite_getupd.
        eapply Hinv; eauto.
      - intros * ?.
        destruct (addressFiniteMap.AMap.E.eq_dec laddr1 laddr);
          destruct (addressFiniteMap.AMap.E.eq_dec laddr2 laddr); subst;
            rewrite_getupd; intros.
        + contradict Hneq; auto.
        + inv Hres1. eapply no_race_lr0; eauto.
        + inv Hres2. eapply permMapsDisjoint2_comm, no_race_lr0; eauto.
        + eapply no_race_lr; try apply Hneq; eauto.
      - intros *.
        destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
          subst; rewrite_getupd; intros.
        + inv Hres; eauto.
        + eapply no_race in Hres; eauto.
      - intros *; split; intros *.
        + subst; intros; rewrite_getupd.
          eapply thread_data_lock_coh in Hinv as [Hinv _]; eauto.
        + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
            subst; rewrite_getupd; intros.
          * inv H; eapply thread_date_lock_coh5.
          * eapply thread_data_lock_coh in Hinv as [_ Hinv]; eauto.
      - intros *; split; intros *; revert Hres.
        + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
            subst; rewrite_getupd; intros.
          * inv Hres. eapply thread_date_lock_coh5. 
          * eapply locks_data_lock_coh in Hinv as [Hinv _]; eauto.
        + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
            destruct (addressFiniteMap.AMap.E.eq_dec laddr' laddr);
            subst; rewrite_getupd; intros.
          * inv Hres; inv H; eauto.
          * inv Hres; eapply locks_data_lock_coh2; eauto.
          * inv H; eapply locks_data_lock_coh2; eauto.
          * pose proof (locks_data_lock_coh _ Hinv _ _ Hres).
            destruct H0. specialize (H1 _ _ H). auto.
      - intros ??. 
        destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs) laddr); subst.
        + match_case; simpl in *; eauto.
          intros.
          rewrite gsolockResUpdLock; auto.
          intros HH; inv HH; omega.
        + rewrite ThreadPool.gsolockResUpdLock; auto; intros.
          match_case; auto; intros.
          
          exploit lockRes_valid; eauto.
          rewrite Heqo.
          dup H as H'.
          intros HH; apply HH in H.
          destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs0) laddr);
            swap 1 2.
          * rewrite ThreadPool.gsolockResUpdLock; auto.
          * subst.
            eapply neq_prod in n.
            2: exact Classical_Prop.classic.
            destruct n; try congruence.
            destruct H0 as [_ H0].
            rewrite ThreadPool.gsolockResUpdLock; auto.
            exploit lockRes_valid2; eauto; simpl.
            simpl in *; intros HH'; rewrite HH' in Heqo;
              congruence.
            

            
        Unshelve.
        all: auto.
    Qed.
    
    Lemma perm_coh_None_not_Free:
      forall b, b <> Some Freeable -> perm_coh None b.
    Proof. intros. hnf; repeat (match_case; eauto). Qed.
   Lemma invariant_empty_updLockSet:
      forall hb (st:ThreadPool (Some hb)) b ofs st',
        invariant st ->
        (forall ofs0 : Z, ofs < ofs0 < ofs + LKSIZE ->
                     ThreadPool.lockRes st (b, ofs0) = None) ->
        (forall ofs0 : Z, ofs0 < ofs < ofs0 + LKSIZE ->
                     ThreadPool.lockRes st (b, ofs0) = None) ->
        st' = ThreadPool.updLockSet st (b, ofs) (pair0 empty_map) ->
        (*coqlib4.isSome (ThreadPool.lockRes st (b, ofs)) ->*)
        invariant st'.
    Proof.
      intros * Hinv ???. eapply invariant_updateLock; simpl in *; eauto.
      - split; eapply empty_disjoint'.
      - intros; eapply permMapsDisjoint2_comm.
        split; eapply empty_disjoint'.
      - simpl. split; try eapply permCoh_empty'.
        + intros ??.
          rewrite empty_is_empty; simpl.
          eapply perm_coh_None_not_Free.
          eapply perm_coh_not_freeable.
          eapply thread_data_lock_coh in Hinv as
              [HH _]; eauto. eapply HH. 
      - eapply permCoh_empty'.
      - simpl. split; try eapply permCoh_empty'.
        intros ??. rewrite empty_is_empty; simpl.
        eapply perm_coh_None_not_Free.
        eapply perm_coh_not_freeable.
        eapply locks_data_lock_coh in Hinv as
            [_ HH]; eauto. eapply HH; eauto.

        Unshelve.
        all: eauto.
    Qed.
    
   Lemma invariant_empty_updLockSet_upd:
      forall hb (st:ThreadPool (Some hb)) b ofs st',
        invariant st ->
        st' = ThreadPool.updLockSet st (b, ofs) (pair0 empty_map) ->
        coqlib4.isSome (ThreadPool.lockRes st (b, ofs)) ->
        invariant st'.
    Proof.
      intros * Hinv ??.
      eapply invariant_empty_updLockSet; eauto.
      - simpl. eapply lockRes_valid in Hinv.
        specialize (Hinv b ofs); simpl in *.
        match_case in Hinv; try now inv H0.
      - simpl. eapply lockRes_valid in Hinv.
        intros. 
        specialize (Hinv b ofs0); simpl in *.
        destruct_lhs; auto.
        rewrite Hinv in H0; eauto. inv H0.
        
        Unshelve.
        all: eauto.
    Qed.
    

  

  (** * The following lemmas prove the injection 
                  of memories unfer setPermBlock.
   *)

  
  Inductive coerce_state_type  {a b T}: forall t, @state_sum a b -> t -> T -> T -> T ->  Prop:=
  | SourceCoerce_T: forall t1 t2 c, coerce_state_type a (@SState _ _ c) c t1 t2 t1
  | TargetCoerce_T: forall t1 t2 c, coerce_state_type b (@TState _ _ c) c t1 t2 t2.
  Definition mach_state n:= ThreadPool (Some n).

  Lemma atx_injection Sem: 
    let CoreSem := sem_coresem Sem in
    forall (SelfSim: (self_simulation semC CoreSem))
      mu b1 b2 delt th_state1 th_state2 m1 m2 FUN ofs,
      mu b1 = Some (b2, delt) ->
      match_self (code_inject semC CoreSem SelfSim) mu th_state1 m1 th_state2 m2 ->
      semantics.at_external CoreSem th_state1 m1 =
      Some (FUN, (Vptr b1 ofs) :: nil) ->
      semantics.at_external CoreSem th_state2 m2 =
      Some (FUN, Vptr b2 (add ofs (repr delt)) :: nil).
  Proof.
    intros * Hinj Hmatch_self Hat_external.
    eapply ssim_preserves_atx in Hat_external as
        (args' & Hatx2 & Hval_inj); eauto.
    - (* unify arg's *)
      inv Hval_inj. inv H3. inv H1.
      rewrite Hinj in H2; inv H2.
      eauto.
  Qed.
  Lemma coerse_state_atx:
    forall shb Sem SemC sum_state (th_state:@semC Sem) m,
      coerce_state_type
        semC sum_state th_state
        (CSem, Clight.state)
        (AsmSem, Asm.state) (Sem, SemC) ->
      semantics.at_external (sem_coresem Sem) th_state m =
      semantics.at_external (sem_coresem (HybridSem shb)) sum_state m.
  Proof.
    intros * Hcoerce. inv Hcoerce; simpl.
    all: replace th_state with c; try reflexivity.
    all: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
  Qed.


  (*This should be parameters of the result.*)
  Definition atx_only_visible {s} (Sem:semantics.CoreSemantics s mem):=
    forall c m m' f_and_args,
      same_visible m m' ->
      semantics.at_external Sem c m = Some f_and_args ->
      semantics.at_external Sem c m' = Some f_and_args.
  Lemma atx_only_visible_Clight:
    atx_only_visible (Clightcore_coop.cl_core_sem Clight_g).
  Proof.
    intros ?* . simpl. unfold Clight.at_external.
    destruct c; simpl; intros; congruence.
  Qed.
  Lemma atx_only_visible_Asm:
    atx_only_visible (Asm_core.Asm_core_sem Asm_g).
  Proof.
    intros ?* . simpl. unfold Asm.at_external; simpl.
    destruct c; simpl.
    intros. repeat match_case in H0. inv H0.
    rewrite <- H, Heqo0; auto.
  Qed.
  
  (** * End of Lemmas for relase diagram*)
  
  Infix "++":= seq.cat.

  (* Definition all_threads_inject_perm
             (f:meminj) {n m} (st1: ThreadPool n) (st2: ThreadPool m) m1 m2:=
    forall (i : nat) (cnt1 : containsThread st1 i) (cnt2 : containsThread st2 i)
      (Hlt1 : permMapLt (thread_perms  _ _ cnt1) (getMaxPerm m1))
      (Hlt2 : permMapLt (thread_perms  _ _ cnt2) (getMaxPerm m2)),
      Mem.inject f (restrPermMap Hlt1) (restrPermMap Hlt2). 

  Definition all_threads_lock_perm_surj
             (f:meminj) {n m} (st1: ThreadPool n) (st2: ThreadPool m):=
    forall (i : nat) (cnt1 : containsThread st1 i) (cnt2 : containsThread st2 i),
      perm_surj f (lock_perms  _ _ cnt1) (lock_perms  _ _ cnt2).
  Lemma perm_surj_updLockSet:
    forall f n m st1 st2 adr1 adr2 lock_perms1 lock_perms2,
      @all_threads_lock_perm_surj f n m st1 st2 ->
      all_threads_lock_perm_surj f
                                 (updLockSet st1 adr1 lock_perms1)
                                 (updLockSet st2 adr2 lock_perms2).
  Proof.
    intros ** ???.
    unfold lock_perms.
    unshelve (do 2 erewrite gLockSetRes); try eapply H.
    all : unshelve eapply cntUpdateL'; auto.
  Qed.
  
  Lemma perm_surj_updThread:
    forall f n m st1 st2 c1 c2 thred_perms1 thred_perms2,
      @all_threads_lock_perm_surj f n m st1 st2 ->
      perm_surj f (snd thred_perms1) (snd thred_perms2) ->
      forall j cntj1 cntj2,
        all_threads_lock_perm_surj f
                                   (@updThread _ _ j st1 cntj1 c1 thred_perms1)
                                   (@updThread _ _ j st2 cntj2 c2 thred_perms2).
  Proof.
    intros ** ???.
    unfold lock_perms.
    destruct (Nat.eq_dec i j).
    - subst.
      do 2 erewrite gssThreadRes; auto.
    - unshelve (do 2 (erewrite gsoThreadRes; auto)); try eapply H.
      all : unshelve eapply cntUpdate'; auto.
  Qed. *)

  
  


  (** *TODO: all follwoing lemmas are about address arithmetic
          maybe move it to a section?
   *)
  
  
  
  
  Lemma lock_update_mem_strict_load_inject:
    forall f b b' ofs delt perms1 perms2 m1 m2 m1' vl vs,
    forall (Hinj_b : f b = Some (b', delt))
      Hlt1 Hlt2
      (Hinj_lock: Mem.inject f (@restrPermMap perms1 m1 Hlt1)
                             (@restrPermMap perms2 m2 Hlt2)),
      lock_update_mem_strict_load b ofs perms1 m1 m1' (Vint vl) (Vint vs) ->
      inject_lock' LKSIZE f b ofs m1 m2 ->
      exists m2',
        lock_update_mem_strict_load b' (ofs+ delt) perms2 m2 m2' (Vint vl) (Vint vs) /\
        Mem.inject f m1' m2'.
  Proof.
    intros. inv H.

    Print Instances Proper.
    rewrite <- (restr_proof_irr_equiv _ _ lock_mem_lt),
    (restr_proof_irr_equiv _ _ Hlt2)
      in Hinj_lock.
    assert (writable_lock b' (ofs + delt) perms2 m2).
    { eapply writable_lock_inject_restr; eauto. }

    
    eapply Mem.store_mapped_inject in Hstore; eauto.
    - destruct Hstore as (m2'&Hstore2&Hinj2).
      exists m2'; split; auto.
      unshelve econstructor; eauto.
      + match goal with
          |- context[?a + ?b + ?c]=>
          replace (a + b + c) with ((a + c) + b) by omega   
        end.
        eapply Mem.range_perm_inject; eauto.
      + eapply Mem.load_inject in Hload; eauto.
        * destruct Hload as (v2 & ? & HH).
          inv HH; eauto.
    - simpl.
      eapply mem_inject_equiv; 
        try (eapply setPermBlock_mem_inject; try eapply Hinj_lock);
        eauto.
      { subst m_writable_lock_1 lock_mem.
        etransitivity; [|eapply restrPermMap_idempotent].
        apply restrPermMap_equiv; try reflexivity.
        eapply setPermBlock_access_map_equiv; eauto.
        rewrite getCur_restr. reflexivity.
        econstructor; auto.  }
      { etransitivity; [|eapply restrPermMap_idempotent].
        apply restrPermMap_equiv; try reflexivity.
        eapply setPermBlock_access_map_equiv; eauto.
        simpl; rewrite getCur_restr. reflexivity.
        econstructor; auto. }
      
      Unshelve.
      all: unfold writable_lock in *;
        try rewrite getCur_restr;
        try rewrite getMax_restr;
        try assumption.
  Qed.
  

  Inductive strict_evolution_diagram cd mu code1 m1 m1' code2 m2':=
  | build_stric_diagram:
      forall lev1 lev2 j m2
        (Hcomp_match : compiler_match cd j code1 m1 code2 m2)
        (Hstrict_evolution : strict_injection_evolution j mu lev1 lev2)
        (Hinterference1 : mem_interference m1 lev1 m1')
        (Hinterference2 : mem_interference m2 lev2 m2'),
        strict_evolution_diagram cd mu code1 m1 m1' code2 m2'.

  
  
  Inductive interference_diagram_atx i code1 code2 m1 f' m1' m2':Prop :=
  | build_inter_diagram_atx:
      forall f FUN m2 args1 args2  lev1 lev2
        (Hinj: Mem.inject f m1 m2)
        (Hinj': Mem.inject f' m1' m2')
        (Hstrict_evolution: strict_injection_evolution f f' lev1 lev2)
        (Hmatch_states: compiler_match i f code1 m1 code2 m2)
        (*Hmatch_states': compiler_match i f' code1 m1' code2 m2'*)
        (* Probably can also add this, but seems like I don't need it*)
        (Hinterference1 : mem_interference m1 lev1 m1')
        (Hinterference2 : mem_interference m2 lev2 m2')
        (Hat_external1: Clight.at_external (Clight.set_mem code1 m1) =
                        Some (FUN, args1))
        (Hat_external1': Clight.at_external (Clight.set_mem code1 m1') =
                         Some (FUN, args1))
        (Hat_external2: Asm.at_external Asm_g (Asm.set_mem code2 m2) =
                        Some (FUN, args2))
        (Hat_external2': Asm.at_external Asm_g (Asm.set_mem code2 m2') =
                         Some (FUN, args2))
        (Hinj_args: Val.inject_list f args1 args2)
      , interference_diagram_atx i code1 code2 m1 f' m1' m2'.

  Lemma retroactive_int_diagram_atx:
    forall  i code1 code2 m1 f' m1' m2' FUN 
       (Hstrict: strict_evolution_diagram i f' code1 m1 m1' code2 m2')
       (Hinj': Mem.inject f' m1' m2')
       args1
       (Hat_external1': Clight.at_external (Clight.set_mem code1 m1') =
                        Some (FUN, args1)),
      interference_diagram_atx i code1 code2 m1 f' m1' m2'.
  Proof.
    intros.
    inversion Hstrict.
    pose proof (atx_only_visible_Clight) as Hsame1.
    pose proof (atx_only_visible_Asm) as Hsame2.
    eapply Hsame1 in Hat_external1' as Hat_external1.
    2: { symmetry. eapply interference_same_visible. eassumption. }
    eapply (Injsim_atxX compiler_sim) in Hat_external1 as HH; eauto.

    destruct HH as (args' & Hat_external2 & Hinj_args).
    rename args' into args2.
    
    eapply Hsame2 in Hat_external2 as Hat_external2'.
    2: { eapply interference_same_visible; eassumption. }
    econstructor; eauto.
    - !goal (Mem.inject j m1 m2).
      eapply (Injfsim_match_meminjX compiler_sim)
        in Hcomp_match.
      destruct code1, code2; eapply Hcomp_match.
  Qed.

  
    Definition compat_restr {Sem tpool m} perms {st} Hlt Hcmpt:=
      @mem_compat_restrPermMap Sem tpool m perms st Hlt Hcmpt.
    
    Instance build_delta_content_equiv:
          Proper (Logic.eq ==>
                           content_equiv ==>
                           Logic.eq) build_delta_content.
        Proof.
          intros ??? ???; subst.
          unfold build_delta_content; simpl.
          f_equal.
          extensionality b.
          extensionality dm_f.
          extensionality ofs.
          do 3 match_case.
        Qed.
    Lemma syncStep_restr:
      forall Sem tpool i st cnt m Hcmpt st' m' ev, 
        @syncStep Sem tpool true i st m cnt Hcmpt st' m' ev ->
        forall p Hlt, let Hcmpt_new:= compat_restr p Hlt Hcmpt in
                      exists p' Hlt',
                        syncStep true cnt Hcmpt_new st' (@restrPermMap p' m' Hlt') ev.
    Proof.
      intros.
      inv H; simpl in *; do 2 eexists;
        match goal with
          |- syncStep _ _ _ _ ?rm ?ev =>
          remember rm as M
        end;
        assert (Hcequiv:content_equiv M m') by
            (subst; eapply restr_content_equiv);
        symmetry in Hcequiv;
        repeat rewrite Hcequiv.
      - (*acquire*)
        econstructor; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).
          erewrite Hstore.
          f_equal. rewrite (mem_is_restr_eq m').
          subst M; reflexivity.
      - (*release*)
        econstructor; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).
          erewrite Hstore.
          f_equal. rewrite (mem_is_restr_eq m').
          subst M; reflexivity.
      - (*create*)
        replace (build_delta_content (fst virtue1) m') with
              (build_delta_content (fst virtue1) M) by
           (rewrite Hcequiv; reflexivity).
           replace (build_delta_content (fst virtue2) m') with
              (build_delta_content (fst virtue2) M) by
           (rewrite Hcequiv; reflexivity).
          subst M.
          econstructor 3; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).
      - (*mklock*)
        econstructor; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).
          erewrite Hstore.
          f_equal. rewrite (mem_is_restr_eq m').
          subst M; reflexivity.
      - (* freelock*)
        subst M;
        econstructor 5; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).
      - (* acqfail *)
        subst M;
        econstructor 6; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).

        Unshelve.
        all: rewrite getMax_restr; eauto.
    Qed.

  
  
  Definition remLockfFullUpdate {sem} st i cnt th_st new_perms adr  :=
    (remLockSet
       (@updThread dryResources sem i st cnt th_st (new_perms)) adr).
  
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
    

    

    
    Lemma map_lt_implication: forall b a,
        permMapLt_pair a b ->
        pair21_prop full_map_option_implication a b.
    Proof.
      intros b. solve_pair.
      intros ** ? **.
      specialize (H b0 ofs).
      red; repeat match_case; auto.
    Qed.

    
    
    
    Lemma permMapJoin_pair_inject_rel:
      forall angel m1
             m2 mu  th_perms1 th_perms2,
        sub_map_virtue angel (getMaxPerm m1) ->
        let newThreadPerm1 := computeMap_pair (th_perms1) (virtueThread angel) in
        permMapJoin_pair newThreadPerm1 (virtueLP angel) (th_perms1) ->
        forall 
          (Hlt_th1 : permMapLt (fst th_perms1) (getMaxPerm m1))
          (Hlt_th2 : permMapLt (fst th_perms2) (getMaxPerm m2))
          (Hlt_lk1 : permMapLt (snd th_perms1) (getMaxPerm m1))
          (Hlt_lk2 : permMapLt (snd th_perms2) (getMaxPerm m2)),
          Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
          Mem.inject mu (restrPermMap Hlt_lk1) (restrPermMap Hlt_lk2) ->
          injects_angel mu angel   ->
          let angel2 := inject_virtue m2 mu angel in
          let newThreadPerm2 := computeMap_pair (th_perms2)
                                                (virtueThread angel2) in
          permMapJoin_pair newThreadPerm2 (virtueLP angel2) (th_perms2).
    Proof.
      intros. subst newThreadPerm2.
      eapply compute_map_join_fwd_pair.
      eapply delta_map_join_inject_pair';
        try match goal with
              |- delta_map_join_pair _ _ _ =>
              eapply compute_map_join_bkw_pair; eassumption
            end; eauto. 
      - !goal (perm_perfect_virtue mu angel angel2).
        subst angel2.
        replace (inject_virtue m2 mu angel) with
            (inject_virtue (restrPermMap Hlt_th2) mu angel).
        eapply inject_virtue_perm_perfect; eauto.
        { eapply map_lt_implication.
          eapply permMapLt_pair_trans211; swap 1 2.
          - rewrite getMax_restr_eq; split; simpl; eauto.
          - eapply permMapJoin_lt_pair2; eauto.
        }
        rewrite getMax_restr_eq.
        pose proof (virtueThread_sub_map _ _ H) as HH.
        clear -HH.
        apply sub_map_implication_dmap_pair; eauto.
        apply inject_virtue_max_eq; eauto.
        rewrite getMax_restr_eq; auto.              
      - !goal(Mem.meminj_no_overlap _ m1).
        rewrite <- (restr_Max_equiv Hlt_th1); eapply H1.
      - !goal (dmap_vis_filtered_pair (virtueThread angel) m1).
        eapply sub_map_filtered_pair, virtueThread_sub_map, H.
      - split; eauto.
      - !goal (almost_perfect_image_pair _ _ _ _).
        eapply inject_almost_perfect_pair; eauto.
    Qed.

    

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
            (MyThreadSimulationDefinitions.sem_coresem (HybridSem (Some (S hb))))
            sum_state2 (restrPermMap abs_proof) = Some (UNLOCK, args').
    Proof.
      intros.
      
      simpl; unfold at_external_sum, sum_func.
      rewrite <- (restr_proof_irr (th_comp _ thread_compat2)).
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

    
    (** *Solve Unsigned: for goals of the shape:
        unsigned (add ofs (repr delta) = unsigned ofs + delta)
     *)
    Ltac solve_unsigned1:=
      (*check the goal *)
      try replace intval with unsigned by reflexivity;
      match goal with
      | [|- unsigned (add ?ofs (repr ?delta)) = unsigned ?ofs + ?delta ] => idtac
      | [|- unsigned ?ofs + ?delta = unsigned (add ?ofs (repr ?delta)) ] => symmetry
      | _ => fail "Not the right goal"
      end.
    Ltac solve_unsigned2:=
      (* find the "Mem.load" *)
      match goal with
      | [ H: lock_update_mem_strict_load _ ?uofs _ _ _ _ _ |- _ = ?uofs + _ ] =>
        inv H
      | [ H: lock_update_mem_strict _ ?uofs _ _ _ |- _ = ?uofs + _ ] =>
        inv H
      end.
    
    Lemma concur_match_perm_restrict' perms1 perms2:
      forall (hb : nat) (cd : option compiler_index) (j : meminj)
        (st1 : ThreadPool (Some hb)) (m1 : mem) (st2 : ThreadPool (Some (S hb)))
        (m2 : mem)(permMapLt1 : permMapLt perms1 (getMaxPerm m1))
        (permMapLt2 : permMapLt perms2 (getMaxPerm m2)),
        MyConcurMatch.concur_match hb cd j st1 (restrPermMap permMapLt1) st2
                                   (restrPermMap permMapLt2) ->
        MyConcurMatch.concur_match hb cd j st1 m1 st2 m2.
    Proof.
      intros.
      rewrite (mem_is_restr_eq m1), (mem_is_restr_eq m2).
      erewrite (@restrPermMap_idempotent_eq _ _ m1).
      erewrite (@restrPermMap_idempotent_eq _ _ m2).
      eapply concur_match_perm_restrict; eauto.

      Unshelve.
      all: rewrite getMax_restr; apply mem_cur_lt_max.
    Qed.
    Ltac solve_solve_unsigned3 H:=
      eapply Mem.valid_access_implies with
        (p2:=Nonempty) in H; try constructor;
      (* Apply the main lemma Mem.address_inject'*)
      eapply Mem.address_inject'; try eapply H.
    Ltac solve_unsigned3:=
      (* convert "Mem.load" into "Mem.access" and apply the main lemma *)
      match goal with
      | [ H: Mem.load _ ?m _ ?uofs = _ |- _ = ?uofs + _ ] =>
        eapply Mem.load_valid_access in H; solve_solve_unsigned3 H
      | H:Mem.store _ ?m _ ?uofs _ = _
        |- _ = ?uofs + _ =>
        eapply Mem.store_valid_access_3 in H; solve_solve_unsigned3 H
      end.
    
    Ltac solve_unsigned4:= idtac;
                           (* Two goals left: 
                      Mem.inject mu lock_mem lock_mem 2 
                      mu b1 = Some (b2, delta)   *)
                           try (subst_set;
                                eapply @INJ_locks;
                                first[
                                    now eapply concur_match_perm_restrict'; eauto|
                                    eassumption]);
                           (* second goal by assumption *)
                           try eassumption.
    Ltac solve_unsigned:=
      solve_unsigned1; solve_unsigned2;
      solve_unsigned3; solve_unsigned4.
    Instance permMapJoin_equivalent:
      Proper (access_map_equiv
                ==> access_map_equiv
                ==> access_map_equiv ==> iff) permMapJoin.
    Proof.
      setoid_help.proper_iff; setoid_help.proper_intros; subst.
      intros ??. rewrite <- H, <- H0, <- H1. auto.
    Qed.
    
    (* 4490 *)
    Lemma acquire_step_diagram_self Sem:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
             (st1 : mach_state hb) (st2 : mach_state (S hb))
             (m1 m1' m2 : mem) (mu : meminj) tid i b b' ofs delt
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
            let st2'':= fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef)
                                       new_perms2 (b', unsigned (add ofs (repr delt))) in
            syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2'' m2' event2.
    Proof.
      (*  4535 - 4490 = 45 *)
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      
      (*inversion Amatch; clear Amatch. *)

      (* Build the new angel *)
      remember (inject_virtue m2 mu angel) as angel2.
      (* remember (virtueThread_inject m2 mu (virtueThread angel),
                (empty_map, empty_map)) as angel2. *)
      remember (virtueThread angel2) as angelThread2.
      remember (virtueLP angel2) as angelLP2.

      (* Inject the loads/stores/mem_range*)
      unshelve( exploit lock_update_mem_strict_load_inject;
                eauto; try (eapply CMatch; eauto)); eauto;
        intros (m2'&Hlock_update_mem_strict_load2&Hinj2).

      assert (Hmax_equiv: Max_equiv m1 m1')
        by (eapply lock_update_mem_strict_load_Max_equiv; eassumption).

      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      exploit address_inj_lock_update_load; eauto; intros Heq.
      
      remember (build_acquire_event (b', unsigned ofs + delt ) (fst angelThread2) m2')
        as event2. 
      
      (* Instantiate some of the existensials *)
      exists event2; exists m2'.  
      split; [|split]. (* 3 goal*)
      
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
        set (newThreadPerm2 := computeMap_pair (getThreadR cnt2) (virtueThread angel2)).
        assert (Hjoin_angel2: permMapJoin_pair
                                (virtueLP_inject m2 mu lock_perm)
                                (getThreadR cnt2)
                                newThreadPerm2).
        { clear -CMatch Hangel_bound Heqangel2 Hmax_equiv Hinj2 thread_compat1 Hjoin_angel HisLock.
          (* exploit full_injects_angel; eauto; try apply CMatch. intros Hinject_angel.
            subst newThreadPerm2; simpl. *)

          (* Look at how its done on release *)
          !goal(permMapJoin_pair _ _ _).




          
          Lemma delta_map_join_inject_pair2
            : forall (m : mem) (f : meminj) 
                     (A1 A2 B1 B2 : Pair access_map)
                     (C1 C2 : Pair delta_map),
              Mem.meminj_no_overlap f m ->
              dmap_vis_filtered_pair C1 m ->
              permMapLt_pair A1 (getMaxPerm m) ->
              perm_perfect_image_dmap_pair f C1 C2 ->
              perm_perfect_image_pair f A1 A2 ->
              almost_perfect_image_pair f (getMaxPerm m) B1 B2 ->
              delta_map_join2_pair A1 B1 C1 -> delta_map_join2_pair A2 B2 C2.
          Proof.
            intros ? ?. unfold delta_map_join2_pair. solve_pair.
            apply delta_map_join2_inject.
          Qed.
          Lemma Lt_valid_map:
            forall m d,
              permMapLt_pair d (getMaxPerm m) ->
              map_valid_pair m d.
          Proof.
            intros ?. solve_pair.
            intros. intros ? **.
            destruct (valid_block_dec m b); try assumption.
            eapply Mem.nextblock_noaccess in n.
            specialize (H b ofs).
            rewrite H0 in H; hnf in H.
            rewrite getMaxPerm_correct in H. simpl in H.
            unfold permission_at in *.
            rewrite n in H; tauto.
          Qed.
          Lemma Lt_option_impl:
            forall b a,
              permMapLt_pair a b  ->
              pair21_prop full_map_option_implication a b.
          Proof.
            intros ?. solve_pair.
            intros ** ??; hnf.
            repeat match_case; eauto.
            specialize (H b0 ofs).
            rewrite Heqo, Heqo0 in H.
            inv H.
          Qed.
          Lemma Lt_inject_map_pair:
            forall mu b a, 
              injects_map mu b ->
              permMapLt_pair a b ->
              injects_map_pair mu a.
          Proof.
            intros ??. solve_pair.
            intros ** ? **.
            exploit H0; rewrite H1.
            intros HH; hnf in HH; match_case in HH.
            eapply H; eauto.
          Qed.
          
          
          Lemma max_map_valid:
            forall m, map_valid m (getMaxPerm m).
          Proof.
            intros ???? HH.
            destruct (valid_block_dec m b); auto.
            eapply Mem.nextblock_noaccess in n.
            rewrite getMaxPerm_correct in HH. unfold permission_at in *.
            rewrite HH in n; congruence.
          Qed.
          
          Lemma permMapJoin_pair_inject_acq:
            forall m1 lock_perm
                   (* (st1:  mach_state hb)
              (st2:  mach_state (S hb)) *)
                   m2 mu  th_perms1 th_perms2 virtueThread
                   (Hangel_bound:
                      pair21_prop sub_map virtueThread (snd (getMaxPerm m1))),
              let newThreadPerm1 := computeMap_pair th_perms1 virtueThread in
              permMapJoin_pair lock_perm th_perms1 newThreadPerm1 ->
              forall
                (Hlt_locks: permMapLt_pair lock_perm (getMaxPerm m1))
                (Hlt_th1 : permMapLt (fst th_perms1) (getMaxPerm m1))
                (Hlt_th2 : permMapLt (fst th_perms2) (getMaxPerm m2))
                (Hlt_lk1 : permMapLt (snd th_perms1) (getMaxPerm m1))
                (Hlt_lk2 : permMapLt (snd th_perms2) (getMaxPerm m2)),
                Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
                Mem.inject mu (restrPermMap Hlt_lk1) (restrPermMap Hlt_lk2) ->
                injects_angel mu (Build_virtue virtueThread lock_perm) ->
                let virtueThread2 := virtueThread_inject m2 mu virtueThread in
                let newThreadPerm2 := computeMap_pair (th_perms2) virtueThread2 in
                permMapJoin_pair (virtueLP_inject m2 mu lock_perm) th_perms2 newThreadPerm2.
          Proof.
            intros. subst newThreadPerm2. inv H2.

            apply compute_map_join_fwd_pair2;
              apply compute_map_join_bkw_pair2 in H.
            eapply delta_map_join_inject_pair2; eauto.
            - !goal(Mem.meminj_no_overlap _ m1).
              rewrite <- (restr_Max_equiv Hlt_th1); eapply H0.
            - !goal (dmap_vis_filtered_pair _ m1).
              eapply sub_map_filtered_pair; eassumption.
            - !goal(perm_perfect_image_dmap_pair _ _ _).
              subst virtueThread2.
              replace (virtueThread_inject m2 mu virtueThread) with
                  (virtueThread_inject (restrPermMap Hlt_th2) mu virtueThread).
              eapply inject_virtue_perm_perfect_image_dmap; eauto.
              { rewrite getMax_restr_eq; eauto. }
              
              unfold virtueThread_inject, tree_map_inject_over_mem.
              rewrite getMax_restr_eq; reflexivity.
            - !goal (perm_perfect_image_pair _ _ _).
              erewrite virtueLP_inject_max_eq_exteny.
              
              { eapply inject_virtue_perm_perfect_image; eauto.
                + move Hangel_bound at bottom.
                  apply Lt_option_impl; auto.
                  rewrite getMax_restr; auto. }
              symmetry; apply getMax_restr_eq.
            - !goal (almost_perfect_image_pair _ _ _ _).
              eapply inject_almost_perfect_pair; eauto.
          Qed.

          assert (permMapLt_pair lock_perm (getMaxPerm m1)) by
              (eapply CMatch; eauto).
          subst newThreadPerm2; subst.
          eapply permMapJoin_pair_inject_acq; try eassumption; eauto;
            try eapply Hangel_bound;
            try eapply CMatch; eauto.

          !goal (injects_angel _ _).
          split; simpl.
          - eapply Lt_inject_map_pair; debug eauto.
            eapply full_inject_map; try eapply CMatch.
            eapply max_map_valid.
          - eapply full_inject_dmap_pair.
            eapply CMatch.
            eapply join_dmap_valid_pair; eauto. }
        
        
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
        exploit INJ_lock_permissions_image; eauto;
          intros (pmap&Hpmap&Hpmap_equiv1&Hpmap_equiv2).
        eapply step_acquire with
            (b0:= b')(m':=m2')
            (virtueThread:=(virtueThread angel2))
            (pmap0:= pmap)
        ; eauto; try reflexivity.
        
        (* 10 goals produced. *)
        
        + subst  angel2 lk_mem1 lk_mem2.
          eapply inject_virtue_sub_map_pair; eauto.
          * apply Hinj_lock.
          * apply Hangel_bound.
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
        + simpl.
          exploit (permMapLt_computeMap_pair (getMaxPerm m2));
            try (intros HH; eapply HH).
          2:{ eapply Hcmpt2. }
          subst angel2. simpl.
          eapply deltaMapLt2_inject_pair.
          * eapply CMatch.
          * eapply permMapLt_computeMap_pair'.
            eapply Hlt_new.
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

          Unshelve.
          all: eauto.
          all: eapply CMatch.
    Qed. (* END acquire_step_diagram_self *)
    
    
    Lemma computeMap_mi_perm_perm_perfect:
      forall mu x1 y1 x2 y2,
        @maps_no_overlap permission _ mu x1 (fun _ : Z => None, y1) ->
        mi_perm_perm mu x1 x2 ->
        perm_perfect_image_dmap mu y1 y2 ->
        mi_perm_perm mu (computeMap x1 y1) (computeMap x2 y2).
    Proof.
      intros ** ????? HH;
        unfold Mem.perm_order'; simpl; intros.
      rename H into Hno_overlap.
      rename H0 into Hperm.
      rename H1 into HHH.
      rename H2 into H.
      match_case in H.
      rewrite computeMap_get in *.
      match_case in Heqo; subst.
      - match_case.
        + exploit HHH; clear HHH; eauto. 
          intros HHH; destruct HHH.
          exploit p_image_dmap; try 
                                  eapply at_least_Some_trivial; eauto.
          intros; normal.
          unify_injection.
          rewrite <- H1, Heqo0 in Heqo; inv Heqo; auto.
        + exploit HHH; clear HHH; eauto. 
          intros HHH; destruct HHH.
          exploit p_image_dmap; try 
                                  eapply at_least_Some_trivial; eauto.
          intros; normal.
          unify_injection.
          rewrite <- H1, Heqo0 in Heqo; inv Heqo; auto.
      - match_case.
        + exploit HHH; clear HHH; eauto. 
          intros HHH; destruct HHH.
          match_case in Heqo1; subst.
          * exploit ppre_perfect_image_dmap;
              try eapply at_least_Some_trivial; eauto.
            intros; normal.
            rewrite Heqo2 in H2; symmetry in H2.
            (*  H2 : dmap_get y1    x  x0  = Some (Some p1)
                          Heqo :     x1 !!    b1 ofs = Some p0 *)
            destruct (base.block_eq_dec b1 x); subst.
            { (* b1 = x *)
              unify_injection.
              replace x0 with ofs in H2 by omega.
              rewrite H2 in Heqo0. inv Heqo0; inv Heqo0.
            }
            {(*b1 <> x, use no_overlap*)
              unfold dmap_get in *.
              exploit Hno_overlap; try rewrite Heqo; try rewrite H2; eauto.
              constructor.
              replace ((fun _ : Z => None, y1) !! x _) with (Some (Some p1)); eauto.
              constructor.
              intros [? | ?]; tauto.
            }
          * exploit Hperm; eauto.
            rewrite Heqo; constructor.
            rewrite Heqo1; intros.
            eapply perm_order_trans; eauto.
        + match_case in Heqo1; subst.
          * destruct HHH.
            exploit ppre_perfect_image_dmap. rewrite Heqo2; constructor.
            intros; normal.
            rewrite Heqo2 in H2; symmetry in H2.
            destruct (base.block_eq_dec b1 x); subst.
            { (* b1 = x *)
              unify_injection.
              replace x0 with ofs in H2 by omega.
              rewrite H2 in Heqo0. inv Heqo0; inv Heqo0.
            }
            { (* b1 <> x *)
              
              (*
                        y1 !! b1 ofs = None     \
                        x1 !! b1 ofs = Some p0  / (x1+y1) !! b1 ofs = Some p0
                        
                        y1 !! x  x0  = Some None
                        
                        x2 !! b2 (ofs + delta) = ??         \
                        y2 !! b2 (ofs + delta) = Some None  /  (x2+y2) !! b2 (ofs+delta) = None
 

               *)
              unfold dmap_get in *.
              exploit Hno_overlap; try rewrite Heqo; try rewrite H2; eauto.
              constructor.
              replace ((fun _ : Z => None, y1) !! x _) with
                  (Some (@None permission)); eauto.
              constructor.
              intros [? | ?]; tauto.
            }
          * exploit Hperm; eauto.
            rewrite Heqo; constructor.
            rewrite Heqo1; intros. inv H1.
    Qed.
    
    Lemma sub_map_sub_map':
      forall A B x y, @sub_map A B x y -> sub_map' x y.
    Proof.
      intros **?**.
      repeat hnf in *.
      revert p y H H0.
      induction x.
      - intros; simpl in H0.
        unfold PTree.get in H0; simpl in H0.
        destruct p; try congruence.
      - intros; hnf in H; match_case in H; subst y.
        normal_hyp.
        destruct p; simpl in H0.
        + simpl; exploit IHx2; eauto.
        + simpl; exploit IHx1; eauto.
        + subst o.
          simpl in H; match_case in H.
          subst o0. simpl.
          do 2 econstructor; eauto.
    Qed.
    Lemma maps_no_overlap_Lt:
      forall mu (x:access_map) (y:delta_map) bound
             (Hno_overlap_bound:map_no_overlap mu bound),
        permMapLt x bound ->
        sub_map y (snd bound) ->
        maps_no_overlap mu x (fun _ : Z => None, y).
    Proof.
      intros ** ? **.
      assert (Hb1:at_least_Some (bound !! b1 ofs1)).
      { clear - H H4.
        hnf in H4; match_case in H4.
        specialize (H b1 ofs1).
        rewrite Heqo in H.
        hnf; match_case. inv H.
      }
      assert (Hb2:at_least_Some (bound !! b2 ofs2)).
      { clear - H5 H0.
        hnf in H5; match_case in H5.
        hnf; match_case.
        unfold PMap.get in *. match_case in Heqo.
        simpl in *.
        eapply sub_map_sub_map' in H0. exploit H0; eauto.
        intros; normal.
        rewrite H in Heqo0.
        specialize (H1 ofs2).
        rewrite Heqo0, Heqo in H1; simpl in H1.
        eapply ssrbool.not_false_is_true; eauto. }
      eapply Hno_overlap_bound; eauto.
    Qed.
    Instance permMapLt_refl:
      Reflexive permMapLt.
    intros ? ? ?. hnf. match_case; constructor. Qed.
    Lemma disjoint_join:
      forall a b c,
        permMapJoin a b c ->
        permMapsDisjoint a b.
      intros ** ??. specialize (H b0 ofs).
      unfold perm_union; match_case.
      + inv H; eexists; simpl; eauto.
      + inv H; eexists; simpl; eauto.
    Qed.
    Lemma disjoint_lt:
      forall A A' B,
        permMapLt A' A ->
        permMapsDisjoint A B ->
        permMapsDisjoint A' B.
    Proof.
      intros ** ??. specialize (H b ofs).
      dup H as HH.
      specialize (H0 b ofs) as [C H0].
      unfold Mem.perm_order'',perm_union in *.
      (* We do all the cases *)
      repeat match_case in H;
        repeat match_case in H0;
        inv H0; inv H; try econstructor; eauto.
    Qed.
    Hint Unfold permMapsDisjoint2: pair.
    Lemma disjoint_lt_pair:
      forall a a' b,
        permMapLt_pair2 a' a ->
        permMapsDisjoint2 a b ->
        permMapsDisjoint2 a' b.
    Proof.
      solve_pair. apply disjoint_lt.
    Qed.
    Lemma join_disjoint:
      forall A B C,
        permMapJoin A B C ->
        permMapsDisjoint A B.
    Proof.
      intros ** b ofs. specialize (H b ofs).
      inv H; econstructor; simpl; eauto.
      unfold perm_union; match_case; eauto.
    Qed.
    Lemma join_disjoint_pair:
      forall A B C,
        permMapJoin_pair A B C ->
        permMapsDisjoint2 A B.
    Proof.
      solve_pair.
      apply disjoint_join.
    Qed.
    Lemma permMapCoherence_Lt:
      forall p1 p2 p1' p2',
        permMapCoherence p1 p2 ->
        permMapLt p1' p1 ->
        permMapLt p2' p2 ->
        permMapCoherence p1' p2'.
    Proof.
      intros ** b ofs.
      eapply perm_coh_lower; eauto.
    Qed.
    
    Lemma mi_perm_perm_threads:
      forall hb i cd mu m1 m2 (st1: @t dryResources (HybridSem (@Some nat hb))) st2 Hcnt1 Hcnt2,
        MyConcurMatch.concur_match hb cd mu st1 m1 st2 m2 ->
        mi_perm_perm mu (thread_perms i st1 Hcnt1) (thread_perms i st2 Hcnt2).
    Proof.
      intros * CMatch.
      match goal with
        |- mi_perm_perm _ ?a ?b =>
        rewrite <- (getCur_restr a);
          rewrite <- (getCur_restr b)
      end.
      eapply mi_inj_mi_perm_perm_Cur, CMatch.
      Unshelve.  all: eapply CMatch.
    Qed.

    Definition mi_memval_perm_dmap f dm cont1 cont2:=
      forall (b1 b2 : block) (delta ofs : Z),
        f b1 = Some (b2, delta) ->
        opt_rel Mem.perm_order'' (dmap_get dm b1 ofs) (Some (Some Readable)) ->
        memval_inject f (ZMap.get ofs cont1 !! b1)
                      (ZMap.get (ofs + delta) cont2 !! b2).
    Lemma mi_inv_option_implication:
      forall m1 m2 f b1 b2 delta,
        Mem.mem_inj f m1 m2 ->
        f b1 = Some(b2,delta) ->
        forall ofs p, (getMaxPerm m1) !! b1 ofs = Some p ->
                      option_implication (snd (getMaxPerm m1)) ! b1 (snd (getMaxPerm m2)) ! b2.
    Proof.
      intros; hnf. do 2 (match_case; auto).
      exploit Mem.mi_perm; eauto.
      - instantiate(2:=Max). 
        hnf. rewrite_getPerm; unfold "!!"; rewrite Heqo; simpl.
        unfold "!!" in H1. rewrite Heqo in H1. rewrite H1. constructor.
      - unfold Mem.perm; rewrite_getPerm; unfold "!!". rewrite Heqo0.
        rewrite Max_isCanonical.
        intros HH; inv HH.
    Qed.
    Lemma mi_memval_perm_computeMap:
      forall mu x y cont1 cont2,
        mi_memval_perm mu x cont1 cont2 ->
        mi_memval_perm_dmap mu y cont1 cont2 ->
        mi_memval_perm mu (computeMap x y) cont1 cont2.
    Proof.
      intros. hnf in *; intros.
      rewrite computeMap_get in H2.
      match_case in H2.
      eapply H0; auto.
      rewrite Heqo. constructor; auto.
    Qed.
    Lemma mi_memval_perm_computeMap_Lt:
      forall mu cont1 cont2 p p',
        mi_memval_perm mu p cont1 cont2 ->
        permMapLt p' p ->
        mi_memval_perm mu p' cont1 cont2.
    Proof.
      intros; hnf; intros.
      eapply H; eauto.
      eapply perm_order_trans211; eauto.
    Qed.    
    
    Fixpoint list_f {A} (f: Z -> A) (n:nat) ofs:=
      match n with
      | S n' => f ofs :: list_f f n' (ofs + 1)
      | _ => nil
      end.
    Lemma forall_range:
      forall n {A} P (f: Z -> A) ofs,
        Forall P (list_f f n ofs) ->
        forall ofs0,
          Intv.In ofs0 (ofs, ofs + (Z.of_nat n)) ->
          P (f ofs0).
    Proof.
      induction n; intros.
      - simpl in H0.
        replace (ofs + 0) with ofs in H0 by omega.
        exfalso; eapply Intv.empty_notin; eauto.
        unfold Intv.empty; simpl; omega.
      - destruct (Z.eq_dec ofs ofs0).
        + subst; inv H; auto.
        + assert (Intv.In ofs0 (ofs + 1, (ofs + 1) + Z.of_nat n)).
          { unfold Intv.In in *.
            simpl in *.
            destruct H0; split.
            * omega.
            * clear - H1.
              replace (ofs + 1 + Z.of_nat n)
                with (ofs + Z.pos (Pos.of_succ_nat n)); auto.
              clear.
              rewrite <- Z.add_assoc, Zpos_P_of_succ_nat.
              omega. }
          clear H0.
          eapply IHn; eauto.
          inv H; auto.
    Qed.
    Lemma fun_range:
      forall n {A} (f f': Z -> A) ofs,
        list_f f n ofs =
        list_f f' n ofs  ->
        forall ofs0,
          Intv.In ofs0 (ofs, ofs + (Z.of_nat n)) ->
          f ofs0 = f' ofs0.
    Proof.
      induction n; intros.
      - simpl in H0.
        replace (ofs + 0) with ofs in H0 by omega.
        exfalso; eapply Intv.empty_notin; eauto.
        unfold Intv.empty; simpl; omega.
      - destruct (Z.eq_dec ofs ofs0).
        + subst; inv H; auto.
        + assert (Intv.In ofs0 (ofs + 1, (ofs + 1) + Z.of_nat n)).
          { unfold Intv.In in *.
            simpl in *.
            destruct H0; split.
            * omega.
            * clear - H1.
              replace (ofs + 1 + Z.of_nat n)
                with (ofs + Z.pos (Pos.of_succ_nat n)); auto.
              clear.
              rewrite <- Z.add_assoc, Zpos_P_of_succ_nat.
              omega. }
          clear H0.
          eapply IHn; eauto.
          inv H; auto.
    Qed.
    Lemma fun_range4:
      forall {A} (f f': Z -> A) ofs,
        f ofs :: f (ofs + 1)
          :: f (ofs + 1 + 1)
          :: f (ofs + 1 + 1 + 1):: nil = 
        f' ofs :: f' (ofs + 1)
           :: f' (ofs + 1 + 1)
           :: f' (ofs + 1 + 1 + 1):: nil ->
        forall ofs0,
          Intv.In ofs0 (ofs, ofs + 4) ->
          f ofs0 = f' ofs0.
    Proof.
      intros.
      eapply (fun_range 4); simpl; eauto.
    Qed.
    
    Inductive same_cnt {hb1 hb2} i (st1: ThreadPool hb1) (st2: ThreadPool hb2):
      containsThread st1 i ->
      containsThread st2 i -> Prop :=
    | Build_same_cnt:
        forall (cnt1: containsThread(Sem:=HybridSem hb1) st1 i)
          (cnt2: containsThread(Sem:=HybridSem hb2) st2 i),
          same_cnt i st1 st2 cnt1 cnt2.

    
    Lemma mi_memval_perm_almosequal:
      forall mu m1 m1' m2 m2' adr1 adr2 p_store p delta
        (Hreadable: forall ofs, Intv.In ofs (snd adr1, snd adr1 + 4) ->
                           Mem.perm_order' (p_store !! (fst adr1) ofs) Readable)
        (Hno_over: maps_no_overlap mu p p_store),
        content_almost_same m1 m1' adr1 ->
        content_almost_same m2 m2' adr2 ->
        mu (fst adr1) = Some (fst adr2, delta) ->
        snd adr2 = snd adr1 + delta ->
        (forall ofs : Z,
            Intv.In ofs (snd adr1, snd adr1 +  4) ->
            memval_inject mu
                          (ZMap.get ofs (Mem.mem_contents m1') !! (fst adr1))
                          (ZMap.get (ofs + delta) (Mem.mem_contents m2') !! (fst adr2)) ) ->
        mi_memval_perm mu p 
                       (Mem.mem_contents m1) (Mem.mem_contents m2) ->
        mi_memval_perm mu p
                       (Mem.mem_contents m1') (Mem.mem_contents m2').
    Proof.
      intros ** ? **.
      eapply perms_no_over_point_to_range in Hno_over.
      pose proof (Classical_Prop.classic (b1 <> fst adr1 \/ ~ Intv.In ofs (snd adr1, snd adr1 +  4))).
      destruct H7.
      destruct (base.block_eq_dec b1 (fst adr1)) eqn:HH; subst.
      destruct H7 as [HH1 |HH1]; try congruence.
      
      
      - (* ~ Intv.In ofs (snd adr1, snd adr1 + LKSIZE) *)
        unify_injection.
        rewrite H,H0; auto.
        rewrite H2; auto.
        right. hnf; simpl. intros.
        unfold Intv.In in *; simpl in *.
        eapply HH1. clear - H7. omega.
      - (* b1 <> fst adr1 *)
        exploit Hno_over; try eassumption.
        + !goal(_<_). instantiate(1:= 4). omega.
        + !goal(Mem.perm_order' _ Nonempty).
          eapply perm_order_trans101; eauto. constructor.
        + intros. instantiate(1:=snd adr1).
          eapply perm_order_trans101; eauto.
          eapply Hreadable. hnf; simpl; omega.
          constructor.
        + intros.
          rewrite H,H0; auto.
          rewrite H2; auto.
      - eapply Classical_Prop.not_or_and in H7; normal.
        apply Classical_Prop.NNPP in H7;
          apply Classical_Prop.NNPP in H8.
        subst b1.
        rewrite H1 in H5; inv H5.
        auto.
    Qed.
    Lemma mi_memval_perm_store:
      forall (b1 b2 : block) v
             (m1 m1' m2 m2' lock_mem : mem)
             (perm1 perm1' perm2' : access_map)
             (delta ofs : Z)
             (mu : meminj) 
             (Hinj_b' : mu b1 = Some (b2, delta))
             (Hlt_th1 : permMapLt perm1 (getMaxPerm m1))
             (Hinj' : Mem.inject mu m1 m2)
             (Hmax_eq: Max_equiv lock_mem m1)
             (Haccess : Mem.range_perm lock_mem b1 ofs (ofs + LKSIZE) Cur Readable)
             (Hwritable_lock1 : permMapLt
                                  (setPermBlock (Some Writable) b1 ofs perm1' LKSIZE_nat)
                                  (getMaxPerm m1))
             (Hwritable_lock0 : permMapLt
                                  (setPermBlock (Some Writable) b2 
                                                (ofs + delta) perm2' LKSIZE_nat) 
                                  (getMaxPerm m2)),
        let m_writable_lock_1 := restrPermMap Hwritable_lock1 : mem in
        let m_writable_lock_0 := restrPermMap Hwritable_lock0 : mem in
        forall (Hstore : Mem.store AST.Mint32 m_writable_lock_1 b1 ofs (Vint v) = Some m1')
               (Hstore0 : Mem.store AST.Mint32 m_writable_lock_0 b2 (ofs + delta) (Vint v) =
                          Some m2'),
          mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2)
          ->
          mi_memval_perm mu perm1 (Mem.mem_contents m1') (Mem.mem_contents m2').
    Proof.
      intros; subst_set.
      eapply (mi_memval_perm_almosequal) with
          (adr1:= (b1,ofs))(adr2:= (b2,ofs+delta)); eauto.
      
      ++ simpl; intros.
         unfold Mem.range_perm in Haccess.
         rewrite getCur_restr.
         rewrite setPermBlock_same.
         instantiate(1:=Some Writable). constructor.
         assert (4< Z.of_nat LKSIZE_nat).
         { unfold LKSIZE_nat, LKSIZE in *.
           rewrite size_chunk_Mptr.
           clear - H0. red in H0; simpl in H0. match_case; simpl; omega. }
         !goal (ofs <= ofs0 < ofs + Z.of_nat LKSIZE_nat)%Z.
         clear - H0 H1. hnf in H0; simpl in H0.
         omega. 
      ++ !goal(maps_no_overlap _ _ _).
         eapply maps_no_overlap_under_mem; eauto. (* *)
         apply Hinj'. 
         rewrite getCur_restr. apply Hwritable_lock1.
      ++ !goal(content_almost_same _ m1' _).
         pose proof (@restr_content_equiv _  _ Hwritable_lock1) as H0; symmetry in H0.
         eapply content_almost_same_proper; try eassumption; try reflexivity.
         eapply store_almost_same; eassumption.
      ++ !goal(content_almost_same _ m2' (b2, (ofs + delta))).
         pose proof (@restr_content_equiv _  _ Hwritable_lock0) as H0; symmetry in H0.
         eapply content_almost_same_proper; try eassumption; try reflexivity.
         eapply store_almost_same; eassumption.
      ++ simpl; intros.
         {   clear - H0 Hstore Hstore0.
             move Hstore at bottom.
             eapply Mem.loadbytes_store_same,loadbytes_D in Hstore.
             destruct Hstore as [? Hstore].
             eapply Mem.loadbytes_store_same,loadbytes_D in Hstore0.
             destruct Hstore0 as [? HH].
             rewrite Hstore in HH.
             simpl in HH.
             assert (Heq_range: forall ofs0,
                        Intv.In ofs0 (ofs, ofs + 4) -> 
                        ZMap.get ofs0 (Mem.mem_contents m1') !! b1 =
                        ZMap.get (ofs0+delta) (Mem.mem_contents m2') !! b2
                    ).
             { eapply fun_range4; eauto.
               repeat match goal with
                      | |- context [ ?x + delta ] =>
                        replace (x + delta) with (delta + x) in * by omega
                      end;
                 repeat rewrite Z.add_assoc; auto. }
             clear HH.
             rewrite <- Heq_range; auto.
             assert (Heq_range_bytes: forall ofs0,
                        Intv.In ofs0 (ofs, ofs + 4) -> 
                        exists bl,
                          ZMap.get ofs0 (Mem.mem_contents m1') !! b1 =
                          Byte bl
                    ).
             { eapply (forall_range 4 (fun (X:memval) => exists bl:byte, X = Byte bl)).
               simpl in *. rewrite <- Hstore.
               repeat econstructor. }
             exploit Heq_range_bytes; eauto;
               intros (bl& -> ).
             econstructor.
             
         }
         Unshelve.
         eauto.
         unfold Max_equiv in *; rewrite Hmax_eq; auto.
    Qed.
    
    Lemma sub_map_implictaion':
      forall (A B : Type) (x : PMap.t (Z -> option A)) (y : PMap.t (Z -> option B)),
        fst x = (fun _ : Z => None) ->
        sub_map (snd x) (snd y) -> forall b : positive,
            forall ofs, option_implication (x !! b ofs) (y !! b ofs).
    Proof.
      intros. eapply sub_map_sub_map' in H0.
      hnf. repeat match_case; eauto.
      unfold "!!" in *.
      rewrite H in Heqo.
      match_case in Heqo. 
      eapply H0 in Heqo1. normal_hyp.
      rewrite H1 in Heqo0.
      hnf in H2. specialize (H2 ofs).
      rewrite Heqo, Heqo0 in H2.
      exploit H2. econstructor.
      intros HH; inv HH.
    Qed.
    Lemma mem_inj_Max_implication:
      forall mu m1 m2,
        Mem.mem_inj mu m1 m2 ->
        forall b1 b2 delta ofs,
          mu b1 = Some (b2, delta) ->
          option_implication ((getMaxPerm m1) !! b1 ofs)
                             ((getMaxPerm m2) !! b2 (ofs + delta)).
    Proof.
      intros.
      hnf; match_case; eauto.
      exploit Mem.mi_perm; try eapply Hinj'; eauto.
      instantiate(1:=Nonempty).
      instantiate(1:=Max).
      instantiate(1:=ofs).
      hnf.
      rewrite_getPerm. rewrite Heqo.
      apply perm_any_N.
      unfold Mem.perm. rewrite_getPerm.
      intros HH; match_case; eauto.
    Qed.
    Lemma mi_perm_inv_perm_compute:
      forall v
             (mu : meminj)
             (m1 m1' m2 : mem)
             (perm1 perm2 : access_map)
             (Hthread_mem1 : access_map_equiv perm1 (getCurPerm m1))
             (Hthread_mem2 : access_map_equiv perm2 (getCurPerm m2))
             (Hangel_bound : sub_map v (snd (getMaxPerm m1)))
             (Hinj' : Mem.inject mu m1 m2)
             (Hmax_eq0 : Max_equiv m1 m1'),
        mi_perm_inv_perm mu (computeMap perm1 v)
                         (computeMap perm2 (tree_map_inject_over_mem m2 mu v)) m1'.
    Proof.
      intros; hnf; intros.
      destruct (Classical_Prop.classic (Mem.perm m1' b1 ofs Max Nonempty))
        as [HH|HH]; eauto.
      unfold Mem.perm in HH.
      
      (*Lem ma about computeMap? *)
      
      
      clear - Hthread_mem1 Hthread_mem2 m1' H Hangel_bound Hmax_eq0 HH Hinj'
                           Hangel_bound m2 H H0.

      rewrite computeMap_get; rewrite computeMap_get in H0.
      (*Maybe best to start destructing the virtue1 and then destruct virtue2*)
      match_case; [|match_case in H0].
      -- (*dmap1 = Some *)
        clear - Hangel_bound m2 H H0 Heqo Hinj'.
        exploit tree_map_inject_over_mem_correct_forward; eauto.
        { instantiate(1:=m2).
          intros ofs0.
          eapply option_implication_trans.
          ++ instantiate(1:=((getMaxPerm m1) !! b1 ofs0)).        
             eapply sub_map_implictaion'; eauto.
          ++ eapply mem_inj_Max_implication; eauto.
             apply Hinj'. }
        { eapply no_overla_dmap_mem.
          intros; eapply sub_map_implication_dmap.
          eapply Hangel_bound.
          eapply Hinj'. }
        { unfold delta_map in *. intros HH'; rewrite HH' in H0. 
          auto. }

      -- (*dmap1 = None | dmap2 = Some *)
        exploit dmap_inject_correct_backwards; eauto.
        intros (?&?&?&?&?&?).
        destruct (base.block_eq_dec b1 x).
        ++ (*b0 = x*)
          subst. repeat unify_injection. assert (ofs=x1) by omega; subst x1.
          unfold delta_map in *. 
          rewrite Heqo in H3; congruence.
        ++           (*b0 <> x*)      
          assert (HHx : Mem.perm_order' ((Mem.mem_access m1) !! x x1 Max) Nonempty).
          { exploit sub_map_implication_dmap.
            eapply Hangel_bound.
            intros HH1; simpl in *.
            unfold option_implication_dmap_access in *.
            unfold delta_map in *; rewrite H3 in HH1.
            simpl in HH1.
            rewrite getMaxPerm_correct in HH1. unfold permission_at in HH1.
            match_case in HH1.
            constructor. }
          assert (HHb1 : Mem.perm_order' ((Mem.mem_access m1) !! b1 ofs Max) Nonempty).
          { revert HH; do 2 rewrite_getPerm. rewrite Hmax_eq0; auto. }
          exploit Mem.mi_no_overlap; try eapply Hinj'; eauto.
          intros [HHH| HHH]; contradict HHH; auto.
      -- (*dmap1 = None | dmap2 = None *)
        rewrite Hthread_mem1.
        rewrite Hthread_mem2 in H0.
        eapply inject_mi_perm_inv_perm_Cur in H0; eauto.
        rewrite <- Hmax_eq0. eassumption.
        
    Qed.
    
    Lemma invariant_update_join_rel:
      forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
             h laddr c lock_perm th_perm
             (Hcnt:ThreadPool.containsThread st h),
        coqlib4.isSome (ThreadPool.lockRes st laddr) ->
        st' =
        ThreadPool.updLockSet (ThreadPool.updThread Hcnt c th_perm) laddr lock_perm ->
        invariant st ->
        permMapJoin_pair th_perm lock_perm (getThreadR Hcnt) ->
        invariant st'.
    Proof.
      intros * ? ? Hinv Hjoin; eapply invariant_update; eauto.
      - intros ; eapply disjoint_lt_pair.
        eapply permMapJoin_lt_pair1; eauto.
        eapply Hinv; auto.
      - intros. eapply disjoint_lt_pair.
        eapply permMapJoin_lt_pair2; eauto.
        exploit no_race; eauto; intros HH; apply HH.
      - eapply join_disjoint_pair; eauto.
      - intros ; eapply disjoint_lt_pair.
        intros; eapply permMapJoin_lt_pair1; eauto.
        exploit no_race; eauto; intros HH; apply HH.
      - intros; eapply permMapsDisjoint2_comm,
                disjoint_lt_pair; eauto. 
        eapply permMapJoin_lt_pair2; eauto.
        eapply Hinv; auto.
      - eapply permMapCoherence_Lt.
        + exploit thread_data_lock_coh; eauto.
          intros [HH ?]. eapply HH.
        + eapply permMapJoin_lt.
          eapply Hjoin.
        + eapply permMapJoin_lt.
          eapply Hjoin.
      - eapply permMapCoherence_Lt.
        + exploit thread_data_lock_coh; eauto.
          intros [HH ?]. eapply HH.
        + eapply permMapJoin_lt.
          eapply permMapJoin_comm, Hjoin.
        + eapply permMapJoin_lt; eapply Hjoin.
      - eapply permMapCoherence_Lt.
        + exploit thread_data_lock_coh; eauto.
          intros [HH ?]. eapply HH.
        + eapply permMapJoin_lt, Hjoin.
        + eapply permMapJoin_lt; eapply permMapJoin_comm, Hjoin.
      - split; eapply permMapCoherence_Lt.
        3,5: reflexivity.
        1,3: exploit thread_data_lock_coh; try apply Hinv;
          intros [HH ?]; eapply HH.
        all: eapply permMapJoin_lt, Hjoin.
      - split; eapply permMapCoherence_Lt.
        2,6: reflexivity.
        1,3: exploit thread_data_lock_coh; try apply Hinv;
          intros [HH ?]; eapply HH.
        all: eapply permMapJoin_lt,permMapJoin_comm, Hjoin.
      - split; eapply permMapCoherence_Lt.
        2,6: reflexivity.
        1: exploit thread_data_lock_coh; eauto; intros [? HH];
          eapply HH; eauto.
        2: exploit locks_data_lock_coh; try eassumption;
          intros [HH ?]; eapply HH.
        all: eapply permMapJoin_lt, Hjoin.
      - eapply permMapCoherence_Lt.
        2,3: eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
        exploit thread_data_lock_coh; eauto; intros [HH ?]; auto.
        eapply HH.
      - intros; split; eapply permMapCoherence_Lt.
        2,6: reflexivity.
        2,4: eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
        2:{  exploit locks_data_lock_coh; eauto.
             intros [HH ?]; eapply HH. }
        {  exploit thread_data_lock_coh; eauto.
           intros [? HH]. eapply HH; eauto. }
    Qed.
    Lemma tree_map_inject_restr:
      forall A p m mu perm Hlt,
        @tree_map_inject_over_mem A m mu perm =
        tree_map_inject_over_mem (@restrPermMap p m Hlt) mu perm.
    Proof.
      intros. unfold tree_map_inject_over_mem.
      rewrite restr_Max_eq; reflexivity.
    Qed.
    
    Lemma mem_eq:
      forall m1 m2,
        Mem.mem_contents m1 = Mem.mem_contents m2 ->
        Mem.mem_access m1 = Mem.mem_access m2 ->
        Mem.nextblock m1 = Mem.nextblock m2 ->
        m1 = m2.
    Proof.
      intros. destruct m1, m2; simpl in *.
      dependent_rewrite H.
      dependent_rewrite H0.
      dependent_rewrite H1.
      f_equal; try apply Axioms.proof_irr.
    Qed.
    Lemma restrPermMap_access_equiv:
      forall p p' m Hlt Hlt',
        access_map_equiv p p'->
        @restrPermMap p m Hlt =
        @restrPermMap p' m Hlt'.
    Proof.
      intros.
      unfold restrPermMap.
      
      eapply mem_eq; try solve[simpl; eauto].
      simpl; do 2 f_equal.
      extensionality b;
        extensionality f;
        extensionality ofs.
      extensionality k. match_case; eauto.
      rewrite H. eauto.
    Qed.
    Lemma virtue_inject:
      forall mu virt m2',
        injects_dmap mu virt ->
        map_no_overlap mu (fun _ => None, virt) ->
        ( forall b1 b2 ofs0 delta,
            mu b1 = Some (b2, delta) ->
            option_implication (dmap_get virt b1 ofs0)
                               ((getMaxPerm m2') !! b2 (ofs0 + delta))) ->
        EventsAux.inject_delta_map mu virt
                                   (tree_map_inject_over_mem m2' mu virt).
    Proof.
      intros. econstructor.
      - intros; exploit H; eauto.
        intros HH; inv HH.
        exploit H2; eauto; intros HH.
        do 2 eexists; split; eauto.
        eapply tree_map_inject_over_mem_correct_forward; eauto.
      - intros. eapply dmap_inject_correct_backwards in H2.
        normal_hyp. subst.
        do 3 eexists. repeat weak_split; eauto.
    Qed.
    (*move to inject_virtue *)
    Lemma virtue_inject_bounded:
      forall mu virt m2 m1,
        Mem.mem_inj mu m1 m2 ->
        injects_dmap mu virt ->
        sub_map virt (snd (getMaxPerm m1)) ->
        Mem.meminj_no_overlap mu m1 ->
        (forall b1 b2 delta, mu b1 = Some (b2, delta) ->
                        Mem.valid_block m2 b2) -> 
        EventsAux.inject_delta_map mu virt (tree_map_inject_over_mem m2 mu virt).
    Proof.
      intros; eapply virtue_inject; eauto.
      - eapply no_overla_perm_mem; eauto.
        eapply sub_map_implication_dmap; eauto.
      - intros. eapply option_implication_trans.
        + eapply sub_map_implictaion'; eauto.
        + eapply mem_inj_Max_implication; eauto.
    Qed.
    
    Lemma lock_update_mem_strict_load_Max_eq:
      forall b ofs p m m' v1 v2,
        lock_update_mem_strict_load b ofs p m m' v1 v2 ->
        getMaxPerm m = getMaxPerm m'.
    Proof.
      intros; inv H.
      erewrite <- getMax_restr_eq.
      eapply store_max_eq; eauto.
    Qed.
    Lemma perm_image_injects_map:
      (* should probably replace perm_image 
                     with full_inject_map*)
      forall mu mp, perm_image mu mp <-> injects_map mu mp.
    Proof.
      split; intros ** ? **.
      - exploit H. eapply at_least_Some_trivial; eauto.
        intros (?&?&?); econstructor; eauto.
      - hnf in H0. match_case in H0.
        exploit H; eauto. intros HH; inv HH.
        repeat econstructor; eauto.
    Qed.
    Lemma map_valid_Lt:
      forall m p1 p2,
        permMapLt p1 p2 ->
        map_valid m p2 ->
        map_valid m p1.
    Proof.
      intros ** ? **. 
      specialize (H b ofs).
      rewrite H1 in H.
      simpl in H; hnf in H.
      match_case in H; eauto.
    Qed.
    Lemma map_valid_proper:
      Proper (mem_equiv ==> access_map_equiv ==> iff)
             map_valid.
    Proof.
      setoid_help.proper_iff.
      setoid_help.proper_intros.
      intros ? **.
      hnf. inv H. rewrite <- nextblock_eqv.
      eapply H1.
      rewrite H0; eauto.
    Qed.
    Lemma release_step_diagram_self Sem:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem)) tid
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
              try eapply HHlock; debug eauto.
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
            by (apply inject_restr; auto).
            assert (Hinj1': Mem.inject mu (restrPermMap Hlt11') (restrPermMap Hlt21'))
            by (apply inject_restr; auto). 
              
          






      
      
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
                -- exploit MyConcurMatch.mtch_source; eauto.
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

    
    Lemma INJ_lock_permissions_None
      : forall (hb : nat) (ocd : option compiler_index) (j : meminj)
          (cstate1 : ThreadPool (Some hb)) (m1 : mem)
          (cstate2 : ThreadPool (Some (S hb))) (m2 : mem) ,
        MyConcurMatch.concur_match hb ocd j cstate1 m1 cstate2 m2 ->
        Mem.meminj_no_overlap j m1 ->
        forall (b b' : block) (delt : Z) (rmap : lock_info) ofs
          (Haccess: Mem.perm m1 b ofs Cur Readable),
          j b = Some (b', delt) ->
          lockRes cstate1 (b, ofs) = None ->
          lockRes cstate2 (b', ofs + delt) = None.
    Proof.
      intros.
      match goal with
        |- ?X = _ => destruct X eqn:HH
      end; eauto.

      eapply INJ_lock_permissions_preimage in HH; eauto;
        destruct HH as (?&?&?&?&?&?&?&?).
      exfalso; destruct (peq x0 b).
      - subst. unify_injection.
        replace x1 with (ofs) in H4. rewrite H2 in H4; congruence.
        omega.
      - exploit H0; try eapply n; eauto.
        -- eapply Mem.perm_implies.
           eapply writable_locks; eauto. constructor.
        -- instantiate(1:= ofs).
           eapply Mem.perm_implies. eapply Mem.perm_cur_max.
           eauto.
           constructor.
        -- intros [HH|HH]; auto.
    Qed.
    Lemma make_step_diagram_self Sem: (*5336*) 
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
             (st1 : mach_state hb) (st2 : mach_state (S hb))
             (m1 m1' m2 : mem) (mu : meminj) tid i b1 b2 ofs delt
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
            syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2.
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

      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      exploit address_inj_lock_update;
        try apply Hlock_update_mem_strict; eauto; intros Heq.
      
      assert (Hinj: Mem.inject mu m1 m2).
      { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
      
      remember (Events.mklock (b2, unsigned ofs + delt ))
        as event2. 
      
      (* Instantiate some of the existensials *)
      exists event2; exists m2'.  
      split; [|split]. (* 3 goal*)
      
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
        
        eapply (step_mklock _ _ _ _ _ )
          with (pmap_tid':= new_perms2);
          eauto; try reflexivity; try solve[apply CMatch].
        
        (* 8 goals produced. *)
        + !goal (semantics.at_external _ _ _ = Some (MKLOCK, _)).
          abstract_proofs; unify_proofs.
          rewrite (cur_equiv_restr_mem_equiv m2 _ abs_proof Hthread_mem2).
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
          

    Qed. (* make_step_diagram_self *)

    Lemma free_step_diagram_self Sem:
      let CoreSem:= sem_coresem Sem in
      forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
             (st1 : mach_state hb) (st2 : mach_state (S hb))
             (m1 m2 : mem) (mu : meminj) tid i b1 b2 ofs delt
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
        let ofs2:=  unsigned ofs + delt in
        let new_perms2:=
            setPermBlock_var_pair b2 ofs2 LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR cnt2) in
        let evnt1:= Events.freelock (b1, unsigned ofs) in
        exists event2 (m2' : mem),
          let Hcmpt2:= memcompat2 CMatch in
          let st2':= remLockfFullUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                        new_perms2 (b2, unsigned ofs + delt) in
          match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
          inject_sync_event mu evnt1 event2 /\
          syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2.
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
      
      exists event2; exists m2.  
      split; [|split]. (* 3 goal*)
      
      - !goal(match_self _ _ _ _ _ _).
        inversion Amatch. constructor; eassumption.
        
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
          erewrite (cur_equiv_restr_mem_equiv _ _ _ Hthread_mem2).
          erewrite <- coerse_state_atx; eauto.
          eapply atx_injection; eauto.
          
          
        + !goal (lockRes _ (b2,_) = Some _).
          simpl in *; rewrite <- Hpmap; repeat f_equal; auto.
        + clear - Hempty_lock hb Hpmap_equiv1 Hpmap_equiv2.
          
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

    Qed. (* free_step_diagram_self *)


    
    Lemma acquire_fail_step_diagram_self Sem:
      let CoreSem:= sem_coresem Sem in
      forall (m1 m2: mem)
             (SelfSim: (self_simulation (@semC Sem) CoreSem))
             (st1 : mach_state hb) (st2 : mach_state (S hb))
             (mu : meminj) tid i b b' ofs delt
             (Hinj_b : mu b = Some (b', delt))
             cnt1 cnt2 (* Threads are contained *)
             (CMatch: concur_match i mu st1 m1 st2 m2)
             
             (* Thread states *)
             (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
             (HState1: coerce_state_type _ sum_state1 th_state1  
                                         (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
             (HState2: coerce_state_type (@semC Sem) sum_state2 th_state2
                                         (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
             (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
             (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
             
             (* angel,lock permissions and new thread permissions *)
             (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
             (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
             (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
             (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                            Some (LOCK, (Vptr b ofs :: nil)%list))
             (Hlock_lt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1)),
        let m1_locks:= restrPermMap Hlock_lt in
        forall (Hload: Mem.load AST.Mint32 m1_locks b (unsigned ofs) = Some vzero)
          (Hrange_perm: perm_interval m1_locks b (unsigned ofs) LKSIZE Cur Readable),
          let evnt1 := Events.failacq (b, unsigned ofs) in
          exists evnt2,
            inject_sync_event mu evnt1 evnt2 /\
            forall perm Hlt_perm,
              let m2_any:= @restrPermMap perm m2 Hlt_perm in
              forall (Hcmpt2: mem_compatible st2 m2_any),
                syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2 m2_any evnt2.
    Proof.
      
      intros; simpl in *.
      (*Add all the memories and theeir relations *)
      get_mem_compatible.
      get_thread_mems.
      
      replace (m1_locks) with lk_mem1 in * by
          (subst m1_locks lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
      clear m1_locks Hlock_lt.
      
      assert (Hmem_equiv1: mem_equiv m1 th_mem1).
      { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      assert (Hmem_equiv2: mem_equiv m2 th_mem2).
      { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
      
      (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
      assert (Heq:unsigned (add ofs (repr delt)) = unsigned ofs + delt).
      { eapply Mem.address_inject; try apply Hinj_lock; eauto.
        unfold perm_interval in Hrange_perm.
        eapply perm_range_perm; eauto.
        move Hrange_perm at bottom.
        { clear. unfold Intv.In; simpl.
          pose proof LKSIZE_pos; omega. }
      }
      
      assert (Hinj: Mem.inject mu m1 m2).
      { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
      
      remember (Events.failacq (b', unsigned ofs + delt )) as evnt2. 
      
      (* Instantiate some of the existensials *)
      exists evnt2; split. (* 3 goal*)
      
      - !goal(inject_sync_event mu evnt1 evnt2).
        subst evnt1 evnt2; do 2 econstructor; auto. assumption.
        
      - intros; !goal (syncStep _ _ _ _ _ _).
        (* Goal: show the source-external-step*)
        (* get the memory and injection *)
        subst evnt2; rewrite <- Heq.
        
        eapply (step_acqfail); eauto; try reflexivity; try solve[apply CMatch].
        
        (* 8 goals produced. *)
        + !goal (semantics.at_external _ _ _ = Some (LOCK, _)).
          
          pose proof (cur_equiv_restr_mem_equiv
                        _ _ (fst (ssrfun.pair_of_and (Hcmpt0 tid cnt2)))).
          erewrite <- coerse_state_atx; eauto.
          (* The following proof comes from acquire_step_diagram ...
               Should probably be turned into a lemm
           *)
          
          { clean_proofs.
            eapply ssim_preserves_atx in Hat_external.
            2: { inversion Amatch; constructor; eauto. }
            destruct Hat_external as (args' & Hat_external2 & val_inj).
            replace ( Vptr b' (add ofs (repr delt)) :: nil) with args'.
            
            simpl; unfold at_external_sum, sum_func.
            subst CoreSem; rewrite <- (restr_proof_irr (proj1 (Hcmpt0 tid cnt2))).
            rewrite <- Hat_external2; simpl.
            clear - Hthread_mem2 HState2 Hthread_mem1.
            
            inversion HState2; subst.
            - !goal ( Clight.at_external _ = _ _ m2).
              replace c with th_state2; auto.
              2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
              (* why can't I rewrite?*)
              
              eapply C_at_external_proper; auto.
              etransitivity.
              
              + symmetry; unshelve eapply restrPermMap_idempotent.
                rewrite Hthread_mem2; exact (cur_lt_max _).
              + rewrite RPM.
                eapply cur_equiv_restr_mem_equiv.
                eassumption.
            - !goal ( Asm.at_external _ _ = _ _ m2).
              replace c with th_state2; auto.
              2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
              simpl.
              (* why can't I rewrite?*)
              eapply Asm_at_external_proper; auto.
              etransitivity.
              
              + symmetry; unshelve eapply restrPermMap_idempotent.
                rewrite Hthread_mem2; exact (cur_lt_max _).
                
              + rewrite RPM.
                eapply cur_equiv_restr_mem_equiv.
                eassumption.
            - clear - val_inj Hinj_b.
              inversion val_inj; subst.
              inversion H3; f_equal.
              inversion H1; subst.
              rewrite Hinj_b in H4; inversion H4; subst.
              reflexivity. }
          
        + !goal(Mem.range_perm _ _ _ _ _ _).
          
          unshelve erewrite <- restrPermMap_idempotent_eq.
          { eapply Hcmpt2. }
          match goal with |- Mem.range_perm ?m _ ?ofs2 _ _ _ =>
                          replace m with lk_mem2;
                            replace ofs2 with (unsigned ofs + delt)
          end.
          replace (unsigned ofs + delt + LKSIZE)
            with (unsigned ofs + LKSIZE + delt) by omega.
          eapply Mem.range_perm_inj; eauto; eapply Hinj_lock.
          subst lk_mem2; simpl; repeat f_equal.
          eapply Axioms.proof_irr.
          

        + !context_goal Mem.load.
          unshelve erewrite <- restrPermMap_idempotent_eq.
          eapply Hcmpt2.
          eapply Mem.load_inject in Hload; eauto.
          destruct Hload as (?&Hload2&Hinj_v).
          inv Hinj_v.
          replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
          eassumption.
    Qed.  (* acquire_fail_step_diagram_self *)
    

    (** *Compiled diagrams*)

    (*TODO: 
              1. Find a better name
              2. Simplify / Clean it?        
     *)

    Lemma lock_doesnt_return:
      doesnt_return LOCK.
    Proof.
      intros ? * Hext_call.
      unfold Events.external_call in Hext_call.
      rewrite AcquireExists in Hext_call.
      inversion Hext_call; reflexivity.
    Qed.


    
    
    (* Large diagram:
         Diagram of steps over external calls. Called "Large"
         because in a thread-local view, it steps all interactions in one step. 
     *)
    Lemma large_external_diagram:
      forall cd f mu j'' code1 code2 cge age args1 rel_trace m1 m1'''
             args2 rel_trace2 FUN
             m2 m2' m2'' m2''' lev1 lev1' lev2 lev2' s1'
             p Hlt dpm1 dpm2 name signature
             (Hfun: FUN = AST.EF_external name signature)
             (Hconsec: consecutive_sem name signature)
             (Hun_dsnt_ret: doesnt_return FUN)
             (Hun_dsnt_ret_sig: AST.sig_res signature = None)
             (Hinj_delts: EventsAux.inject_delta_map mu dpm1 dpm2)
             (Heqrel_trace1 : rel_trace = Events.Event_acq_rel lev1 dpm1 lev1' :: nil)
             (Heqrel_trace : rel_trace2 = Events.Event_acq_rel lev2 dpm2 lev2' :: nil)
             (HAge: age =  (Genv.globalenv Asm_program))
             (HCge: cge = (Clight.globalenv C_program) )
             (Hext_rel1 : Events.external_call
                            FUN (Clight.genv_genv cge) 
                            args1 m1 rel_trace Vundef m1''')
             (Hext_rel2 : Events.external_call
                            FUN age 
                            args2 m2 rel_trace2 Vundef m2''')
             (Hnb_eq : Mem.nextblock m2'' = Mem.nextblock m2')
             (Hstrict_evolution : strict_injection_evolution f mu lev1 lev2)
             (Hstrict_evolution' : strict_injection_evolution mu j'' lev1' lev2')
             (Hafter_ext : Clight.after_external None code1 m1''' = Some s1')
             (Hmatch_states : compiler_match cd f code1 m1 code2 m2)
             (Hat_external1 : Clight.at_external (Clight.set_mem code1 m1) =
                              Some (FUN, args1))
             (Hat_external2 : Asm.at_external Asm_g (Asm.set_mem code2 m2) =
                              Some (FUN, args2))
             (Hinterference2' : mem_interference (@restrPermMap p m2'' Hlt) lev2' m2''')
             (Hconsecutive : consecutive_until (Mem.nextblock m2) lev2 (Mem.nextblock m2'))
             (Hconsecutive' : consecutive_until (Mem.nextblock m2'') lev2' (Mem.nextblock m2''')),
      exists (cd' : compiler_index) (j''' : meminj) (s2' : Asm.state),
        Asm.after_external Asm_g None code2 m2''' = Some s2' /\
        inject_incr mu j''' /\ compiler_match cd' j''' s1' m1''' s2' m2'''.
    Proof.
      intros; subst FUN.
      
      (* remove this comment *)
      (** *1. Prove that this is a CompCert step (en external step).
       *)
      exploit C_large_step_as_compcert_step; eauto.
      replace Values.Vundef with Vundef; eauto; simpl.
      intros Hstep.
      
      
      (** *2. Apply the simulation
                To construct the step in Asm
       *)
      subst cge;
        eapply (Injsim_simulation_atxX compiler_sim) in Hstep; eauto.
      specialize (Hstep _ _ _ Hmatch_states).
      destruct Hstep as (j2'&Hincr&Hstep_str&Hstep).
      clear Hat_external1 Hafter_ext.

      (* Notice that memories before and after stroe have same next_block*)
      
      (** *3. Following steps we prove each of the things we need. *)

      move Hstep_str at bottom.
      destruct Hstep_str as
          (i2_str & s2_str & t_str &
           Hstep_str & Hmatch_str & Hinj_trace_str).
      
      assert (Hincr_j'': inject_incr j'' j2').
      { (*
                    ( ) ---- lev1 + lev1' ---> ( )
                     |                          |  \
                     f     regular diagram      j'' \
                     |                          |    \
                    ( ) ---- lev2 + lev2' ---> ( )    \
                      \                                \
                      =eq=  strong/principled diagram  j2'
                        \                                \
                        ( )---- lev2_str + lev2_str --->( )
         *)
        eapply principled_diagram_correct'.
        - (** *Full strong diagram *)
          rewrite Hnb_eq in Hconsecutive'.
          eapply principled_diagram_exists'.
          + exploit (strict_inj_evolution_cat f mu j''); eauto.
          + exploit (consecutive_until_cat lev2 lev2');
              try eassumption.
            eapply consecutive_until_consecutive.
        - subst rel_trace.
          inv Hinj_trace_str. clear H3; inv H1.
          do 2 econstructor; auto. 
          + eapply list_inject_mem_effect_cat; 
              eapply list_inject_weaken;
              eassumption.
          + unfold Asm.at_external in Hat_external2.
            repeat match_case in Hat_external2.
            inv Hstep_str.
            * (*Can't be a builtin, it's at_ext*) exfalso.
              inv H.
              rewrite Heqs in H9; inv H9.
              rewrite Heqv in H0; inv H0.
              unfold Asm_g,the_ge in *.
              rewrite Heqo in H1. congruence.
            * simpl in *.
              rewrite Heqs in H; inv H.
              rewrite Heqv in H0; inv H0.
              unfold Asm_g,the_ge in *.
              rewrite Heqo in H1. inv H1.
              inv Hat_external2.
              replace m2 with m.
              2:{ destruct code2; inv Heqs; auto. }
              eapply Hconsec; try reflexivity; eauto.
      }

      
      assert (Hincr_mu : inject_incr mu j2').
      { eapply inject_incr_trans.
        eapply (evolution_inject_incr).
        all: eassumption. }

      assert (Hinj_trace: Events.inject_trace j2' rel_trace rel_trace2).
      { subst rel_trace rel_trace2.
        econstructor; try solve[constructor].
        econstructor.
        - emonotonicity; eauto.
          emonotonicity; eauto.
          eapply evolution_list_inject_mem; eauto.
        - emonotonicity; eauto.
        - emonotonicity; try apply Hincr_j''.
          eapply evolution_list_inject_mem in Hstrict_evolution'; assumption.
      }
      clear Hstrict_evolution'.

      subst rel_trace.
      destruct  (Hstep _ Hinj_trace)
        as (cd' & s2' & step & comp_match).

      (* Assert the after_external we know:
               Given from 
               Hat_external2: Asm.at_externalge (c2, m2) = Blah
               step: (c2, m2) --> s2' *)
      exploit asm_after_external_when_external_step;
        subst rel_trace2; simpl in *; eauto; try reflexivity.
      intros Hafter_x.

      (* Now change the mem to the one we need *)
      replace (Asm.get_mem s2') with m2''' in Hafter_x.
      2:{ !goal (m2''' = _).
          clear - Hun_dsnt_ret_sig HAge hb step Hat_external2 Hafter_x Hext_rel2.
          replace m2''' with (Asm.get_mem (Asm.set_mem s2' m2'''))
            by (destruct s2'; auto); f_equal. 
          eapply asm_step_determ; try eassumption.
          eapply thread_step_from_external; simpl; eauto.
          - simpl; eauto.
          - subst age; eauto.  }
      
      do 3 eexists; repeat (split; eauto).
      unfold compiler_match; simpl.
      eapply after_x_mem in Hafter_x.
      rewrite <- Hafter_x, asm_set_mem_get_mem.
      eassumption.
    Qed.
    Ltac unify_at_ext:=
      repeat match goal with
               [H: semantics.at_external _ _ _ = Some _ |- _] =>
               simpl in H
             end;
      match goal with
        [H1: Clight.at_external ?X = _,
             H2: Clight.at_external ?X = _ |- _] =>
        rewrite H1 in H2; invert H2
      end.
    Ltac inj_args_inv:=
      match goal with
        [Hinj_args: Val.inject_list ?f (Vptr ?b1 ?ofs :: nil) _  |- _ ]=>
        invert Hinj_args;
        match goal with
        | [ Hinj_ptr: Val.inject _ (Vptr b1 ofs) _,
                      Hinj_nil: Val.inject_list _ nil _ |- _ ] =>
          invert Hinj_ptr; invert Hinj_nil;
          match goal with
          | [Hinj_b_badname: f b1 = Some _ |- _ ] =>
            let Hinj_b:= fresh "Hinj_b" in rename Hinj_b_badname into Hinj_b;
                                           try (let Hinj_b':= fresh "Hinj_b'" in
                                                eapply evolution_inject_incr in Hinj_b as Hinj_b';
                                                eauto; [idtac] (*check only one goal left.*) )
          end
        end
      end.
    Ltac inject_lock_update_mem_strict_load:=
      lazymatch goal with
        [CMatch: concur_match _ ?mu ?st1 ?m1' ?st2 ?m2',
                 Hlock: lock_update_mem_strict_load _ _ _ _ _ _ _ |- _ ] =>
        let Hlock_update_mem_strict_load1:= fresh "Hlock_update_mem_strict_load1" in
        dup Hlock as Hlock_update_mem_strict_load1;
        let m2'':=fresh "m2''" in 
        let Hlock_update_mem_strict_load2:=fresh "Hlock_update_mem_strict_load2" in 
        let Hinj2:=fresh "Hinj2" in 
        eapply lock_update_mem_strict_load_inject in Hlock
          as (m2''&Hlock_update_mem_strict_load2&Hinj2);
        eauto; try (eapply CMatch; eauto); [idtac]
      end.
    Ltac get_injection_thread_mem:=
      match goal with
        [CMatch: concur_match _ ?mu ?st1 ?m1' ?st2 ?m2' |- _ ] =>
        let Hinj':= fresh "Hinj'" in
        assert (Hinj': Mem.inject mu m1' m2') by
            (rewrite <- (cur_equiv_restr_mem_equiv m1') by eassumption;
             rewrite <- (cur_equiv_restr_mem_equiv m2') by eassumption;
             eapply INJ_threads; eauto)
      end.
    Ltac use_retroactive_int_diagram_atx:=
      match goal with
        [Hstrict: strict_evolution_diagram _ _ _ _ _ _ _  |- _] =>
        eapply retroactive_int_diagram_atx in Hstrict;
        eauto; [idtac]; (* This checks there is only one goal left! *)
        inversion Hstrict; unify_at_ext      
      end.
    
    Ltac inject_lock_update_mem_strict:=
      lazymatch goal with
        [CMatch: concur_match _ ?mu ?st1 ?m1' ?st2 ?m2',
                 Hlock: lock_update_mem_strict _ _ _ _ _ |- _ ] =>
        let Hlock_update_mem_strict1:= fresh "Hlock_update_mem_strict1" in
        dup Hlock as Hlock_update_mem_strict1;
        let m2'':=fresh "m2''" in 
        let Hlock_update_mem_strict2:=fresh "Hlock_update_mem_strict2" in 
        let Hinj2:=fresh "Hinj2" in 
        eapply lock_update_mem_strict_inject in Hlock
          as (m2''&Hlock_update_mem_strict2&Hinj2);
        eauto; try (eapply CMatch; eauto); [ ]
      end.
    Ltac left_diagram:=
      (* 1. Set up the injection*)
      get_injection_thread_mem;
      (* 2. Now we expand the diagram backwards *)
      use_retroactive_int_diagram_atx;
      inj_args_inv;
      (* There are different types of left diagram.
`            each case is a different type. *)
      first 
        [inject_lock_update_mem_strict_load
        | inject_lock_update_mem_strict].
    


    
    
    (*
        Definition pos_descend p: positive:=
        match p with
        | xI p' => p'
        | xO p' => p'
        | xH => xH
        end.
      Definition pos_descend_rev p:=
        PTree.prev (pos_descend (PTree.prev p)).
      
      Definition pos_ascend p b: positive:=
        match p with
        | xI p' => (xI b)
        | xO p' => (xO b)
        | xH => b
        end. *)


    
    
    
    (*  Lemma computeMap_get:
                  forall a1 b1 b ofs,
                    (computeMap a1 b1) !! b ofs  =
                    match dmap_get b1 b ofs with
                      Some x => x | _ => a1 !! b ofs
                    end.
                Proof.
                  intros.
                  match_case; unfold computeMap, "!!"; simpl.
                  - rewrite PTree.gcombine; auto.
                    unfold dmap_get in *.
                    match_case; simpl in *.
                    + unfold "!!" in *; simpl in *.
                      match_case in Heqo.
                      match_case in Heqo0;
                        inv Heqo0; rewrite Heqo; reflexivity.
                    + unfold "!!" in *; simpl in *.
                      match_case in Heqo.
                      match_case in Heqo0;
                        inv Heqo0; rewrite Heqo; reflexivity.
                  - rewrite PTree.gcombine; auto.
                    unfold dmap_get in *.
                    match_case; simpl in *.
                    + unfold "!!" in *; simpl in *;
                        match_case in Heqo; match_case.
                      * inv Heqo0; match_case.
                      * inv Heqo0; match_case.
                    +   unfold "!!" in *; simpl in *;
                          match_case in Heqo; match_case.
                Qed. *)
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
          Set Printing Implicit.
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
    Qed.
    
    
    Lemma lock_update_mem_strict_load_mem_update_restr:
      forall (b : block) (ofs : Z) (p : access_map) (m m' : mem) (vload vstore : val),
        lock_update_mem_strict_load b ofs p m m' vload vstore ->
        forall (Hlt: @permMapLt (getCurPerm m) (getMaxPerm m')),  
          lock_update_mem m (b, ofs) (encode_val AST.Mint32 vstore) (restrPermMap Hlt).
    Proof.
      intros.
      unshelve eapply lock_update_mem_restr'; swap 5 1; swap 6 2.
      eapply lock_update_mem_strict_load_mem_update.
      * eapply lock_update_mem_strict_load_restr.
        erewrite <- restrPermMap_idempotent_eq.
        erewrite <- (mem_is_restr_eq).
        eapply H.
      * red. eapply getCur_restr.
      * symmetry; eapply getCur_restr.
      * rewrite getCur_restr.
        eapply lock_update_mem_strict_load_Max_equiv in H.
        unfold Max_equiv in *.
        rewrite H.
        apply mem_cur_lt_max.
      * rewrite getMax_restr.
        apply mem_cur_lt_max.
    Qed.
    Lemma INJ_lock_content':
      forall hb ocd j cstate1 m1 cstate2 m2,
        MyConcurMatch.concur_match hb ocd j cstate1 m1 cstate2 m2 ->
        forall (b : block) (ofs : Z) (rmap : lock_info),
          lockRes cstate1 (b, ofs) = Some rmap ->
          mi_memval_perm j
                         (fst rmap) (*LOCKED DATA*)
                         (Mem.mem_contents m1)
                         (Mem.mem_contents m2).
    Proof.
      intros. 
      (* Seems like I need to add this to the concur_match*)
    Admitted.
    Lemma INJ_lock_content'':
      forall hb ocd j cstate1 m1 cstate2 m2,
        MyConcurMatch.concur_match hb ocd j cstate1 m1 cstate2 m2 ->
        forall (b : block) (ofs : Z) (rmap : lock_info),
          lockRes cstate1 (b, ofs) = Some rmap ->
          mi_memval_perm j
                         (snd rmap)
                         (Mem.mem_contents m1)
                         (Mem.mem_contents m2).
    Proof.
      (* Seems like I need to add this to the concur_match*)
    Admitted.
    
    Lemma lockSet_is_not_readable:
      forall hb ocd j cstate1 m1 cstate2 m2,
        MyConcurMatch.concur_match hb ocd j cstate1 m1 cstate2 m2 ->
        forall b (ofs : Z) (rec : lock_info),
          lockRes cstate1 (b, ofs) = Some rec ->
          (forall i (cnt:containsThread cstate1 i),
              forall ofs0, ofs <= ofs0 < ofs + LKSIZE -> 
              ((thread_perms i cstate1 cnt) !! b ofs0) = Some Nonempty) /\
          (forall b' ofs' rec',
              lockRes cstate1 (b', ofs') = Some rec' ->
              forall ofs0, ofs <= ofs0 < ofs + LKSIZE ->
              ((fst rec') !! b ofs0)  = Some Nonempty ).
    Proof.
      (*This has to be added to concur_match*)
    Admitted.

    
    Lemma writable_is_not_lock:
      forall hb ocd j cstate1 m1 cstate2 m2,
        MyConcurMatch.concur_match hb ocd j cstate1 m1 cstate2 m2 ->
        forall b ofs i (cnt:containsThread cstate1 i),
          Mem.perm_order' ((thread_perms i cstate1 cnt) !! b ofs) Readable ->
          lockRes cstate1 (b, ofs) = None.
    Proof.
      intros. destruct_lhs; eauto.
      eapply lockSet_is_not_readable in Heqo as (?&?); eauto.
      rewrite H1 in H0; eauto. inv H0.
      pose proof LKSIZE_pos; omega.
    Qed.
    Lemma invariant_update_join_acq:
      forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
        h laddr c lock_perm th_perm
        (Hcnt:ThreadPool.containsThread st h),
        ThreadPool.lockRes st laddr = Some lock_perm ->
        st' =
        ThreadPool.updLockSet (ThreadPool.updThread Hcnt c th_perm) laddr
                              (empty_map, empty_map) ->
        invariant st ->
        permMapJoin_pair lock_perm (getThreadR Hcnt) th_perm ->
        invariant st'.
    Proof.
      intros * ? ? Hinv Hjoin; eapply invariant_update; eauto.
      - intros.
    (* This is wrong: 
           IF Nonempty + Writable = Freeable
           we know: 
              disjoin Nonempty Nonempty    
              disjoin Writable Nonempty
           but it's not true that:
              disjoin Freeable Nonempty *)
           (** * SOLUTION add the invariant of st1'
               to the lemmas statement.     
               with  an extra safety step, we know the second 
           state satisfies the invariant.
     *)
    Admitted.
    
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
                                (SyncCallsDiagrams.lock_perms hb st1 Hcnt1)
                                (getCurPerm lk_mem1)).
                   { subst lk_mem1; unfold SyncCallsDiagrams.lock_perms.
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

          
          
    Qed.          

    (* HERE!! *)
    
    Lemma invariant_makelock:
      forall (hb1 hb2:nat) c st1 b1 ofs cnt perms,
        @invariant _ (TP (Some hb2)) st1 ->
        set_new_mems b1 ofs (@getThreadR _ _ hb1 st1 cnt) LKSIZE_nat perms ->
        (forall ofs0 : Z, ofs <= ofs0 < ofs + LKSIZE ->
                     Mem.perm_order' ((thread_perms hb1 st1 cnt) !! b1 ofs0) Writable) ->
        @invariant _ (TP (Some hb2)) (@updThread _ (HybridSem (Some hb2))
                                                 hb1 st1 cnt c perms).
    Proof.
      (* CHECKED: EASY*)
    (* Before solving, solve the lemma invariant preservation for acquire
       ** *we are adding [invariant st1'] to the lemmas, preserved from the CSL proof*
         We might want to remove the necessity to preserve invariant for source.
     *)
      (* Consider moving this where the invariant lemmas are. *)
    Admitted.

    


    

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
        (*HybridMachineSig.external_step
          (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
          U tr2 st2 m2' (HybridMachineSig.schedSkip U)
          (tr2 ++ (Events.external hb evnt2 :: nil)) st2' m2'' /\*)
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
              eapply lockSet_is_not_readable in H4 as [HH' _];eauto.
               exploit HH'. instantiate(1:= (unsigned ofs + delta) - x2).
               rewrite Hunsign in *.
               subst; clear - H2 H. try omega. intros <-.
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
               
               eapply lockSet_is_not_readable in H4 as [H4 _]; eauto.
               exploit H4. instantiate(1:=unsigned ofs); omega.

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
            - 
              eapply mklock_doesnt_return.
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
        + !context_goal (@lock_update (@Some nat hb)).
          subst st1'. econstructor.
          destruct new_perms1; eauto.
        + !context_goal (@lock_update (@Some nat (S hb))).
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
    (*HERE HERE*)
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
                    _ _ (th_comp _ thread_compat1) Hthread_mem1) as
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
        
        (edestruct (release_step_diagram_self AsmSem)
                                              with (tid:=tid) as
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

        
        (edestruct (release_step_diagram_self CSem)
                   with (tid:=tid)
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

        (edestruct (acquire_step_diagram_self AsmSem) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step);
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        +  eassumption.
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
          split ; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (fullThUpd_comp _ _ _ _ _ _ ) _ _ _).
            admit. (* Haven't proven this? *)
          * clear - Htrace_inj. 
            unfold build_release_event in *. (*subst virtueThread0; *) eauto.
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
          * !goal(mem_interference m1 lev1 m1'). admit.   
          * !goal(mem_interference m2 lev2 m2'). admit.
        + subst virtueThread1.
          clear. 
          intros (?&?&?&?&?&?).
          do 3 eexists; repeat weak_split eauto.
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
        
        (edestruct (acquire_step_diagram_self CSem) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step);
         first[ eassumption|
                econstructor; eassumption|
                solve[econstructor; eauto] |
                eauto]).
        + eassumption.
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply H3.
          * simpl.
            move matchmem at bottom.
            admit. (* match_mem proper with mem_equiv*)
        (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
        + exists e'. eexists. exists m2'.
          split ; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (fullThUpd_comp _ _ _ _ _ _ ) _ _ _).
            admit.
          * clear - Htrace_inj. 
            unfold build_release_event in *. (*subst virtueThread0; *) eauto.
          (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
          * clean_proofs; eauto.
            
            
    Admitted. (* acquire_step_diagram *)

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
      pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp _ thread_compat1) Hthread_mem1) as
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
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

        (edestruct (make_step_diagram_self AsmSem) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl.
            move matchmem at bottom.
            admit. (* match_mem proper with mem_equiv*)
        (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
        + exists e'. eexists. exists m2'.
          split ; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (fullThreadUpdate _ _ _ _ _ _ ) _ _ _).
            admit.
          * clear - Htrace_inj. 
            unfold build_release_event in *. (*subst virtueThread0; *) eauto.
          (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
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
        
        rename H8 into Hinterference1.
        rename H6 into Hinterference2.
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
          * !goal(mem_interference m1 lev1 m1'). admit.   
          * !goal(mem_interference m2 lev2 m2'). admit.
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
        destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

        (edestruct (make_step_diagram_self CSem) as
            (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl.
            move matchmem at bottom.
            admit. (* match_mem proper with mem_equiv*)
        (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
        + exists e'. eexists. exists m2'.
          split ; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (fullThreadUpdate _ _ _ _ _ _ ) _ _ _).
            admit.
          * clear - Htrace_inj. 
            unfold build_release_event in *. (*subst virtueThread0; *) eauto.
          (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
          * clean_proofs; eauto.
            
    Admitted. (* make_step_diagram*)

    Lemma free_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (m1 m1' m1'': mem) (cd : compiler_index) mu pdata
             (st1 : ThreadPool (Some hb))  new_perms1
             (st2 : ThreadPool (Some (S hb))) (m2' : mem) Hcnt1 Hcnt2
             (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
             b1 ofs (code1 : semC)  (code2 : Asm.state) lock_data
             (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
             (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
             (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
             (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
             (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
             (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
             (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                              Some (FREE_LOCK, (Vptr b1 ofs :: nil)%list))
             (Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1' m1'' vzero)
             (Hlock_map: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = Some lock_data)
             (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
             (HlocksLt: permMapLt (lock_perms _ _ Hcnt1) (getMaxPerm m1') )
             (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                         b1 (unsigned ofs) LKSIZE Cur Writable)
             (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                            Mem.perm_order'' (pdata (S i)) (Some Writable))
             (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        let new_perms2:=
            setPermBlock_var_pair b1 (unsigned ofs) LKSIZE_nat
                                  (pdata, fun _:nat => None) (getThreadR Hcnt1) in
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
    Admitted.
    (*

        unify_injection. rename b0 into b2.
        set (ofs2:= add ofs (repr delta)).
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
        
        (** * 4. Finally we proceed with the goal: existentials. *)

        set (evnt2:= (Events.mklock (b2, unsigned ofs2))).
        
        exists evnt2, st2', m2''.
        split; [|split].
        - eapply concur_match_update_lock; eauto; try solve[subst st1'; eauto].
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
              admit.
            * !goal (mi_memval_perm mu _ _ _).
              admit.
            * !goal (mi_perm_inv_perm mu _ _ _).
              admit.
          + !goal (@invariant (HybridSem _) _ _). admit.
          + !goal (invariant st2'). admit.
          + !goal(perm_surj mu _ _).
            instantiate(1:=snd new_perms2); instantiate(1:=snd new_perms1).
            simpl in *. admit.
          + !goal (Mem.inject mu _ _).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (snd new_perms1) (snd new_perms2)).
              admit.
            * !goal (mi_memval_perm mu (snd new_perms1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (snd new_perms1) (snd new_perms2) m1'').
              admit.
          +  (* Proof of match goes after the comment *)
            { !context_goal one_thread_match.
              eapply build_match_compiled; auto.
              admit.
            }
          + constructor; constructor.
          + simpl in *. econstructor.
            subst st1'; destruct new_perms1; reflexivity.
          + simpl in *. econstructor.
            subst st2' ofs2; destruct new_perms2. repeat f_equal.
            !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta).
            admit.
            !goal (pair0 empty_map = virtueLP_inject _ _ (pair0 empty_map)).
            admit.

        - subst evnt2. replace (unsigned ofs2) with (unsigned ofs + delta).
          repeat econstructor; eassumption.
          admit.
        - split; [admit|].

          assert (Hofs2: intval ofs2 = unsigned ofs + delta).
          { admit. }
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
            rewrite Hofs2.
            eapply range_perm_mem_equiv_Cur; try apply eq_refl; eauto.
            * eapply Cur_equiv_restr; reflexivity.
            * eapply permMapLt_range_mem.
              admit. (*by injecting from above*)
              
          + (* the store *)
            inversion Hlock_update_mem_strict2; subst vstore.
            rewrite (mem_is_restr_eq m2') in Hstore.
            erewrite restrPermMap_equiv_eq; eauto.
          + simpl; inv HH0; auto.
          + simpl; inv HH0; auto.
          + !goal (lockRes _ (b2,_) = None).
            eapply INJ_lock_permissions_None; eauto.

        
      Admitted.*) (* free_step_diagram_compiled *)
    
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
                    _ _ (th_comp _ thread_compat1) Hthread_mem1) as
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
            (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl.
            move matchmem at bottom.
            admit. (* match_mem proper with mem_equiv*)
        + exists e'; eexists; exists m2'.
          split; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (remLockfFullUpdate _ _ _ _ _ _ ) _ _ _).
            admit.
          * clear - Htrace_inj; auto.
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
        + admit.
        + !goal (strict_evolution_diagram _ _ _ _ _ _ _).
          econstructor; eauto.
          admit. (* There is some problem here with equivalences *)
          admit. (* There is some problem here with equivalences *)
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
            (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
          first[ eassumption|
                 econstructor; eassumption|
                 solve[econstructor; eauto] |
                 eauto].
        + clean_proofs; eassumption.
        + (*match_self*)
          econstructor.
          * eapply cinject.
          * simpl.
            move matchmem at bottom.
            admit. (* match_mem proper with mem_equiv*)
        + exists e'; eexists; exists m2'.
          split; [|split].
          * (* reestablish concur *)
            rename b into BB.
            !goal (concur_match _ _ (remLockfFullUpdate _ _ _ _ _ _ ) _ _ _).
            admit.
          * clear - Htrace_inj; auto.
          * clean_proofs; eauto.
            
    Admitted.


    (*TODO move to Mem_equiv*)
    
    Lemma acquire_fail_step_diagram_compiled:
      let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
      forall (m1 m1' m1'' : mem) (cd : compiler_index)
             mu st1 st2 (m2' : mem) Hcnt1 Hcnt2
             (Hsame_sch: same_cnt hb st1 st2 Hcnt1 Hcnt2)
             b1 ofs (code1 : semC)  (code2 : Asm.state)
             (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
             (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
             (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
             (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
             (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
             (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                              Some (LOCK, (Vptr b1 ofs :: nil)%list))
             (Hlock_lt: permMapLt (lock_perms _ _ Hcnt1) (getMaxPerm m1')),
        let m1_locks:= restrPermMap Hlock_lt in
        forall (Hload: Mem.load AST.Mint32 m1_locks b1 (unsigned ofs) = Some vzero)
               (Hrange_perm: perm_interval m1_locks b1 (unsigned ofs) LKSIZE Cur Readable)
               (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        exists evnt2,
        forall m2_any (Hcmpt2: mem_compatible st2 m2_any),
          let evnt:= (Events.failacq (b1, unsigned ofs)) in
          concur_match (Some cd) mu st1 m1'' st2 m2_any /\
          inject_sync_event mu evnt evnt2 /\
          forall (Hcmpt2: mem_compatible st2 m2_any),  
            syncStep(Sem:=HybridSem (Some (S hb)))
                    true Hcnt2 Hcmpt2 st2 m2_any evnt2.
    (*
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2_any (HybridMachineSig.schedSkip U)
              (tr2 ++ (Events.external hb evnt2 :: nil)) st2 m2_any.*)
    Proof.
      (* TODO SUNDAY: *)
    Admitted.
    




    


    
    Lemma acquire_fail_step_diagram:
      let hybrid_sem:= (sem_coresem (HybridSem(Some hb))) in 
      forall (m1 m2: mem) tid mu cd b ofs c
             (st1 : ThreadPool (Some hb)) cnt1
             (st2 : ThreadPool (Some (S hb))) cnt2
             (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
             (CMatch: concur_match cd mu st1 m1 st2 m2)
             (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
             (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
             (Hat_external: semantics.at_external hybrid_sem c m1  =
                            Some (LOCK, (Vptr b ofs :: nil)%list))
             (Hlock_lt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1)),
        let m1_locks:= restrPermMap Hlock_lt in
        forall (Hload: Mem.load AST.Mint32 m1_locks b (unsigned ofs) = Some vzero)
               (Hrange_perm: perm_interval m1_locks b (unsigned ofs) LKSIZE Cur Readable)
               (Hcode: getThreadC cnt1 = Kblocked c),
        forall perm Hlt_perm,
          let any_mem:= @restrPermMap perm m2 Hlt_perm in
          exists evnt2,
            concur_match cd mu st1 m1 st2 any_mem /\
            let evnt:= (Events.failacq (b, unsigned ofs)) in
            inject_sync_event mu evnt evnt2 /\
            forall (Hcmpt2: mem_compatible st2 any_mem),  
              syncStep(Sem:=HybridSem (Some (S hb)))
                      true cnt2 Hcmpt2 st2 any_mem evnt2.
    (* HybridMachineSig.external_step
                (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                U tr2 st2 any_mem (HybridMachineSig.schedSkip U)
                (seq.cat tr2 (Events.external tid evnt' :: nil)) st2 any_mem. *)
    Proof.
      intros; simpl in *.
      inv Hsame_sch.
      pose proof (memcompat1 CMatch) as Hcmpt1.
      get_mem_compatible.
      get_thread_mems.
      pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp _ thread_compat1) Hthread_mem1) as
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

        assert (Hth_lt1: permMapLt (thread_perms tid st1 cnt1) (getMaxPerm m1))
          by eapply CMatch.
        assert (Hth_lt2: permMapLt (thread_perms tid st2 cnt2) (getMaxPerm m2))
          by eapply CMatch.
        remember (restrPermMap Hth_lt1) as m1_thread.
        remember (restrPermMap Hth_lt2) as m2_thread.
        
        unshelve (edestruct (acquire_fail_step_diagram_self
                               AsmSem m1_thread m2_thread) as
                     (e' & Htrace_inj & external_step);
                  eauto; try eapply Hlock_lt;
                  first[ eassumption|
                         econstructor; eassumption|
                         solve[econstructor; eauto] |
                         eauto]); subst m1_thread m2_thread.
        1,2,3: shelve.
        + rewrite getMax_restr; assumption.
        + eapply concur_match_perm_restrict; eassumption.
        + rewrite getCur_restr; reflexivity.
        + rewrite getCur_restr; clean_proofs; reflexivity.
        + (* match_self*)
          inv H3; econstructor; eauto.
          clean_proofs; assumption.
        + simpl. !goal(Asm.at_external _ _ = _).
          instantiate(1:=ofs).
          pose proof (Asm_at_external_proper
                        Asm_g code1 _ eq_refl
                        (restrPermMap Hth_lt1) m1).
          unfold Asm_g in *. simpl in H; rewrite H; eauto.
          eapply cur_equiv_restr_mem_equiv; assumption.
        + rewrite <- restrPermMap_idempotent; eauto.
        + unfold perm_interval.
          rewrite <- restrPermMap_idempotent; eauto.
        + eexists.
          repeat (weak_split eauto).
          * rewrite (mem_is_restr_eq m1); subst any_mem.
            eapply concur_match_perm_restrict; eauto.
          * simpl in external_step.
            clean_proofs. simpl. subst any_mem.

            specialize (external_step perm ).
            unshelve (exploit external_step); intros.
            -- do 2 apply mem_compat_restrPermMap.
               eapply CMatch.
            -- rewrite getMax_restr. assumption.
            -- revert H; clear. clean_proofs.
               pose proof (restrPermMap_idempotent_eq _ Hlt_perm abs_proof0) as Heq.
               dependent_rewrite Heq.
               clean_proofs; auto.


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
        (*rename Hlt' into Hlt_setbBlock1. *)
        rename Hat_external into Hat_external1.
        rename b into b1.
        rename Hload into Hload1.
        
        symmetry in H0; clean_proofs.
        exploit (acquire_fail_step_diagram_compiled m1 m1' m2') ;
          try eapply CMatch; eauto;
            try reflexivity.
        + econstructor; eassumption.
        + econstructor; debug eauto.
          * !goal(mem_interference m1 lev1 m1'). admit.   
          * !goal(mem_interference m2 lev2 m2'). admit.
        + clear - CMatch Hcnt1.
          intros (?&?&?&?).
          { apply mem_compat_restrPermMap; apply CMatch. }

          eexists; eauto.
          repeat weak_split eauto.
          * rewrite (mem_is_restr_eq m1'); subst any_mem.
            eapply concur_match_perm_restrict; eauto.
            
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

        assert (Hth_lt1: permMapLt (thread_perms tid st1 cnt1) (getMaxPerm m1))
          by eapply CMatch.
        assert (Hth_lt2: permMapLt (thread_perms tid st2 cnt2) (getMaxPerm m2))
          by eapply CMatch.
        remember (restrPermMap Hth_lt1) as m1_thread.
        remember (restrPermMap Hth_lt2) as m2_thread.
        
        unshelve (edestruct (acquire_fail_step_diagram_self
                               CSem m1_thread m2_thread) as
                     (e' & Htrace_inj & external_step);
                  eauto; try eapply Hlock_lt;
                  first[ eassumption|
                         econstructor; eassumption|
                         solve[econstructor; eauto] |
                         eauto]); subst m1_thread m2_thread.
        1,2,3: shelve.
        + rewrite getMax_restr; assumption.
        + eapply concur_match_perm_restrict; eassumption.
        + rewrite getCur_restr; reflexivity.
        + rewrite getCur_restr; clean_proofs; reflexivity.
        + (* match_self*)
          inv H3; econstructor; eauto.
          clean_proofs; assumption.
          
        + simpl. !goal(Clight.at_external _ = _).
          instantiate(1:=ofs).
          pose proof (C_at_external_proper
                        Clight_g code1 _ eq_refl
                        (restrPermMap Hth_lt1) m1).
          unfold Clight_g in *. simpl in H; rewrite H; eauto.
          eapply cur_equiv_restr_mem_equiv; assumption.
        + rewrite <- restrPermMap_idempotent; eauto.
        + unfold perm_interval.
          rewrite <- restrPermMap_idempotent; eauto.
        + eexists.
          repeat (weak_split eauto).
          * rewrite (mem_is_restr_eq m1); subst any_mem.
            eapply concur_match_perm_restrict; eauto.
          * simpl in external_step.
            clean_proofs. simpl. subst any_mem.

            specialize (external_step perm ).
            unshelve (exploit external_step); intros.
            -- do 2 apply mem_compat_restrPermMap.
               eapply CMatch.
            -- rewrite getMax_restr. assumption.
            -- revert H; clear. clean_proofs.
               pose proof (restrPermMap_idempotent_eq _ Hlt_perm abs_proof0) as Heq.
               dependent_rewrite Heq.
               clean_proofs; auto.
               
               Unshelve.
               eapply CMatch.
               eapply CMatch. 
               
    Admitted.
    
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
      rewrite H0; reflexivity.
    Qed.
    

    
    Lemma external_step_diagram:
      forall (U : list nat)
             (tr1 tr2 : HybridMachineSig.event_trace)
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
        unshelve edestruct (acquire_step_diagram angel' m1 m1') as
            (?&?&?&?&?&?); subst angel'; simpl in *; eauto;
          try rewrite (restr_proof_irr _ (proj1 (Hcmpt tid cnt1))).
        + !goal(concur_match _ _ _ _ _ _).
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
        
        unshelve edestruct (release_step_diagram angel' m1 m1') as
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
        
        unshelve edestruct (make_step_diagram m1 m1' m2) as (?&?&?&?&?&?);
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

        unshelve edestruct (free_step_diagram m1 m2)
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
        
        unshelve edestruct (acquire_fail_step_diagram m1_restr m2_restr) as (?&?&?&?);
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
