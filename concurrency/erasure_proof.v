Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.dry_machine. Import Concur.
(*Require Import concurrency.dry_machine_lemmas. *)
Require Import concurrency.lksize.
Require Import concurrency.permissions.
Require Import concurrency.sync_preds.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import concurrency.ssromega. (*omega in ssrnat *)

(*The simulations*)
Require Import sepcomp.wholeprog_simulations.

(*The semantics*)
Require Import concurrency.JuicyMachineModule.
Require Import concurrency.DryMachineSource.

(*General erasure*)
Require Import concurrency.erasure_signature.

From mathcomp.ssreflect Require Import ssreflect seq.

Import addressFiniteMap.

(* I will import this from CLight once we port it*)
(*Module ClightSEM<: Semantics.
  Definition G:= nat.
  Definition C:= nat.
  Definition M:= Mem.mem.
  Definition  
End ClightSEM.*)

(*Module Type DecayingSemantics.
  Include Semantics.
  Axiom step_decay: forall g c m tr c' m',
      event_semantics.ev_step (Sem) g c m tr c' m' ->

      decay m m'.
End DecayingSemantics. *)

Set Bullet Behavior "Strict Subproofs".

Module Parching <: ErasureSig.
  Import THE_JUICY_MACHINE.
  Module SCH:= THE_JUICY_MACHINE.SCH.
  Module SEM:= THE_JUICY_MACHINE.SEM.
  Import SCH SEM.

  Module JSEM := THE_JUICY_MACHINE.JSEM.
  Module JuicyMachine := THE_JUICY_MACHINE.JuicyMachine.
  Notation JMachineSem:= THE_JUICY_MACHINE.JMachineSem.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=THE_JUICY_MACHINE.JTP.

  Import JSEM.JuicyMachineLemmas.
  (*Module SCH:= ListScheduler NatTID.            
  Module SEM:= DecayingSEM.
  

  Module JSEM := JuicyMachineShell SEM. (* JuicyMachineShell : Semantics -> ConcurrentSemanticsSig *)
  Module JuicyMachine := CoarseMachine SCH JSEM. (* CoarseMachine : Schedule -> ConcurrentSemanticsSig -> ConcurrentSemantics *)
  Notation JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=JuicyMachine.SIG.ThreadPool.
  Import JSEM.JuicyMachineLemmas.*)
  Import THE_DRY_MACHINE_SOURCE.
  
  Module DSEM := THE_DRY_MACHINE_SOURCE.DSEM. 
  Module DryMachine <: ConcurrentMachine:= THE_DRY_MACHINE_SOURCE.DryMachine.
  Notation DMachineSem:= DryMachine.MachineSemantics. 
  Notation dstate:= DryMachine.SIG.ThreadPool.t.
  Notation dmachine_state:= DryMachine.MachState.
  Module DTP:=THE_DRY_MACHINE_SOURCE.DTP.
  Import DSEM.DryMachineLemmas event_semantics.



  (** * Match relation between juicy and dry state : *)
  (* 1-2. Same threads are contained in each state: 
     3.   Threads have the same c 
     4-5.   Threads have the same permissions up to erasure 
     6.   the locks are in the same addresses. 
     7-8-9. Lock contents match up to erasure. *)
  (*Definition lock_perm_of_res (r: resource) := 
    (*  perm_of_sh (res_retain' r) (valshare r). *)
    match r with
    | YES rsh sh (LK _) _ => perm_of_sh rsh (pshare_sh sh)
    | YES rsh sh (CT _) _ => perm_of_sh rsh (pshare_sh sh)
    | _ => None
    end.*)

  Inductive match_st' : jstate ->  dstate -> Prop:=
    MATCH_ST: forall (js:jstate) ds
                (mtch_cnt: forall {tid},  JTP.containsThread js tid -> DTP.containsThread ds tid )
                (mtch_cnt': forall {tid}, DTP.containsThread ds tid -> JTP.containsThread js tid )
                (mtch_gtc: forall {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    JTP.getThreadC Htid = DTP.getThreadC Htid' )
                (mtch_perm1: forall b ofs {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    juicy_mem.perm_of_res (resource_at (JTP.getThreadR Htid) (b, ofs)) =
                    ((DTP.getThreadR Htid').1 !! b) ofs )
                (mtch_perm2: forall b ofs {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    juicy_mem.perm_of_res_lock (resource_at (JTP.getThreadR Htid) (b, ofs)) =
                    ((DTP.getThreadR Htid').2 !! b) ofs )
                (mtch_locks: forall a,
                    ssrbool.isSome (JSEM.ThreadPool.lockRes js a) = ssrbool.isSome (DSEM.ThreadPool.lockRes ds a))
                (mtch_locksEmpty: forall lock dres,
                    JSEM.ThreadPool.lockRes js lock = Some (None) -> 
                    DSEM.ThreadPool.lockRes ds lock = Some dres ->
                   dres = (empty_map, empty_map))
                (mtch_locksRes: forall lock jres dres,
                    JSEM.ThreadPool.lockRes js lock = Some (Some jres) -> 
                    DSEM.ThreadPool.lockRes ds lock = Some dres ->
                     forall b ofs,
                       juicy_mem.perm_of_res (resource_at jres (b, ofs)) = (dres.1 !! b) ofs )
                (mtch_locksRes: forall lock jres dres,
                    JSEM.ThreadPool.lockRes js lock = Some (Some jres) -> 
                    DSEM.ThreadPool.lockRes ds lock = Some dres ->
                     forall b ofs,
                    juicy_mem.perm_of_res_lock (resource_at jres (b, ofs)) = (dres.2 !! b) ofs )
                (*mtch_locks: AMap.map (fun _ => tt) (JTP.lockGuts js) = DTP.lockGuts ds*),
      match_st' js ds.
  Definition match_st:= match_st'.
  
  
  (** *Match lemmas*)
  Lemma MTCH_cnt: forall {js tid ds},
           match_st js ds ->
           JTP.containsThread js tid -> DTP.containsThread ds tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt. Qed.
  Lemma MTCH_cnt': forall {js tid ds},
           match_st js ds ->
           DTP.containsThread ds tid -> JTP.containsThread js tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt'. Qed.

  Lemma MTCH_perm: forall {js ds i},
      forall (cnt: JSEM.ThreadPool.containsThread js i)
      (MTCH: match_st js ds),
      forall b ofs,
        juicy_mem.perm_of_res ((JTP.getThreadR cnt) @ (b, ofs)) = ((DTP.getThreadR (MTCH_cnt MTCH cnt)).1 !! b) ofs.
  Proof. intros ? ? ? ? MTCH ? ?. inversion MTCH. apply mtch_perm1. Qed.
  
  Lemma MTCH_perm2: forall {js ds i},
      forall (cnt: JSEM.ThreadPool.containsThread js i)
      (MTCH: match_st js ds),
      forall b ofs,
        juicy_mem.perm_of_res_lock  ((JTP.getThreadR cnt) @ (b, ofs)) = ((DTP.getThreadR (MTCH_cnt MTCH cnt)).2 !! b) ofs.
  Proof. intros. inversion MTCH. apply mtch_perm2. Qed.
  
  Lemma MTCH_perm': forall {js ds i},
      forall (cnt: DSEM.ThreadPool.containsThread ds i)
      (MTCH: match_st js ds),
      forall b ofs,
        ((DTP.getThreadR cnt).1 !! b) ofs =
        juicy_mem.perm_of_res ((JTP.getThreadR (MTCH_cnt' MTCH cnt)) @ (b, ofs)).
  Proof. intros. inversion MTCH. symmetry. apply mtch_perm1; eauto. Qed.
  
  Lemma MTCH_perm2': forall {js ds i},
      forall (cnt: DSEM.ThreadPool.containsThread ds i)
      (MTCH: match_st js ds),
      forall b ofs,
        ((DTP.getThreadR cnt).2 !! b) ofs =
        juicy_mem.perm_of_res_lock ((JTP.getThreadR (MTCH_cnt' MTCH cnt)) @ (b, ofs)).
  Proof. intros. inversion MTCH. symmetry; apply mtch_perm2. Qed.
  
  Lemma cnt_irr: forall tid ds (cnt1 cnt2: DTP.containsThread ds tid),
      DTP.getThreadC cnt1 = DTP.getThreadC cnt2.
  Proof. intros.
         unfold DTP.getThreadC.
         destruct ds; simpl.
         f_equal; f_equal.
         eapply proof_irrelevance.
  Qed.

  Lemma MTCH_getThreadC: forall js ds tid c,
      forall (cnt: JTP.containsThread js tid)
        (cnt': DTP.containsThread ds tid)
        (M: match_st js ds),
        JTP.getThreadC cnt =  c ->
        DTP.getThreadC cnt'  =  c.
  Proof. intros ? ? ? ? ? MTCH; inversion MTCH; subst.
         intros HH; inversion HH; subst.
         intros AA; rewrite <- AA. symmetry; apply mtch_gtc.
  Qed.

  Lemma MTCH_lockSet: forall js ds,
      match_st js ds ->
      forall b ofs, (JTP.lockSet js) !! b ofs = (DTP.lockSet ds) !! b ofs.
  Proof.
    intros js ds MATCH b ofs.
    inversion MATCH. clear - mtch_locks.
    destruct (DSEM.ThreadPool.lockRes_range_dec ds b ofs).
    - destruct e as [z [ineq dLR]].
      specialize (mtch_locks (b, z)).
      destruct ( DSEM.ThreadPool.lockRes ds (b, z)) eqn:AA; inversion dLR.
      destruct (JSEM.ThreadPool.lockRes js (b, z)) eqn:BB; inversion mtch_locks.
      erewrite JSEM.ThreadPool.lockSet_spec_2; eauto.
      erewrite DSEM.ThreadPool.lockSet_spec_2; eauto.
      rewrite BB; constructor.
      rewrite AA in dLR; inversion dLR.
    - destruct (JSEM.ThreadPool.lockRes_range_dec js b ofs).
      + clear e.
        destruct e0 as [z [ineq dLR]].
        specialize (mtch_locks (b, z)).
        destruct (JSEM.ThreadPool.lockRes js (b, z)) eqn:AA; inversion dLR.
        * destruct ( DSEM.ThreadPool.lockRes ds (b, z)) eqn:BB; inversion mtch_locks.
          erewrite JSEM.ThreadPool.lockSet_spec_2; eauto.
          erewrite DSEM.ThreadPool.lockSet_spec_2; eauto.
          rewrite BB; constructor.
        * rewrite AA in dLR; inversion dLR.
      + erewrite JSEM.ThreadPool.lockSet_spec_3; eauto.
        erewrite DSEM.ThreadPool.lockSet_spec_3; eauto.
  Qed.
  
  Lemma MTCH_compat: forall js ds m,
      match_st js ds ->
      JSEM.mem_compatible js m ->
      DSEM.mem_compatible ds m.
  Proof. 
    intros ? ? ? MTCH mc.
    inversion MTCH; subst.
    constructor.
    - intros tid cnt.
      assert (th_coh:= JSEM.thread_mem_compatible mc).
      specialize (th_coh tid (mtch_cnt' _ cnt)).
      inversion th_coh.
      unfold permMapLt; 
        split; intros b ofs; rewrite getMaxPerm_correct; eapply po_trans;
      try solve [eapply (max_coh (b,ofs))].
      + rewrite <- (mtch_perm1 _ _ _ (mtch_cnt' tid cnt));
        eapply perm_of_res_op1.
      + rewrite <- (mtch_perm2 _ _ _ (mtch_cnt' tid cnt));
        eapply perm_of_res_op2.
    - intros.
      assert(HH: exists jres, JSEM.ThreadPool.lockRes js l = Some jres).
      { specialize (mtch_locks  l); rewrite H in mtch_locks.
      destruct (JSEM.ThreadPool.lockRes js l); try solve[inversion mtch_locks].
      exists l0; reflexivity. }
      destruct HH as [jres HH].
      destruct jres.
      + specialize (mtch_locksRes _ _ _ HH H).
        specialize (mtch_locksRes0 _ _ _ HH H).
        split; intros b ofs.
        * rewrite <- mtch_locksRes.
          eapply JSEM.JuicyMachineLemmas.compat_lockLT;
            eassumption.
        * rewrite <- mtch_locksRes0.
          eapply po_trans.
          eapply JSEM.JuicyMachineLemmas.compat_lockLT';
            eassumption.
          eapply perm_of_res_op2.
      + specialize (mtch_locksEmpty _ _ HH H).
        rewrite mtch_locksEmpty.
        split; apply empty_LT.
   (* - intros b ofs.
      rewrite <- (MTCH_lockSet _ _ MTCH).
      apply JSEM.compat_lt_m; assumption.*)
    - intros l rmap0 H.
      destruct (valid_block_dec m l.1); try assumption.
      eapply m with (ofs:=l.2) (k:=Max) in n.
      specialize (mtch_locks l).
      rewrite H in mtch_locks.
      destruct (JSEM.ThreadPool.lockRes js l) eqn:lock_in_l; try solve[inversion mtch_locks]; clear mtch_locks.
      destruct mc as [all_juice mc']; destruct mc'.
      move lset_in_juice at bottom.
      specialize (lset_in_juice l).
      unfold JSEM.ThreadPool.lockRes in lock_in_l.
      unfold juicy_machine.LocksAndResources.lock_info in lock_in_l.
      rewrite lock_in_l in lset_in_juice. simpl in lset_in_juice.
      assert (HH:true) by auto; apply lset_in_juice in HH.
      destruct HH as [sh [psh [p HH]]].
      destruct all_cohere.
      specialize (max_coh l).
      rewrite HH in max_coh.
      simpl in max_coh.
      unfold max_access_at, access_at in max_coh.
      rewrite n in max_coh.
      cut (Mem.perm_order'' None (Some Nonempty)).
      { intros AA; inversion AA. }
      eapply po_trans; eauto. 
      destruct (perm_of_sh_pshare sh psh) as [P is_Some].
      rewrite is_Some. constructor.
  Qed.
  
  Lemma MTCH_updt:
    forall js ds tid c
      (H0:match_st js ds)
      (cnt: JTP.containsThread js tid)
      (cnt': DTP.containsThread ds tid),
      match_st (JTP.updThreadC cnt c)
               (DTP.updThreadC cnt' c).
  Proof.
    intros. constructor; intros.
    - apply DTP.cntUpdateC.
      inversion H0; subst.
      apply mtch_cnt.
      eapply JTP.cntUpdateC'; apply H.
    - apply JTP.cntUpdateC.
      inversion H0; subst.
      apply mtch_cnt'.
        eapply DTP.cntUpdateC'; apply H.
    - destruct (NatTID.eq_tid_dec tid tid0) as [e|ine].
      + subst.
          rewrite JTP.gssThreadCC;
          rewrite DTP.gssThreadCC.
          reflexivity.
      + assert (cnt2:= JTP.cntUpdateC' _ cnt Htid).
        rewrite <- (JTP.gsoThreadCC ine cnt cnt2 c Htid) by assumption.
        inversion H0; subst.
          (* pose (cnt':=(@MTCH_cnt js tid ds H0 cnt)). *)
          assert (cnt2':= DTP.cntUpdateC' _ cnt' Htid').
          (*fold cnt';*)
          rewrite <- (DTP.gsoThreadCC ine cnt' cnt2' c Htid') by assumption.
          apply mtch_gtc; assumption.
    - inversion H0; apply mtch_perm1.
    - inversion H0; apply mtch_perm2.
    - inversion H0; apply mtch_locks.
    - inversion H0; eapply mtch_locksEmpty; eauto.
    - inversion H0; eapply mtch_locksRes; eauto.
    - inversion H0; eapply mtch_locksRes0; eauto.
  Qed.
    
    Lemma MTCH_restrict_personal:
      forall ds js m i
        (MTCH: match_st js ds)
        (Hi: JTP.containsThread js i)
        (Hi': DTP.containsThread ds i)
        Hcmpt
        (Hcmpt': DSEM.mem_compatible ds m),
        restrPermMap (DSEM.compat_th Hcmpt' Hi').1 =
        m_dry (@JSEM.personal_mem m (@JTP.getThreadR i js Hi) Hcmpt).
    Proof.
      intros.
      inversion MTCH; subst.
      unfold JSEM.personal_mem; simpl; unfold JSEM.juicyRestrict; simpl.
      apply restrPermMap_ext; intros.
      extensionality ofs;
      erewrite <- mtch_perm1.
      instantiate(1:=Hi).
      erewrite JSEM.juic2Perm_correct. reflexivity.
      apply JSEM.acc_coh; assumption.
    Qed.
      
    Lemma MTCH_halted:
      forall ds js i
        (cnt: JTP.containsThread  js i)
        (cnt': DTP.containsThread  ds i),
        match_st js ds->
        JSEM.threadHalted cnt ->
        DSEM.invariant ds ->
        DSEM.threadHalted cnt'.
    Proof.
      intros.
      inversion H0; subst.
      econstructor.
      - assumption.
      - inversion H; subst. erewrite <- mtch_gtc. eassumption.
      - apply Hcant.
    Qed.
    
    Lemma MTCH_updLockS:
             forall js ds loc jres dres1 dres2,
               match_st js ds ->
             (forall b ofs, perm_of_res (jres @ (b, ofs)) = dres1 !! b ofs) ->
             (forall b ofs, perm_of_res_lock (jres @ (b, ofs)) = dres2 !! b ofs) ->
                      match_st
                        (JSEM.ThreadPool.updLockSet js loc (Some jres))
                        (DSEM.ThreadPool.updLockSet ds loc (dres1,dres2)).
    Proof. intros.
           constructor.
           + intros. apply DTP.cntUpdateL.
             destruct H; apply mtch_cnt.
             apply JTP.cntUpdateL' in H2; assumption.
           + intros. apply JTP.cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntUpdateL' in H2; assumption.
           + intros. rewrite JSEM.ThreadPool.gLockSetCode DSEM.ThreadPool.gLockSetCode.
             inversion H; subst. apply mtch_gtc. 
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DSEM.ThreadPool.gLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DSEM.ThreadPool.gLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock DSEM.ThreadPool.gsslockResUpdLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock.
               rewrite DSEM.ThreadPool.gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
               assumption.
               assumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock in H2; inversion H2. 
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H2. rewrite DSEM.ThreadPool.gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksEmpty; eassumption.
               assumption. assumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H2.
               rewrite DSEM.ThreadPool.gsslockResUpdLock in H3.
               inversion H2; inversion H3; subst.
               apply H0.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H2. rewrite DSEM.ThreadPool.gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksRes; eassumption.
               assumption.
               assumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H2.
               rewrite DSEM.ThreadPool.gsslockResUpdLock in H3.
               inversion H2; inversion H3; subst.
               apply H1.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H2. rewrite DSEM.ThreadPool.gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksRes0; eassumption.
               assumption.
               assumption.
    Qed.
    
    Lemma MTCH_updLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (JSEM.ThreadPool.updLockSet js loc None)
          (DSEM.ThreadPool.updLockSet ds loc (empty_map,empty_map)).
           intros.
           constructor.
           + intros. apply DTP.cntUpdateL.
             destruct H; apply mtch_cnt.
             apply JTP.cntUpdateL' in H0; assumption.
           + intros. apply JTP.cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntUpdateL' in H0; assumption.
           + intros. rewrite JSEM.ThreadPool.gLockSetCode DSEM.ThreadPool.gLockSetCode.
             inversion H; subst. apply mtch_gtc. 
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DSEM.ThreadPool.gLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DSEM.ThreadPool.gLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock DSEM.ThreadPool.gsslockResUpdLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock.
               rewrite DSEM.ThreadPool.gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
               assumption. assumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite DSEM.ThreadPool.gsslockResUpdLock in H1; inversion H1; reflexivity. 
             * rewrite DSEM.ThreadPool.gsolockResUpdLock in H1.
               rewrite JSEM.ThreadPool.gsolockResUpdLock in H0.
               inversion H. eapply mtch_locksEmpty; eassumption.
               assumption.
               assumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H0.
               rewrite DSEM.ThreadPool.gsslockResUpdLock in H1.
               inversion H0. 
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H0. 2: assumption.
               rewrite DSEM.ThreadPool.gsolockResUpdLock in H1. 2: assumption.
               inversion H. eapply mtch_locksRes; eassumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H0.
               rewrite DSEM.ThreadPool.gsslockResUpdLock in H1.
               inversion H0. 
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H0. 2: assumption.
               rewrite DSEM.ThreadPool.gsolockResUpdLock in H1. 2: assumption.
               inversion H. eapply mtch_locksRes0; eassumption.
    Qed.
    
    Lemma MTCH_remLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (JSEM.ThreadPool.remLockSet js loc)
          (DSEM.ThreadPool.remLockSet ds loc).
           intros.
           constructor.
           + intros. apply DTP.cntRemoveL.
             destruct H; apply mtch_cnt.
             apply JTP.cntRemoveL' in H0; assumption.
           + intros. apply JTP.cntRemoveL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntRemoveL' in H0; assumption.
           + intros. rewrite JSEM.ThreadPool.gRemLockSetCode DSEM.ThreadPool.gRemLockSetCode.
             inversion H; subst. apply mtch_gtc. 
           + intros. rewrite JSEM.ThreadPool.gRemLockSetRes  DSEM.ThreadPool.gRemLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite JSEM.ThreadPool.gRemLockSetRes  DSEM.ThreadPool.gRemLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResRemLock DSEM.ThreadPool.gsslockResRemLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResRemLock.
               2: exact NEQ.
               rewrite DSEM.ThreadPool.gsolockResRemLock.
               2: exact NEQ.
               inversion H. solve[apply mtch_locks].
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite DSEM.ThreadPool.gsslockResRemLock in H1; inversion H1; reflexivity. 
             * rewrite DSEM.ThreadPool.gsolockResRemLock in H1.
               2: exact NEQ.
               rewrite JSEM.ThreadPool.gsolockResRemLock in H0.
               2: exact NEQ.
               inversion H. eapply mtch_locksEmpty; eassumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResRemLock in H0.
               rewrite DSEM.ThreadPool.gsslockResRemLock in H1.
               inversion H0. 
             * rewrite JSEM.ThreadPool.gsolockResRemLock in H0. 
               2: exact NEQ.
               rewrite DSEM.ThreadPool.gsolockResRemLock in H1.
               2: exact NEQ.
               inversion H. eapply mtch_locksRes; eassumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResRemLock in H0.
               rewrite DSEM.ThreadPool.gsslockResRemLock in H1.
               inversion H0. 
             * rewrite JSEM.ThreadPool.gsolockResRemLock in H0. 
               2: exact NEQ.
               rewrite DSEM.ThreadPool.gsolockResRemLock in H1.
               2: exact NEQ.
               inversion H. eapply mtch_locksRes0; eassumption.
    Qed.
    
    Lemma MTCH_update:
      forall js ds Kc phi p1 p2 i
        (Hi : JTP.containsThread js i)
        (Hi': DTP.containsThread ds i),
        match_st js ds ->
        ( forall b ofs,
            perm_of_res (phi @ (b, ofs)) = p1 !! b ofs) -> 
        ( forall b ofs,
            perm_of_res_lock (phi @ (b, ofs)) = p2 !! b ofs) -> 
        match_st (JSEM.ThreadPool.updThread Hi  Kc phi)
                 (DSEM.ThreadPool.updThread Hi' Kc (p1,p2)).
    Proof.
      intros. inversion H; subst.
      constructor; intros.
      - apply DTP.cntUpdate. apply mtch_cnt.
        eapply JTP.cntUpdate'; eassumption.
      - apply JTP.cntUpdate. apply mtch_cnt'.
        eapply DTP.cntUpdate'; eassumption.
      - destruct (NatTID.eq_tid_dec i tid).
        + subst.
          rewrite JTP.gssThreadCode DTP.gssThreadCode; reflexivity.
        + assert (jcnt2:= JTP.cntUpdateC' Kc Hi Htid).
          assert (dcnt2:= DTP.cntUpdateC' Kc Hi' Htid').
          rewrite (JTP.gsoThreadCode n Hi  jcnt2 _ _ Htid); auto.
          rewrite (DTP.gsoThreadCode n Hi' dcnt2 _ _  Htid'); auto.
      - destruct (NatTID.eq_tid_dec i tid).
        + subst.
          rewrite (JTP.gssThreadRes Hi _ _ Htid); auto.
          rewrite (DTP.gssThreadRes Hi'  _ _  Htid'); auto.
        + assert (jcnt2:= JTP.cntUpdateC' Kc Hi Htid).
          assert (dcnt2:= DTP.cntUpdateC' Kc Hi' Htid').
          rewrite (JTP.gsoThreadRes Hi jcnt2 n _ _ Htid); auto.
          rewrite (DTP.gsoThreadRes Hi' dcnt2 n _ _  Htid'); auto.
      - destruct (NatTID.eq_tid_dec i tid).
        + subst.
          rewrite (JTP.gssThreadRes Hi _ _ Htid); auto.
          rewrite (DTP.gssThreadRes Hi'  _ _  Htid'); simpl; auto.
        + assert (jcnt2:= JTP.cntUpdateC' Kc Hi Htid).
          assert (dcnt2:= DTP.cntUpdateC' Kc Hi' Htid').
          rewrite (JTP.gsoThreadRes Hi jcnt2 n _ _ Htid); auto.
          rewrite (DTP.gsoThreadRes Hi' dcnt2 n _ _  Htid'); auto.
      - simpl;  apply mtch_locks.
      - simpl. eapply mtch_locksEmpty; eassumption.
      - simpl; eapply mtch_locksRes; eassumption.
      - simpl; eapply mtch_locksRes0; eassumption.
    Qed.

    Lemma match_st_age_tp_to tp n ds :
      match_st tp ds -> match_st (JSEM.age_tp_to n tp) ds.
    Proof.
      intros M.
      inversion M as [? ? A B C D E F G H I J]; subst.
      constructor; intros.
      - now apply A; (eapply cnt_age; eauto).
      - now erewrite <-cnt_age; eauto.
      - now erewrite <-gtc_age; eauto.
      - erewrite <-D.
        erewrite <-getThreadR_age; eauto.
        erewrite JSEM.perm_of_age.
        reflexivity.
      - erewrite <- E.
        erewrite <-getThreadR_age; eauto.
        erewrite JSEM.perm_of_age_lock.
        reflexivity.
      - erewrite <-F.
        apply LockRes_age.
      - unshelve eapply G with (lock := lock); auto.
        unfold JSEM.ThreadPool.lockRes in *.
        unfold JSEM.ThreadPool.lockGuts in *.
        rewrite lset_age_tp_to in H0.
        rewrite AMap_find_map_option_map in H0.
        unfold juicy_machine.LocksAndResources.lock_info in *.
        destruct (AMap.find (elt:=option rmap) lock (JSEM.ThreadPool.lset tp))
          as [[o|]|]; simpl in *; congruence.
      - unfold JSEM.ThreadPool.lockRes in *.
        unfold juicy_machine.LocksAndResources.lock_info in *.
        specialize (H lock).
        unfold JSEM.ThreadPool.lockRes in *.
        unfold JSEM.ThreadPool.lockGuts in *.
        rewrite lset_age_tp_to in H0.
        rewrite AMap_find_map_option_map in H0.
        destruct (AMap.find (elt:=option rmap) lock (JSEM.ThreadPool.lset tp))
          as [[o|]|]; simpl in *; try congruence.
        specialize (H o dres Logic.eq_refl ltac:(assumption)).
        rewrite <-H.
        injection H0 as <-.
        apply JSEM.perm_of_age.
        (* again aging lset. *)
      - unfold JSEM.ThreadPool.lockRes in *.
        unfold juicy_machine.LocksAndResources.lock_info in *.
        specialize (I lock).
        unfold JSEM.ThreadPool.lockRes in *.
        unfold JSEM.ThreadPool.lockGuts in *.
        rewrite lset_age_tp_to in H0.
        rewrite AMap_find_map_option_map in H0.
        destruct (AMap.find (elt:=option rmap) lock (JSEM.ThreadPool.lset tp))
          as [[o|]|]; simpl in *; try congruence.
        specialize (I o dres Logic.eq_refl ltac:(assumption)).
        rewrite <-I.
        injection H0 as <-.
        apply JSEM.perm_of_age_lock.
        (* again aging lset. *)
        Unshelve. auto. auto. auto.
    Qed.
    
    Definition match_rmap_perm (rmap : rmap) (pmap: access_map): Prop:=
      forall b ofs, perm_of_res (rmap @ (b, ofs)) = pmap !! b ofs.

    Lemma MTCH_initial:
      forall  c rmap pmap,
        match_rmap_perm rmap pmap ->
        match_st (JSEM.initial_machine rmap c) (DSEM.initial_machine (*genv*) pmap c).
    Proof.
      intros.
      constructor.
      - intro i. unfold JTP.containsThread, JSEM.initial_machine; simpl.
        unfold DTP.containsThread, DSEM.initial_machine; simpl.
        trivial.
      - intro i. unfold JTP.containsThread, JSEM.initial_machine; simpl.
        unfold DTP.containsThread, DSEM.initial_machine; simpl.
        trivial.
      - reflexivity.
      - intros.
        unfold JTP.getThreadR; unfold JSEM.initial_machine; simpl.
        unfold DTP.getThreadR; unfold DSEM.initial_machine; simpl.
        unfold match_rmap_perm in H. apply H. 
      - intros.
        unfold JTP.getThreadR; unfold JSEM.initial_machine; simpl.
        unfold DTP.getThreadR; unfold DSEM.initial_machine; simpl.
        unfold match_rmap_perm in H. apply H. 
      - unfold empty_rmap, "@"; simpl.
        reflexivity.
      - unfold DSEM.ThreadPool.lockRes, DSEM.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H1; inversion H1.
      - unfold DSEM.ThreadPool.lockRes, DSEM.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H1; inversion H1.
    Qed.

    (*Lemma to prove MTCH_latestThread*)
      Lemma contains_iff_num:
        forall js ds
          (Hcnt: forall i, JTP.containsThread js i <-> DTP.containsThread ds i),
          JSEM.ThreadPool.num_threads js = DSEM.ThreadPool.num_threads ds.
      Proof.
        intros.
        unfold JTP.containsThread, DTP.containsThread in *.
        remember (JSEM.ThreadPool.num_threads js).
        remember (DSEM.ThreadPool.num_threads ds).
        destruct p, p0; simpl in *.
        assert (n = n0).
        { clear - Hcnt.
          generalize dependent n0.
          induction n; intros.
          destruct n0; auto.
          destruct (Hcnt 0%nat).
          exfalso.
          specialize (H0 ltac:(ssromega));
            by ssromega.

          destruct n0.
          exfalso.
          destruct (Hcnt 0%nat).
          specialize (H ltac:(ssromega));
            by ssromega.
          erewrite IHn; eauto.
          intros; split; intro H.
          assert (i.+1 < n.+1) by ssromega.
          specialize (proj1 (Hcnt (i.+1)) H0).
          intros.
          clear -H1;
            by ssromega.
          assert (i.+1 < n0.+1) by ssromega.
          specialize (proj2 (Hcnt (i.+1)) H0).
          intros.
          clear -H1;
            by ssromega. }
        subst.
          by erewrite proof_irr with (a1 := N_pos) (a2 := N_pos0).
      Qed.
      
      
      Lemma MTCH_latestThread: forall js ds,
          match_st js ds ->
          JTP.latestThread js = DTP.latestThread ds.
      Proof.
        intros js ds MATCH.
        unfold JTP.latestThread.
        unfold DTP.latestThread.
        erewrite contains_iff_num.
        - reflexivity.
        - split; generalize i; inversion MATCH; assumption.
      Qed.

      Lemma MTCH_addThread: forall js ds parg arg phi res,
          match_st js ds ->
          (forall b0 ofs0, perm_of_res (phi@(b0, ofs0)) = res !! b0 ofs0) ->
          match_st
            (JTP.addThread js parg arg phi)
            (DTP.addThread ds parg arg res).
      Proof.
        intros ? ? ? ? ? ? MATCH DISJ. constructor.
        - intros tid HH.
          apply JTP.cntAdd' in HH. destruct HH as [[HH ineq] | HH].
          + apply DTP.cntAdd. inversion MATCH. apply mtch_cnt. assumption.
          + 
            erewrite MTCH_latestThread in HH.
            rewrite HH.
            apply DSEM.ThreadPool.contains_add_latest.
            assumption.
        - intros tid HH.
          apply DTP.cntAdd' in HH. destruct HH as [[HH ineq] | HH].
          + apply JTP.cntAdd. inversion MATCH. eapply  mtch_cnt'; assumption.
          + erewrite <- MTCH_latestThread in HH.
            rewrite HH.
            apply JSEM.ThreadPool.contains_add_latest.
            assumption.
        - intros.
            destruct (JTP.cntAdd' _ _ _ Htid) as [[jcnt jNLast]| jLast];
              destruct (DTP.cntAdd' _ _ _ Htid') as [[dcnt dNLast]| dLast].
            * erewrite JSEM.ThreadPool.gsoAddCode; try eassumption.
              erewrite DSEM.ThreadPool.gsoAddCode; try eassumption.
              inversion MATCH. eapply mtch_gtc.
            * contradict jNLast.
              rewrite <- (MTCH_latestThread js ds) in dLast.
              rewrite dLast; reflexivity.
              assumption.
            * contradict dNLast.
              rewrite (MTCH_latestThread js ds) in jLast.
              rewrite jLast; reflexivity.
              assumption.
            * erewrite JSEM.ThreadPool.gssAddCode; try eassumption.
              erewrite DSEM.ThreadPool.gssAddCode; try eassumption.
              reflexivity.
        - intros.
          destruct (JTP.cntAdd' _ _ _ Htid) as [[jcnt jNLast]| jLast];
            destruct (DTP.cntAdd' _ _ _ Htid') as [[dcnt dNLast]| dLast].
          * erewrite JSEM.ThreadPool.gsoAddRes; try eassumption.
            erewrite DSEM.ThreadPool.gsoAddRes; try eassumption.
            inversion MATCH. eapply mtch_perm.
          * contradict jNLast.
            rewrite <- (MTCH_latestThread js ds) in dLast.
            rewrite dLast; reflexivity.
            assumption.
          * contradict dNLast.
            rewrite (MTCH_latestThread js ds) in jLast.
            rewrite jLast; reflexivity.
            assumption.
          * erewrite JSEM.ThreadPool.gssAddRes; try eassumption.
            erewrite DSEM.ThreadPool.gssAddRes; try eassumption.
            apply DISJ.
        - intros. rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
          inversion MATCH. apply mtch_locks.
        - intros lock dres.
          rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
          inversion MATCH. apply mtch_locksEmpty.
        - intros lock jres dres .
          rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
          inversion MATCH. apply mtch_locksRes.
          Grab Existential Variables.
          assumption.
          assumption.
          assumption.
          assumption.
      Qed.

      Lemma MTCH_age: forall js ds age,
          match_st js ds ->
          match_st (JSEM.age_tp_to age js) ds. 
      Proof.
        intros js ds age MATCH; inversion MATCH. constructor.
        - 
          intros i HH. apply JSEM.JuicyMachineLemmas.cnt_age in HH.
          apply mtch_cnt; assumption.
        - intros i HH. apply @JSEM.JuicyMachineLemmas.cnt_age.
          apply mtch_cnt'; assumption.
        - intros i cnt cnt'.
          
          erewrite <- JSEM.JuicyMachineLemmas.gtc_age.
          eapply mtch_gtc.
        - intros.
          
          erewrite <- JSEM.JuicyMachineLemmas.getThreadR_age. simpl.
          
          rewrite JSEM.perm_of_age.
          apply mtch_perm.
        - intros.
          
          rewrite JSEM.JuicyMachineLemmas.LockRes_age. apply mtch_locks.
        - intros.
          
          apply JSEM.JuicyMachineLemmas.LockRes_age_content1 in H1.
          eapply mtch_locksEmpty; eassumption.
        -
          intros. apply JSEM.JuicyMachineLemmas.LockRes_age_content2 in H1.
          destruct H1 as [r [AA BB]].
          rewrite BB.
          rewrite JSEM.perm_of_age.
          eapply mtch_locksRes; eassumption.

          Grab Existential Variables.
          eapply JSEM.JuicyMachineLemmas.cnt_age; eassumption.
          eapply JSEM.JuicyMachineLemmas.cnt_age; eassumption.
      Qed.

    Lemma init_diagram:
      forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
        (vals : list Values.val) (m : Mem.mem) rmap pmap main genv,
        init_inj_ok j m ->
        match_rmap_perm rmap pmap ->
        initial_core (JMachineSem U (Some rmap)) genv main vals = Some (U, nil, js) ->
        exists (mu : SM_Injection) (ds : dstate),
          as_inj mu = j /\
          initial_core (DMachineSem U (Some pmap)) genv main vals = Some (U, nil,ds) /\
          DSEM.invariant ds /\
          match_st js ds.
    Proof.
      intros.

      (* Build the structured injection*)
      exists (initial_SM (valid_block_dec m) (valid_block_dec m) (fun _ => false) (fun _ => false) j).

      (* Build the dry state *)
      simpl in H1.
      unfold JuicyMachine.init_machine in H1.
      unfold JSEM.init_mach in H1. simpl in H1.
      destruct ( initial_core (msem JSEM.ThreadPool.SEM.Sem) genv main vals) eqn:C; try solve[inversion H1].
      inversion H1.
      exists (DSEM.initial_machine pmap c).

      split; [|split;[|split]].
      
      (*Proofs*)
      - apply initial_SM_as_inj.
      - simpl.
        unfold DryMachine.init_machine.
        unfold DSEM.init_mach.
        rewrite C.
        f_equal.
      - apply initial_invariant.
      - apply MTCH_initial. assumption.
    Qed.
   
  Lemma conc_step_diagram:
    forall m m' U js js' ds i genv ev
      (MATCH: match_st js ds)
      (dinv: DSEM.invariant ds)
      (Hi: JSEM.ThreadPool.containsThread js i)
      (Hcmpt: JSEM.mem_compatible js m)
      (HschedN: schedPeek U = Some i)
      (Htstep:  JSEM.syncStep genv Hi Hcmpt js' m' ev),
      exists ds' : dstate, exists ev',
        DSEM.invariant ds' /\
        match_st js' ds' /\
        DSEM.syncStep genv (MTCH_cnt MATCH Hi) (MTCH_compat _ _ _ MATCH Hcmpt) ds' m'
                      ev'.
  Proof.

    intros.
    inversion Htstep; try subst.
    
    (* step_acquire  *)
    {
    assert (Htid':= MTCH_cnt MATCH Hi).
    pose (inflated_delta:=
            fun loc => match (d_phi @ loc ) with
                      NO s => if Share.EqDec_share s Share.bot then None else Some ( perm_of_res (phi' @ loc))
                    | _ => Some (perm_of_res (phi' @ loc))
                    end).
         pose (virtue:= PTree.map
                                      (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                                         (inflated_delta (block, ofs))) (snd (getCurPerm m)) ).
         assert (virtue_some: forall l p, inflated_delta l = Some p ->
                             p = perm_of_res (phi' @ l)).
            {
              intros l p; unfold inflated_delta.
              destruct (d_phi @ l); try solve[intros HH; inversion HH; reflexivity].
              destruct ( proj_sumbool (Share.EqDec_share t Share.bot));
                [congruence| intros HH; inversion HH; reflexivity]. }
            
         pose (ds':= DSEM.ThreadPool.updThread Htid' (Kresume c Vundef)
                  (computeMap
                     (DSEM.ThreadPool.getThreadR Htid') virtue)).
         pose (ds'':= DSEM.ThreadPool.updLockSet ds'
                      (b, Int.intval ofs) empty_map).
         exists ds'', (DSEM.Events.acquire (b, Int.intval ofs) (Some (empty_map, virtue))).
         split; [|split].
    - unfold ds''.
      rewrite DSEM.ThreadPool.updLock_updThread_comm.
      pose (ds0:= (DSEM.ThreadPool.updLockSet ds (b, (Int.intval ofs)) empty_map)).
      
      cut (DSEM.invariant ds0).
      { (* Proving: invariant ds0' *)
        intros dinv0.
        apply updThread_inv.
        - assumption.
        - Inductive deltaMap_cases (dmap:delta_map) b ofs:=
        | DMAPS df p:  dmap ! b = Some df -> df ofs = Some p -> deltaMap_cases dmap b ofs
        | DNONE1 df:  dmap ! b = Some df -> df ofs = None -> deltaMap_cases dmap b ofs
        | DNONE2:  dmap ! b = None -> deltaMap_cases dmap b ofs.
          Lemma deltaMap_dec: forall dmap b ofs, deltaMap_cases dmap b ofs.
          Proof. intros. destruct (dmap ! b) eqn:H1; [destruct (o ofs) eqn:H2 | ]; econstructor; eassumption. Qed.

          Definition deltaMap_cases_analysis dmap b ofs H1 H2 H3 :Prop:=
            match deltaMap_dec dmap b ofs with
              | DMAPS df p A B => H1 df p A B
              | DNONE1 df A B => H2 df A B
              | DNONE2 A => H3 A 
            end.

          Definition deltaMap_cases_analysis' dmap b ofs H1 H2 :Prop:=
            match deltaMap_dec dmap b ofs with
              | DMAPS df p A B => H1 df p
              | DNONE1 df A B => H2
              | DNONE2 A => H2 
            end.

          Definition dmap_option_get (dmap:delta_map) b ofs: option (option permission) :=
            match dmap ! b with
              Some df => match df ofs with
                          Some operm => Some operm
                        | None => None
                        end
            | None => None
            end.
                          
          
          Lemma Disjoint_computeMap: forall pmap1 pmap2 dmap,
              (forall b ofs,
                  deltaMap_cases_analysis' dmap b ofs
                                           (fun _ p => permDisjoint p (pmap2 !! b ofs))
                                           (permDisjoint (pmap1 !! b ofs) (pmap2 !! b ofs))) ->
              permMapsDisjoint (computeMap pmap1 dmap) pmap2.
          Proof.
            intros. intros b0 ofs0.
            generalize (H b0 ofs0); clear H; unfold deltaMap_cases_analysis'.
            destruct (deltaMap_dec dmap b0 ofs0); intros H.
            -  rewrite (computeMap_1 _ _ _ _ e e0).
               destruct H as [k H3].
               exists k; assumption.
            - rewrite (computeMap_2 _ _ _ _ e e0).
              destruct H as [k H3].
              exists k; assumption.
            - rewrite (computeMap_3 _ _ _ _ e).
               destruct H as [k H3].
               exists k; assumption.
          Qed.
               
          (*virtue is disjoint from other threads. *)
          intros. rewrite DTP.gLockSetRes.
          apply Disjoint_computeMap. intros. 
          unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
          + unfold virtue in e.
            rewrite PTree.gmap in e. destruct ((snd (getCurPerm m)) ! b0); inversion e.
            clear e. rewrite <- H1 in e0.
            
            rewrite (virtue_some _ _ e0).
            erewrite MTCH_perm' with (MTCH:=MATCH).
            apply joins_permDisjoint.
            Lemma triple_joins_exists:
              forall (a b c ab: rmap),
                sepalg.join a b ab ->
                joins b c ->
                joins a c ->
                joins ab c.
            Proof.
              intros a b c ab Hab [bc Hbc] [ac Hac].
              destruct (triple_join_exists a b c ab bc ac Hab Hbc Hac).
              exists x; assumption.
            Qed.
            Lemma resource_at_joins:
              forall r1 r2,
                joins r1 r2 ->
                forall l,
                  joins (r1 @ l) (r2 @ l).
            Proof. intros r1 r2 [r3 HH] l.
                   exists (r3 @l); apply resource_at_join. assumption.
            Qed.

            apply resource_at_joins.
            eapply triple_joins_exists.
            eassumption.
            { eapply joins_comm. eapply JSEM.JuicyMachineLemmas.compatible_threadRes_lockRes_join.
              eassumption.
              apply His_unlocked.
            }
            { eapply JSEM.JuicyMachineLemmas.compatible_threadRes_join.
              eassumption.
              assumption.
            }
          +  inversion dinv0; eapply no_race; assumption.
          +  inversion dinv0; eapply no_race; assumption.
        - apply permMapsDisjoint_comm.
          apply Disjoint_computeMap. intros b0 ofs0. 
          unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
          + unfold virtue in e.
            rewrite PTree.gmap in e. destruct ((snd (getCurPerm m)) ! b0); inversion e.
            clear e. rewrite <- H0 in e0.
            rewrite (virtue_some _ _ e0).
            inversion MATCH.
            destruct (ident_eq b b0).
            subst b0; destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs +LKSIZE)).
            * erewrite DTP.gssLockSet.
              assert (Hadd_lock_res':=Hadd_lock_res).
              apply (resource_at_join _ _ _ (b, ofs0)) in 
                  Hadd_lock_res.

              
              assert (exists sh psh X, phi' @ (b, Int.intval ofs) = YES sh psh (LK LKSIZE) X).
              { apply (resource_at_join _ _ _ (b, Int.intval ofs )) in 
                    Hadd_lock_res'.
                rewrite HJcanwrite in Hadd_lock_res'.
                inversion Hadd_lock_res'.
                - exists rsh3, psh, (JSEM.pack_res_inv R) .
                  reflexivity.
                - exists rsh3, sh3, (JSEM.pack_res_inv R) .
                  reflexivity.
              }
              
             Lemma perm_inRangeOfLock: forall rm b ofs ofs0 sh psh n X,
                  rm @ (b, ofs) = YES sh psh (LK n) X -> 
                  Intv.In ofs0 (ofs, ofs + n) ->
                  perm_of_res (rm @ (b, ofs0)) = Some Nonempty.
              Proof.
                intros.
                destruct (zeq ofs ofs0).
                - subst ofs0; rewrite H; reflexivity.
                - assert (VALID:= phi_valid rm).
                  specialize (VALID b ofs). unfold "oo" in VALID.
                  rewrite H in VALID. simpl in VALID.
                  specialize (VALID  (ofs0 - ofs)).
                  assert (ineq: 0 < ofs0 - ofs < n).
                  generalize H0; clear - n0. unfold Intv.In; simpl. intros.  xomega.
                  apply VALID in ineq.
                  replace (ofs + (ofs0 - ofs)) with ofs0 in ineq by xomega.
                  destruct (rm @ (b,ofs0)); inversion ineq.
                  reflexivity.
              Qed.
              destruct H2 as [sh3 [psh3 [X HH]]].
              rewrite (perm_inRangeOfLock _ _ _ _ _ _ _ _ HH).
              exists (Some Writable); reflexivity.
              assumption.
              apply i0.
            * {erewrite DTP.gsoLockSet_1.
               eapply join_permDisjoint.
               - apply resource_at_join; eassumption.
               - rewrite mtch_perm.
                 apply permMapsDisjoint_permDisjoint; apply permMapsDisjoint_comm.
                 inversion dinv. apply lock_set_threads. 
                 
               - assert (exists dres, DSEM.ThreadPool.lockRes ds (b,Int.intval ofs) = Some dres).
                 { specialize (mtch_locks (b, Int.intval ofs)).
                   rewrite His_unlocked in mtch_locks.
                   destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)); inversion mtch_locks.
                   exists l; reflexivity. }
                 destruct H2 as [dres H2].
                 rewrite (mtch_locksRes _ _ dres His_unlocked H2). 
                 inversion dinv. eapply lock_res_set. eassumption.
               - apply Intv.range_notin in n. apply n. unfold LKSIZE; simpl; xomega.
              }
            * { erewrite DTP.gsoLockSet_2 by assumption.
                eapply join_permDisjoint.
                - apply resource_at_join; eassumption.
                - rewrite mtch_perm.
                  apply permMapsDisjoint_permDisjoint; apply permMapsDisjoint_comm.
                  inversion dinv. apply lock_set_threads. 
                  
                - assert (exists dres, DSEM.ThreadPool.lockRes ds (b,Int.intval ofs) = Some dres).
                  { specialize (mtch_locks (b, Int.intval ofs)).
                    rewrite His_unlocked in mtch_locks.
                  destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)); inversion mtch_locks.
                  exists l; reflexivity. }
                  destruct H2 as [dres H2].
                  rewrite (mtch_locksRes _ _ dres His_unlocked H2). 
                  inversion dinv. eapply lock_res_set. eassumption.
              }
          + destruct (ident_eq b b0).
            subst b0; destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs +LKSIZE)).
            * rewrite DTP.gssLockSet.
              assert (Hadd_lock_res':=Hadd_lock_res).
              apply (resource_at_join _ _ _ (b, ofs0)) in 
                  Hadd_lock_res.

              inversion MATCH. erewrite <- mtch_perm.
              instantiate(1:=Hi). (*Why am I needing this now. It wasn't the case before! *)
              rewrite (perm_inRangeOfLock _ _ _ _ _ _ _ _ HJcanwrite).
              exists (Some Writable); reflexivity.
              assumption.
              apply i0.
            * { erewrite DTP.gsoLockSet_1.
                inversion dinv. eapply permDisjoint_comm.
                apply permMapsDisjoint_permDisjoint.
                apply lock_set_threads.
                 apply Intv.range_notin in n. apply n. unfold LKSIZE; simpl; xomega.
              }
            * { erewrite DTP.gsoLockSet_2 by assumption.
                inversion dinv. eapply permDisjoint_comm.
                apply permMapsDisjoint_permDisjoint.
                apply lock_set_threads.
              }
          + destruct (ident_eq b b0).
            subst b0; destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs +LKSIZE)).
            * rewrite DTP.gssLockSet.
              assert (Hadd_lock_res':=Hadd_lock_res).
              apply (resource_at_join _ _ _ (b, ofs0)) in 
                  Hadd_lock_res.
              inversion MATCH. erewrite <- mtch_perm.
              instantiate(1:=Hi).
              rewrite (perm_inRangeOfLock _ _ _ _ _ _ _ _ HJcanwrite).
              exists (Some Writable); reflexivity.
              assumption.
              apply i0.
            * { erewrite DTP.gsoLockSet_1.
                inversion dinv. eapply permDisjoint_comm.
                apply permMapsDisjoint_permDisjoint.
                apply lock_set_threads.
                 apply Intv.range_notin in n. apply n. unfold LKSIZE; simpl; xomega.
              }
            * { erewrite DTP.gsoLockSet_2 by assumption.
                inversion dinv. eapply permDisjoint_comm.
                apply permMapsDisjoint_permDisjoint.
                apply lock_set_threads.
              }
(*        There was a proof here...  *)
        - intros l pmap0 Lres. apply permMapsDisjoint_comm.
          apply Disjoint_computeMap. intros b0 ofs0. 
          unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
          + unfold virtue in e.
            rewrite PTree.gmap in e. destruct ((snd (getCurPerm m)) ! b0); inversion e.
            clear e. rewrite <- H0 in e0.
            rewrite (virtue_some _ _ e0).
            destruct (AMap.E.eq_dec (b, Int.intval ofs) l).
            * destruct l; inversion e; subst.
              rewrite DTP.gssLockRes in Lres.
              inversion Lres; subst.
              rewrite empty_map_spec.
              apply permDisjoint_comm.
              exists (perm_of_res (phi' @ (b0, ofs0))); reflexivity.
            * rewrite DTP.gsoLockRes in Lres; try assumption.
              assert (exists smthng, JTP.lockRes js l = Some smthng).
              { inversion MATCH. specialize (mtch_locks l).
                rewrite Lres in mtch_locks.
                destruct (JTP.lockRes js l); inversion mtch_locks.
                exists l0; reflexivity. }
              destruct H as [smthng H].
              inversion MATCH.
              destruct smthng.
              (*smthng = Some r*)
              rewrite <- (mtch_locksRes _ _ _ H Lres b0 ofs0).
              apply joins_permDisjoint.
              apply resource_at_joins.
              eapply (juicy_mem_lemmas.components_join_joins ).
              apply Hadd_lock_res.
              inversion Hcompatible.
              eapply JSEM.JuicyMachineLemmas.compatible_threadRes_lockRes_join; eassumption.
              eapply JSEM.compatible_lockRes_join; eassumption.
              (*smthng = None*)
              rewrite (mtch_locksEmpty _ _ H Lres).
              rewrite empty_map_spec. apply permDisjoint_comm.
              exists (perm_of_res (phi' @ (b0, ofs0))); reflexivity.
              
          +  inversion dinv0; apply permDisjoint_comm;
            eapply lock_res_threads. eassumption.
          +  inversion dinv0. apply permDisjoint_comm;
            eapply lock_res_threads. eassumption.
      }
      { apply updLock_inv.
        - assumption. (*Another lemma for invariant.*)
        - cut ( exists p, DSEM.ThreadPool.lockRes ds (b, Int.intval ofs) = Some p).
          {
            intros HH i0 cnt ofs0 ineq. destruct HH as [p HH]; simpl.
            inversion dinv.
            
            destruct (zeq ofs0 (Int.intval ofs)).
            - specialize (lock_set_threads i0 cnt b (Int.intval ofs)).
              destruct lock_set_threads as [pu lst].
              rewrite DSEM.ThreadPool.lockSet_spec_1 in lst. 2: (rewrite HH; trivial).
              subst ofs0. exists pu; assumption.
            - (*other*)
              specialize (lockRes_valid b (Int.intval ofs)).
              rewrite HH in lockRes_valid.
              specialize (lock_set_threads i0 cnt b ofs0).
              destruct lock_set_threads as [pu lst].
              erewrite DSEM.ThreadPool.lockSet_spec_2 in lst. 
              exists pu; assumption. unfold LKSIZE in ineq; apply ineq.
              simpl. rewrite HH; constructor.
          }
          { inversion MATCH; subst. specialize (mtch_locks (b,Int.intval ofs)).
          rewrite His_unlocked in mtch_locks.
          destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)) eqn: AA; try solve[inversion mtch_locks].
          exists l. reflexivity. }
        - intros. apply empty_disjoint'.
        - apply permMapsDisjoint_comm; apply empty_disjoint'.
        - simpl; intros ofs0 ineq.
          rewrite empty_map_spec; exists (Some Writable); reflexivity.
        - intros. simpl. inversion dinv. apply lock_res_set in H.
          apply permMapsDisjoint_comm in H.
          cut (is_true(isSome( DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)))).
          { intros HH.
              specialize (H b ofs0).
            destruct (zeq ofs0 (Int.intval ofs)).
            - subst ofs0.
              rewrite DSEM.ThreadPool.lockSet_spec_1 in H; auto.
            - simpl.
              move H at bottom.
              erewrite DSEM.ThreadPool.lockSet_spec_2 in H; eauto.
          }
          { inversion MATCH; subst. specialize (mtch_locks (b, Int.intval ofs)).
            rewrite His_unlocked in mtch_locks. 
            rewrite <- mtch_locks; reflexivity. }
        - simpl; intros.
          cut (JSEM.ThreadPool.lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH.
            specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            clear - mtch_locks.
            destruct (DSEM.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; try reflexivity.
            - inversion mtch_locks.
            - assumption. }
          {(*the cut*)
            move HJcanwrite at bottom.
            destruct Hcmpt as [all_juice Hcmpt].
            inversion Hcmpt.
            unfold JSEM.juicyLocks_in_lockSet in jloc_in_set.
            eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            destruct juice_join.
            apply resource_at_join with (loc:=(b, Int.intval ofs)) in H0.
            rewrite HJcanwrite in H0.
            inversion H0.
            -
            symmetry in H7.
            apply jloc_in_set in H7.
            assert (VALID:= JSEM.compat_lr_valid Hcompatible).
            specialize (VALID b (Int.intval ofs)).
            unfold JSEM.ThreadPool.lockRes in VALID.
            destruct (AMap.find (elt:=juicy_machine.LocksAndResources.lock_info)
                                (b, Int.intval ofs) (JSEM.ThreadPool.lockGuts js)) eqn:AA;
              rewrite AA in H7; try solve[inversion H7].
            apply VALID. auto.
            -
            symmetry in H7.
            apply jloc_in_set in H7.
            assert (VALID:= JSEM.compat_lr_valid Hcompatible).
            specialize (VALID b (Int.intval ofs)).
            unfold JSEM.ThreadPool.lockRes in VALID.
            destruct (AMap.find (elt:=juicy_machine.LocksAndResources.lock_info)
                                (b, Int.intval ofs) (JSEM.ThreadPool.lockGuts js)) eqn:AA;
              rewrite AA in H7; try solve[inversion H7].
            apply VALID. auto.
          }
        - simpl. intros ofs0 ineq. move HJcanwrite at bottom.
          cut ( JSEM.ThreadPool.lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH.
            specialize (mtch_locks (b, ofs0)). rewrite HH in mtch_locks.
            destruct (DSEM.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks; auto. }
          {
            destruct (JSEM.ThreadPool.lockRes js (b, ofs0)) eqn:MAP; try reflexivity. exfalso.
            move HJcanwrite at bottom.
            destruct Hcmpt as [all_juice Hcmpt].
            inversion Hcmpt.
            unfold JSEM.juicyLocks_in_lockSet in jloc_in_set.
            eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            destruct juice_join.
            apply resource_at_join with (loc:=(b, Int.intval ofs)) in H.
            rewrite HJcanwrite in H.
            inversion H.
            -
            symmetry in H6. 
            apply jloc_in_set in H6.
            assert (VALID:= JSEM.compat_lr_valid Hcompatible).
            specialize (VALID b ofs0).
            rewrite MAP in VALID.
            apply VALID in ineq.
            move ineq at bottom.
            unfold JSEM.ThreadPool.lockRes in ineq; rewrite ineq in H6.
            inversion H6.
            -
            symmetry in H6. 
            apply jloc_in_set in H6.
            assert (VALID:= JSEM.compat_lr_valid Hcompatible).
            specialize (VALID b ofs0).
            rewrite MAP in VALID.
            apply VALID in ineq.
            move ineq at bottom.
            unfold JSEM.ThreadPool.lockRes in ineq; rewrite ineq in H6.
            inversion H6.
              
          }
      }
    - unfold ds''.
      apply match_st_age_tp_to.
        apply MTCH_updLockN.
        unfold ds'.
        apply MTCH_update; auto.
        intros.
        {
          (*Can turn this into a mini-lemma to show virtue is "correct" *)
          clear - MATCH Hi Hadd_lock_res Hcompatible Hcmpt His_unlocked.
          (* Showing virtue is correct *)
          unfold computeMap.
          unfold PMap.get; simpl.
          rewrite PTree.gcombine; auto.
          unfold virtue, inflated_delta; simpl.
          rewrite PTree.gmap.
          rewrite PTree.gmap1.
          unfold option_map at 2.
          destruct ((snd (Mem.mem_access m)) ! b0) eqn:valb0MEM; simpl.
          - (*Some 1*)
            destruct ((snd (DSEM.ThreadPool.getThreadR Htid')) ! b0) eqn:valb0D; simpl.
            + (*Some 2*)
              destruct (d_phi @ (b0, ofs0)) eqn:valb0ofs0; rewrite valb0ofs0; simpl; try solve[reflexivity].
                 destruct ((Share.EqDec_share t Share.bot)) eqn:isBot; simpl; try solve [reflexivity].
                   { subst. (*bottom share*)
                     simpl. inversion MATCH; subst.
                     unfold PMap.get in mtch_perm.
                     specialize (mtch_perm b0 ofs0 i Hi Htid'); rewrite valb0D in mtch_perm.
                     rewrite <- mtch_perm. f_equal.
                     clear - Hadd_lock_res valb0ofs0.
                     (*unfold sepalg.join, Join_rmap in Hadd_lock_res.*)
                     apply (resource_at_join _ _ _ (b0, ofs0)) in Hadd_lock_res.
                     rewrite valb0ofs0 in Hadd_lock_res.
                     inversion Hadd_lock_res; subst.
                     - inversion RJ. rewrite Share.lub_bot in H1. subst rsh1; reflexivity.
                     - inversion RJ. rewrite Share.lub_bot in H1. subst rsh1; reflexivity.
                   }

               +(* None 2*)
                 destruct (d_phi @ (b0, ofs0)) eqn:valb0ofs0; rewrite valb0ofs0; simpl; try solve[reflexivity].
                 destruct ((Share.EqDec_share t Share.bot)) eqn:isBot; simpl; try solve [reflexivity].
                  { subst. (*bottom share*)
                     simpl. inversion MATCH; subst.
                     unfold PMap.get in mtch_perm.
                     specialize (mtch_perm b0 ofs0 i Hi Htid'); rewrite valb0D in mtch_perm.
                     rewrite <- mtch_perm. f_equal.
                     clear - Hadd_lock_res valb0ofs0.
                     (*unfold sepalg.join, Join_rmap in Hadd_lock_res.*)
                     apply (resource_at_join _ _ _ (b0, ofs0)) in Hadd_lock_res.
                     rewrite valb0ofs0 in Hadd_lock_res.
                     inversion Hadd_lock_res; subst.
                     - inversion RJ. rewrite Share.lub_bot in H1. subst rsh1; reflexivity.
                     - inversion RJ. rewrite Share.lub_bot in H1. subst rsh1; reflexivity.
                  }
             - (*None 1*)
               destruct ((snd (DSEM.ThreadPool.getThreadR Htid')) ! b0) eqn:valb0D; simpl.
               inversion MATCH; subst.
               unfold PMap.get in mtch_perm.
               specialize (mtch_perm b0 ofs0 i Hi Htid'); rewrite valb0D in mtch_perm.
               pose (Hcompatible':= Hcompatible).
               apply JSEM.thread_mem_compatible in Hcompatible'.
               move Hcompatible at bottom. specialize (Hcompatible' i Hi).
               inversion Hcompatible'.
               specialize (acc_coh (b0, ofs0)).
               unfold max_access_at, access_at, PMap.get  in acc_coh; simpl in acc_coh.
               rewrite valb0MEM in acc_coh.
               simpl in acc_coh.
               rewrite mtch_perm in acc_coh.
               rewrite JSEM.Mem_canonical_useful in acc_coh. destruct (o ofs0); try solve[inversion acc_coh].
               + (*Some 1.1*)
                 (*TODO: This lemma should be moved, but don't know where yet. *)
                 Lemma blah: forall r, perm_of_res r = None ->
                                  r = NO Share.bot.
                 Proof.  intros. destruct r; try solve[reflexivity]; inversion H.
                         destruct (eq_dec t Share.bot); subst; try solve[reflexivity]; try solve[inversion H1].
                         destruct k; inversion H1.
                         apply perm_of_empty_inv in H1; destruct H1 as [A B] . subst t.
                         exfalso; eapply (juicy_mem_ops.Abs.pshare_sh_bot _ B).
                 Qed.
                 apply blah in mtch_perm.
                 apply (resource_at_join _ _ _ (b0, ofs0)) in Hadd_lock_res.
                 move Hadd_lock_res at bottom. rewrite mtch_perm in Hadd_lock_res.
                 apply join_unit1_e in Hadd_lock_res; try solve[ exact NO_identity].
                 rewrite <- Hadd_lock_res.
                 assert (Hcmpt':= Hcmpt).
                 apply JSEM.lock_mem_compatible in Hcmpt'.
                 apply Hcmpt' in His_unlocked.
                 inversion His_unlocked.
                 specialize (acc_coh0 (b0, ofs0)).
                 unfold max_access_at, access_at, PMap.get  in acc_coh0; simpl in acc_coh0.
                 rewrite valb0MEM in acc_coh0.
                 rewrite JSEM.Mem_canonical_useful in acc_coh0.
                 destruct (perm_of_res (d_phi @ (b0, ofs0))); try solve[inversion acc_coh0].
                 reflexivity.

               + (*None 1.2*)
                 
                 apply (MTCH_compat _ _ _ MATCH) in Hcompatible.
                 rewrite (@threads_canonical _ m _ Htid'); [|eapply MTCH_compat; eassumption].
                 replace (phi' @ (b0, ofs0)) with (NO Share.bot).
                 simpl.
                 rewrite if_true; reflexivity.
                 apply (resource_at_join _ _ _ (b0, ofs0)) in Hadd_lock_res.
                 replace (JSEM.ThreadPool.getThreadR Hi @ (b0, ofs0)) with (NO Share.bot) in Hadd_lock_res.
                 replace (d_phi @ (b0, ofs0)) with (NO Share.bot) in Hadd_lock_res.
                 * apply join_unit1_e in Hadd_lock_res.
                 assumption.
                 apply NO_identity.
                 * clear Hadd_lock_res.
                   symmetry.
                   
                   destruct
                     (JSEM.JuicyMachineLemmas.compatible_lockRes_cohere _
                                                His_unlocked
                                                Hcmpt).
                   clear - acc_coh valb0MEM.
                   unfold JSEM.access_cohere' in acc_coh.
                   unfold max_access_at, access_at in acc_coh.
                   specialize (acc_coh (b0, ofs0)).
                   simpl in acc_coh.
                   unfold PMap.get in acc_coh. rewrite valb0MEM in acc_coh.
                   rewrite JSEM.Mem_canonical_useful in acc_coh.
                   destruct (perm_of_res (d_phi @ (b0, ofs0))) eqn:AA.
                   inversion acc_coh.
                   apply blah in AA. assumption.
                 * symmetry.
                   destruct
                     (JSEM.JuicyMachineLemmas.compatible_threadRes_cohere Hi
                                                  Hcmpt).
                   clear - acc_coh valb0MEM.
                   unfold JSEM.access_cohere' in acc_coh.
                   unfold max_access_at, access_at in acc_coh.
                   specialize (acc_coh (b0, ofs0)).
                   simpl in acc_coh.
                   unfold PMap.get in acc_coh. rewrite valb0MEM in acc_coh.
                   rewrite JSEM.Mem_canonical_useful in acc_coh.
                   destruct  (perm_of_res (JSEM.ThreadPool.getThreadR Hi @ (b0, ofs0))) eqn:AA.
                   inversion acc_coh.
                   apply blah in AA. assumption.
        }
           
         - assert (H: exists l, DSEM.ThreadPool.lockRes ds (b, Int.intval ofs) = Some l).
           { inversion MATCH; subst.
             specialize (mtch_locks (b, (Int.intval ofs) )).
             rewrite His_unlocked in mtch_locks.
             destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)); try solve[inversion mtch_locks]. exists l; reflexivity. }
           destruct H as [l dlockRes].
           econstructor 1.
           10: reflexivity.
           10: now unfold ds'', ds'; repeat f_equal; apply proof_irr.
           + assumption.
           + eapply MTCH_getThreadC; eassumption.
           + eassumption.
           + eapply MTCH_compat; eassumption.
           + instantiate(1:=(restrPermMap
               (JSEM.mem_compatible_locks_ltwritable Hcompatible))). 
             apply restrPermMap_ext.
             intros b0.
             inversion MATCH; subst.
             extensionality ofs0.
             symmetry; apply MTCH_lockSet. assumption.
           + assumption.
           + assumption.
           + exact dlockRes.
           + { constructor.
               - intros b0 ofs0 H.
                 destruct (virtue ! b0) eqn:vb0.
                 destruct (o ofs0) eqn:oofs0.
                 + rewrite (computeMap_1 _ _ _  _ vb0 oofs0) in H.
                   unfold virtue in vb0. rewrite PTree.gmap in vb0.
                   unfold inflated_delta in vb0.
                   destruct ((snd (getCurPerm m)) ! b0) ; inversion vb0.
                   rewrite <- H1 in oofs0. clear H1.
                   replace o0 with (perm_of_res (phi' @ (b0, ofs0))) in H. clear oofs0.
                   Lemma preservationOfReads1: forall r1 r2 r3,
                       sepalg.join r1 r2 r3 ->
                       Mem.perm_order' (perm_of_res r3) Readable ->
                       Mem.perm_order' (perm_of_res r1) Readable \/
                       Mem.perm_order' (perm_of_res r2) Readable.
                   Proof. intros  ? ? ? J po.
                          inversion J; subst; simpl in po; try inversion po; simpl.
                          - destruct (eq_dec rsh3 Share.bot); inversion po.
                          - destruct k; try inversion po.
                            unfold perm_of_sh. destruct (eq_dec sh pfullshare).
                            destruct (eq_dec rsh1 Share.top).
                            subst; simpl. rewrite if_true. left; constructor. reflexivity.
                            subst; simpl. rewrite if_true. left; constructor. reflexivity.
                            subst; simpl. rewrite if_false.
                            rewrite if_false. simpl; left; constructor.
                            intros HH.
                            eapply juicy_mem_ops.Abs.pshare_sh_bot. eassumption.
                            intros HH. apply n.
                            apply shares.top_pfullshare; assumption.
                          - destruct k; try inversion po.
                            unfold perm_of_sh. destruct (eq_dec sh pfullshare).
                            destruct (eq_dec rsh2 Share.top).
                            right; subst; simpl. rewrite if_true. constructor. reflexivity.
                            right; subst; simpl. rewrite if_true. constructor. reflexivity.
                            right; subst; simpl. rewrite if_false.
                            rewrite if_false. simpl; constructor.
                            intros HH.
                            eapply juicy_mem_ops.Abs.pshare_sh_bot. eassumption.
                            intros HH. apply n.
                            apply shares.top_pfullshare; assumption.
                          - destruct k; try inversion po.
                            unfold perm_of_sh. destruct (eq_dec sh1 pfullshare).
                            destruct (eq_dec rsh1 Share.top).
                            subst; simpl. rewrite if_true. left; constructor. reflexivity.
                            subst; simpl. rewrite if_true. left; constructor. reflexivity.
                            subst; simpl. rewrite if_false.
                            rewrite if_false. simpl; left; constructor.
                            intros HH.
                            eapply juicy_mem_ops.Abs.pshare_sh_bot. eassumption.
                            intros HH. apply n.
                            apply shares.top_pfullshare; assumption.
                   Qed.
                   inversion MATCH.
                   erewrite <- mtch_perm. erewrite <- mtch_locksRes.
                   eapply preservationOfReads1. apply resource_at_join. eassumption.
                   assumption.
                   eassumption.
                   eassumption.
                   { (*prove the replacement above*)
                     clear - oofs0.
                     destruct (d_phi @ (b0, ofs0));
                       try ( destruct ((Share.EqDec_share t Share.bot))); (*For the no case*)
                       inversion oofs0; try reflexivity.
                   }
                 + erewrite (computeMap_2) in H; try left; eassumption.
                 + rewrite (computeMap_3) in H; try left; eassumption.
               - intros. rewrite empty_map_spec.
                 simpl. destruct ((l !! b0 ofs0)); constructor.
             }
    }  
    
    (* step_release *)
    {
      
    assert (Htid':= MTCH_cnt MATCH Hi).
    pose (inflated_delta:=
            fun loc => match (d_phi @ loc ) with
                      NO s => if Share.EqDec_share s Share.bot then None else Some ( perm_of_res (phi' @ loc))
                    | _ => Some (perm_of_res (phi' @ loc))
                    end).
      pose (virtue:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta (block, ofs))) (snd (getMaxPerm m)) ).
    pose (ds':= DSEM.ThreadPool.updThread Htid' (Kresume c Vundef)
                                          (computeMap
                                             (DSEM.ThreadPool.getThreadR Htid') virtue)).
    pose (ds'':= DSEM.ThreadPool.updLockSet ds' (b, Int.intval ofs)
                                            (JSEM.juice2Perm d_phi m)).
    
    assert (virtue_spec: forall b0 ofs0, perm_of_res (phi' @ (b0, ofs0)) =
                                    (computeMap (DSEM.ThreadPool.getThreadR Htid') virtue) !! b0 ofs0).
    {
      intros b0 ofs0.
           destruct (virtue ! b0) eqn:VIRT.
           destruct (o ofs0) eqn:O.
           - erewrite computeMap_1; try eassumption.
             unfold virtue in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0); inversion VIRT.
             unfold inflated_delta in H0. rewrite <- H0 in O.
             clear VIRT H0.
             replace o0 with (perm_of_res (phi' @ (b0, ofs0))).
             + reflexivity.
             + destruct (d_phi @ (b0, ofs0)) eqn:AA; rewrite AA in O; try destruct (Share.EqDec_share t Share.bot);
               inversion O; reflexivity.
           - erewrite computeMap_2; try eassumption.
             unfold virtue in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0); inversion VIRT.
             unfold inflated_delta in H0. rewrite <- H0 in O.
             apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_lock_res.
             move Hrem_lock_res at bottom.
             replace (d_phi @ (b0, ofs0)) with (NO Share.bot) in Hrem_lock_res.
             + inversion MATCH; rewrite <- mtch_perm with (Htid:= Hi).
               f_equal.
               Lemma join_NO_bot: forall x y,
                   sepalg.join (NO Share.bot) x y -> x = y.
               Proof. intros ? ? J.
                      inversion J; f_equal;
                      eapply sepalg.join_eq;
                      try apply bot_join_eq;
                      assumption.
               Qed.
               apply join_NO_bot; assumption.
             + destruct (d_phi @ (b0, ofs0)) eqn:HH; rewrite HH in O; try solve[inversion O].
               destruct ((Share.EqDec_share t Share.bot)); try solve[ inversion O].
               subst; reflexivity.
           - erewrite computeMap_3; try eassumption.
             unfold virtue in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m) !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DSEM.ThreadPool.getThreadR Htid') !! b0 ofs0) with
             (perm_of_res ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply JSEM.JuicyMachineLemmas.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'. unfold JSEM.access_cohere' in acc_coh.
               specialize (acc_coh (b0,ofs0)).
               unfold max_access_at, access_at in acc_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in acc_coh.
               Lemma po_None1: forall p, Mem.perm_order'' None p -> p = None.
               Proof. intros. simpl in H. destruct p; inversion H; reflexivity. Qed.
               apply po_None1 in acc_coh.
               move Hrem_lock_res at bottom.
               apply join_comm in Hrem_lock_res.
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_lock_res.
               apply join_join_sub in Hrem_lock_res.
               assert (HH:= juicy_mem_lemmas.po_join_sub _ _ Hrem_lock_res).
               rewrite acc_coh in HH. rewrite acc_coh.
               apply po_None1 in HH. assumption.
             + inversion MATCH; rewrite mtch_perm; reflexivity.
    }
    
    exists ds'',  (JSEM.Events.release (b, Int.intval ofs)
                                  (Some (JSEM.juice2Perm d_phi m, virtue))).
    split; [|split].
    - unfold ds''.
      cut (DSEM.invariant ds').
      { intros dinv'.
        apply updLock_inv.
        - assumption. (*Another lemma for invariant.*)
        - cut ( exists p, DSEM.ThreadPool.lockRes ds' (b, Int.intval ofs) = Some p).
          { intros HH i0 cnt ofs0 ineq. destruct HH as [p HH].
            inversion dinv.

            destruct (NatTID.eq_tid_dec i0 i).
            - subst i0; rewrite DTP.gssThreadRes.
              rewrite <- virtue_spec.
              simpl.
              destruct Hcompatible as [allj Hcompatible].
              inversion Hcompatible.

              (*By using the joins transfer the property to the join
               * of all juice *)
              eapply permDisjoint_comm.
              eapply permDisjoint_sub.
              eapply resource_at_join_sub.
              eapply join_sub_trans.
              eapply join_join_sub; eapply join_comm.
              eassumption.
              eapply JSEM.compatible_threadRes_sub; eassumption.
              
              move His_locked at bottom.
              unfold JSEM.ThreadPool.lockRes in His_locked.
              specialize (lset_in_juice (b, Int.intval ofs) ltac:(rewrite His_locked; constructor)).
              destruct lset_in_juice as [sh' [psh' [P MAP]]].
              assert (VALID:= phi_valid allj).
              specialize (VALID b (Int.intval ofs)).
              unfold "oo" in VALID.
              rewrite MAP in VALID; simpl in VALID.
              destruct (zeq ofs0 (Int.intval ofs)).
              + subst. rewrite MAP; exists (Some Writable); reflexivity.
              + 
                assert (ineq': 0 < (ofs0 - Int.intval ofs) < juicy_machine.LKSIZE ).
                {clear - ineq n. destruct ineq; simpl in *.
                 replace (juicy_machine.LKSIZE) with LKSIZE by auto.  omega. }
                apply VALID in ineq'.
                replace (Int.intval ofs + (ofs0 - Int.intval ofs)) with ofs0 in ineq' by xomega.
                destruct (allj @ (b, ofs0)); inversion ineq'.
                exists (Some Writable); reflexivity.
              
              
            - rewrite DTP.gsoThreadRes; auto.
              destruct (zeq ofs0 (Int.intval ofs)).
              + specialize (lock_set_threads i0 cnt b (Int.intval ofs)).
                destruct lock_set_threads as [pu lst].
                rewrite DSEM.ThreadPool.lockSet_spec_1 in lst. 
                subst ofs0. exists pu; assumption.
                unfold ds' in HH; erewrite DTP.gsoThreadLPool in HH.
                rewrite HH; constructor.
              + (*other*)
                specialize (lockRes_valid b (Int.intval ofs)).
                unfold ds' in HH; erewrite DTP.gsoThreadLPool in HH.
                rewrite HH in lockRes_valid.
                specialize (lock_set_threads i0 cnt b ofs0).
                destruct lock_set_threads as [pu lst].
                erewrite DSEM.ThreadPool.lockSet_spec_2 in lst. 
                exists pu; assumption. unfold LKSIZE in ineq; apply ineq.
                simpl. rewrite HH; constructor.
          }
          { inversion MATCH; subst. specialize (mtch_locks (b,Int.intval ofs)).
          rewrite His_locked in mtch_locks.
          destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)) eqn: AA; try solve[inversion mtch_locks].
          exists l; assumption. }
        - intros.
          assert (dphi_coh: JSEM.access_cohere' m d_phi).
          {  (* *)
            destruct Hcompatible as [all_juice Hcompatible].
            eapply access_cohere_sub' with (phi1:=all_juice).
            - inversion Hcompatible. apply JSEM.acc_coh; assumption.
            - inversion Hcompatible.
              apply join_sub_trans with (b0:=(JSEM.ThreadPool.getThreadR Hi)).
              + exists phi'. apply Hrem_lock_res.
              + apply JSEM.compatible_threadRes_sub; assumption.
          }
          { destruct (NatTID.eq_tid_dec i i0).
            - subst i0. rewrite (DTP.gssThreadRes).
              apply permMapsDisjoint_comm.
              apply Disjoint_computeMap; intros b0 ofs0.
              unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
              + unfold virtue in e; rewrite PTree.gmap in e.
                destruct ((snd (getMaxPerm m)) ! b0) eqn:CURb0; inversion e.
                unfold inflated_delta in H0.
                rewrite <- H0 in e0.
                assert (HH: p = perm_of_res (phi' @ (b0, ofs0))).
                { destruct (d_phi @ (b0, ofs0)); try solve[inversion e0; reflexivity].
                  destruct (proj_sumbool (Share.EqDec_share t Share.bot)); inversion e0; reflexivity. }
                rewrite HH.
                rewrite <- JSEM.juic2Perm_correct.
                apply joins_permDisjoint. apply resource_at_joins.
                eapply joins_comm; eapply join_joins; exact Hrem_lock_res.
                assumption.
              + rewrite <- JSEM.juic2Perm_correct.
                assert (HH: (d_phi @ (b0, ofs0)) = NO Share.bot).
                { unfold virtue in e.
                  rewrite PTree.gmap in e.
                  destruct ((snd (getMaxPerm m)) ! b0); inversion e. (* solves one of the subgoals*)
                  rewrite <- H0 in e0.
                  unfold inflated_delta in e0.
                  destruct (d_phi @ (b0, ofs0)); try solve[inversion e0].
                  destruct ((Share.EqDec_share t Share.bot)) eqn:TT; try solve[inversion e0].
                  subst t; reflexivity. }
                rewrite HH. simpl; rewrite if_true.
                apply permDisjoint_comm; apply permDisjoint_None. reflexivity.
                assumption.
              + unfold virtue in e.
                rewrite PTree.gmap in e.
                destruct ((snd (getMaxPerm m)) ! b0) eqn:AA; inversion e.
                simpl in AA. rewrite PTree.gmap1 in AA.
                destruct ((snd (Mem.mem_access m)) ! b0) eqn:BB; inversion AA.
                simpl in AA.
                assert (MAA_none: max_access_at m (b0, ofs0) = None).
                { unfold max_access_at, access_at.
                  unfold PMap.get. rewrite BB.
                  simpl. apply JSEM.Mem_canonical_useful. }
                replace ((DSEM.ThreadPool.getThreadR Htid') !! b0 ofs0) with (max_access_at m (b0, ofs0)).
                * rewrite MAA_none.  exists ((JSEM.juice2Perm d_phi m) !! b0 ofs0); reflexivity.
                * { rewrite MAA_none.
                    destruct Hcompatible as [x Hcompatible].
                    inversion Hcompatible.
                    assert (acc_coh:= JSEM.acc_coh all_cohere).
                    specialize (acc_coh (b0, ofs0)).
                    rewrite MAA_none in acc_coh.
                    apply po_trans with (c:=(DSEM.ThreadPool.getThreadR Htid') !! b0 ofs0) in acc_coh.
                    - apply po_None1 in acc_coh. symmetry; assumption.
                    - erewrite MTCH_perm' with (MTCH:=MATCH).
                      apply juicy_mem_lemmas.po_join_sub.
                      apply resource_at_join_sub.
                      apply JSEM.compatible_threadRes_sub.
                      assumption.
                  }
            - rewrite (DTP.gsoThreadRes); try assumption.
              apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
              rewrite <- JSEM.juic2Perm_correct.
            erewrite MTCH_perm' with (MTCH:=MATCH).
              eapply permDisjoint_sub.
              apply resource_at_join_sub.
              exists  phi'. eassumption.
              apply joins_permDisjoint.
              apply resource_at_joins.
              eapply compatible_threadRes_join; eassumption.
              assumption.
          }
        - rewrite DTP.gsoThreadLock. apply permDisjoint_permMapsDisjoint.
          intros b0 ofs0.
          rewrite <- JSEM.juic2Perm_correct.
          inversion MATCH. apply permDisjoint_comm.
          apply permDisjoint_sub with (r1:=(JSEM.ThreadPool.getThreadR Hi) @ (b0, ofs0)). eapply resource_at_join_sub.
          exists phi'; assumption.
          rewrite mtch_perm. apply permDisjoint_comm; apply permMapsDisjoint_permDisjoint.
          inversion dinv. apply lock_set_threads.
          apply access_cohere_sub' with (phi1:= (JSEM.ThreadPool.getThreadR Hi)).
          destruct Hcompatible as [all_juice Hcompatible].
          inversion Hcompatible.
          apply access_cohere_sub' with (phi1:= all_juice).
          apply JSEM.acc_coh; assumption.
          apply JSEM.compatible_threadRes_sub; assumption.
          eexists; eassumption.
        - simpl.
          assert (JOIN:= Hrem_lock_res).
          apply (resource_at_join _ _ _ (b, (Int.intval ofs))) in
              Hrem_lock_res.
          rewrite HJcanwrite in Hrem_lock_res.
          simpl in Hrem_lock_res.
          intros ofs0 ineq.
          
          (*cut ((JSEM.juice2Perm d_phi m) !! b ofs0 = None \/
               (JSEM.juice2Perm d_phi m) !! b ofs0 = Some Nonempty).
          + intros HH; destruct HH as [A | A]; rewrite A;
            exists (Some Writable); reflexivity. *)
          
          + rewrite <- JSEM.juic2Perm_correct.
            * { eapply permDisjoint_comm; eapply permDisjoint_sub.
                eapply join_join_sub. eapply resource_at_join; eassumption.
                destruct (zeq ofs0 (Int.intval ofs)).
                - subst ofs0. rewrite HJcanwrite. exists (Some Writable); reflexivity.
                - assert (VALID:= phi_valid (JSEM.ThreadPool.getThreadR Hi)).
                  specialize (VALID b (Int.intval ofs)).
                  unfold "oo" in VALID.
                  rewrite HJcanwrite in VALID. simpl in VALID.
                  cut (0<ofs0 - (Int.intval ofs) < juicy_machine.LKSIZE)%Z.
                  { intros HH; apply VALID in HH. replace (Int.intval ofs + (ofs0 - Int.intval ofs)) with ofs0 in HH.
                    destruct ((JSEM.ThreadPool.getThreadR Hi @ (b, ofs0))); inversion HH.
                    exists (Some Writable); reflexivity.
                    xomega. }
                  { unfold juicy_machine.LKSIZE; simpl. unfold LKSIZE in ineq; simpl in ineq.
                    clear - n ineq; unfold Intv.In in ineq; simpl in ineq; omega. }
              }
              
            * { destruct Hcompatible as [allj Hcompatible].
              inversion Hcompatible. inversion all_cohere.
              eapply access_cohere_sub'; eauto.
              eapply join_sub_trans.
              eapply join_join_sub. move JOIN at bottom. eassumption.
              eapply JSEM.compatible_threadRes_sub; assumption.
            }
        - simpl; intros; simpl.
          assert (exists r, JSEM.ThreadPool.lockRes js l = Some r).
          { rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool in H.
            inversion MATCH. specialize (mtch_locks l); rewrite H in mtch_locks.
            destruct (JSEM.ThreadPool.lockRes js l) eqn:AA; inversion mtch_locks.
            exists l0; reflexivity. }
          destruct H1 as [l0 H1].
          destruct l0.
          + inversion MATCH. erewrite <- mtch_locksRes; eauto.
            apply permDisjoint_comm.
            eapply compatible_threadRes_lockRes_join with (cnti:=Hi) in H1; eauto.
            apply resource_at_joins with (l:= (b, ofs0)) in H1.
            destruct (zeq ofs0 (Int.intval ofs)).
            * subst ofs0. rewrite HJcanwrite in H1. inversion H1.
              { inversion H4; exists (Some Writable); auto.
                simpl. destruct (eq_dec rsh2 Share.bot); reflexivity. }
            * assert (VALID:= phi_valid (JSEM.ThreadPool.getThreadR Hi)).
              specialize (VALID b (Int.intval ofs)).
              unfold "oo" in VALID.
              rewrite HJcanwrite in VALID. simpl in VALID.
              cut (0<ofs0 - (Int.intval ofs) < juicy_machine.LKSIZE)%Z.
              { intros HH; apply VALID in HH. replace (Int.intval ofs + (ofs0 - Int.intval ofs)) with ofs0 in HH by omega.
                move H1 at bottom.
                destruct ((JSEM.ThreadPool.getThreadR Hi @ (b, ofs0))); inversion HH; subst k;
                destruct H1 as [x H1]; inversion H1;
                exists (Some Writable); simpl.
                destruct (eq_dec rsh2 Share.bot ); reflexivity.
                reflexivity. }
              { clear - H0 n. inversion H0; simpl in *.
              replace juicy_machine.LKSIZE with LKSIZE by reflexivity; omega.
               }
          + inversion MATCH.
            replace pmap0 with empty_map.
            * rewrite empty_map_spec. exists (Some Writable); reflexivity.
            * symmetry; eapply mtch_locksEmpty; eauto.
        - simpl; intros ofs0 ineq.
          rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          cut (JuicyMachine.SIG.ThreadPool.lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH. specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            destruct (DSEM.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks.
            assumption. }
          { destruct Hcompatible as [allj Hcompatible].
            inversion Hcompatible.
            assert (VALID:= JSEM.compat_lr_valid Hcmpt).
            specialize (VALID b (Int.intval ofs)).
            eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            eapply resource_at_join_sub with (l:=(b,Int.intval ofs)) in juice_join.
            rewrite HJcanwrite in juice_join.
            destruct juice_join as [x HH].
            inversion HH.

            - symmetry in H.
            apply jloc_in_set in H.
            destruct (JSEM.ThreadPool.lockRes js (b, Int.intval ofs)) eqn:AA;
              try solve [unfold JSEM.ThreadPool.lockRes in AA; rewrite AA in H; inversion H].
            inversion ineq.
            apply VALID; auto. 
          - unfold JSEM.ThreadPool.lockRes in VALID. move VALID at bottom.
            
             symmetry in H5.
              apply jloc_in_set in H5.
              destruct (JSEM.ThreadPool.lockRes js (b, Int.intval ofs)) eqn:BB;
                try solve [unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in H5; inversion H5].
              unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in VALID.
              apply VALID; auto. 
          }
        - simpl; intros ofs0 ineq.
          rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          cut (JuicyMachine.SIG.ThreadPool.lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH. specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            destruct (DSEM.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks.
            assumption. }
          { destruct (JuicyMachine.SIG.ThreadPool.lockRes js (b, ofs0)) eqn:AA; try reflexivity. exfalso.
            destruct Hcompatible as [allj Hcompatible].
            inversion Hcompatible.
            assert (VALID:= JSEM.compat_lr_valid Hcmpt).
            specialize (VALID b ofs0).
            rewrite AA in VALID.
            apply VALID in ineq.
            eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            eapply resource_at_join_sub with (l:=(b,Int.intval ofs)) in juice_join.
            rewrite HJcanwrite in juice_join.
            destruct juice_join as [x HH].
            inversion HH.

            - symmetry in H.
            apply jloc_in_set in H.
            destruct (JSEM.ThreadPool.lockRes js (b, Int.intval ofs)) eqn:BB.
              + inversion ineq.
              + unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in H; inversion H.
            - symmetry in H5.
              apply jloc_in_set in H5.
              destruct (JSEM.ThreadPool.lockRes js (b, Int.intval ofs)) eqn:BB;
                try solve [unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in H5; inversion H5].
              inversion ineq. 
          }
            
      }
      { (*Proof DSEM.invariant ds'*)
        apply updThread_inv.
        - assumption.
        - intros.
          apply Disjoint_computeMap.
          intros.
          unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
          + unfold virtue in e. rewrite PTree.gmap in e.
            destruct ((snd (getMaxPerm m)) ! b0); inversion e.
            rewrite <- H1 in e0.
            unfold inflated_delta in e0.
            replace p with (perm_of_res (phi' @ (b0, ofs0))).
            { inversion MATCH. rewrite <- (mtch_perm b0 ofs0 j (mtch_cnt' j cnt) _).
              apply joins_permDisjoint. apply resource_at_joins.
              eapply (join_sub_joins_trans ).
              apply join_comm in Hrem_lock_res.
              apply (join_join_sub Hrem_lock_res).
              eapply compatible_threadRes_join; eassumption. }
            { destruct (d_phi @ (b0, ofs0));
              [destruct (Share.EqDec_share t Share.bot) | |]; inversion e0;
              reflexivity. }
          +  inversion MATCH.
             rewrite <- (mtch_perm b0 ofs0 _ (mtch_cnt' _ Htid'));
               rewrite <- (mtch_perm b0 ofs0 _ (mtch_cnt' _ cnt)).
             apply joins_permDisjoint;  apply resource_at_joins.
             eapply compatible_threadRes_join; eassumption.
          + inversion MATCH.
             rewrite <- (mtch_perm b0 ofs0 _ (mtch_cnt' _ Htid'));
               rewrite <- (mtch_perm b0 ofs0 _ (mtch_cnt' _ cnt)).
             apply joins_permDisjoint;  apply resource_at_joins.
             eapply compatible_threadRes_join; eassumption.
        - intros. apply permMapsDisjoint_comm.

          apply Disjoint_computeMap.
          intros.

          cut (permDisjoint ((DSEM.ThreadPool.getThreadR Htid') !! b0 ofs0)
                            ((DSEM.ThreadPool.lockSet ds) !! b0 ofs0)).
          { intros CUT.
            unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
            + unfold virtue in e. rewrite PTree.gmap in e.
              destruct ((snd (getMaxPerm m)) ! b0); inversion e.
              rewrite <- H0 in e0.
              unfold inflated_delta in e0.
              replace p with (perm_of_res (phi' @ (b0, ofs0))).
              {
                apply (@permDisjoint_sub ((JSEM.ThreadPool.getThreadR Hi) @ (b0, ofs0)) ).
                apply resource_at_join_sub.
                apply join_comm in Hrem_lock_res; apply (join_join_sub Hrem_lock_res).
                inversion MATCH. rewrite mtch_perm; assumption.
              }
              { destruct (d_phi @ (b0, ofs0));
                [destruct (Share.EqDec_share t Share.bot) | |]; inversion e0;
                reflexivity. }
            + assumption.
            + assumption. }

        { apply permDisjoint_comm.
          apply permMapsDisjoint_permDisjoint.
          inversion dinv. apply lock_set_threads. }

        - intros.
          intros. apply permMapsDisjoint_comm.
          apply Disjoint_computeMap.
          intros.
          cut (permDisjoint ((DSEM.ThreadPool.getThreadR Htid') !! b0 ofs0)
                            (pmap0 !! b0 ofs0)).
          { intros CUT.
            unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
            + unfold virtue in e. rewrite PTree.gmap in e.
              destruct ((snd (getMaxPerm m)) ! b0); inversion e.
              rewrite <- H1 in e0.
              unfold inflated_delta in e0.
              replace p with (perm_of_res (phi' @ (b0, ofs0))).
              { inversion MATCH.
                apply (@permDisjoint_sub ((JSEM.ThreadPool.getThreadR Hi) @ (b0, ofs0))).
                apply resource_at_join_sub.
                apply join_comm in Hrem_lock_res; apply (join_join_sub Hrem_lock_res).
                rewrite mtch_perm.
                inversion dinv.
                apply CUT.
              }
              { destruct (d_phi @ (b0, ofs0));
                [destruct (Share.EqDec_share t Share.bot) | |]; inversion e0;
                reflexivity. }
            + assumption.
            + assumption. }
          { apply permMapsDisjoint_permDisjoint.
            apply permMapsDisjoint_comm.
            inversion dinv.
            eapply lock_res_threads; eassumption. }
                
          
      }
      
    - (*match_st*)
      unfold ds''.
      apply match_st_age_tp_to.
      apply MTCH_updLockS.
      Focus 2.
      {
      inversion MATCH; subst.
      intros; apply JSEM.juic2Perm_correct.
      inversion Hcompatible; inversion H.
      eapply JSEM.mem_cohere_sub.
      - eassumption.
      - eapply join_sub_trans.
        + unfold join_sub. exists phi'. eassumption.
        + eapply JSEM.compatible_threadRes_sub.
      assumption. }

      Unfocus.
      unfold ds'.
      apply MTCH_update; auto.

    - assert (H: exists l, DSEM.ThreadPool.lockRes ds (b, Int.intval ofs) = Some l).
      { inversion MATCH; subst.
        specialize (mtch_locks (b, (Int.intval ofs) )).
        rewrite His_locked in mtch_locks.
        destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)); try solve[inversion mtch_locks]. exists l; reflexivity. }
           destruct H as [l dlockRes].
      econstructor 2.
      9: reflexivity.
      9: unfold ds'', ds'; repeat f_equal; apply proof_irr.
      + assumption.
      + eapply MTCH_getThreadC; eassumption.
      + eassumption.
(*      + eapply MTCH_compat; eassumption. *)
      + instantiate(1:=(restrPermMap
               (JSEM.mem_compatible_locks_ltwritable Hcompatible))). 
             apply restrPermMap_ext.
             intros b0.
             inversion MATCH; subst.
             extensionality ofs0.
             symmetry; apply MTCH_lockSet.
             assumption.
      + assumption.
      + assumption.
      + exact dlockRes.
      + { move virtue_spec at bottom.
          constructor.
          - intros b0 ofs0.
            replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
            rewrite <- virtue_spec.
            rewrite <- JSEM.juic2Perm_correct.
            inversion MATCH. erewrite <- mtch_perm. split.
            + eapply preservationOfReads1.
              apply resource_at_join. eassumption.
            + Lemma preservationOfReads2: forall r1 r2 r3,
                sepalg.join r1 r2 r3 ->
                Mem.perm_order' (perm_of_res r1) Readable \/
                Mem.perm_order' (perm_of_res r2) Readable ->
                Mem.perm_order' (perm_of_res r3) Readable.
              Proof. intros ? ? ? JOIN.
                     do 3 erewrite po_oo; intros [H | H];
                     eapply po_trans; try eassumption;
                     apply juicy_mem_lemmas.po_join_sub; eapply join_join_sub.
                     - eassumption.
                     - eapply join_comm; eassumption.
              Qed.
              apply preservationOfReads2.
              apply resource_at_join; assumption.

              (*  JSEM.access_cohere' m d_phi *)
            + intros addr.
              destruct Hcompatible as [all_juice Hcompatible].
              inversion Hcompatible. 
              eapply po_trans.
              apply all_cohere.
              apply juicy_mem_lemmas.po_join_sub.
              apply resource_at_join_sub.
              eapply join_sub_trans.
              eapply join_join_sub; apply Hrem_lock_res.
              apply JSEM.compatible_threadRes_sub. assumption.
          - intros.
            replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
            rewrite <- virtue_spec.
            inversion MATCH; erewrite <- mtch_perm.
            apply juicy_mem_lemmas.po_join_sub.
            apply resource_at_join_sub.
            eapply join_join_sub.
            eapply join_comm. eassumption.
        }
    }
    (* step_create *)
    {
      pose (inflated_delta1:=
              fun loc => match (d_phi @ loc ) with
                        NO s => if Share.EqDec_share s Share.bot then None else  Some ( perm_of_res (phi' @ loc))
                      | _ => Some ( perm_of_res (phi' @ loc))
                      end).
      pose (virtue1:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta1 (block, ofs))) (snd (getMaxPerm m')) ).
      assert (virtue_spec1: forall b0 ofs0,
                 (computeMap (DTP.getThreadR (MTCH_cnt MATCH Hi)) virtue1) !! b0 ofs0 =
                 perm_of_res (phi' @ (b0, ofs0))).
      { intros b0 ofs0.
        destruct (virtue1 ! b0) eqn:VIRT.
        destruct (o ofs0) eqn:O.
        - erewrite computeMap_1; try eassumption.
          unfold virtue1 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta1 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share t Share.bot); inversion O.
          reflexivity.
        - erewrite computeMap_2; try eassumption.
          unfold virtue1 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta1 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share t Share.bot); inversion O.
          subst.
          apply resource_at_join with (loc:= (b0,ofs0)) in Hrem_fun_res.
          rewrite AA in Hrem_fun_res.
          apply join_NO_bot in Hrem_fun_res; rewrite Hrem_fun_res.
          inversion MATCH.
          symmetry.
          apply mtch_perm.
        - erewrite computeMap_3; try eassumption.
             unfold virtue1 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m')) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m') !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DSEM.ThreadPool.getThreadR (MTCH_cnt MATCH Hi)) !! b0 ofs0) with
             (perm_of_res ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'. unfold JSEM.access_cohere' in acc_coh.
               specialize (acc_coh (b0,ofs0)).
               unfold max_access_at, access_at in acc_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in acc_coh.
               apply po_None1 in acc_coh.
               move Hrem_fun_res at bottom.
               apply join_comm in Hrem_fun_res.
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_fun_res.
               apply join_join_sub in Hrem_fun_res.
               assert (HH:= juicy_mem_lemmas.po_join_sub _ _ Hrem_fun_res).
               rewrite acc_coh in HH. rewrite acc_coh.
               apply po_None1 in HH. symmetry; assumption.
             + inversion MATCH.  apply mtch_perm.
      }
      pose (inflated_delta2:=fun loc => Some (perm_of_res (d_phi @ loc))).
      pose (virtue2:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta2 (block, ofs))) (snd (getMaxPerm m')) ).
      assert (virtue_spec2: forall b0 ofs0,
                 (computeMap empty_map virtue2) !! b0 ofs0 = (perm_of_res (d_phi @(b0, ofs0)))).
      { intros b0 ofs0.
        destruct (virtue2 ! b0) eqn:VIRT.
        destruct (o ofs0) eqn:O.
        - erewrite computeMap_1; try eassumption.
          unfold virtue2 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          inversion O; reflexivity.
        - erewrite computeMap_2; try eassumption.
          rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          inversion O.
        - erewrite computeMap_3; try eassumption.
          rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0) eqn:notInMem; inversion VIRT.
          clear VIRT.
          assert (THE_CURE: (getMaxPerm m') !! b0 = fun _ => None).
          { unfold PMap.get. rewrite notInMem.
            apply Max_isCanonical.
             }
          assert (the_cure:= equal_f THE_CURE ofs0).
          rewrite getMaxPerm_correct in the_cure.
          replace ((DSEM.ThreadPool.getThreadR (MTCH_cnt MATCH Hi)) !! b0 ofs0) with
          (perm_of_res ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
          + assert (Hcohere':= Hcompatible).
            apply compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
            inversion Hcohere'. unfold JSEM.access_cohere' in acc_coh.
            specialize (acc_coh (b0,ofs0)).
            unfold max_access_at, access_at in acc_coh.
            unfold permission_at in the_cure.
            rewrite the_cure in acc_coh.
            apply po_None1 in acc_coh.
            move Hrem_fun_res at bottom.
            apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_fun_res.
            apply join_join_sub in Hrem_fun_res.
            assert (HH:= juicy_mem_lemmas.po_join_sub _ _ Hrem_fun_res).
            rewrite acc_coh in HH.
            apply po_None1 in HH. rewrite HH.
            rewrite empty_map_spec; reflexivity.
          + inversion MATCH.  apply mtch_perm.
      }
      pose (ds_upd:= DTP.updThread (MTCH_cnt MATCH Hi) (Kresume c Vundef) (computeMap (DTP.getThreadR (MTCH_cnt MATCH Hi)) virtue1)).
      pose (ds':= DTP.addThread ds_upd (Vptr b ofs) arg (computeMap empty_map virtue2)).
      exists ds', (JSEM.Events.spawn (b, Int.intval ofs)).
      split ;[|split].
      { (* invariant *)  
        cut (DSEM.invariant ds_upd).
        { intros HH. unfold ds'.
          eapply addThrd_inv.
          - assumption.
          - intros.
            destruct (NatTID.eq_tid_dec i i0).
            + subst i0.
              rewrite DryMachine.SIG.ThreadPool.gssThreadRes.
              apply permDisjoint_permMapsDisjoint.
              intros b0 ofs0.
              rewrite virtue_spec1 virtue_spec2.
              apply joins_permDisjoint.
              apply joins_comm.
              apply resource_at_joins.
              eapply join_joins.
              eassumption.
            + rewrite DryMachine.SIG.ThreadPool.gsoThreadRes. 2: assumption.
              apply permDisjoint_permMapsDisjoint.
              intros b0 ofs0.
              rewrite virtue_spec2.
            erewrite MTCH_perm' with (MTCH:=MATCH).
              apply joins_permDisjoint. apply joins_comm.
              eapply join_sub_joins_trans.
              eapply join_join_sub.
              move Hrem_fun_res at bottom.
              apply resource_at_join. eassumption.
              simpl.
              eapply resource_at_joins.
              eapply (compatible_threadRes_join).
              eassumption.
              assumption.
          - rewrite DSEM.ThreadPool.gsoThreadLock.
            apply permDisjoint_permMapsDisjoint.
            intros b0 ofs0.
            rewrite virtue_spec2.
            apply permDisjoint_comm.
            eapply permDisjoint_sub.
            eapply join_join_sub.
            eapply resource_at_join.
            eassumption.
            inversion MATCH; rewrite mtch_perm.
            apply mtch_cnt; assumption.
            intros; apply permMapsDisjoint_permDisjoint.
            inversion dinv.
            apply permMapsDisjoint_comm; apply lock_set_threads.
          - intros l lmap.
            rewrite DTP.gsoThreadLPool.
            intros H. 
            apply permDisjoint_permMapsDisjoint.
            intros b0 ofs0.
            rewrite virtue_spec2.
            apply permDisjoint_comm.
            eapply permDisjoint_sub.
            eapply join_join_sub.
            eapply resource_at_join.
            eassumption.
            inversion MATCH; rewrite mtch_perm.
            apply mtch_cnt; assumption.
            intros; apply permMapsDisjoint_permDisjoint.
            inversion dinv.
            apply permMapsDisjoint_comm. eapply lock_res_threads.
            eassumption.
        }
        { (*invariant ds_upd*)
          eapply updThread_inv.
          - assumption.
          - intros.
            apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
            rewrite virtue_spec1.
            eapply permDisjoint_sub.
            eapply join_join_sub.
            eapply resource_at_join.
            eapply join_comm.
            eassumption.
            inversion MATCH; rewrite mtch_perm.
            apply mtch_cnt; assumption.
            intros. 
            apply permMapsDisjoint_comm.
            inversion dinv. apply no_race.
            intros HH; apply H; symmetry; exact HH.
          - intros.
            apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
            rewrite virtue_spec1.
            eapply permDisjoint_comm.
            eapply permDisjoint_sub.
            eapply join_join_sub.
            eapply resource_at_join.
            eapply join_comm.
            eassumption.
            inversion MATCH; rewrite mtch_perm.
            apply mtch_cnt; assumption.
            intros. 
            apply permMapsDisjoint_comm.
            inversion dinv. apply lock_set_threads.
          - intros.
            apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
            rewrite virtue_spec1.
            eapply permDisjoint_comm.
            eapply permDisjoint_sub.
            eapply join_join_sub.
            eapply resource_at_join.
            eapply join_comm.
            eassumption.
            inversion MATCH; rewrite mtch_perm.
            apply mtch_cnt; assumption.
            intros. 
            apply permMapsDisjoint_comm.
            inversion dinv. eapply lock_res_threads.
            eassumption.
        }
      } 
      { (*match_st*)
        apply MTCH_addThread.
        - apply MTCH_update.
          + assumption.
          + intros. symmetry; apply virtue_spec1.
        - intros. symmetry; apply virtue_spec2.
      }
      {
        eapply DSEM.step_create with (virtue1:=virtue1)(virtue2:=virtue2).
        - assumption.
        - inversion MATCH. erewrite <- mtch_gtc; eassumption.
        - eassumption.
        - intros. rewrite virtue_spec1.
          inversion MATCH. erewrite <- mtch_perm.
          eapply juicy_mem_lemmas.po_join_sub.
          eapply join_join_sub.
          apply resource_at_join.
          simpl in Hrem_fun_res.
          eapply join_comm; eassumption.
        - intros. rewrite virtue_spec2.
          apply JSEM.almost_empty_perm.
          assumption.
        - reflexivity.
        - reflexivity.
      }
    }
    
    (* step_mklock *)
    { 
      assert (Htid':= MTCH_cnt MATCH Hi).
     (* (Htp': tp' = updThread cnt0 (Kresume c) pmap_tid')
            (Htp'': tp'' = updLockSet tp' pmap_lp), *)
      pose (pmap_tid  := DTP.getThreadR Htid').
      pose (pmap_tid' := setPermBlock (Some Nonempty) b (Int.intval ofs) pmap_tid LKSIZE_nat).
      pose (pmap_lp   := setPerm (Some Writable) b (Int.intval ofs)
                                               (DTP.lockSet ds)).

      pose (ds':= DTP.updThread Htid' (Kresume c Vundef) pmap_tid').
      pose (ds'':= DTP.updLockSet ds' (b, Int.intval ofs) empty_map).

      exists ds'',  (JSEM.Events.mklock (b, Int.intval ofs)).
      split ; [|split].
      - (*DSEM.invariant ds''*)
        cut (DSEM.invariant ds').
        { intros dinv'.
          apply updLock_inv.
        - assumption.
        - intros i0 cnt0 ofs0 ineq.
          simpl (fst (b, Int.intval ofs)).
          simpl (snd (b, ofs0)).
          assert ((DTP.getThreadR cnt0) !! b ofs0 = None \/
                 (DTP.getThreadR cnt0) !! b ofs0 = Some Nonempty).
          {  destruct (NatTID.eq_tid_dec i i0).
             - right. subst i0. 
               rewrite DTP.gssThreadRes. unfold pmap_tid'.
               apply setPermBlock_same.
               clear - ineq. unfold LKSIZE in ineq; destruct ineq; auto.
             - rewrite DTP.gsoThreadRes.
               inversion MATCH. rewrite <- (mtch_perm _ _ _ (mtch_cnt' _ cnt0)).
               
               assert (HH:= compatible_threadRes_join Hcmpt Hi (mtch_cnt' i0 cnt0)).
               destruct HH as [SOME_RES HH]. assumption.
               apply (resource_at_join _ _ _ (b, ofs0)) in HH.
               rewrite Hpersonal_juice in HH.
               destruct (Hct ofs0) as [val Hlock_old].
               { unfold juicy_machine.LKSIZE, juicy_machine.LKCHUNK. simpl (align_chunk Mint32).
                 clear - ineq. unfold LKSIZE in ineq; destruct ineq; auto. }
               rewrite Hlock_old in HH.
               apply YES_join_full in HH.
               destruct HH as [? HH]. rewrite HH; simpl.
               destruct (eq_dec x Share.bot); auto.
               assumption.
          }
          { destruct H as [HH | HH]; rewrite HH; exists (Some Writable); reflexivity. }
        - intros. apply empty_disjoint'.
        - apply permMapsDisjoint_comm; apply empty_disjoint'.
        - intros. rewrite empty_map_spec. exists (Some Writable); reflexivity.
        - intros; simpl.
          assert (exists r, JSEM.ThreadPool.lockRes js l = Some r).
          { rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool in H.
            inversion MATCH. specialize (mtch_locks l); rewrite H in mtch_locks.
            destruct (JSEM.ThreadPool.lockRes js l) eqn:AA; inversion mtch_locks.
            exists l0; reflexivity. }
          destruct H1 as [l0 HH].
          destruct l0.
          + inversion MATCH. erewrite <- mtch_locksRes; eauto.
            apply permDisjoint_comm.
            eapply compatible_threadRes_lockRes_join with (cnti:=Hi) in HH; eauto.
            apply resource_at_joins with (l:= (b, ofs0)) in HH.
            move HH at bottom.
            assert (ineq':Int.intval ofs <= ofs0 < Int.intval ofs + juicy_machine.LKSIZE).
            { clear - H0; destruct H0; auto. }
            apply Hct in ineq'.
            destruct ineq' as [val MAP].
            rewrite MAP in HH.
            destruct HH as [? HH]; inversion HH.
            * simpl. destruct (eq_dec rsh2 Share.bot); exists (Some Writable); reflexivity.
            * exfalso. apply join_joins in H9. apply pshare_join_full_false1 in H9.
              exact H9.
          + inversion MATCH. replace pmap0 with empty_map.
            rewrite empty_map_spec; exists (Some Writable); reflexivity.
            symmetry; eapply mtch_locksEmpty; eauto.
        - intros ofs0 ineq.
          simpl. rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          destruct (DryMachine.SIG.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; rewrite AA; try reflexivity.
          inversion MATCH. specialize (mtch_locks (b,ofs0)).
          rewrite AA in mtch_locks.
          destruct (JSEM.ThreadPool.lockRes js (b, ofs0)) eqn:BB; inversion mtch_locks.
          destruct Hcompatible as [allj Hcompatible]. 
          inversion Hcompatible.
          unfold JSEM.ThreadPool.lockRes in BB.
          specialize (lset_in_juice (b, ofs0)). rewrite BB in lset_in_juice.
          destruct lset_in_juice as [sh' [psh [P MAP]]]; auto.
          assert (HH:= JSEM.compatible_threadRes_sub Hi juice_join).
          apply resource_at_join_sub with (l:= (b,ofs0)) in HH.
          rewrite MAP in HH.
          assert (ineq': Int.intval ofs <= ofs0 < Int.intval ofs + juicy_machine.LKSIZE).
          { clear - ineq. destruct ineq; auto. simpl in *.
            replace juicy_machine.LKSIZE with LKSIZE by auto.
            xomega. }
          apply Hct in ineq'.
          destruct ineq' as [val MAP'].
          rewrite <- Hpersonal_juice in MAP'; rewrite MAP' in HH.
          destruct HH as [f HH]; inversion HH.

        - intros ofs0 ineq.
          simpl. rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          destruct (DryMachine.SIG.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; rewrite AA; try reflexivity.
          inversion MATCH. specialize (mtch_locks (b,ofs0)).
          rewrite AA in mtch_locks.
          destruct (JSEM.ThreadPool.lockRes js (b, ofs0)) eqn:BB; inversion mtch_locks.
          destruct Hcompatible as [allj Hcompatible]. 
          inversion Hcompatible.
          unfold JSEM.ThreadPool.lockRes in BB.
          specialize (lset_in_juice (b, ofs0)). rewrite BB in lset_in_juice.
          destruct lset_in_juice as [sh' [psh [P MAP]]]; auto.
          assert (HH:= JSEM.compatible_threadRes_sub Hi juice_join).
          assert (VALID:= phi_valid allj).
          specialize (VALID b ofs0).
          unfold "oo" in VALID.
          rewrite MAP in VALID.
          simpl in VALID.
          assert (ineq': 0 < Int.intval ofs - ofs0 < LKSIZE).
          { clear - ineq. simpl in ineq; destruct ineq. xomega. }
          apply VALID in ineq'.
          replace (ofs0 + (Int.intval ofs - ofs0)) with (Int.intval ofs) in ineq' by omega.
          apply resource_at_join_sub with (l:= (b,Int.intval ofs)) in HH.
          replace juicy_machine.LKSIZE with 4 in Hct by auto.
          specialize (Hct (Int.intval ofs) ltac:(omega)).
          destruct Hct as [val MAP'].
          rewrite <- Hpersonal_juice in MAP'. 
          rewrite MAP' in HH.
          destruct HH as [X HH].
          inversion HH;
          rewrite <- H7 in ineq';
          inversion ineq'.
        }
          
        { (*DSEM.invariant ds' *)
          apply updThread_inv.
          - eassumption.
          - intros.
           apply permDisjoint_permMapsDisjoint. intros b0 ofs0.
            unfold pmap_tid'.

            destruct (ident_eq b b0).
            + subst b0.
              destruct (Intv.In_dec ofs0 ((Int.intval ofs),(Int.intval ofs) + LKSIZE )).
              * { rewrite setPermBlock_same; try assumption.
                  simpl.
                  erewrite MTCH_perm' with (MTCH:=MATCH).
                  
                  eapply (@permDisjointLT (perm_of_res (JTP.getThreadR Hi @ (b, ofs0)))).
                  apply joins_permDisjoint.
                  apply resource_at_joins.
                  eapply compatible_threadRes_join.
                  eassumption.
                  assumption.
                  rewrite Hpersonal_juice.
                  destruct (Hct ofs0) as [v Hct'].
                  move i0 at bottom.
                  exact i0.
                  rewrite Hct'; simpl.
                  unfold perm_of_sh, fullshare.
                  rewrite if_true.
                  destruct (eq_dec sh Share.top); simpl; constructor.
                  reflexivity.
                }
              * { rewrite setPermBlock_other_1; try assumption.
                  inversion dinv.
                  apply permMapsDisjoint_permDisjoint.
                  unfold pmap_tid. apply no_race; assumption.
                  apply Intv.range_notin in n; simpl in n.
                  replace (Z.of_nat LKSIZE_nat) with LKSIZE.
                  exact n.
                  reflexivity.
                  unfold LKSIZE; simpl; xomega.
                }
            + { rewrite setPermBlock_other_2; try assumption.
                inversion dinv.
                apply permMapsDisjoint_permDisjoint.
                unfold pmap_tid. apply no_race; assumption. }
          - intros.
            apply permDisjoint_permMapsDisjoint. intros b0 ofs0.
            unfold pmap_tid'.

            destruct (ident_eq b b0).
            + subst b0.
              destruct (Intv.In_dec ofs0 ((Int.intval ofs), (Int.intval ofs)+LKSIZE)).
              * { rewrite setPermBlock_same; try assumption.
                  simpl.
                  inversion MATCH.
                  destruct (DSEM.ThreadPool.lockSet_WorNE ds b ofs0) as [HH | HH]; rewrite HH.
                  - exists (Some Writable); reflexivity.
                  - exists (Some Nonempty); reflexivity.
                }
              * { rewrite setPermBlock_other_1; try assumption.
                  inversion dinv.
                  apply permMapsDisjoint_permDisjoint.
                  unfold pmap_tid. apply lock_set_threads; assumption.
                  apply Intv.range_notin in n.
                  replace (Z.of_nat LKSIZE_nat) with LKSIZE by reflexivity.
                  exact n.
                  unfold LKSIZE; simpl; omega.
                }
            + { rewrite setPermBlock_other_2; try assumption.
                inversion dinv.
                apply permMapsDisjoint_permDisjoint.
                unfold pmap_tid. apply lock_set_threads; assumption. }

          - intros.
            apply permDisjoint_permMapsDisjoint. intros b0 ofs0.
            unfold pmap_tid'.
            
            destruct (ident_eq b b0).
            + subst b0.
              destruct (Intv.In_dec ofs0 ((Int.intval ofs), (Int.intval ofs)+LKSIZE)).
              * { rewrite setPermBlock_same; try assumption.
                  simpl.
                  apply permDisjoint_comm.
                  apply (@permDisjointLT (pmap_tid !! b ofs0)).
                  apply permMapsDisjoint_permDisjoint.
                  unfold pmap_tid.
                  inversion dinv.
                  apply permMapsDisjoint_comm.
                  eapply lock_res_threads; eassumption.
                  unfold pmap_tid.
                  inversion MATCH.
                  erewrite <- (mtch_perm _ _ _ Hi).
                  rewrite Hpersonal_juice.
                  destruct (Hct ofs0) as [v Hct'].
                  apply i0.
                  rewrite Hct'. simpl.
                  unfold perm_of_sh, fullshare.
                  rewrite if_true.
                  destruct (eq_dec sh Share.top); simpl; constructor.
                  reflexivity. }
              * { rewrite setPermBlock_other_1; try assumption.
                  inversion dinv.
                  apply permMapsDisjoint_permDisjoint.
                  unfold pmap_tid. eapply lock_res_threads; eassumption.
                  apply Intv.range_notin in n. replace (Z.of_nat LKSIZE_nat) with LKSIZE by reflexivity.
                  exact n.
                  unfold LKSIZE; simpl; omega.
                }
            + { rewrite setPermBlock_other_2; try assumption.
                inversion dinv.
                apply permMapsDisjoint_permDisjoint.
                unfold pmap_tid. eapply lock_res_threads; eassumption. }
        }
        
      - (*rewrite Htp''; *) unfold ds''.
        apply MTCH_age.
        apply MTCH_updLockN.
        (*rewrite Htp';*) unfold ds'.
        apply MTCH_update.
        assumption.

        (* Now I prove the map construction is correct*)
        {
          inversion MATCH; subst js0 ds0.
          unfold pmap_tid', pmap_tid.
          intros.
          (*unfold setPerm.*)
          destruct (ident_eq b b0). rewrite e.
          + subst b0.
            (*I consider three cases:
             * ofs = ofs0 
             * 0 < ofs0 - ofs < LOCKSIZE 
             * ~ 0 < ofs0 - ofs <= LOCKSIZE
             *)
            destruct (Intv.In_dec ofs0 ((Int.intval ofs), (Int.intval ofs)+LKSIZE)).
            * { rewrite setPermBlock_same; try assumption.
                destruct (zeq (Int.intval ofs) ofs0).
                - subst ofs0.
                  rewrite Hlock. reflexivity.
                - rewrite (Hct0 (ofs0)). reflexivity.
                  clear - i0 n. 
                  replace (juicy_machine.LKSIZE) with LKSIZE by reflexivity.
                  unfold Intv.In in i0. simpl in i0.
                  xomega. }
              * { rewrite setPermBlock_other_1; try assumption.
                  inversion dinv.
                  rewrite <- Hj_forward.
                  inversion MATCH. erewrite <- mtch_perm.
                  rewrite <- Hpersonal_juice; reflexivity.
                  simpl. right.
                  clear -n.
                  replace (juicy_machine.LKSIZE) with LKSIZE by reflexivity.
                  apply Intv.range_notin in n.
                  intros [H1 H2].
                  simpl in n; destruct n; xomega.
                  unfold LKSIZE; simpl; xomega.
                  clear -n.
                  replace (juicy_machine.LKSIZE) with LKSIZE by reflexivity.
                  apply Intv.range_notin in n.
                  replace (Z.of_nat LKSIZE_nat) with LKSIZE by reflexivity. exact n.
                  unfold LKSIZE; simpl; xomega. }
            + { rewrite setPermBlock_other_2; try assumption.
                rewrite <- Hj_forward.
                inversion MATCH. erewrite <- mtch_perm. 
                  rewrite <- Hpersonal_juice; reflexivity.
                  left; assumption. }
        }
      - econstructor 4. (*The step *)
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + eassumption.
        (*      + eapply MTCH_compat; eassumption. *)
        + reflexivity.
        + rewrite <- Hstore. f_equal.
          erewrite <- (MTCH_restrict_personal ).
          * reflexivity.
          * auto.
            (* instantiate(1:= m_dry jm).
          subst tp''.
          rewrite <- Hpersonal_perm.
          erewrite <- (MTCH_restrict_personal ).
          reflexivity.
          assumption.
        + rewrite <- Hright_juice; assumption. *)
        + reflexivity.
        + reflexivity.
        + replace (MTCH_cnt MATCH Hi) with Htid'.
          reflexivity.
          apply proof_irrelevance.
    }
    
    (* step_freelock *)
    { assert (Htid':= MTCH_cnt MATCH Hi).
     (* (Htp': tp' = updThread cnt0 (Kresume c) pmap_tid')
            (Htp'': tp'' = updLockSet tp' pmap_lp), *)
      Definition WorF (sh: share): permission:=
        if eq_dec sh Share.top then Freeable else Writable.
       pose (delta_b:=
               fun ofs0 => if (Intv.In_dec ofs0 ( Int.intval ofs,  Int.intval ofs + LKSIZE)%Z) then
                           Some (perm_of_res (phi' @ (b, ofs0)))
                        else None).
       Definition empty_delta_map: delta_map:= PTree.empty (Z -> option (option permission)).
       pose (virtue:= PTree.set b delta_b empty_delta_map).
       
       pose (pmap_tid  := DTP.getThreadR Htid').
       pose (pmap_tid' := (computeMap pmap_tid virtue)).

       assert (virtue_spec: forall (b0 : block) (ofs0 : Z),
                  perm_of_res (phi' @ (b0, ofs0)) =
                  (computeMap (DTP.getThreadR Htid') virtue) !! b0 ofs0).
       { intros b0 ofs0.
         destruct (virtue ! b0) eqn:VIRT.
         destruct (o ofs0) eqn:O.
         - erewrite computeMap_1; try eassumption.
           unfold virtue in VIRT.
           destruct (ident_eq b0 b).
           + subst b0.
             rewrite PTree.gss in VIRT. inversion VIRT. subst o.
             unfold delta_b in O.
             destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs + LKSIZE)); inversion O.
             reflexivity.
           + rewrite PTree.gso in VIRT. unfold empty_delta_map in VIRT.
             rewrite PTree.gempty in VIRT; inversion VIRT.
             assumption.
         - erewrite computeMap_2; try eassumption.
           unfold virtue in VIRT.
           destruct (ident_eq b0 b).
           + subst b0.
             rewrite PTree.gss in VIRT. inversion VIRT. subst o.
             unfold delta_b in O.
             destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs + LKSIZE)); inversion O.
             rewrite <- Hj_forward.
             * inversion MATCH; rewrite mtch_perm; reflexivity.
             * right. replace juicy_machine.LKSIZE with LKSIZE by reflexivity; simpl.
               intros HH; apply n. unfold Intv.In; simpl; xomega.
               
           + rewrite PTree.gso in VIRT. unfold empty_delta_map in VIRT.
             rewrite PTree.gempty in VIRT; inversion VIRT.
             assumption.
         - erewrite computeMap_3; try eassumption.
           unfold virtue in VIRT.
           destruct (ident_eq b0 b).
           + subst b0.
             rewrite PTree.gss in VIRT. inversion VIRT.
           + rewrite PTree.gso in VIRT; try assumption.
             unfold empty_delta_map in VIRT.
             rewrite PTree.gempty in VIRT; inversion VIRT.
             rewrite <- Hj_forward.
             * inversion MATCH; rewrite mtch_perm; reflexivity.
             * left. intros HH; apply n; symmetry; assumption.
       }

       pose (ds':= DTP.updThread Htid' (Kresume c Vundef) pmap_tid').
       pose (ds'':= DTP.remLockSet ds' (b,(Int.intval ofs))).
       
       exists ds'', (JSEM.Events.freelock (b, Int.intval ofs)).
       split ; [|split].

       
      unfold ds''; rewrite DSEM.ThreadPool.remLock_updThread_comm.
      pose (ds0:= (DSEM.ThreadPool.remLockSet ds (b, (Int.intval ofs)))).
      
      - cut (DSEM.invariant ds0).
        { (*DSEM.invariant ds' *)
          intros dinv0.
          apply updThread_inv.
          - eassumption.
          - intros.
            apply Disjoint_computeMap; intros b0 ofs0. 
            unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
            { unfold virtue in e.
              destruct (ident_eq b0 b).
              - subst b0.
                rewrite PTree.gss in e; inversion e.
                rewrite <- H1 in e0. unfold delta_b in e0.
                destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs + LKSIZE)); inversion e0. 

                inversion MATCH.
                rewrite DSEM.ThreadPool.gRemLockSetRes.
                erewrite <- mtch_perm with (Htid:=mtch_cnt' _ cnt). 
                apply joins_permDisjoint.
                assert (AA:= compatible_threadRes_join Hcompatible Hi (mtch_cnt' j cnt) H).
                apply resource_at_joins with (l:=(b,ofs0)) in AA.
                destruct AA as [result AA].
                (*First discharge when ofs0 = Int.intval ofs*)
                destruct (zeq ofs0 (Int.intval ofs)).
                + subst ofs0.
                  rewrite Hlock in AA.
                  destruct Hlock' as [val Hlock'].
                  rewrite Hlock'.
                  assert (BB:= YES_join_full _ _ _ _ _ AA);
                    destruct BB as [rsh2 BB]. rewrite BB; rewrite BB in AA.
                  inversion AA; subst.
                  eexists; econstructor; exact RJ.
                +  destruct (Hct ofs0) as [val [Hct1 Hct2]].
                   clear - i0 n. unfold Intv.In in i0.
                   replace (juicy_machine.LKSIZE) with LKSIZE by reflexivity.
                   simpl in i0; xomega. rewrite Hct2.
                   rewrite Hct1 in AA.
                   assert (BB:= YES_join_full _ _ _ _ _ AA);
                     destruct BB as [rsh2 BB]; rewrite BB; rewrite BB in AA.
                   inversion AA; subst.
                   eexists; econstructor. exact RJ.
              - rewrite PTree.gso in e.
                + rewrite PTree.gempty in e; inversion e.
                + assumption.
            }
            { unfold pmap_tid. rewrite DSEM.ThreadPool.gRemLockSetRes.
              erewrite MTCH_perm' with (MTCH:=MATCH).
              erewrite MTCH_perm' with (MTCH:=MATCH).
              apply joins_permDisjoint. apply resource_at_joins.
              eapply compatible_threadRes_join.
              eassumption.
              assumption.
            }
            { unfold pmap_tid. rewrite DSEM.ThreadPool.gRemLockSetRes.
              erewrite MTCH_perm' with (MTCH:=MATCH).
              erewrite MTCH_perm' with (MTCH:=MATCH).
              apply joins_permDisjoint. apply resource_at_joins.
              eapply compatible_threadRes_join.
              eassumption.
              assumption.
            }


            
          - intros.
            apply permMapsDisjoint_comm.
            apply Disjoint_computeMap; intros b0 ofs0. 
            unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
            + {
                unfold virtue in e. 
                destruct (ident_eq b b0).
                - subst b0. rewrite PTree.gss in e.
                  inversion e. rewrite <- H0 in e0.
                  unfold delta_b in e0.
                  destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs + LKSIZE)); inversion e0.
                  rewrite DSEM.ThreadPool.gsslockSet_rem.
                  apply permDisjoint_comm.
                  exists (perm_of_res (phi' @ (b, ofs0)));
                    reflexivity.
                  + Lemma MTCH_lr_valid: forall js ds,
                      match_st js ds ->
                      JSEM.ThreadPool.lr_valid (JTP.lockRes js) ->
                      DSEM.ThreadPool.lr_valid (DTP.lockRes ds).
                    Proof. intros js ds MATCH.
                           unfold JSEM.ThreadPool.lr_valid, DSEM.ThreadPool.lr_valid.
                           inversion MATCH. clear - mtch_locks.
                           intros HH b ofs.
                           destruct (DTP.lockRes ds (b, ofs)) eqn:AA; auto.
                           assert (mtch_locks':=mtch_locks).
                           specialize (mtch_locks (b, ofs)); rewrite AA in mtch_locks.
                           destruct (JTP.lockRes js (b, ofs)) eqn:BB; inversion mtch_locks.
                           specialize (HH b ofs).
                           rewrite BB in HH.
                           intros ofs0 ineq.
                           specialize (HH ofs0 ineq).
                           specialize (mtch_locks' (b, ofs0)).
                           rewrite HH in mtch_locks'.
                           destruct (DTP.lockRes ds (b, ofs0)); inversion mtch_locks'; auto.
                    Qed.
                    eapply MTCH_lr_valid; eauto.
                    eapply JSEM.compat_lr_valid; eauto.
                  + auto.
                + cut (is_true (isSome( JSEM.ThreadPool.lockRes js (b, Int.intval ofs)))).
                  { intros HH; inversion MATCH. specialize (mtch_locks (b, Int.intval ofs)).
                    destruct (JSEM.ThreadPool.lockRes js (b, Int.intval ofs)) eqn:LR; inversion HH.
                    destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)) eqn:LR'; inversion mtch_locks.
                    constructor.
                  }
                  { destruct Hcompatible as [allj Hcompatible].
                    inversion Hcompatible. unfold JSEM.ThreadPool.lockRes.
                    eapply JSEM.compatible_threadRes_sub with (cnt:=Hi) in juice_join.
                    eapply resource_at_join_sub with (l:=(b, Int.intval ofs)) in juice_join.
                    rewrite Hlock in juice_join.
                    destruct juice_join as [X JOIN].
                    inversion JOIN.
                    - eapply jloc_in_set;
                    rewrite <- H; 
                    reflexivity.
                    - eapply jloc_in_set;
                    rewrite <- H7; 
                    reflexivity. }
                - rewrite DSEM.ThreadPool.gsolockSet_rem1. 2 : assumption.
                  unfold empty_delta_map in e.
                  rewrite PTree.gso in e. rewrite PTree.gempty in e; inversion e.
                  intro e. apply n; symmetry; assumption.
              }
            + { unfold virtue in e.            
                destruct (ident_eq b0 b).
                - subst b0.
                  unfold empty_delta_map in e.
                  rewrite PTree.gss in e; inversion e.
                  rewrite <- H0 in e0. unfold delta_b in e0.
                  destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs + LKSIZE)); inversion e0.
                  rewrite DSEM.ThreadPool.gsolockSet_rem2. 3: exact n.
                  unfold pmap_tid.
                  inversion dinv. eapply permDisjoint_comm; eapply permMapsDisjoint_permDisjoint.
                  eapply lock_set_threads.
                  
                    eapply MTCH_lr_valid; eauto.
                    eapply JSEM.compat_lr_valid; eauto.
                - auto.
                  unfold empty_delta_map in e. rewrite PTree.gso in e. rewrite PTree.gempty in e; inversion e.
                  assumption. } 
            + unfold virtue in e.      
              destruct (ident_eq b0 b).
              * subst; rewrite PTree.gss in e; inversion e.
              * rewrite PTree.gso in e; try assumption.
                rewrite DSEM.ThreadPool.gsolockSet_rem1.
                unfold pmap_tid.
                inversion dinv. apply permDisjoint_comm; apply permMapsDisjoint_permDisjoint.
                apply lock_set_threads.
                intros eq; apply n; symmetry; exact eq.
          - { intros.
              unfold pmap_tid'.
              apply permMapsDisjoint_comm.
              assert (HH: DSEM.ThreadPool.lockRes  ds l = Some pmap0).
              { (*prove the assert. *)
                clear - H. destruct (AMap.E.eq_dec (b, Int.intval ofs) l).
                - subst l.
                  rewrite DSEM.ThreadPool.gsslockResRemLock in H. inversion H.
                - rewrite DSEM.ThreadPool.gsolockResRemLock in H. assumption.
                  assumption.
              }
              assert (H5: exists k, JSEM.ThreadPool.lockRes js l = Some k).
              { inversion MATCH. specialize (mtch_locks l); rewrite HH in mtch_locks.
                destruct (JSEM.ThreadPool.lockRes js l); inversion mtch_locks.
                exists l0; reflexivity. }
              destruct H5 as [k H5].
              destruct k.
              Focus 2. { inversion MATCH. specialize (mtch_locksEmpty l pmap0 H5 HH).
                         rewrite  mtch_locksEmpty.
                         eapply permDisjoint_permMapsDisjoint. intros b0 ofs0.
                         rewrite empty_map_spec.
                         apply permDisjoint_comm.
                         exists ((computeMap pmap_tid virtue) !! b0 ofs0); reflexivity. }
              Unfocus.  
              
              apply Disjoint_computeMap; intros b0 ofs0. 
              unfold deltaMap_cases_analysis'; destruct (deltaMap_dec virtue b0 ofs0).
              - { unfold virtue in e.
                  destruct (ident_eq b0 b).
                  - subst b0.
                    rewrite PTree.gss in e; inversion e.
                    rewrite <- H1 in e0. unfold delta_b in e0.
                    destruct (Intv.In_dec ofs0 (Int.intval ofs, Int.intval ofs + LKSIZE)); inversion e0. 
                    
                    inversion MATCH.
                    { specialize (mtch_locksRes l r pmap0 H5 HH b ofs0).
                      rewrite <- mtch_locksRes.
                      apply joins_permDisjoint.
                      assert (AA:= compatible_threadRes_lockRes_join Hcompatible Hi _ H5).
                      apply resource_at_joins with (l:=(b,ofs0)) in AA.
                      destruct AA as [result AA].
                      (*First discharge when ofs0 = Int.intval ofs*)
                      destruct (zeq ofs0 (Int.intval ofs)).
                      * subst ofs0.
                        rewrite Hlock in AA.
                        destruct Hlock' as [val Hlock'].
                        rewrite Hlock'.
                        assert (BB:= YES_join_full _ _ _ _ _ AA);
                          destruct BB as [rsh2 BB]. rewrite BB; rewrite BB in AA.
                        inversion AA; subst.
                        eexists; econstructor; exact RJ.
                      *  destruct (Hct ofs0) as [val [Hct1 Hct2]].
                         clear - i0 n. unfold Intv.In in i0.
                         replace (juicy_machine.LKSIZE) with LKSIZE by reflexivity.
                         simpl in i0; xomega. rewrite Hct2.
                         rewrite Hct1 in AA.
                         assert (BB:= YES_join_full _ _ _ _ _ AA);
                           destruct BB as [rsh2 BB]; rewrite BB; rewrite BB in AA.
                         inversion AA; subst.
                         eexists; econstructor. exact RJ.
                    }
                  - rewrite PTree.gso in e.
                    + rewrite PTree.gempty in e; inversion e.
                    + assumption.
                }
                
              - { unfold pmap_tid. 
                  inversion MATCH.
                  specialize (mtch_locksRes l r pmap0 H5 HH b0 ofs0).
                  rewrite <- mtch_locksRes.
                  erewrite <- mtch_perm.
                  apply joins_permDisjoint. apply resource_at_joins.
                  eapply compatible_threadRes_lockRes_join.
                  eassumption.
                  eassumption.
                }
              - { unfold pmap_tid. 
                  inversion MATCH.
                  specialize (mtch_locksRes l r pmap0 H5 HH b0 ofs0).
                  rewrite <- mtch_locksRes.
                  erewrite <- mtch_perm.
                  apply joins_permDisjoint. apply resource_at_joins.
                  eapply compatible_threadRes_lockRes_join.
                  eassumption.
                  eassumption.
                }
            }   
        }
        { 
          eapply remLock_inv.
          - assumption.
            
        }
        
      - unfold ds''.
        apply MTCH_age.
        apply MTCH_remLockN.
        unfold ds'.
        apply MTCH_update.
        assumption.

        (* Now I prove the map construction is correct*)
        {
          unfold pmap_tid'. intros.
          apply virtue_spec.
        }
        
      - econstructor 5. (*The step *)
        
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + eassumption.
        + inversion MATCH. rewrite <- mtch_locks.
          destruct Hcompatible as [all_juice Hcompatible].
          inversion Hcompatible.
          assert (all_sub: join_sub (JSEM.ThreadPool.getThreadR Hi) all_juice).
          { apply JSEM.compatible_threadRes_sub; assumption. }
          clear - Hlock all_sub jloc_in_set.
          apply resource_at_join_sub with (l:=(b, Int.intval ofs)) in all_sub. 
          destruct all_sub as [whatever all_join].
          rewrite Hlock in all_join.
          inversion all_join;
            eapply jloc_in_set;
            symmetry; eassumption. (*Solves two goals*)
        + reflexivity.
        + intros ofs0 intv.
          instantiate (1:=virtue).
          unfold virtue.
          replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
          erewrite <- virtue_spec.
          destruct (zeq ofs0 (Int.intval ofs)).
          * subst ofs0. destruct Hlock' as [val Hlock'].
            rewrite Hlock'; simpl.
            destruct (eq_dec sh Share.top).
            subst sh. rewrite perm_of_sh_fullshare; constructor.
            rewrite perm_of_writable; try assumption; constructor.
          * destruct (Hct ofs0) as [val [Hct_old Hval_new]]. 
            clear -intv n. unfold Intv.In in intv. simpl in intv.
            unfold juicy_machine.LKSIZE; simpl. xomega.
            rewrite Hval_new. simpl.
            destruct (eq_dec sh Share.top).
            subst sh. rewrite perm_of_sh_fullshare; constructor.
            rewrite perm_of_writable; try assumption; constructor.
        + intros. 
          replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
          rewrite <- virtue_spec.
          inversion MATCH; erewrite <- mtch_perm.
          destruct H as [[BB notIn] | BB];
          rewrite <- (Hj_forward (b', ofs'));
          try reflexivity; [right | left]; try (simpl; assumption).
        + reflexivity.
        + do 2 (replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance); reflexivity.
        + reflexivity.
    }

    (* step_acqfail *)
    {
      exists ds, (JSEM.Events.failacq (b, Int.intval ofs)).
      split ; [|split].
      + assumption.
      + assumption.
      + { econstructor 6.
          + assumption.
          + inversion MATCH; subst.
            rewrite <- (mtch_gtc i Hi).
            eassumption.
          + eassumption.
          + reflexivity.
          + erewrite restrPermMap_ext.
            eassumption.
            intros b0.
            inversion MATCH; subst.
            extensionality x. symmetry; apply MTCH_lockSet;
                              assumption.
        }
    }
    Grab Existential Variables.
    assumption.
    assumption.
  Qed.
    
    

  
  Lemma core_diagram':
    forall (m : Mem.mem)  (U0 U U': schedule) 
     (ds : dstate) (js js': jstate) rmap pmap
     (m' : Mem.mem) genv,
   match_st js ds ->
   DSEM.invariant ds ->
   corestep (JMachineSem U0 rmap) genv (U,nil, js) m (U',nil, js') m' ->
   exists (ds' : dstate),
     DSEM.invariant ds' /\
     match_st js' ds' /\
     corestep (DMachineSem U0 pmap) genv (U,nil, ds) m (U',nil, ds') m'.
       intros m U0 U U' ds js js' rmap pmap m' genv MATCH dinv.
       unfold JuicyMachine.MachineSemantics; simpl.
       unfold JuicyMachine.MachStep; simpl.
       intros STEP;
         inversion STEP; subst.
      
       (* start_step *)
       { inversion Htstep; subst.
         pose (ds':= (DSEM.ThreadPool.updThreadC (MTCH_cnt MATCH ctn) (Krun c_new))).
         exists ds'. split; [|split].
         - apply updCinvariant. assumption.
         - apply MTCH_updt; assumption.
         - econstructor 1.
           + eassumption.
           + eapply MTCH_compat; eassumption.
           + { econstructor.
               - eapply MTCH_getThreadC. eassumption. eassumption.
               - eassumption.
               - eassumption.
               - reflexivity.
             }
       }
       
       (* resume_step *)
       { inversion MATCH; subst.
         inversion Htstep; subst.
         exists (DTP.updThreadC (mtch_cnt _ ctn) (Krun c')).
         split;[|split].
         (*Invariant*)
         { apply updCinvariant; assumption. }
         (*Match *)
         { (*This should be a lemma *)
           apply MTCH_updt; assumption.
         }
         (*Step*)
         { econstructor 2; try eassumption.
           - simpl. eapply MTCH_compat; eassumption.
           - simpl. econstructor; try eassumption.
             + rewrite <- Hcode. symmetry. apply mtch_gtc.
             + reflexivity.
         }
       }
       
       (* core_step *)
       {
         inversion MATCH; subst.
         inversion Htstep; subst.
         assert (Htid':=mtch_cnt _ Htid).
         exists (DTP.updThread Htid' (Krun c') (permissions.getCurPerm (m_dry jm'))).
         split ; [|split].
         {
           inversion Hcorestep.
           eapply ev_step_ax2 in H; destruct H as [T H].
           apply SEM.step_decay in H.
           
           
           eapply DSEM.DryMachineLemmas.step_decay_invariant
           with (Hcompatible:= MTCH_compat _ _ _ MATCH Hcmpt); try eapply H; eauto.
           eapply MTCH_restrict_personal.
           auto.
           inversion MATCH. erewrite <- mtch_gtc0; eassumption.
         }
         {
           apply MTCH_update.
           apply MTCH_age.
           assumption.
           intros.
           assert (HH:= juicy_mem_access jm').
           rewrite <- HH.
           rewrite getCurPerm_correct.
           reflexivity.
         }
         {  assert (Hcmpt': DSEM.mem_compatible ds m) by
               (eapply MTCH_compat; eassumption).
            inversion Hcorestep.
             eapply ev_step_ax2 in H.
             destruct H as [T evSTEP].
            
           econstructor; simpl.
           - eassumption.
           - econstructor; try eassumption.
             Focus 3. reflexivity.
             Focus 2. eapply (MTCH_getThreadC _ _ _ _ _ _ _ Hthread).
             instantiate(1:=Hcmpt').
             apply MTCH_restrict_personal.
             assumption.
         }
       }
           
       (* suspend_step *)
       inversion MATCH; subst.
       inversion Htstep; subst.
       exists (DTP.updThreadC (mtch_cnt _ ctn) (Kblocked c)).
       split;[|split].
       (*Invariant*)
       { apply updCinvariant; assumption. }
       (*Match *)
       { apply MTCH_updt; assumption.        }
       (*Step*)
       { econstructor 4; try eassumption.
         - simpl. reflexivity.
         - eapply MTCH_compat; eassumption.
         - simpl. econstructor; try eassumption.
           + rewrite <- Hcode. symmetry. apply mtch_gtc.
           + reflexivity.
       }

       (*Conc step*)
       {
         destruct (conc_step_diagram m m' U js js' ds tid genv ev MATCH dinv Htid Hcmpt HschedN Htstep)
           as [ds' [ev' [dinv' [MTCH' step']]]]; eauto.
         exists ds'; split; [| split]; try assumption.
         econstructor 5; simpl; try eassumption.
         reflexivity.
       }
       
       (* step_halted *)
       exists ds.
       split; [|split]. 
       { assumption. }
       { assumption. }
       { inversion MATCH; subst. 
         assert (Htid':=Htid); apply mtch_cnt in Htid'.
         econstructor 6; try eassumption.
         simpl; reflexivity.
         simpl. eapply MTCH_compat; eassumption; instantiate(1:=Htid').
         eapply MTCH_halted; eassumption.
       }
       
           
       (* schedfail *)
       { exists ds.
       split;[|split]; try eassumption.
       econstructor 7; try eassumption; try reflexivity.
       unfold not; simpl; intros.
       apply Htid. inversion MATCH; apply mtch_cnt'; assumption. }
       
       Grab Existential Variables.
       - simpl. apply mtch_cnt. assumption.
       - assumption.
       - simpl. eapply MTCH_cnt ; eauto.
Qed.
  
  Lemma core_diagram:
    forall (m : Mem.mem)  (U0 U U': schedule) rmap pmap 
     (ds : dstate) (js js': jstate) 
     (m' : Mem.mem) genv,
   corestep (JMachineSem U0 rmap) genv (U,nil, js) m (U',nil, js') m' ->
   match_st js ds ->
   DSEM.invariant ds ->
   exists (ds' : dstate),
     DSEM.invariant ds' /\
     match_st js' ds' /\
     corestep (DMachineSem U0 pmap) genv (U,nil, ds) m (U',nil, ds') m'.
  Proof.
    intros. destruct (core_diagram' m U0 U U' ds js js' rmap0 pmap m' genv H0 H1 H) as [ds' [A[B C]]].
    exists ds'; split;[|split]; try assumption.
  Qed.

  
  Lemma halted_diagram:
    forall U ds js rmap pmap,
      fst (fst js) = fst (fst ds) ->
      halted (JMachineSem U rmap) js = halted (DMachineSem U pmap) ds.
        intros until pmap. destruct ds as [dp ?], js as [jp ?]; destruct dp, jp; simpl; intros HH; rewrite HH.
        reflexivity.
  Qed.

  Lemma jstep_empty_trace: forall genv U0 U tr tr' c m c' m' U' rmap,
      corestep (JMachineSem U0 rmap) genv (U,tr,c) m (U', tr', c') m' ->
      tr = nil /\ tr' = nil.
  Proof. intros. inversion H; simpl in *; subst; auto. Qed.
    

                   
  Lemma dstep_empty_trace: forall genv U0 U tr tr' c m c' m' U' rmap,
      corestep (DMachineSem U0 rmap) genv (U,tr,c) m (U', tr', c') m' ->
      tr = nil /\ tr' = nil.
  Proof. intros. inversion H; simpl in *; subst; auto. Qed.
  
End Parching.
(*Export Parching.*)
