Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.TheSchedule.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.dry_machine. Import Concur.
Require Import VST.concurrency.dry_machine_lemmas.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.sync_preds.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.ssromega. (*omega in ssrnat *)

(*The simulations*)
Require Import VST.sepcomp.wholeprog_simulations.

(*The semantics*)
Require Import VST.concurrency.JuicyMachineModule.
Require Import VST.concurrency.DryMachineSource.

(*General erasure*)
Require Import VST.concurrency.erasure_signature.

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

(* Where Does this lemma fit better?
 * Uses definitions from
 * concurrency.permissions.v and
 * veric.juicy_mem_lemmas.v          *)




Set Bullet Behavior "Strict Subproofs".

Module Parching <: ErasureSig.
  Import THE_JUICY_MACHINE.
  Module SCH:= THESCH.
  Module SEM:= THE_JUICY_MACHINE.SEM.
  Import SCH SEM.

  Module JMS := THE_JUICY_MACHINE.JSEM.
  Module JuicyMachine := THE_JUICY_MACHINE.JuicyMachine.
  Notation JMachineSem:= THE_JUICY_MACHINE.JMachineSem.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=THE_JUICY_MACHINE.JTP.

  Import JSEM.JuicyMachineLemmas.
  (*Module SCH:= ListScheduler NatTID.
  Module SEM:= DecayingSEM.


  Module JSEM := JuicyMachineShell SEM. (* JuicyMachineShell : Semantics -> ConcurrentSemanticsSig *)
  Module JuicyMachine := CoarseMachine SCH JSEM.
 (* CoarseMachine : Schedule -> ConcurrentSemanticsSig -> ConcurrentSemantics *)
  Notation JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=JuicyMachine.SIG.ThreadPool.
  Import JSEM.JuicyMachineLemmas.*)

  Import THE_DRY_MACHINE_SOURCE.
  Import DMS.

  (*UNCOMMENT THE LINE BELOW AFTER CHANGES ARE MADE (WHENEVER THE FILE COMPILES)*)
  (*Module DSEM := DMS.SEM*)
  Module DMS := DryMachine.
  Module DryMachine <: ConcurrentMachine:= DMS.DryConc.
  Notation DMachineSem:= DryMachine.MachineSemantics.
  Notation dstate:= DMS.DTP.t.
  Notation dmachine_state:= DryMachine.MachState.
  Module DTP<: ThreadPoolSig := DMS.DTP. (* DSEM.ThreadPool. *)
  Module DTP':= DryMachine.ThreadPool.

 (* Module SourceTPWF:= ThreadPoolWF DSEM DryMachine.*)


  Import THE_DRY_MACHINE_SOURCE.DryMachineLemmas event_semantics.



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
                    ssrbool.isSome (JSEM.ThreadPool.lockRes js a) = ssrbool.isSome (DTP.lockRes ds a))
                (mtch_locksEmpty: forall lock dres,
                    JSEM.ThreadPool.lockRes js lock = Some (None) ->
                    DTP.lockRes ds lock = Some dres ->
                   dres = (empty_map, empty_map))
                (mtch_locksRes: forall lock jres dres,
                    JSEM.ThreadPool.lockRes js lock = Some (Some jres) ->
                    DTP.lockRes ds lock = Some dres ->
                     forall b ofs,
                       juicy_mem.perm_of_res (resource_at jres (b, ofs)) = (dres.1 !! b) ofs )
                (mtch_locksRes: forall lock jres dres,
                    JSEM.ThreadPool.lockRes js lock = Some (Some jres) ->
                    DTP.lockRes ds lock = Some dres ->
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
      forall (cnt: DTP.containsThread ds i)
      (MTCH: match_st js ds),
      forall b ofs,
        ((DTP.getThreadR cnt).1 !! b) ofs =
        juicy_mem.perm_of_res ((JTP.getThreadR (MTCH_cnt' MTCH cnt)) @ (b, ofs)).
  Proof. intros. inversion MTCH. symmetry. apply mtch_perm1; eauto. Qed.

  Lemma MTCH_perm2': forall {js ds i},
      forall (cnt: DTP.containsThread ds i)
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


  Lemma MTCH_locks: forall ds js laddr rmap,
      match_st js ds ->
      DMS.DTP.lockRes ds laddr = Some rmap ->
      exists x, JTP.lockRes js laddr = Some x.
  Proof.
    move=> ? js laddr ? MTCH HH.
    destruct (JTP.lockRes js laddr) eqn:AA.
    - exists l; reflexivity.
    - inversion MTCH.
      specialize (mtch_locks laddr).
      rewrite HH AA in mtch_locks; inversion mtch_locks.
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
    destruct (DTP'.lockRes_range_dec ds b ofs).
    - destruct e as [z [ineq dLR]].
      specialize (mtch_locks (b, z)).
      destruct ( DTP.lockRes ds (b, z)) eqn:AA; inversion dLR.
      destruct (JSEM.ThreadPool.lockRes js (b, z)) eqn:BB; inversion mtch_locks.
      erewrite JSEM.ThreadPool.lockSet_spec_2; eauto.
      erewrite DTP.lockSet_spec_2; eauto.
      rewrite BB; constructor.
      rewrite AA in dLR; inversion dLR.
    - destruct (JSEM.ThreadPool.lockRes_range_dec js b ofs).
      + clear e.
        destruct e0 as [z [ineq dLR]].
        specialize (mtch_locks (b, z)).
        destruct (JSEM.ThreadPool.lockRes js (b, z)) eqn:AA; inversion dLR.
        * destruct ( DTP.lockRes ds (b, z)) eqn:BB; inversion mtch_locks.
          erewrite JSEM.ThreadPool.lockSet_spec_2; eauto.
          erewrite DTP.lockSet_spec_2; eauto.
          rewrite BB; constructor.
        * rewrite AA in dLR; inversion dLR.
      + erewrite JSEM.ThreadPool.lockSet_spec_3; eauto.
        erewrite DTP.lockSet_spec_3; eauto.
  Qed.

  Lemma MTCH_compat: forall js ds m,
      match_st js ds ->
      JSEM.mem_compatible js m ->
      DryMachine.mem_compatible ds m.
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
      destruct (perm_of_sh _) eqn:?; inversion max_coh.
      apply perm_of_empty_inv in Heqo.
      subst.
      exfalso; apply shares.bot_unreadable; assumption.
      
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
      + assert (cnt2:= JTP.cntUpdateC' Htid).
        rewrite <- (JTP.gsoThreadCC ine cnt2 ) by assumption.
        inversion H0; subst.
          (* pose (cnt':=(@MTCH_cnt js tid ds H0 cnt)). *)
          assert (cnt2':= DTP.cntUpdateC' Htid').
          (*fold cnt';*)
          rewrite <- (DTP.gsoThreadCC ine cnt2') by assumption.
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
        (Hcmpt': DryMachine.mem_compatible ds m),
        restrPermMap (DryMachine.compat_th Hcmpt' Hi').1 =
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
        DryMachine.invariant ds ->
        DryMachine.threadHalted cnt'.
    Proof.
      intros.
      inversion H0; subst.
      econstructor.
     (* - assumption.*)
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
                        (DTP.updLockSet ds loc (dres1,dres2)).
    Proof. intros.
           constructor.
           + intros. apply DTP.cntUpdateL.
             destruct H; apply mtch_cnt.
             apply JTP.cntUpdateL' in H2; assumption.
           + intros. apply JTP.cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntUpdateL' in H2; assumption.
           + intros. rewrite JSEM.ThreadPool.gLockSetCode DTP.gLockSetCode.
             inversion H; subst. apply mtch_gtc.
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DTP.gLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DTP.gLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock DTP.gsslockResUpdLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock.
               rewrite DTP.gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
               assumption.
               assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock in H2; inversion H2.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H2. rewrite DTP.gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksEmpty; eassumption.
               assumption. assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H2.
               rewrite DTP.gsslockResUpdLock in H3.
               inversion H2; inversion H3; subst.
               apply H0.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H2. rewrite DTP.gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksRes; eassumption.
               assumption.
               assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H2.
               rewrite DTP.gsslockResUpdLock in H3.
               inversion H2; inversion H3; subst.
               apply H1.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H2. rewrite DTP.gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksRes0; eassumption.
               assumption.
               assumption.
    Qed.

    Lemma MTCH_updLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (JSEM.ThreadPool.updLockSet js loc None)
          (DTP.updLockSet ds loc (empty_map,empty_map)).
           intros.
           constructor.
           + intros. apply DTP.cntUpdateL.
             destruct H; apply mtch_cnt.
             apply JTP.cntUpdateL' in H0; assumption.
           + intros. apply JTP.cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntUpdateL' in H0; assumption.
           + intros. rewrite JSEM.ThreadPool.gLockSetCode DTP.gLockSetCode.
             inversion H; subst. apply mtch_gtc.
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DTP.gLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DTP.gLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock DTP.gsslockResUpdLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock.
               rewrite DTP.gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
               assumption. assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite DTP.gsslockResUpdLock in H1; inversion H1; reflexivity.
             * rewrite DTP.gsolockResUpdLock in H1.
               rewrite JSEM.ThreadPool.gsolockResUpdLock in H0.
               inversion H. eapply mtch_locksEmpty; eassumption.
               assumption.
               assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H0.
               rewrite DTP.gsslockResUpdLock in H1.
               inversion H0.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H0. 2: assumption.
               rewrite DTP.gsolockResUpdLock in H1. 2: assumption.
               inversion H. eapply mtch_locksRes; eassumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H0.
               rewrite DTP.gsslockResUpdLock in H1.
               inversion H0.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H0. 2: assumption.
               rewrite DTP.gsolockResUpdLock in H1. 2: assumption.
               inversion H. eapply mtch_locksRes0; eassumption.
    Qed.

    Lemma MTCH_remLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (JSEM.ThreadPool.remLockSet js loc)
          (DTP.remLockSet ds loc).
           intros.
           constructor.
           + intros. apply DTP.cntRemoveL.
             destruct H; apply mtch_cnt.
             apply JTP.cntRemoveL' in H0; assumption.
           + intros. apply JTP.cntRemoveL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntRemoveL' in H0; assumption.
           + intros. rewrite JSEM.ThreadPool.gRemLockSetCode DryMachine.ThreadPool.gRemLockSetCode.
             inversion H; subst. apply mtch_gtc.
           + intros. rewrite JSEM.ThreadPool.gRemLockSetRes  DryMachine.ThreadPool.gRemLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite JSEM.ThreadPool.gRemLockSetRes  DryMachine.ThreadPool.gRemLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResRemLock DTP.gsslockResRemLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResRemLock.
               2: exact NEQ.
               rewrite DTP.gsolockResRemLock.
               2: exact NEQ.
               inversion H. solve[apply mtch_locks].
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite DTP.gsslockResRemLock in H1; inversion H1; reflexivity.
             * rewrite DTP.gsolockResRemLock in H1.
               2: exact NEQ.
               rewrite JSEM.ThreadPool.gsolockResRemLock in H0.
               2: exact NEQ.
               inversion H. eapply mtch_locksEmpty; eassumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResRemLock in H0.
               rewrite DTP.gsslockResRemLock in H1.
               inversion H0.
             * rewrite JSEM.ThreadPool.gsolockResRemLock in H0.
               2: exact NEQ.
               rewrite DTP.gsolockResRemLock in H1.
               2: exact NEQ.
               inversion H. eapply mtch_locksRes; eassumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResRemLock in H0.
               rewrite DTP.gsslockResRemLock in H1.
               inversion H0.
             * rewrite JSEM.ThreadPool.gsolockResRemLock in H0.
               2: exact NEQ.
               rewrite DTP.gsolockResRemLock in H1.
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
                 (DTP.updThread Hi' Kc (p1,p2)).
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
        + assert (jcnt2:= @JTP.cntUpdateC' _ _ _ Kc Hi Htid).
          assert (dcnt2:= @DTP.cntUpdateC' _ _ _ Kc Hi' Htid').
          rewrite (JTP.gsoThreadCode n jcnt2); auto.
          rewrite (DTP.gsoThreadCode n dcnt2); auto.
      - destruct (NatTID.eq_tid_dec i tid).
        + subst.
          rewrite (JTP.gssThreadRes Htid); auto.
          rewrite (DTP.gssThreadRes Htid'); auto.
        + assert (jcnt2:= @JTP.cntUpdateC' _ _ _ Kc Hi Htid).
          assert (dcnt2:= @DTP.cntUpdateC' _ _ _ Kc Hi' Htid').
          rewrite (JTP.gsoThreadRes jcnt2); auto.
          rewrite (DTP.gsoThreadRes dcnt2); auto.
      - destruct (NatTID.eq_tid_dec i tid).
        + subst.
          rewrite (JTP.gssThreadRes Htid); auto.
          rewrite (DTP.gssThreadRes Htid'); simpl; auto.
        + assert (jcnt2:= @JTP.cntUpdateC' _ _ _ Kc Hi Htid).
          assert (dcnt2:= @DTP.cntUpdateC' _ _ _ Kc Hi' Htid').
          rewrite (JTP.gsoThreadRes jcnt2); auto.
          rewrite (DTP.gsoThreadRes dcnt2); auto.
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

    Definition match_rmap_perm (rmap : rmap) (pmap: access_map * access_map): Prop:=
      forall b ofs, perm_of_res (rmap @ (b, ofs)) = pmap.1 !! b ofs /\
               pmap.2 = empty_map.

     Definition no_locks_perm (rmap : rmap): Prop:=
      forall b ofs, perm_of_res_lock (rmap @ (b, ofs)) = None.

    Lemma MTCH_initial:
      forall  c rmap pmap,
        match_rmap_perm rmap pmap ->
        no_locks_perm rmap ->
        match_st (JSEM.initial_machine rmap c) (DryMachine.initial_machine (*genv*) pmap.1 c).
    Proof.
      intros.
      constructor.
      - intro i. unfold JTP.containsThread, JSEM.initial_machine; simpl.
        unfold DTP.containsThread, DryMachine.initial_machine; simpl.
        trivial.
      - intro i. unfold JTP.containsThread, JSEM.initial_machine; simpl.
        unfold DTP.containsThread, DryMachine.initial_machine; simpl.
        trivial.
      - reflexivity.
      - intros.
        unfold JTP.getThreadR; unfold JSEM.initial_machine; simpl.
        unfold DTP.getThreadR; unfold DryMachine.initial_machine; simpl.
        unfold match_rmap_perm in H. apply H.
      - intros.
        unfold JTP.getThreadR; unfold JSEM.initial_machine; simpl.
        rewrite empty_map_spec; apply H0.
      - unfold empty_rmap, "@"; simpl.
        reflexivity.
      - unfold DTP.lockRes, DryMachine.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H2; inversion H2.
      - unfold DTP.lockRes, DryMachine.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H2; inversion H2.
      - unfold DTP.lockRes, DryMachine.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H2; inversion H2.
    Qed.

    (*Lemma to prove MTCH_latestThread*)
    Lemma contains_iff_num:
      forall js ds
        (Hcnt: forall i, JTP.containsThread js i <-> DTP.containsThread ds i),
        JSEM.ThreadPool.num_threads js = DryMachine.ThreadPool.num_threads ds.
    Proof.
      intros.
      unfold JTP.containsThread, DTP.containsThread in *.
      remember (JSEM.ThreadPool.num_threads js).
      remember (DryMachine.ThreadPool.num_threads ds).
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

    Lemma MTCH_addThread: forall js ds parg arg phi res lres,
        match_st js ds ->
        (forall b0 ofs0, perm_of_res (phi@(b0, ofs0)) = res !! b0 ofs0) ->
        (forall b0 ofs0, perm_of_res_lock (phi@(b0, ofs0)) = lres !! b0 ofs0) ->
        match_st
          (JTP.addThread js parg arg phi)
          (DTP.addThread ds parg arg (res,lres)).
    Proof.
      intros ? ? ? ? ? ? ? MATCH DISJ. constructor.
      - intros tid HH.
        apply JTP.cntAdd' in HH. destruct HH as [[HH ineq] | HH].
        + apply DTP.cntAdd. inversion MATCH. apply mtch_cnt. assumption.
        +
          erewrite MTCH_latestThread in HH.
          rewrite HH.
          apply DryMachine.ThreadPool.contains_add_latest.
          assumption.
      - intros tid HH.
        apply DTP.cntAdd' in HH. destruct HH as [[HH ineq] | HH].
        + apply JTP.cntAdd. inversion MATCH. eapply  mtch_cnt'; assumption.
        + erewrite <- MTCH_latestThread in HH.
          rewrite HH.
          apply JSEM.ThreadPool.contains_add_latest.
          assumption.
      - intros.
        destruct (JTP.cntAdd' Htid) as [[jcnt jNLast]| jLast];
          destruct (DTP.cntAdd' Htid') as [[dcnt dNLast]| dLast].
        * erewrite JSEM.ThreadPool.gsoAddCode; try eassumption.
          erewrite DryMachine.ThreadPool.gsoAddCode; try eassumption.
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
          erewrite DryMachine.ThreadPool.gssAddCode; try eassumption.
          reflexivity.
      - intros.
        destruct (JTP.cntAdd' Htid) as [[jcnt jNLast]| jLast];
          destruct (DTP.cntAdd' Htid') as [[dcnt dNLast]| dLast].
        * erewrite JSEM.ThreadPool.gsoAddRes; try eassumption.
          erewrite DryMachine.ThreadPool.gsoAddRes; try eassumption.
          inversion MATCH. eapply mtch_perm1.
        * contradict jNLast.
          rewrite <- (MTCH_latestThread js ds) in dLast.
          rewrite dLast; reflexivity.
          assumption.
        * contradict dNLast.
          rewrite (MTCH_latestThread js ds) in jLast.
          rewrite jLast; reflexivity.
          assumption.
        * erewrite JSEM.ThreadPool.gssAddRes; try eassumption.
          erewrite DryMachine.ThreadPool.gssAddRes; try eassumption.
          apply DISJ.
      - intros.
        destruct (JTP.cntAdd' Htid) as [[jcnt jNLast]| jLast];
          destruct (DTP.cntAdd' Htid') as [[dcnt dNLast]| dLast].
        * erewrite JSEM.ThreadPool.gsoAddRes; try eassumption.
          erewrite DryMachine.ThreadPool.gsoAddRes; try eassumption.
          inversion MATCH. eapply mtch_perm2.
        * contradict jNLast.
          rewrite <- (MTCH_latestThread js ds) in dLast.
          rewrite dLast; reflexivity.
          assumption.
        * contradict dNLast.
          rewrite (MTCH_latestThread js ds) in jLast.
          rewrite jLast; reflexivity.
          assumption.
        * erewrite JSEM.ThreadPool.gssAddRes; try eassumption.
          erewrite DryMachine.ThreadPool.gssAddRes; try eassumption.
          simpl; apply H.
      - intros. rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
        inversion MATCH. apply mtch_locks.
      - intros lock dres.
        rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
        inversion MATCH. apply mtch_locksEmpty.
      - intros lock jres dres .
        rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
        inversion MATCH. apply mtch_locksRes.
      - intros lock jres dres .
        rewrite JTP.gsoAddLPool DTP.gsoAddLPool.
        inversion MATCH. apply mtch_locksRes0.
        Grab Existential Variables.
        assumption.
        assumption.
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
        apply mtch_perm1.
      - intros.
        erewrite <- JSEM.JuicyMachineLemmas.getThreadR_age. simpl.
        rewrite JSEM.perm_of_age_lock.
        apply mtch_perm2.
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
      -
        intros. apply JSEM.JuicyMachineLemmas.LockRes_age_content2 in H1.
        destruct H1 as [r [AA BB]].
        rewrite BB.
        rewrite JSEM.perm_of_age_lock.
        eapply mtch_locksRes0; eassumption.

        Grab Existential Variables.
        eapply JSEM.JuicyMachineLemmas.cnt_age; eassumption.
        eapply JSEM.JuicyMachineLemmas.cnt_age; eassumption.
        eapply JSEM.JuicyMachineLemmas.cnt_age; eassumption.
    Qed.

    Lemma MTCH_tp_update: forall js ds phi js' phi',
        match_st js ds -> tp_update js phi js' phi' ->
        match_st js' ds.
    Proof.
      inversion 1; subst.
      intros (Hl & Hr & Hj & Hcnt & Hget & Hlock). constructor.
      - intros i HH. apply Hcnt in HH.
        apply mtch_cnt; assumption.
      - intros i HH. apply Hcnt.
        apply mtch_cnt'; assumption.
      - intros i cnt cnt'.
        assert (JTP.containsThread js i) as cnt0 by (apply Hcnt; auto).
        specialize (Hget _ cnt0) as [Hget _].
        replace (proj2 _ _) with cnt in Hget by apply proof_irr.
        rewrite <- Hget; auto.
      - intros.
        assert (JTP.containsThread js tid) as cnt0 by (apply Hcnt; auto).
        specialize (Hget _ cnt0) as (_ & _ & Hget).
        replace (proj2 _ _) with Htid in Hget by apply proof_irr.
        rewrite <- Hget; auto.
      - intros.
        assert (JTP.containsThread js tid) as cnt0 by (apply Hcnt; auto).
        specialize (Hget _ cnt0) as (_ & _ & Hget).
        replace (proj2 _ _) with Htid in Hget by apply proof_irr.
        rewrite <- Hget; auto.
      - intros.
        destruct Hlock as (_ & _ & -> & _); auto.
      - intros.
        destruct Hlock as (_ & _ & Hlock & _); rewrite Hlock in H0.
        eapply mtch_locksEmpty; eassumption.
      - intros.
        destruct Hlock as (_ & _ & Hlock & _); rewrite Hlock in H0.
        eapply mtch_locksRes; eassumption.
      - intros.
        destruct Hlock as (_ & _ & Hlock & _); rewrite Hlock in H0.
        eapply mtch_locksRes0; eassumption.
    Qed.

    Lemma init_diagram:
      forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
        (vals : list Values.val) (m : Mem.mem) rmap pmap main genv h,
        init_inj_ok j m ->
        match_rmap_perm rmap pmap ->
        no_locks_perm rmap ->
        initial_core (JMachineSem U (Some rmap)) h genv m main vals = Some ((U, nil, js),None) ->
        exists (ds : dstate),
          initial_core (DMachineSem U (Some pmap)) h genv m main vals = Some ((U, nil,ds),None) /\
          DryMachine.invariant ds /\
          match_st js ds.
    Proof.
      intros.

      (* Build the structured injection*)
      (* exists (initial_SM (valid_block_dec m) (valid_block_dec m) (fun _ => false) (fun _ => false) j).*)

      (* Build the dry state *)
      simpl in H2.
      unfold JuicyMachine.init_machine in H2.
      unfold JSEM.init_mach in H2. simpl in H2.
      destruct ( initial_core (msem JSEM.ThreadPool.SEM.Sem) 0 genv m main vals) as [[? ?]|] eqn:C; try solve[inversion H2].
      destruct o; inv H2.
      exists (DryMachine.initial_machine pmap.1 c).

      split; [|split].

      (*Proofs*)
      - simpl.
        unfold DryMachine.init_machine.
        unfold DryMachine.init_mach.
        rewrite C.
        f_equal.
      - (* THIS COULD BE A LEMMA*)
        eapply initial_invariant0.

      - apply MTCH_initial; assumption.
    Qed.


  Lemma conc_step_diagram:
    forall m m' U js js' ds i genv ev
      (MATCH: match_st js ds)
      (dinv: DryMachine.invariant ds)
      (Hi: JSEM.ThreadPool.containsThread js i)
      (Hcmpt: JSEM.mem_compatible js m)
      (HschedN: schedPeek U = Some i)
      (Htstep:  JSEM.syncStep true genv Hi Hcmpt js' m' ev),
      exists ds' : dstate, exists ev',
        DryMachine.invariant ds' /\
        match_st js' ds' /\
        DryMachine.syncStep true genv (MTCH_cnt MATCH Hi) (MTCH_compat _ _ _ MATCH Hcmpt) ds' m'
                      ev'.
  Proof.

    intros.
    inversion Htstep; try subst.

    (* step_acquire  *)
    {
    assert (Htid':= MTCH_cnt MATCH Hi).
    pose (inflated_delta1:=
            fun loc => match (d_phi @ loc ) with
                      NO s _ => if Share.EqDec_share s Share.bot then None else Some ( perm_of_res (phi' @ loc))
                    | _ => Some (perm_of_res (phi' @ loc))
                    end).
    pose (inflated_delta2:=
            fun loc =>  match (d_phi @ loc ) with
                       NO s _ => if Share.EqDec_share s Share.bot then None else
                                Some ( perm_of_res_lock (phi' @ loc))
                    | _ => Some (perm_of_res_lock (phi' @ loc))
                    end).
         pose (virtue1:= PTree.map
                                      (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                                         (inflated_delta1 (block, ofs))) (snd (getMaxPerm m)) ).

         pose (virtue2:= PTree.map
                                      (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                                         (inflated_delta2 (block, ofs))) (snd (getMaxPerm m)) ).
         assert (virtue_some1: forall l p, inflated_delta1 l = Some p ->
                             p = perm_of_res (phi' @ l)).
            {
              intros l p; unfold inflated_delta1.
              destruct (d_phi @ l); try solve[intros HH; inversion HH; reflexivity].
              destruct (proj_sumbool (Share.EqDec_share sh0 Share.bot));
                [congruence| intros HH; inversion HH; reflexivity]. }
            assert (virtue_some2: forall l p, inflated_delta2 l = Some p ->
                                        p = perm_of_res_lock (phi' @ l)).
            {
               intros l p; unfold inflated_delta2.
              destruct (d_phi @ l); try solve[intros HH; inversion HH; reflexivity].
              destruct ( proj_sumbool (Share.EqDec_share sh0 Share.bot));
                [congruence| intros HH; inversion HH; reflexivity]. }


            Inductive deltaMap_cases (dmap:delta_map) b ofs:=
            | DMAPS df p:  dmap ! b = Some df -> df ofs = Some p -> deltaMap_cases dmap b ofs
            | DNONE1 df:  dmap ! b = Some df -> df ofs = None -> deltaMap_cases dmap b ofs
            | DNONE2:  dmap ! b = None -> deltaMap_cases dmap b ofs.

            Lemma deltaMap_dec: forall dmap b ofs, deltaMap_cases dmap b ofs.
            Proof. intros. destruct (dmap ! b) eqn:H1; [destruct (o ofs) eqn:H2 | ]; econstructor; eassumption. Qed.

            assert (virtue_correct1: forall b ofs,
                       (computeMap (DTP.getThreadR Htid').1 virtue1)  !! b ofs
                       = perm_of_res (phi' @ (b, ofs))
                   ).
            { intros. simpl.
              destruct (deltaMap_dec virtue1 b0 ofs0).
              -  rewrite (computeMap_1 _ _ _ _ e e0).
                 move: e.
                 rewrite /virtue1 /inflated_delta1 PTree.gmap.
                 destruct (((getMaxPerm m).2) ! b0);
                   intros HH; inversion HH as [H0].
                 move :e0; rewrite -H0.
                 destruct (d_phi @ (b0, ofs0)); intros HH';
                 try solve[inversion HH'; reflexivity].
                 destruct (proj_sumbool (Share.EqDec_share sh0 Share.bot)); inversion HH'.
                 reflexivity.
              -  rewrite (computeMap_2 _ _ _ _ e).
                 move: e.
                 rewrite /virtue1 /inflated_delta1 PTree.gmap.
                 destruct (((getMaxPerm m).2) ! b0);
                   intros HH; inversion HH as [H0].
                 move :e0; rewrite -H0.
                 destruct (d_phi @ (b0, ofs0)) eqn:dphibo; intros HH';
                 try solve[inversion HH'].
                 destruct (proj_sumbool (Share.EqDec_share sh0 Share.bot)) eqn:isBot; inversion HH'.
                 move: Hadd_lock_res => /(resource_at_join _ _ _ (b0, ofs0)).
                 rewrite dphibo.
                 replace (NO sh0 n) with (NO Share.bot shares.bot_unreadable).
                 move => /join_comm
                 /(@join_unit1_e _ _ _ (NO Share.bot _) _ _ (NO_identity shares.bot_unreadable)) <-.
                 symmetry. inversion MATCH; auto.
                 destruct (Share.EqDec_share sh0 Share.bot); inversion isBot.
                 subst sh0; f_equal. apply proof_irr.
                 assumption.
              - rewrite (computeMap_3 _ _ _ _ e).
                move: e.
                rewrite /virtue1 /inflated_delta1 PTree.gmap.
                destruct (((getMaxPerm m).2) ! b0) eqn:isNO;
                  intros HH; try solve[inversion HH].
                clear HH.
                move: Hadd_lock_res => /(resource_at_join _ _ _ (b0, ofs0)).
                cut (d_phi @ (b0,ofs0) = NO Share.bot shares.bot_unreadable).
                { move => -> .
                  move => /join_comm
                          /(@join_unit1_e _ _ _ (NO Share.bot _) _ _ (NO_identity shares.bot_unreadable)) <-.
                  symmetry. inversion MATCH; auto.
                }
                destruct Hcmpt as [x Hcmpt']; inversion Hcmpt'.
                move: juice_join => /JSEM.compatible_lockRes_sub.
                move => /(_ _ _ His_unlocked) /(resource_at_join_sub _ _ (b0, ofs0)) .
                cut (x @ (b0, ofs0) = NO Share.bot shares.bot_unreadable).
                { move=> -> . elim=> X Join. inversion Join; subst.
                  apply permjoin.join_to_bot_l in RJ; subst sh1.
                  f_equal. apply proof_irr. }
                { inversion all_cohere.
                  specialize (max_coh (b0, ofs0)). move: isNO max_coh.
                  rewrite /max_access_at /access_at /getMaxPerm /PMap.get PTree.gmap1 /=.
                  destruct (((Mem.mem_access m).2) ! b0)=> HH; try solve[ inversion HH].
                  rewrite THE_JUICY_MACHINE.JSEM.Mem_canonical_useful /=.
                  destruct (x @ (b0, ofs0))=> /=.
                  - destruct (eq_dec sh0 Share.bot); subst => //.
                    intros; f_equal. apply proof_irr.
                  - destruct (perm_of_sh sh0) eqn:POSsh0;
                      try (intros ?; exfalso; assumption).
                    apply perm_of_empty_inv in POSsh0; subst.
                    exfalso; apply shares.bot_unreadable; assumption.
                  - tauto.
                }
            }

             assert (virtue_correct2: forall b ofs,
                       (computeMap (DTP.getThreadR Htid').2 virtue2)  !! b ofs
                       = perm_of_res_lock (phi' @ (b, ofs))
                   ).
            { intros. simpl.
              destruct (deltaMap_dec virtue2 b0 ofs0).
              -  rewrite (computeMap_1 _ _ _ _ e e0).
                 move: e.
                 rewrite /virtue2 /inflated_delta2 PTree.gmap.
                 destruct (((getMaxPerm m).2) ! b0);
                   intros HH; inversion HH as [H0].
                 move :e0; rewrite -H0.
                 destruct (d_phi @ (b0, ofs0)); intros HH';
                 try solve[inversion HH'; reflexivity].
                 destruct (proj_sumbool (Share.EqDec_share sh0 Share.bot)); inversion HH'.
                 reflexivity.
              -  rewrite (computeMap_2 _ _ _ _ e).
                 move: e.
                 rewrite /virtue2 /inflated_delta2 PTree.gmap.
                 destruct (((getMaxPerm m).2) ! b0);
                   intros HH; inversion HH as [H0].
                 move :e0; rewrite -H0.
                 destruct (d_phi @ (b0, ofs0)) eqn:dphibo; intros HH';
                 try solve[inversion HH'].
                 destruct (proj_sumbool (Share.EqDec_share sh0 Share.bot)) eqn:isBot; inversion HH'.
                 move: Hadd_lock_res => /(resource_at_join _ _ _ (b0, ofs0)).
                 rewrite dphibo;
                 replace (NO sh0 n) with (NO Share.bot shares.bot_unreadable).
                 move => /join_comm
                         /(@join_unit1_e _ _ _ (NO Share.bot _) _ _ (NO_identity shares.bot_unreadable)) <-.
                 symmetry. inversion MATCH; auto.
                 destruct (Share.EqDec_share sh0 Share.bot); inversion isBot; auto.
                 subst sh0; f_equal; apply proof_irr.
                 assumption.
              - rewrite (computeMap_3 _ _ _ _ e).
                move: e.
                rewrite /virtue2 /inflated_delta2 PTree.gmap.
                destruct (((getMaxPerm m).2) ! b0) eqn:isNO;
                  intros HH; try solve[inversion HH].
                clear HH.
                move: Hadd_lock_res => /(resource_at_join _ _ _ (b0, ofs0)).
                cut (d_phi @ (b0,ofs0) = NO Share.bot shares.bot_unreadable).
                { move => -> .
                  move => /join_comm /(@join_unit1_e _ _ _ (NO Share.bot _) _ _
                                                    (NO_identity shares.bot_unreadable)) <-.
                  symmetry. inversion MATCH; auto.
                }
                destruct Hcmpt as [x Hcmpt']; inversion Hcmpt'.
                move: juice_join => /JSEM.compatible_lockRes_sub.
                move => /(_ _ _ His_unlocked) /(resource_at_join_sub _ _ (b0, ofs0)) .
                cut (x @ (b0, ofs0) = NO Share.bot shares.bot_unreadable).
                { move=> -> . elim=> X Join. inversion Join; subst.
                  apply permjoin.join_to_bot_l in RJ.
                  subst. f_equal; apply proof_irr. }
                { inversion all_cohere.
                  specialize (max_coh (b0, ofs0)). move: isNO max_coh.
                  rewrite /max_access_at /access_at /getMaxPerm /PMap.get PTree.gmap1 /=.
                  destruct (((Mem.mem_access m).2) ! b0)=> HH; try solve[ inversion HH].
                  rewrite THE_JUICY_MACHINE.JSEM.Mem_canonical_useful /=.
                  destruct (x @ (b0, ofs0))=> /=.
                  - destruct (eq_dec sh0 Share.bot) eqn:?; subst => //.
                    intros; f_equal; apply proof_irr.
                  - destruct (perm_of_sh sh0) eqn:POSsh0;
                      try (intros ?; exfalso; assumption).
                    apply perm_of_empty_inv in POSsh0; subst.
                    exfalso; apply shares.bot_unreadable; assumption.
                  - tauto.
                }
            }


         pose (ds':= DTP.updThread Htid' (Kresume c Vundef)
                  (computeMap
                     (DTP.getThreadR Htid').1 virtue1,
              computeMap
                     (DTP.getThreadR Htid').2 virtue2)).
         pose (ds'':= DTP.updLockSet ds'
                      (b, Ptrofs.intval ofs) (empty_map,empty_map)).
         exists ds'', (DryMachine.Events.acquire (b, Ptrofs.intval ofs) (Some (virtue1, virtue2)) ).
         split; [|split].
    - { (* invariant ds''*)

        unfold ds''.
        rewrite DryMachine.ThreadPool.updLock_updThread_comm.
        pose (ds0:= (DryMachine.ThreadPool.updLockSet ds (b, (Ptrofs.intval ofs)) (empty_map,empty_map))).

        cut (DryMachine.invariant ds0).
        { (* Proving: invariant ds0' *)
          intros dinv0.
          apply updThread_inv.

          - assumption.
          - intros.
            assert (joins phi' (JTP.getThreadR (MTCH_cnt' MATCH cnt))).
            {assert (Hcmpt':=Hcmpt).
              assert (Hcmpt'':=Hcmpt).
              eapply
                JMS.JuicyMachineLemmas.compatible_threadRes_join
                with (cnti:=Hi)(cntj:=(MTCH_cnt' MATCH cnt))
                in Hcmpt'; auto.
              eapply
                JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join
              with (cnti:=(MTCH_cnt' MATCH cnt))
                     (l:=(b, Ptrofs.intval ofs))
                     (phi:=d_phi)
                in Hcmpt''; auto.
              eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
              eapply joins_comm; auto.
            }

            split;
            eapply permDisjoint_permMapsDisjoint; intros b0 ofs0; simpl.
            + rewrite virtue_correct1 (MTCH_perm' _ MATCH b0 ofs0).
              apply joins_permDisjoint.
              apply resource_at_joins; assumption.
            + rewrite virtue_correct2 (MTCH_perm2' _ MATCH b0 ofs0).
              apply joins_permDisjoint_lock.
              apply resource_at_joins; assumption.
          - intros; intros b0 ofs0.
            destruct (NatTID.eq_tid_dec i j).
            + subst j.
              rewrite virtue_correct2 (MTCH_perm' _ MATCH b0 ofs0).
              contradiction.
            + rewrite virtue_correct2 (MTCH_perm' _ MATCH b0 ofs0).
              assert (joins phi' (JTP.getThreadR (MTCH_cnt' MATCH cnt))).
              {assert (Hcmpt':=Hcmpt).
               assert (Hcmpt'':=Hcmpt).
               eapply
                 JMS.JuicyMachineLemmas.compatible_threadRes_join
               with (cnti:=Hi)(cntj:=(MTCH_cnt' MATCH cnt))
                 in Hcmpt'; auto.
               eapply
                 JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join
               with (cnti:=(MTCH_cnt' MATCH cnt))
                      (l:=(b, Ptrofs.intval ofs))
                      (phi:=d_phi)
                 in Hcmpt''; auto.
               eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
               eapply joins_comm; auto.
              }


              apply perm_coh_joins.
              apply joins_comm; apply resource_at_joins;
              assumption.

          - intros; intros b0 ofs0.
            destruct (NatTID.eq_tid_dec i j).
            + subst j.
              contradiction.
            + rewrite virtue_correct1 (MTCH_perm2' _ MATCH b0 ofs0).
              assert (joins phi' (JTP.getThreadR (MTCH_cnt' MATCH cnt))).
              {assert (Hcmpt':=Hcmpt).
               assert (Hcmpt'':=Hcmpt).
               eapply
                 JMS.JuicyMachineLemmas.compatible_threadRes_join
               with (cnti:=Hi)(cntj:=(MTCH_cnt' MATCH cnt))
                 in Hcmpt'; auto.
               eapply
                 JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join
               with (cnti:=(MTCH_cnt' MATCH cnt))
                      (l:=(b, Ptrofs.intval ofs))
                      (phi:=d_phi)
                 in Hcmpt''; auto.
               eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
               eapply joins_comm; auto.
              }
              apply perm_coh_joins.
              apply resource_at_joins;
              assumption.
          - intros l pmap0.
            destruct (AMap.E.eq_dec l (b, Ptrofs.intval ofs)).
            + subst l; rewrite DMS.DTP.gssLockRes; simpl; intros HH; inversion HH; simpl.
              split; apply empty_disjoint'.
            + rewrite DMS.DTP.gsoLockRes; auto; simpl; intros HH.
              assert (exists pmap1, JTP.lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite HH in mtch_locks.
                destruct (JTP.lockRes js l).
                - exists l0; reflexivity.
                - inversion mtch_locks.
              }
              destruct H as [pmap1 HH'].
              destruct pmap1.
              * assert (joins r phi').
               { assert (Hcmpt':=Hcmpt).
                 assert (Hcmpt'':=Hcmpt).
                 eapply
                   JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join
                 with (cnti:=Hi)
                        (l:=l)
                        (phi:=r)
                   in Hcmpt'; auto.
                 eapply
                   JSEM.compatible_lockRes_join
                 with (l2:=(b, Ptrofs.intval ofs))
                        (l1:=l)
                        (phi2:=d_phi)
                        (phi1:=r)
                   in Hcmpt''; auto.
                 eapply joins_comm.
                 eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
                 eapply joins_comm; auto. }
               split;
                 eapply permDisjoint_permMapsDisjoint; intros b0 ofs0.
               -- rewrite virtue_correct1.
                inversion MATCH.
                erewrite <- mtch_locksRes; eauto.
                apply joins_permDisjoint;
                  apply resource_at_joins; assumption.
               -- rewrite virtue_correct2.
                  inversion MATCH.
                  erewrite <- mtch_locksRes0; eauto.
                  apply joins_permDisjoint_lock;
                    apply resource_at_joins; assumption.
              * inversion MATCH.
                specialize (mtch_locksEmpty l pmap0 HH' HH);
                  subst pmap0;
                  simpl; split; apply permDisjoint_permMapsDisjoint; intros b0 ofs0;
                rewrite empty_map_spec;
                apply permDisjoint_None.
          - intros l pmap0.
            destruct (AMap.E.eq_dec l (b, Ptrofs.intval ofs)); simpl.
            + subst l; rewrite DMS.DTP.gssLockRes; simpl; intros HH; inversion HH; simpl.
              (*here*)
              split; [apply permCoh_empty | apply permCoh_empty'].
              { move=> b0 ofs0;
                  rewrite virtue_correct2.
                apply perm_of_res_lock_not_Freeable. }

            + rewrite DMS.DTP.gsoLockRes; auto; simpl; intros HH.
              assert (HH':=HH).
              eapply MTCH_locks in HH'; eauto.
              destruct HH' as [x HH'].
              destruct x.
              * assert (joins r phi').
               { assert (Hcmpt':=Hcmpt).
                 assert (Hcmpt'':=Hcmpt).
                 eapply
                   JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join
                 with (cnti:=Hi)
                        (l:=l)
                        (phi:=r)
                   in Hcmpt'; auto.
                 eapply
                   JSEM.compatible_lockRes_join
                 with (l2:=(b, Ptrofs.intval ofs))
                        (l1:=l)
                        (phi2:=d_phi)
                        (phi1:=r)
                   in Hcmpt''; auto.
                 eapply joins_comm.
                 eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
                 eapply joins_comm; auto. }
                split; intros b0 ofs0.
                -- rewrite virtue_correct2.
                   inversion MATCH.
                   erewrite <- mtch_locksRes; eauto.
                   apply perm_coh_joins;
                     apply resource_at_joins; assumption.
                -- rewrite virtue_correct1.
                   inversion MATCH.
                   erewrite <- mtch_locksRes0; eauto.
                   apply perm_coh_joins;
                     apply resource_at_joins;
                     apply joins_comm; assumption.
              * inversion MATCH.
                specialize (mtch_locksEmpty l _ HH' HH).
                subst pmap0; split; intros b0 ofs0;
                simpl; rewrite empty_map_spec.

                apply perm_coh_empty_2.
                rewrite virtue_correct2.
                apply perm_of_res_lock_not_Freeable.
                apply perm_coh_empty_1.
          - simpl. intros b0 ofs0.
            rewrite virtue_correct1 virtue_correct2.
            eapply perm_coh_self.
        }

            { apply updLock_inv.
              - assumption.
              - intros.
                Lemma permMapsDisjoint2_empty: forall rmap,
                    permMapsDisjoint2 (empty_map, empty_map) rmap.
                Proof.
                  intros rmap.
                  split; simpl;
                  apply permDisjoint_permMapsDisjoint;
                  intros b ofs.
                  - rewrite empty_map_spec.
                    apply permDisjoint_None.
                  - rewrite empty_map_spec.
                    apply permDisjoint_None.
                Qed.
                apply permMapsDisjoint2_empty.

              - intros.
                apply permMapsDisjoint2_comm.
                apply permMapsDisjoint2_empty.
              - intros.
                split; [apply permCoh_empty | apply permCoh_empty'].
                { move=> b0 ofs0.
                  apply (invariant_not_freeable) with (b:=b0)(ofs:= ofs0) in dinv.
                  destruct dinv as [AA BB].
                  eapply BB in H0.
                  destruct ((rmap'0.2) # b0 ofs0); try constructor.
                  destruct p; try constructor.
                  exfalso; apply H0; reflexivity. }
              - simpl.
                apply permCoh_empty'.
              - intros.
                split; [apply permCoh_empty | apply permCoh_empty'].
                { move=> b0 ofs0.
                  rewrite (MTCH_perm2' _ MATCH).
                  apply perm_of_res_lock_not_Freeable. }
              - simpl; intros.
                cut (JSEM.ThreadPool.lockRes js (b, ofs0) = None).
                { intros HH. inversion MATCH.
                  specialize (mtch_locks (b, ofs0)).
                  rewrite HH in mtch_locks.
                  clear - mtch_locks.
                  destruct (DTP.lockRes ds (b, ofs0)) eqn:AA; try reflexivity.
                  - inversion mtch_locks.
                }
                {(*the cut*)
                  move HJcanwrite at bottom.
                  destruct Hcmpt as [all_juice Hcmpt].
                  inversion Hcmpt.
                  unfold JSEM.juicyLocks_in_lockSet in jloc_in_set.
                  eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
                  destruct juice_join.
                  apply resource_at_join with (loc:=(b, Ptrofs.intval ofs)) in H0.
                  rewrite HJcanwrite in H0.
                  inversion H0.
                  - subst.
                    symmetry in H6.
                    apply jloc_in_set in H6.
                    assert (VALID:= JSEM.compat_lr_valid Hcompatible).
                    specialize (VALID b (Ptrofs.intval ofs)).
                    unfold JSEM.ThreadPool.lockRes in VALID.
                    destruct (AMap.find (elt:=juicy_machine.LocksAndResources.lock_info)
                                        (b, Ptrofs.intval ofs) (JSEM.ThreadPool.lockGuts js)) eqn:AA;
                      rewrite AA in H6; try solve[inversion H6].
                    apply VALID. auto.
                  -
                    symmetry in H6.
                    apply jloc_in_set in H6.
                    assert (VALID:= JSEM.compat_lr_valid Hcompatible).
                    specialize (VALID b (Ptrofs.intval ofs)).
                    unfold JSEM.ThreadPool.lockRes in VALID.
                    destruct (AMap.find (elt:=juicy_machine.LocksAndResources.lock_info)
                                        (b, Ptrofs.intval ofs) (JSEM.ThreadPool.lockGuts js)) eqn:AA;
                      rewrite AA in H6; try solve[inversion H6].
                    apply VALID. auto.
                }
              - simpl. intros ofs0 ineq. move HJcanwrite at bottom.
                cut ( JSEM.ThreadPool.lockRes js (b, ofs0) = None).
                { intros HH. inversion MATCH.
                  specialize (mtch_locks (b, ofs0)). rewrite HH in mtch_locks.
                  destruct (DTP.lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks; auto. }
                {
                  destruct (JSEM.ThreadPool.lockRes js (b, ofs0)) eqn:MAP; try reflexivity. exfalso.
                  move HJcanwrite at bottom.
                  destruct Hcmpt as [all_juice Hcmpt].
                  inversion Hcmpt.
                  unfold JSEM.juicyLocks_in_lockSet in jloc_in_set.
                  eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
                  destruct juice_join.
                  apply resource_at_join with (loc:=(b, Ptrofs.intval ofs)) in H.
                  rewrite HJcanwrite in H.
                  inversion H.
                  -
                    symmetry in H5.
                    apply jloc_in_set in H5.
                    assert (VALID:= JSEM.compat_lr_valid Hcompatible).
                    specialize (VALID b ofs0).
                    rewrite MAP in VALID.
                    apply VALID in ineq.
                    move ineq at bottom.
                    unfold JSEM.ThreadPool.lockRes in ineq; rewrite ineq in H5.
                    inversion H5.
                  -
                    symmetry in H5.
                    apply jloc_in_set in H5.
                    assert (VALID:= JSEM.compat_lr_valid Hcompatible).
                    specialize (VALID b ofs0).
                    rewrite MAP in VALID.
                    apply VALID in ineq.
                    move ineq at bottom.
                    unfold JSEM.ThreadPool.lockRes in ineq; rewrite ineq in H5.
                    inversion H5.

                }
            }
      }
    - unfold ds''.
      apply match_st_age_tp_to.
      apply MTCH_updLockN.
      unfold ds'.
      apply MTCH_update; auto.

    - assert (H: exists l, DTP.lockRes ds (b, Ptrofs.intval ofs) = Some l).
      { inversion MATCH; subst.
        specialize (mtch_locks (b, (Ptrofs.intval ofs) )).
        rewrite His_unlocked in mtch_locks.
        destruct (DTP.lockRes ds (b, Ptrofs.intval ofs));
          try solve[inversion mtch_locks]. exists l; reflexivity. }
      destruct H as [l dlockRes].
      assert (Hlt'':  permMapLt (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
                                              (DryMachine.ThreadPool.getThreadR
                                                 (MTCH_cnt MATCH Hi)).2 LKSIZE_nat)
                                (getMaxPerm m)).
      { intros b0 ofs0.
        move: (Hlt' b0 ofs0).
        (*Do the cases *)
        destruct (peq b b0);
          [subst b0;
            destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
        - do 2 (rewrite setPermBlock_same; auto).
        - apply Intv.range_notin in n; [|simpl; pose proof LKSIZE_pos; omega].
          do 2 (rewrite setPermBlock_other_1; auto).

          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt; inversion all_cohere.
          rewrite -JSEM.juic2Perm_locks_correct.
          rewrite -(MTCH_perm2 _ MATCH); auto.
          apply JMS.mem_access_coh_sub with (phi1:=jall).
          assumption.
          eapply JMS.compatible_threadRes_sub; eauto.
        - do 2 (rewrite setPermBlock_other_2; auto).
          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt; inversion all_cohere.
          rewrite -JSEM.juic2Perm_locks_correct.
          rewrite -(MTCH_perm2 _ MATCH); auto.
          apply JMS.mem_access_coh_sub with (phi1:=jall).
          assumption.
          eapply JMS.compatible_threadRes_sub; eauto.
      }


      econstructor 1.

      14: reflexivity.
      14: now unfold ds'', ds'; repeat f_equal; apply proof_irr.
      7: eassumption.
      9: eassumption.
      + (*boundedness*)
        split.
        *
          Lemma same_shape_map:
            forall {A B} m f,
              @bounded_maps.same_shape A B
                                       (PTree.map f m) m.
          Proof.
            intros until m.
            unfold PTree.map.
            pose (i:=1%positive); fold i.
            generalize i; clear i.
            induction m.
            - intros;
              unfold bounded_maps.same_shape;
              simpl; auto.
            - intros;
              unfold bounded_maps.same_shape;
              split; [| split].
              + destruct o; simpl; auto.
              + eapply IHm1.
              + eapply IHm2.
          Qed.
          eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].

          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta1 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh0 Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption.
          }
          { move: (JMS.JuicyMachineLemmas.compat_lockLT
                        Hcmpt _ His_unlocked p b0).
            Lemma po_None1: forall p, Mem.perm_order'' None p -> p = None.
            Proof. intros. simpl in H. destruct p; inversion H; reflexivity. Qed.

            rewrite /PMap.get HH' is_none => /po_None1 //.
            }
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta2 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh0 Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          { move: (JMS.JuicyMachineLemmas.compat_lockLT
                        Hcmpt _ His_unlocked p b0).
            rewrite /PMap.get HH' is_none => /po_None1 //.
            }

          (*eapply bounded_maps.treemap_sub_map.*)
      + assumption.
      + eapply MTCH_getThreadC; eassumption.
      + eassumption.
      (*   + move Hload at bottom.
             rewrite -Hload; f_equal.
             eapply restrPermMap_ext.*)

      (*   + eapply MTCH_compat; eassumption.*)
      + unfold JSEM.juicyRestrict_locks.
        apply restrPermMap_ext;
          intros b0.
        inversion MATCH; subst.
        extensionality ofs0.
        rewrite <- JSEM.juic2Perm_locks_correct.
        symmetry. apply mtch_perm2.
        apply THE_JUICY_MACHINE.JSEM.mem_compat_thread_max_cohere.
        assumption.
      + admit.
      (* Range of lock permisison, now it spans multiple locations given my LKSIZE *)
      + reflexivity.
      + instantiate (1:= Hlt'').
        apply restrPermMap_ext.
        intros b0.
        extensionality ofs0.
        destruct (ident_eq b b0); [
            destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z) |].
        * unfold Intv.In in i0.
          subst. repeat (rewrite setPermBlock_same; auto).
        * subst. apply Intv.range_notin in n; auto.
          repeat (rewrite setPermBlock_other_1; auto).
          rewrite -JSEM.juic2Perm_locks_correct.
          inversion MATCH. symmetry. eapply mtch_perm2.
          eapply JSEM.mem_compat_thread_max_cohere; auto.
          simpl; pose proof LKSIZE_pos; xomega.
        * repeat (rewrite setPermBlock_other_2; auto).
          rewrite -JSEM.juic2Perm_locks_correct.
          inversion MATCH. symmetry. eapply mtch_perm2.
          eapply JSEM.mem_compat_thread_max_cohere; auto.
      + exact dlockRes.
      + simpl; intros b0 ofs0. inversion MATCH; subst.
        specialize (mtch_locksRes _ _ _ His_unlocked dlockRes).
        rewrite <- mtch_locksRes.
        rewrite <- mtch_perm1 with (Htid:=Hi).
        replace (MTCH_cnt MATCH Hi) with Htid' by eapply proof_irr.
        rewrite virtue_correct1.
        eapply permjoin.join_permjoin.
        eapply resource_at_join.
        apply join_comm.
        assumption.
      + simpl; intros b0 ofs0. inversion MATCH; subst.
        specialize (mtch_locksRes0 _ _ _ His_unlocked dlockRes).
        rewrite <- mtch_locksRes0.
        rewrite <- mtch_perm2 with (Htid:=Hi).
        replace (MTCH_cnt MATCH Hi) with Htid' by eapply proof_irr.
        rewrite virtue_correct2.

             apply permjoin.join_permjoin_lock.
             eapply resource_at_join.
             apply join_comm.
             assumption.
    }

    (* step_release *)
    {

    assert (Htid':= MTCH_cnt MATCH Hi).
    pose (inflated_delta1:=
            fun loc => match (d_phi @ loc ) with
                      NO s _ => if Share.EqDec_share s Share.bot then None else Some ( perm_of_res (phi' @ loc))
                    | _ => Some (perm_of_res (phi' @ loc))
                    end).
    pose (inflated_delta2:=
            fun loc => match (d_phi @ loc ) with
                      NO s _ => if Share.EqDec_share s Share.bot then None
                             else Some ( perm_of_res_lock (phi' @ loc))
                    | _ => Some (perm_of_res_lock (phi' @ loc))
                    end).
    pose (virtue1:= PTree.map
                     (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                        (inflated_delta1 (block, ofs))) (snd (getMaxPerm m)) ).
    pose (virtue2:= PTree.map
                      (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                         (inflated_delta2 (block, ofs))) (snd (getMaxPerm m)) ).
    pose (ds':= DTP.updThread Htid' (Kresume c Vundef)
                                          (computeMap
                                             (DTP.getThreadR Htid').1 virtue1,
                                           computeMap
                                             (DTP.getThreadR Htid').2 virtue2)).
    pose (ds'':= DTP.updLockSet ds' (b, Ptrofs.intval ofs)
                                            (JSEM.juice2Perm d_phi m, JSEM.juice2Perm_locks d_phi m )).

    assert (virtue_spec1: forall b0 ofs0, perm_of_res (phi' @ (b0, ofs0)) =
                                    (computeMap (DTP.getThreadR Htid').1 virtue1) !! b0 ofs0).
    {
      intros b0 ofs0. simpl.
      destruct (virtue1 ! b0) eqn:VIRT.
      destruct (o ofs0) eqn:O.
      - erewrite computeMap_1; try eassumption.
        unfold virtue1 in VIRT. rewrite PTree.gmap in VIRT.
        destruct ((snd (getMaxPerm m)) ! b0); inversion VIRT.
        unfold inflated_delta1 in H0. rewrite <- H0 in O.
        clear VIRT H0.
        replace o0 with (perm_of_res (phi' @ (b0, ofs0))).
        + reflexivity.
        + destruct (d_phi @ (b0, ofs0)) eqn:AA;
            rewrite AA in O;
            try destruct (Share.EqDec_share sh0 Share.bot);
          inversion O; reflexivity.
           - erewrite computeMap_2; try eassumption.
             unfold virtue1 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0); inversion VIRT.
             unfold inflated_delta1 in H0. rewrite <- H0 in O.
             apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_lock_res.
             move Hrem_lock_res at bottom.
             replace (d_phi @ (b0, ofs0)) with (NO Share.bot shares.bot_unreadable)
               in Hrem_lock_res.
             + inversion MATCH; rewrite <- mtch_perm1 with (Htid:= Hi).
               f_equal.
               eapply join_unit1_e; eauto.
               eapply NO_identity.
             + destruct (d_phi @ (b0, ofs0)) eqn:HH; rewrite HH in O; try solve[inversion O].
               destruct ((Share.EqDec_share sh0 Share.bot)); try solve[ inversion O].
               subst; f_equal; apply proof_irr.
           - erewrite computeMap_3; try eassumption.
             unfold virtue1 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m) !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DTP.getThreadR Htid').1 !! b0 ofs0) with
             (perm_of_res ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply JSEM.JuicyMachineLemmas.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply THE_JUICY_MACHINE.JSEM.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold JSEM.access_cohere' in acc_coh.
               specialize (acc_coh (b0,ofs0)).
               unfold max_access_at, access_at in acc_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in acc_coh.

               apply po_None1 in acc_coh.
               move Hrem_lock_res at bottom.
               apply join_comm in Hrem_lock_res.
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_lock_res.
               apply join_join_sub in Hrem_lock_res.
               assert (HH:= juicy_mem_lemmas.po_join_sub _ _ Hrem_lock_res).
               rewrite acc_coh in HH. rewrite acc_coh.
               apply po_None1 in HH. assumption.
             + inversion MATCH; rewrite mtch_perm1; reflexivity.
    }

    assert (virtue_spec2: forall b0 ofs0, perm_of_res_lock (phi' @ (b0, ofs0)) =
                                    (computeMap (DTP.getThreadR Htid').2 virtue2) !! b0 ofs0).
    {
      intros b0 ofs0. simpl.
      destruct (virtue2 ! b0) eqn:VIRT.
      destruct (o ofs0) eqn:O.
      - erewrite computeMap_1; try eassumption.
        unfold virtue2 in VIRT. rewrite PTree.gmap in VIRT.
        destruct ((snd (getMaxPerm m)) ! b0); inversion VIRT.
        unfold inflated_delta2 in H0. rewrite <- H0 in O.
        clear VIRT H0.
        replace o0 with (perm_of_res_lock (phi' @ (b0, ofs0))).
        + reflexivity.
        + destruct (d_phi @ (b0, ofs0)) eqn:AA; rewrite AA in O;
            try destruct (Share.EqDec_share sh0 Share.bot);
          inversion O; reflexivity.
           - erewrite computeMap_2; try eassumption.
             unfold virtue2 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0); inversion VIRT.
             unfold inflated_delta2 in H0. rewrite <- H0 in O.
             apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_lock_res.
             move Hrem_lock_res at bottom.
             replace (d_phi @ (b0, ofs0)) with (NO Share.bot shares.bot_unreadable) in Hrem_lock_res.
             + inversion MATCH; rewrite <- mtch_perm2 with (Htid:= Hi).
               f_equal.
               eapply join_unit1_e; eauto.
               eapply NO_identity.
             + destruct (d_phi @ (b0, ofs0)) eqn:HH; rewrite HH in O; try solve[inversion O].
               destruct ((Share.EqDec_share sh0 Share.bot)); try solve[ inversion O].
               subst; f_equal; apply proof_irr. 
           - erewrite computeMap_3; try eassumption.
             unfold virtue2 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m)) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m) !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DTP.getThreadR Htid').2 !! b0 ofs0) with
             (perm_of_res_lock ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply JSEM.JuicyMachineLemmas.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply THE_JUICY_MACHINE.JSEM.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold max_access_cohere in max_coh.
               specialize (max_coh (b0,ofs0)).
               unfold max_access_at, access_at in max_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in max_coh.

               pose (HERE:= perm_of_res_op2 (JSEM.ThreadPool.getThreadR Hi @ (b0, ofs0))).
               eapply juicy_mem_lemmas.perm_order''_trans in HERE; eauto.
               apply po_None1 in HERE.
               move Hrem_lock_res at bottom.
               apply join_comm in Hrem_lock_res.
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_lock_res.
               apply join_join_sub in Hrem_lock_res.
               assert (HH:= po_join_sub_lock Hrem_lock_res).
               rewrite HERE in HH. rewrite HERE.
               apply po_None1 in HH. assumption.
             + inversion MATCH; rewrite mtch_perm2; reflexivity.
}
    (*TODO Fix the even trace*)
    exists ds'',  (JSEM.Events.release (b, Ptrofs.intval ofs)
                                  (Some (JSEM.juice2Perm d_phi m, JSEM.juice2Perm_locks d_phi m)) ).
    split; [|split].
    - unfold ds''.
      cut (DryMachine.invariant ds').
      { intros dinv'.
        apply updLock_inv.
        - assumption.
        - move=> laddr ramp0 laddr_neq .
          unfold ds'; rewrite DMS.DTP.gsoThreadLPool => get_lres.
          (*move this*)
          move: (get_lres) => /(MTCH_locks) /= /(_ _ MATCH) [] l.
          destruct l.
          + (*Some case: lock is not acquyired*)
            inversion MATCH => jget_lres.
            split.
            * apply permDisjoint_permMapsDisjoint;
              intros b0 ofs0.
              move : (mtch_locksRes _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite -JSEM.juic2Perm_correct.
              apply joins_permDisjoint.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              -- exists phi'; eassumption.
              -- eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join; eauto.
              -- apply JMS.max_acc_coh_acc_coh.
                 destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
            * apply permDisjoint_permMapsDisjoint;
              intros b0 ofs0.
              move : (mtch_locksRes0 _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite -JSEM.juic2Perm_locks_correct.
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              -- exists phi'; eassumption.
              -- eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join; eauto.
              -- destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
          + (*None case: lock was acquired before*)
            inversion MATCH.
            move => /(mtch_locksEmpty) // /(_ _ get_lres) ->.
            apply permMapsDisjoint2_comm;
            apply permMapsDisjoint2_empty.

        (*empty map disjoit!*)
        - rewrite /ds'=> i0.
          destruct (NatTID.eq_tid_dec i i0).
          + subst=> cnti.
            rewrite DMS.DTP.gssThreadRes; split=> /=;
              apply permDisjoint_permMapsDisjoint => b0 ofs0.
            * rewrite - virtue_spec1.
              rewrite - JSEM.juic2Perm_correct.
              apply joins_permDisjoint.
              apply resource_at_joins.
              apply joins_comm.
              eexists; eassumption.

              apply JSEM.max_acc_coh_acc_coh.
              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
            * rewrite - virtue_spec2.
              rewrite - JSEM.juic2Perm_locks_correct.
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              apply joins_comm.
              eexists; eassumption.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
          + move => cnti. rewrite DMS.DTP.gsoThreadRes => //.
            split=> /=;
              apply permDisjoint_permMapsDisjoint => b0 ofs0.
            * rewrite (MTCH_perm' _ MATCH).
              rewrite - JSEM.juic2Perm_correct.
              apply joins_permDisjoint.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join;
                eassumption.

              apply JSEM.max_acc_coh_acc_coh.
              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
            * rewrite (MTCH_perm2' _ MATCH).
              rewrite - JSEM.juic2Perm_locks_correct.
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join;
                eassumption.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
        - move=> laddr ramp0 laddr_neq .
          unfold ds'; rewrite DMS.DTP.gsoThreadLPool => get_lres.
          (*move this*)
          move: (get_lres) => /(MTCH_locks) /= /(_ _ MATCH) [] l.
          destruct l.
          + (*Some case: lock is not acquyired*)
            inversion MATCH => jget_lres.
            split.
            * intros b0 ofs0.
              move : (mtch_locksRes0 _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite - JSEM.juic2Perm_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join ; eassumption.

              apply JSEM.max_acc_coh_acc_coh.
              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
            * intros b0 ofs0.
              move : (mtch_locksRes _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite - JSEM.juic2Perm_locks_correct.
               apply perm_coh_joins.
               apply resource_at_joins.
               apply joins_comm.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join ; eassumption.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.


          + (*None case: lock was acquired before*)
            inversion MATCH.
            move => /(mtch_locksEmpty) // /(_ _ get_lres) -> /=.
            split; first [apply permCoh_empty'| apply permCoh_empty].
            { move => b0 ofs0.
              rewrite -JMS.juic2Perm_locks_correct.
              apply perm_of_res_lock_not_Freeable.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.

            }

        - move=> b0 ofs0 /=.
          assert ( max_access_cohere m d_phi).
          {
             destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption. }

          rewrite - JSEM.juic2Perm_locks_correct.
          rewrite - JSEM.juic2Perm_correct.
          apply perm_coh_self.

          + apply JSEM.max_acc_coh_acc_coh; assumption.
          + assumption.
        - rewrite /ds'=> i0.
          destruct (NatTID.eq_tid_dec i i0).
          + subst=> cnti. rewrite DMS.DTP.gssThreadRes; split=> /= b0 ofs0.
            * rewrite - virtue_spec2.
              rewrite - JSEM.juic2Perm_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              eexists; eassumption.

              apply JSEM.max_acc_coh_acc_coh.
               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.

            * rewrite - virtue_spec1.
              rewrite - JSEM.juic2Perm_locks_correct.
              apply perm_coh_joins.
              apply joins_comm.
              apply resource_at_joins.
              eexists; eassumption.

               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
          + move => cnti. rewrite DMS.DTP.gsoThreadRes => //.
            split=> /= b0 ofs0.
            * rewrite (MTCH_perm2' _ MATCH).
              rewrite - JSEM.juic2Perm_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              eexists phi'; eassumption.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eassumption.

               apply JSEM.max_acc_coh_acc_coh.
               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.
            * rewrite (MTCH_perm' _ MATCH).
              rewrite - JSEM.juic2Perm_locks_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              eexists phi'; eassumption.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eassumption.

               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply JMS.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(JSEM.ThreadPool.getThreadR Hi)).
                 exists phi'; assumption.
                 apply JMS.compatible_threadRes_sub; assumption.

        - simpl; intros ofs0 ineq.
          rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          cut (JuicyMachine.SIG.ThreadPool.lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH. specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            destruct (DTP.lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks.
            reflexivity.
          }
          { destruct Hcompatible as [allj Hcompatible].
            inversion Hcompatible.
            assert (VALID:= JSEM.compat_lr_valid Hcmpt).
            specialize (VALID b (Ptrofs.intval ofs)).
            eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            eapply resource_at_join_sub with (l:=(b,Ptrofs.intval ofs)) in juice_join.
            rewrite HJcanwrite in juice_join.
            destruct juice_join as [x HH].
            inversion HH.

            - symmetry in H.
            apply jloc_in_set in H.
            destruct (JSEM.ThreadPool.lockRes js (b, Ptrofs.intval ofs)) eqn:AA;
              try solve [unfold JSEM.ThreadPool.lockRes in AA; rewrite AA in H; inversion H].
            inversion ineq.
            apply VALID; auto.
          - unfold JSEM.ThreadPool.lockRes in VALID. move VALID at bottom.

             symmetry in H.
              apply jloc_in_set in H.
              destruct (JSEM.ThreadPool.lockRes js (b, Ptrofs.intval ofs)) eqn:BB;
                try solve [unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in H; inversion H].
              unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in VALID.
              subst; apply VALID; auto.
          }
        - simpl; intros ofs0 ineq.
          rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          cut (JuicyMachine.SIG.ThreadPool.lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH. specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            destruct (DTP.lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks.
            reflexivity.
          }
          { destruct (JuicyMachine.SIG.ThreadPool.lockRes js (b, ofs0)) eqn:AA; try reflexivity. exfalso.
             destruct Hcompatible as [allj Hcompatible].
            inversion Hcompatible.
            assert (VALID:= JSEM.compat_lr_valid Hcmpt).
            specialize (VALID b ofs0).
            rewrite AA in VALID.
            apply VALID in ineq.
            eapply JSEM.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            eapply resource_at_join_sub with (l:=(b,Ptrofs.intval ofs)) in juice_join.
            rewrite HJcanwrite in juice_join.
            destruct juice_join as [x HH].
            inversion HH.

            - symmetry in H.

             apply jloc_in_set in H.
            destruct (JSEM.ThreadPool.lockRes js (b, Ptrofs.intval ofs)) eqn:BB.
              + inversion ineq.
              + unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in H; inversion H.
            - symmetry in H.
              apply jloc_in_set in H.
              destruct (JSEM.ThreadPool.lockRes js (b, Ptrofs.intval ofs)) eqn:BB;
                try solve [unfold JSEM.ThreadPool.lockRes in BB; rewrite BB in H; inversion H].
              inversion ineq.
          }

      }


      { (*Proof DryMachine.invariant ds'*) (*repeat lemma*)
        (*apply updThread_decr.*)
        apply invariant_decr.
        - assumption.
        - move=> /= b0 ofs0.
          rewrite -virtue_spec1 (MTCH_perm' _ MATCH).
          apply juicy_mem_lemmas.po_join_sub;
            apply resource_at_join_sub.
          exists (d_phi); apply join_comm.
          replace (MTCH_cnt' MATCH Htid') with Hi by (apply proof_irrelevance); assumption.
        - move=> /= b0 ofs0.
          rewrite -virtue_spec2 (MTCH_perm2' _ MATCH).

          apply po_join_sub_lock.
           apply resource_at_join_sub.
          exists (d_phi); apply join_comm.
          replace (MTCH_cnt' MATCH Htid') with Hi by (apply proof_irrelevance); assumption.
      }



    - (*match_st _ _*)
      unfold ds''.
      apply match_st_age_tp_to.
      cut (max_access_cohere m d_phi).
      intros maxcoh.
      apply MTCH_updLockS.

      Focus 2.
      {
      inversion MATCH; subst.
      intros; apply JSEM.juic2Perm_correct.
      inversion Hcompatible; inversion H; inversion all_cohere.
      apply JSEM.max_acc_coh_acc_coh.
      assumption.
      (*
      eapply JSEM.mem_access_coh_sub.
      - eassumption.
      - eapply join_sub_trans.
        + unfold join_sub. exists phi'. eassumption.
        + eapply JSEM.compatible_threadRes_sub.
      assumption. *) }

      Unfocus.
      unfold ds'.
      apply MTCH_update; eauto.
      move=> b0 ofs0.
      apply JSEM.juic2Perm_locks_correct.
      assumption.

      (*the cut*)
      { inversion Hcompatible; inversion H; inversion all_cohere.
        eapply JSEM.mem_access_coh_sub.
         - eassumption.
         - eapply join_sub_trans.
           + unfold join_sub. exists phi'. eassumption.
           + eapply JSEM.compatible_threadRes_sub.
             assumption.
      }


    - assert (H: exists l, DTP.lockRes ds (b, Ptrofs.intval ofs) = Some l).
      { inversion MATCH; subst.
        specialize (mtch_locks (b, (Ptrofs.intval ofs) )).
        rewrite His_locked in mtch_locks.
        destruct (DTP.lockRes ds (b, Ptrofs.intval ofs)); try solve[inversion mtch_locks]. exists l; reflexivity. }
           destruct H as [l dlockRes].
      econstructor 2.
      17: reflexivity.
      16: instantiate (2:= (virtue1, virtue2));
        unfold ds'; repeat f_equal; try reflexivity; try apply proof_irrelevance.
      8: eassumption.
      10: eassumption.
      8: reflexivity.
      + (*boundedness 1*)
        split.
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta1 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh0 Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          {
            apply join_join_sub in Hrem_lock_res.
            apply resource_at_join_sub with (l:=(p,b0)) in Hrem_lock_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_lock_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_lock_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p, b0)).
            destruct m; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }
          (* eapply bounded_maps.treemap_sub_map. *)
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta2 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh0 Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          {
            apply join_join_sub in Hrem_lock_res.
            apply resource_at_join_sub with (l:=(p,b0)) in Hrem_lock_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_lock_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_lock_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p, b0)).
            destruct m; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }


          (* eapply bounded_maps.treemap_sub_map. *)
      + (*boundedness 2*)
        repeat split.
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { intros HHH; rewrite HHH in f1b0.
            inversion f1b0.  }
          {
            apply join_join_sub in Hrem_lock_res.
            apply resource_at_join_sub with (l:=(p,b0)) in Hrem_lock_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_lock_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_lock_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p, b0)).
            destruct m; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }
          (* eapply bounded_maps.treemap_sub_map. *)
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res_lock (d_phi @ (p, b0)) = None).
          { intros HHH; rewrite HHH in f1b0.
            inversion f1b0.  }
          {
            apply join_join_sub in Hrem_lock_res.
            apply resource_at_join_sub with (l:=(p,b0)) in Hrem_lock_res.
            apply po_join_sub_lock in Hrem_lock_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_lock_res;
              [|eapply perm_of_res_op2].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p, b0)).
            destruct m; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }
      + assumption.
      + eapply MTCH_getThreadC; eassumption.
      + eassumption.
(*REmove      + eapply MTCH_compat; eassumption. *)
      + apply restrPermMap_ext.
        intros b0.
        inversion MATCH; subst.
        extensionality ofs0.
        rewrite -JSEM.juic2Perm_locks_correct.
        symmetry; apply mtch_perm2.
        inversion Hcompatible; inversion H; inversion all_cohere.
        eapply JSEM.mem_access_coh_sub.
        * eassumption.
        *  eapply JSEM.compatible_threadRes_sub.
           assumption.
      + admit.
      (* Range of lock permisison, now it spans multiple locations given my LKSIZE *)
      + apply restrPermMap_ext.
        intros b0.
        extensionality ofs0.
        destruct (peq b b0); [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
        * unfold Intv.In in i0; simpl in i0.
          repeat rewrite setPermBlock_same; auto.
        * apply Intv.range_notin in n; auto.
          repeat rewrite setPermBlock_other_1; auto.
          rewrite -JSEM.juic2Perm_locks_correct.
          symmetry; eapply MTCH_perm2.
          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt. inversion all_cohere.
          eapply JMS.mem_access_coh_sub; eauto.
          apply JMS.compatible_threadRes_sub; assumption.
          pose proof LKSIZE_pos; simpl; xomega.
        * repeat rewrite setPermBlock_other_2; auto.
          rewrite -JSEM.juic2Perm_locks_correct.
          symmetry; eapply MTCH_perm2.
          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt. inversion all_cohere.
          eapply JMS.mem_access_coh_sub; eauto.
          apply JMS.compatible_threadRes_sub; assumption.

      + exact dlockRes.
      + inversion MATCH.
        specialize (mtch_locksEmpty _ _ His_locked dlockRes).
        inversion mtch_locksEmpty; simpl.
        move=> b0 ofs0.
        rewrite empty_map_spec; tauto.
      + simpl; intros b0 ofs0.
        replace (MTCH_cnt MATCH Hi) with Htid'.
        rewrite -virtue_spec1.
        rewrite -JSEM.juic2Perm_correct.
        rewrite (MTCH_perm' _ MATCH b0 ofs0).
        apply permjoin.join_permjoin.
        move Hrem_lock_res at bottom.
        eapply resource_at_join; apply join_comm.
        replace (MTCH_cnt' MATCH Htid') with Hi.
        assumption.
        apply proof_irrelevance.
        2:
        apply proof_irrelevance.
        apply JSEM.max_acc_coh_acc_coh.
        inversion Hcompatible; inversion H; inversion all_cohere.
        eapply JSEM.mem_access_coh_sub.
        * eassumption.
        *  eapply join_sub_trans.
           -- unfold join_sub. exists phi'. eassumption.
           -- eapply JSEM.compatible_threadRes_sub.
              assumption.
      + simpl; intros b0 ofs0.
        replace (MTCH_cnt MATCH Hi) with Htid'.
        rewrite -virtue_spec2.
        rewrite -JSEM.juic2Perm_locks_correct.
        rewrite (MTCH_perm2' _ MATCH b0 ofs0).
        apply permjoin.join_permjoin_lock.
        apply resource_at_join.
        apply join_comm.
        replace (MTCH_cnt' MATCH Htid') with Hi by apply proof_irrelevance.
        assumption.
        2:
        apply proof_irrelevance.
        inversion Hcompatible; inversion H; inversion all_cohere.
        eapply JSEM.mem_access_coh_sub.
        * eassumption.
        *  eapply join_sub_trans.
           -- unfold join_sub. exists phi'. eassumption.
           -- eapply JSEM.compatible_threadRes_sub.
              assumption.
  
    }




    (*step_create*)
    {


      (*First two deltas correspoind to the two access maps removed from the thread:
       *
       *
       *
       *)
      pose (inflated_delta11:=
              fun loc => match (d_phi @ loc ) with
                        NO s _ => if Share.EqDec_share s Share.bot then None else  Some ( perm_of_res (phi' @ loc))
                      | _ => Some ( perm_of_res (phi' @ loc))
                      end).
      pose (virtue11:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta11 (block, ofs))) (snd (getMaxPerm m')) ).
      assert (virtue_spec11: forall b0 ofs0,
                 (computeMap (DTP.getThreadR (MTCH_cnt MATCH Hi)).1 virtue11) !! b0 ofs0 =
                 perm_of_res (phi' @ (b0, ofs0))).
      { intros b0 ofs0.
        destruct (virtue11 ! b0) eqn:VIRT.
        destruct (o ofs0) eqn:O.
        - erewrite computeMap_1; try eassumption.
          unfold virtue11 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta11 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          reflexivity.
        - erewrite computeMap_2; try eassumption.
          unfold virtue11 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta11 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          subst.
          apply resource_at_join with (loc:= (b0,ofs0)) in Hrem_fun_res.
          rewrite AA in Hrem_fun_res.
          eapply (join_unit1_e) in Hrem_fun_res.
          rewrite Hrem_fun_res.
          inversion MATCH.
          symmetry.
          apply mtch_perm1.
          apply NO_identity.
        - erewrite computeMap_3; try eassumption.
             unfold virtue11 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m')) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m') !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DTP.getThreadR (MTCH_cnt MATCH Hi)).1 !! b0 ofs0) with
             (perm_of_res ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply JSEM.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold JSEM.access_cohere' in acc_coh.
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
             + inversion MATCH.  apply mtch_perm1.
      }

      pose (inflated_delta12:=
              fun loc => match (d_phi @ loc ) with
                        NO s _ => if Share.EqDec_share s Share.bot then None
                               else  Some ( perm_of_res_lock (phi' @ loc))
                      | _ => Some ( perm_of_res_lock (phi' @ loc))
                      end).
      pose (virtue12:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta12 (block, ofs))) (snd (getMaxPerm m')) ).
      assert (virtue_spec12: forall b0 ofs0,
                 (computeMap (DTP.getThreadR (MTCH_cnt MATCH Hi)).2 virtue12) !! b0 ofs0 =
                 perm_of_res_lock (phi' @ (b0, ofs0))).
      { intros b0 ofs0.
        destruct (virtue12 ! b0) eqn:VIRT.
        destruct (o ofs0) eqn:O.
        - erewrite computeMap_1; try eassumption.
          unfold virtue12 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta12 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          reflexivity.
        - erewrite computeMap_2; try eassumption.
          unfold virtue12 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta12 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          subst.
          apply resource_at_join with (loc:= (b0,ofs0)) in Hrem_fun_res.
          rewrite AA in Hrem_fun_res.
          apply join_unit1_e in Hrem_fun_res; try apply NO_identity; rewrite Hrem_fun_res.
          inversion MATCH.
          symmetry.
          apply mtch_perm2.
        - erewrite computeMap_3; try eassumption.
             unfold virtue12 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m')) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m') !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DTP.getThreadR (MTCH_cnt MATCH Hi)).2 !! b0 ofs0) with
             (perm_of_res_lock ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               (*apply JSEM.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold JSEM.access_cohere' in acc_coh.*)
               specialize (max_coh (b0,ofs0)).
               unfold max_access_at, access_at in max_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in max_coh.
               apply po_None1 in max_coh.
               move Hrem_fun_res at bottom.
               apply join_comm in Hrem_fun_res.
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_fun_res.
               apply join_join_sub in Hrem_fun_res.
               assert (HH:= po_join_sub_lock Hrem_fun_res).

               move:
                 (perm_of_res_op2 (JSEM.ThreadPool.getThreadR Hi @ (b0, ofs0))).

               rewrite max_coh => /po_None1 is_none.
               rewrite is_none in HH; rewrite is_none.
               apply po_None1 in HH. symmetry; assumption.
             + inversion MATCH.  apply mtch_perm2.
      }


     (*Second two deltas correspoind to the two access maps for the new thread:
       *
       *
       *
       *)
      pose (inflated_delta21:=
              fun loc => match (d_phi @ loc ) with
                        NO s _ => if Share.EqDec_share s Share.bot then None
                               else  Some ( perm_of_res (d_phi @ loc))
                      | _ => Some ( perm_of_res (d_phi @ loc))
                      end).
      pose (virtue21:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta21 (block, ofs))) (snd (getMaxPerm m')) ).
      assert (virtue_spec21: forall b0 ofs0,
                 (computeMap empty_map virtue21) !! b0 ofs0 = (perm_of_res (d_phi @(b0, ofs0)))).
      { intros b0 ofs0.
        destruct (virtue21 ! b0) eqn:VIRT.
        destruct (o ofs0) eqn:O.
        - erewrite computeMap_1; try eassumption.
          unfold virtue21 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta21 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          reflexivity.
        - erewrite computeMap_2; try eassumption.
          unfold virtue21 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta21 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          subst; simpl.
          destruct (eq_dec Share.bot Share.bot).
          + rewrite empty_map_spec; auto.
          + exfalso; apply n; auto. contradiction.
        - erewrite computeMap_3; try eassumption.
             unfold virtue21 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m')) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m') !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DTP.getThreadR (MTCH_cnt MATCH Hi)).1 !! b0 ofs0) with
             (perm_of_res ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply JSEM.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold JSEM.access_cohere' in acc_coh.
               specialize (acc_coh (b0,ofs0)).
               unfold max_access_at, access_at in acc_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in acc_coh.
               apply po_None1 in acc_coh.
               move Hrem_fun_res at bottom.
               (*apply join_comm in Hrem_fun_res.*)
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_fun_res.
               apply join_join_sub in Hrem_fun_res.
               assert (HH:= juicy_mem_lemmas.po_join_sub _ _ Hrem_fun_res).
               rewrite acc_coh in HH.
               apply po_None1 in HH.
               rewrite empty_map_spec.
               symmetry; assumption.
             + inversion MATCH.  apply mtch_perm1.
      }



      pose (inflated_delta22:=

              fun loc => match (d_phi @ loc ) with
                        NO s _ => if Share.EqDec_share s Share.bot then None
                               else  Some ( perm_of_res_lock (d_phi @ loc))
                      | _ => Some (perm_of_res_lock (d_phi @ loc))
                      end).

      pose (virtue22:= PTree.map
                       (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                          (inflated_delta22 (block, ofs))) (snd (getMaxPerm m')) ).
      assert (virtue_spec22: forall b0 ofs0,
                 (computeMap empty_map virtue22) !! b0 ofs0 =
                 (perm_of_res_lock (d_phi @(b0, ofs0)))).
      {intros b0 ofs0.
        destruct (virtue22 ! b0) eqn:VIRT.
        destruct (o ofs0) eqn:O.
        - erewrite computeMap_1; try eassumption.
          unfold virtue22 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta22 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          reflexivity.
        - erewrite computeMap_2; try eassumption.
          unfold virtue22 in VIRT. rewrite PTree.gmap in VIRT.
          destruct ((snd (getMaxPerm m')) ! b0); inversion VIRT.
          rewrite <- H0 in O.
          unfold inflated_delta22 in O.
          destruct (d_phi @ (b0, ofs0)) eqn:AA;
          try (inversion O; reflexivity).
          destruct (Share.EqDec_share sh Share.bot); inversion O.
          subst. simpl;
            rewrite empty_map_spec; auto.
        - erewrite computeMap_3; try eassumption.
             unfold virtue22 in VIRT. rewrite PTree.gmap in VIRT.
             destruct ((snd (getMaxPerm m')) ! b0) eqn:notInMem; inversion VIRT.
             clear VIRT.
             assert (THE_CURE: (getMaxPerm m') !! b0 = fun _ => None).
             { unfold PMap.get. rewrite notInMem.
               apply Max_isCanonical.
             }
             assert (the_cure:= equal_f THE_CURE ofs0).
             rewrite getMaxPerm_correct in the_cure.
             replace ((DTP.getThreadR (MTCH_cnt MATCH Hi)).2 !! b0 ofs0) with
             (perm_of_res_lock ((JSEM.ThreadPool.getThreadR Hi)@ (b0, ofs0))).
          + assert (Hcohere':= Hcompatible).
               apply compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               (*apply JSEM.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold JSEM.access_cohere' in acc_coh.*)
               specialize (max_coh (b0,ofs0)).
                unfold max_access_at, access_at in max_coh.
               unfold permission_at in the_cure.

               rewrite the_cure in max_coh.
               apply po_None1 in max_coh.
               move Hrem_fun_res at bottom.
               (*apply join_comm in Hrem_fun_res.*)
               apply resource_at_join with (loc:=(b0,ofs0)) in Hrem_fun_res.
               apply join_join_sub in Hrem_fun_res.
               assert (HH:= po_join_sub_lock Hrem_fun_res).

               move:
                 (perm_of_res_op2 (JSEM.ThreadPool.getThreadR Hi @ (b0, ofs0))).

               rewrite max_coh => /po_None1 is_none.
               rewrite empty_map_spec.
               rewrite is_none in HH.
               apply po_None1 in HH. symmetry; assumption.
             + inversion MATCH.  apply mtch_perm2.

      }







      (*Having computed and specified the virtues, we can prove the create step.*)



      pose (ds_upd:= DTP.updThread
                       (MTCH_cnt MATCH Hi)
                       (Kresume c Vundef)
                       (computeMap (DTP.getThreadR (MTCH_cnt MATCH Hi)).1 virtue11,
                        computeMap (DTP.getThreadR (MTCH_cnt MATCH Hi)).2 virtue12)).

      pose (ds':= DTP.addThread
                    ds_upd
                    (Vptr b ofs)
                    arg
                    (computeMap empty_map virtue21,
                     computeMap empty_map virtue22)).
      exists ds'.
      exists (JSEM.Events.spawn
           (b, Ptrofs.intval ofs)
           (Some ((DTP.getThreadR (MTCH_cnt MATCH Hi)) , (virtue11, virtue12)))
      (Some (virtue21, virtue22))) .
      split ;[|split].
      { (* invariant *)
        cut (DryMachine.invariant ds_upd).
        {
          Lemma addThrd_inv: forall ds vf arg new_perm,
            DryMachine.invariant ds  ->
            (forall i cnti,
                permMapsDisjoint2 new_perm (@DTP.getThreadR i ds cnti)) ->
            (forall l rm,  DTP.lockRes ds l = Some rm ->
                      permMapsDisjoint2 new_perm rm) ->
            permMapCoherence new_perm.1 new_perm.2 ->
            (forall i cnti,
                permMapCoherence new_perm.1 (@DTP.getThreadR i ds cnti).2) ->
            (forall i cnti,
                permMapCoherence (@DTP.getThreadR i ds cnti).1 new_perm.2) ->
            (forall l rm,  DTP.lockRes ds l = Some rm ->
                       permMapCoherence new_perm.1 rm.2) ->
            (forall l rm,  DTP.lockRes ds l = Some rm ->
                       permMapCoherence rm.1 new_perm.2) ->
            DryMachine.invariant (DTP.addThread ds vf arg new_perm).
          Proof.
            move => ds vf arg new_perm dinv
                      DISJ_RES DISJ_LOCK COH_SELF COH_RES1
                      COH_RES2 COH_LOCK1 COH_LOCK2.
            constructor.
            - move => i j cnti cntj neq.
              assert (cntj':=cntj).
              assert (cnti':=cnti).
              apply DMS.DTP.cntAdd' in cnti'.
              apply DMS.DTP.cntAdd' in cntj'.
              destruct cntj' as [[H1 H2] | H1];
                destruct cnti' as [[H3 H4] | H3]; subst;
              try solve[exfalso; apply neq; reflexivity].
              + rewrite (DTP.gsoAddRes H1) .
                rewrite (DTP.gsoAddRes H3).
                inversion dinv; eauto.
              + rewrite (DTP.gsoAddRes H1).
                erewrite DTP.gssAddRes; auto.
              + rewrite (DTP.gsoAddRes H3).
                apply permMapsDisjoint2_comm.
                erewrite DTP.gssAddRes; auto.
            - move => l1 l2 mr1 mr2.
              rewrite DTP.gsoAddLPool.
              rewrite DTP.gsoAddLPool.
              inversion dinv; eauto.
            - move => i l cnti rm.
              rewrite DTP.gsoAddLPool.
              assert (cnti':=cnti).
              apply DMS.DTP.cntAdd' in cnti'.
              destruct cnti' as [[H1 H2] | H1].
              + rewrite (DTP.gsoAddRes H1).
                inversion dinv; eauto.
              + erewrite DTP.gssAddRes; eauto.
            - move => i cnti; split.
              + assert (cnti':=cnti).
                apply DMS.DTP.cntAdd' in cnti'.
                destruct cnti' as [[H1 H2] | H1].
                * inversion dinv.
                  move: (thread_data_lock_coh i H1)=> [] AA _.
                  move => j cntj.
                  assert (cntj':=cntj).
                  apply DMS.DTP.cntAdd' in cntj'.
                  destruct cntj' as [[H3 H4] | H3].
                  -- rewrite (DTP.gsoAddRes H1) .
                     rewrite (DTP.gsoAddRes H3).
                     eapply AA.
                  -- rewrite (DTP.gsoAddRes H1) .
                     rewrite (DTP.gssAddRes); auto.
                * move => j cntj.
                  assert (cntj':=cntj).
                  apply DMS.DTP.cntAdd' in cntj'.
                  destruct cntj' as [[H3 H4] | H3].
                  -- rewrite (DTP.gsoAddRes H3).
                     rewrite (DTP.gssAddRes); auto.
                  -- do 2 (rewrite (DTP.gssAddRes); auto).
              + assert (cnti':=cnti).
                apply DMS.DTP.cntAdd' in cnti'.
                destruct cnti' as [[H1 H2] | H1].
                * inversion dinv.
                  move: (thread_data_lock_coh i H1)=> [] _ BB.
                  move => l rm.
                  rewrite (DTP.gsoAddRes H1).
                  rewrite DTP.gsoAddLPool.
                  eauto.
                * move => l rm.
                  rewrite (DTP.gssAddRes); auto.
                  rewrite DTP.gsoAddLPool.
                  eauto.
            - move=> l rm;
                rewrite DTP.gsoAddLPool => isLock.
              inversion dinv.
              move: (locks_data_lock_coh l rm isLock)=> [] AA BB.
              split.
              + move => j cntj.
                assert (cntj':=cntj).
                apply DMS.DTP.cntAdd' in cntj'.
                destruct cntj' as [[H3 H4] | H3].
                -- rewrite (DTP.gsoAddRes H3).
                   inversion dinv; eauto.
                -- (rewrite (DTP.gssAddRes); auto).
                   eauto.
              + move => l2 rm2;
                  rewrite DTP.gsoAddLPool => isLock2.
                eauto.
            - move => b ofs.
              inversion dinv; simpl; eauto.
              apply lockRes_valid.
          Qed.

          (*This is a new lemma that is missing.*)
          intro HH; apply addThrd_inv.
          - assumption.
          - move=> j cntj .
            split;
              apply permDisjoint_permMapsDisjoint => b0 ofs0.
            + rewrite virtue_spec21.
              destruct (NatTID.eq_tid_dec i j).
              * subst. rewrite DMS.DTP.gssThreadRes.
                rewrite virtue_spec11.
                apply joins_permDisjoint.
                apply resource_at_joins.
                eexists; eassumption.
              * rewrite DMS.DTP.gsoThreadRes; auto.
                rewrite (MTCH_perm' _ MATCH).
                apply joins_permDisjoint.
                apply resource_at_joins.
                eapply join_sub_joins_trans; eauto.
                exists phi'; eauto.
                simpl.
                eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
            + rewrite virtue_spec22.
              destruct (NatTID.eq_tid_dec i j).
              * subst. rewrite DMS.DTP.gssThreadRes.
                rewrite virtue_spec12.
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                eexists; eassumption.
              * rewrite DMS.DTP.gsoThreadRes; auto.
                rewrite (MTCH_perm2' _ MATCH).
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                eapply join_sub_joins_trans; eauto.
                exists phi'; eauto.
                simpl.
                eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
          - move => l rm.
            rewrite DMS.DTP.gsoThreadLPool => isLock2.
            split; apply permDisjoint_permMapsDisjoint=> b0 ofs0 /=.
            + rewrite virtue_spec21.

              assert (exists pmap1, JTP.lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock2 in mtch_locks.
                destruct (JTP.lockRes js l).
                - exists l0; reflexivity.
                - inversion mtch_locks.
              }
              destruct H as [rm' H].
              destruct rm'.
              * inversion MATCH.
                rewrite -(mtch_locksRes _ _ _ H isLock2).
                apply joins_permDisjoint.
                apply resource_at_joins.
                eapply join_sub_joins_trans.
                exists phi'; eassumption.
                eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join;
                  eauto.
              * inversion MATCH.
                specialize (mtch_locksEmpty _ _ H isLock2).
                inversion mtch_locksEmpty.
                rewrite empty_map_spec.
                eapply permDisjoint_comm.
                eapply permDisjoint_None.
            + rewrite virtue_spec22.

              assert (exists pmap1, JTP.lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock2 in mtch_locks.
                destruct (JTP.lockRes js l).
                - exists l0; reflexivity.
                - inversion mtch_locks.
              }
              destruct H as [rm' H].
              destruct rm'.
              * inversion MATCH.
                rewrite -(mtch_locksRes0 _ _ _ H isLock2).
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                eapply join_sub_joins_trans.
                exists phi'; eassumption.
                eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join;
                  eauto.
              * inversion MATCH.
                specialize (mtch_locksEmpty _ _ H isLock2).
                inversion mtch_locksEmpty.
                rewrite empty_map_spec.
                eapply permDisjoint_comm.
                eapply permDisjoint_None.
          - move=> b0 ofs0;
              simpl.
            rewrite virtue_spec21 virtue_spec22.
            apply perm_coh_self.
          - move=> j cntj b0 ofs0.
            rewrite virtue_spec21.
            destruct (NatTID.eq_tid_dec i j).
            * subst. rewrite DMS.DTP.gssThreadRes.
              rewrite virtue_spec12.
              apply perm_coh_joins.
              apply resource_at_joins.
              eexists; eauto.
            * rewrite DMS.DTP.gsoThreadRes; auto.
              rewrite (MTCH_perm2' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              -- eexists; eauto.
              --  eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
          - move=> j cntj b0 ofs0.
            rewrite virtue_spec22.
            destruct (NatTID.eq_tid_dec i j).
            * subst. rewrite DMS.DTP.gssThreadRes.
              rewrite virtue_spec11.
              apply perm_coh_joins.
              apply resource_at_joins.
              eexists; eauto.
            * rewrite DMS.DTP.gsoThreadRes; auto.
              rewrite (MTCH_perm' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              -- eexists; eauto.
              --  eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
          - move => l rm .
            rewrite DMS.DTP.gsoThreadLPool => isLock b0 ofs0.
            rewrite virtue_spec21.
             assert (exists pmap1, JTP.lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock in mtch_locks.
                destruct (JTP.lockRes js l).
                - exists l0; reflexivity.
                - inversion mtch_locks.
              }
              destruct H as [rm' H].
              destruct rm'.
              + inversion MATCH.
                rewrite -(mtch_locksRes0 _ _ _ H isLock).
                apply perm_coh_joins.
                apply resource_at_joins.
                eapply join_sub_joins_trans.
                exists phi'; eassumption.
                eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join;
                  eauto.
              + inversion MATCH.
                specialize (mtch_locksEmpty _ _ H isLock).
                inversion mtch_locksEmpty.
                rewrite empty_map_spec.
                eapply perm_coh_empty_1.
          - move => l rm .
            rewrite DMS.DTP.gsoThreadLPool => isLock b0 ofs0.
            rewrite virtue_spec22.
             assert (exists pmap1, JTP.lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock in mtch_locks.
                destruct (JTP.lockRes js l).
                - exists l0; reflexivity.
                - inversion mtch_locks.
              }
              destruct H as [rm' H].
              destruct rm'.
              + inversion MATCH.
                rewrite -(mtch_locksRes _ _ _ H isLock).
                apply perm_coh_joins.
                apply resource_at_joins.
                apply joins_comm.
                eapply join_sub_joins_trans.

                exists phi'; eassumption.
                eapply JMS.JuicyMachineLemmas.compatible_threadRes_lockRes_join;
                  eauto.
              + inversion MATCH.
                specialize (mtch_locksEmpty _ _ H isLock).
                inversion mtch_locksEmpty.
                rewrite empty_map_spec.
                eapply perm_coh_empty_2.
                apply juicy_mem_lemmas.perm_of_res_lock_not_Freeable.
        }

        { (*invariant ds_upd*)
          (*eapply updThread_inv.*)
          apply invariant_decr.
          - assumption.
          - simpl=> b0 ofs0.
            rewrite virtue_spec11.
            rewrite -MTCH_perm.
            apply juicy_mem_lemmas.po_join_sub.
            move Hrem_fun_res at bottom.
            replace
              (m_phi
                      (JSEM.personal_mem
                         (JSEM.thread_mem_compatible Hcompatible Hi)))
            with
            (JTP.getThreadR Hi) in Hrem_fun_res by reflexivity.
            eapply resource_at_join_sub.
            exists d_phi. apply join_comm; assumption.
          - simpl=> b0 ofs0.
            rewrite virtue_spec12.
            rewrite -MTCH_perm2.
            (* lemma equivalent to juicy_mem_lemmas.po_join_sub*)
            apply po_join_sub_lock.
            apply resource_at_join_sub.
            exists d_phi.
            apply join_comm.
            assumption.
        }
      }

      { (*match_st*)
        apply match_st_age_tp_to.
        apply MTCH_addThread.
        - apply MTCH_update.
          + assumption.
          + intros. symmetry; apply virtue_spec11.
          + intros. symmetry; apply virtue_spec12.
        - intros. symmetry; apply virtue_spec21.
        - intros. symmetry; apply virtue_spec22.
      }
      {
        eapply DryMachine.step_create with
        (virtue1:=(virtue11,virtue12))
          (virtue2:=(virtue21,virtue22)).
        - (*boundedness 1*)
          split.
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p0 f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta11 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p0, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p0, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          {
            apply join_join_sub in Hrem_fun_res.
            apply resource_at_join_sub with (l:=(p0,b0)) in Hrem_fun_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_fun_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_fun_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p0, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p0, b0)).
            destruct m'; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p0) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }
          (* eapply bounded_maps.treemap_sub_map. *)
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta12 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          {
            apply join_join_sub in Hrem_fun_res.
            apply resource_at_join_sub with (l:=(p,b0)) in Hrem_fun_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_fun_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_fun_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p, b0)).
            destruct m'; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }

        - (*boundedness 2*)
           split.
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p0 f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta21 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p0, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p0, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          {
            apply join_join_sub in Hrem_fun_res.
            apply resource_at_join_sub with (l:=(p0,b0)) in Hrem_fun_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_fun_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_fun_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p0, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p0, b0)).
            destruct m'; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p0) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }
          (* eapply bounded_maps.treemap_sub_map. *)
        * eapply bounded_maps.sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply bounded_maps.map_leq_apply in HH';
            try apply bounded_maps.treemap_sub_map.
          rewrite PTree.gmap in HH.
          destruct HH'  as [f2 HH'].
          rewrite HH' in HH; simpl in HH; inversion HH.
          exists f2; split; auto.
          move => b0 f1b0.
          unfold inflated_delta22 in f1b0.
          destruct (f2 b0) eqn:is_none; auto.
          cut (perm_of_res (d_phi @ (p, b0)) = None).
          { rewrite /perm_of_res.
            destruct (d_phi @ (p, b0)) eqn:DELT;
              try solve[intros delt; inversion delt].
            destruct (eq_dec sh Share.bot) eqn:DELT';
              try solve[intros delt; inversion delt].
            unfold eq_dec in DELT'.
            rewrite DELT' in f1b0; inversion f1b0.
            destruct k; intros NADA; inversion NADA.
            apply perm_of_empty_inv in NADA.
            subst; exfalso. apply shares.bot_unreadable; assumption. }
          {
            apply join_join_sub in Hrem_fun_res.
            apply resource_at_join_sub with (l:=(p,b0)) in Hrem_fun_res.
            apply juicy_mem_lemmas.po_join_sub in Hrem_fun_res.
            eapply juicy_mem_lemmas.perm_order''_trans in Hrem_fun_res;
              [|eapply perm_of_res_op1].

            cut ((perm_of_res'
                    (JSEM.ThreadPool.getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (JMS.mem_compat_thread_max_cohere
                        Hcmpt Hi (p, b0)).
            destruct m'; simpl in *.
            rewrite  /max_access_at
                    /access_at
                    /PMap.get /=.

            move : HH'.

            rewrite /getMaxPerm PTree.gmap1; simpl.
            destruct ((mem_access.2) ! p) eqn:AA;
              try solve [simpl; intros FALSE; inversion FALSE].
            simpl; intros TT; inversion TT.
            rewrite -H1 in is_none.
            rewrite is_none => /po_None1.
            auto.
            }


        - assumption.
        - inversion MATCH. erewrite <- mtch_gtc; eassumption.
        - eassumption.
        - move => b0 ofs0 /=.
          rewrite virtue_spec11.
          rewrite virtue_spec21.
          inversion MATCH. erewrite <- MTCH_perm.
          eapply permjoin.join_permjoin.
          apply resource_at_join.
          move Hrem_fun_res at bottom.
            replace
              (m_phi
                      (JSEM.personal_mem
                         (JSEM.thread_mem_compatible Hcompatible Hi)))
            with
            (JTP.getThreadR Hi) in Hrem_fun_res by reflexivity.
            assumption.
        -move => b0 ofs0 /=.
          rewrite virtue_spec12.
          rewrite virtue_spec22.
          inversion MATCH. erewrite <- MTCH_perm2.
          eapply permjoin.join_permjoin_lock. (*for _locks *)
          apply resource_at_join.
          move Hrem_fun_res at bottom.
            replace
              (m_phi
                      (JSEM.personal_mem
                         (JSEM.thread_mem_compatible Hcompatible Hi)))
            with
            (JTP.getThreadR Hi) in Hrem_fun_res by reflexivity.
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
      pose (pdata:= fun i:nat => pmap_tid.1 !! b (Z.of_nat i)).
      pose (pmap_tid' :=
              (setPermBlock
                (Some Nonempty)
                b
                (Ptrofs.intval ofs)
                pmap_tid.1
                LKSIZE_nat,
               (setPermBlock
                  (Some Writable)
                  b
                  (Ptrofs.intval ofs)
                  pmap_tid.2
                  LKSIZE_nat

           ))).
   assert (pmap_spec1: forall b0 ofs0, perm_of_res (phi' @ (b0, ofs0)) =
                                    pmap_tid'.1 !! b0 ofs0).
   { move => b0 ofs0.
     rewrite /pmap_tid'.
     destruct (peq b b0);
       [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
     - rewrite setPermBlock_same.

       assert (HH':adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
       { split; auto. }

       move: Hrmap => /=.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
       intros [X Hg]; destruct (X _ HH') as (val & sh & Rsh & sh_before & Wsh & sh_after); clear X.
       rewrite sh_after.
       if_tac; reflexivity.
       auto.
     - rewrite setPermBlock_other_1.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
        { intros [ H1 [H2 H2']]; apply n; split; auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm' _ MATCH); repeat f_equal;
       apply proof_irrelevance.

       apply Intv.range_notin in n; auto.
       pose proof LKSIZE_pos; simpl. xomega.
     - rewrite setPermBlock_other_2.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b0,ofs0)).
        { intros [ H1 [H2 H2']]; apply n. auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm' _ MATCH); repeat f_equal;
       apply proof_irrelevance.

       auto.

       }

   assert (pmap_spec2: forall b0 ofs0, perm_of_res_lock (phi' @ (b0, ofs0)) =
                                    pmap_tid'.2 !! b0 ofs0).
    { move => b0 ofs0.
     rewrite /pmap_tid'.
     destruct (peq b b0);
       [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
     - rewrite setPermBlock_same.

       assert (HH':adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
       { split; auto. }

       move: Hrmap => /=.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
       intros [X Hg]; destruct (X _ HH') as (val & sh & Rsh & sh_before & Wsh & sh_after); clear X.
       rewrite sh_after.
       if_tac; apply perm_of_writable;
         try apply shares.writable_share_glb_Rsh; eauto;
           apply glb_Rsh_not_top.
       auto.

     - rewrite setPermBlock_other_1.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
        { intros [ H1 [H2 H2']]; apply n; split; auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm2' _ MATCH); repeat f_equal;
       apply proof_irrelevance.

       apply Intv.range_notin in n; auto.
       pose proof LKSIZE_pos; simpl. xomega.
     - rewrite setPermBlock_other_2.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b0,ofs0)).
        { intros [ H1 [H2 H2']]; apply n. auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm2' _ MATCH); repeat f_equal;
       apply proof_irrelevance.

       auto.

       }



      (*HERE*)
      (*pose (pmap_lp   := setPerm (Some Writable) b (Ptrofs.intval ofs)
                                               (DTP.lockSet ds)).*)
      pose (ds':= DTP.updThread Htid' (Kresume c Vundef) (pmap_tid')).
      pose (ds'':= DTP.updLockSet ds' (b, Ptrofs.intval ofs) (empty_map,empty_map)).
      exists ds'',  (JSEM.Events.mklock (b, Ptrofs.intval ofs)).
      split ; [|split].
      - (*DryMachine.invariant ds''*)
        cut (DryMachine.invariant ds').
        { intros dinv'.
          apply updLock_inv.
          - assumption.
          - intros i0 cnt0 ofs0 ineq.
            apply permMapsDisjoint2_empty.
          - intros i0 cnti.
            apply permMapsDisjoint2_comm;
            apply permMapsDisjoint2_empty.
          - intros laddr rmap'0 H H0; split;
            first [ apply permCoh_empty | apply permCoh_empty'].
            { move=> b0 ofs0.
              apply (invariant_not_freeable) with (b:=b0)(ofs:= ofs0) in dinv.
              destruct dinv as [AA BB].
              eapply BB in H0.
              destruct ((rmap'0.2) # b0 ofs0); try constructor.
              destruct p; try constructor.
              exfalso; apply H0; reflexivity. }
          - intros i0 cnti; apply permCoh_empty'.
          - intros i0 cnti; split;
            first [ apply permCoh_empty | apply permCoh_empty'].
            { move=> b0 ofs0.
              destruct (NatTID.eq_tid_dec i0 i).
              - subst i0.
                rewrite DMS.DTP.gssThreadRes.
                rewrite <- pmap_spec2.
                apply perm_of_res_lock_not_Freeable.
              - rewrite DMS.DTP.gsoThreadRes; auto.

                rewrite (MTCH_perm2' _ MATCH).

              apply perm_of_res_lock_not_Freeable. }
          - intros ofs0  ineq.
          simpl. rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.

          destruct (DryMachine.SIG.ThreadPool.lockRes ds (b, ofs0)) eqn:AA;  try reflexivity.

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

          assert (ineq': Ptrofs.intval ofs <= ofs0 < Ptrofs.intval ofs + LKSIZE).
          { clear - ineq.
            destruct ineq; auto. simpl in *.
            xomega.
          }
          assert (HH':adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
          { split; auto. }
          move: Hrmap => /=.
          rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
          intros [X Hg]; destruct (X _ HH') as (val & sh & Rsh & sh_before & Wsh & sh_after); clear X.
          rewrite sh_before in HH.
          destruct HH as [x HH]. inversion HH.

        - intros ofs0 ineq.
          simpl. rewrite DryMachine.SIG.ThreadPool.gsoThreadLPool.
          destruct (DryMachine.SIG.ThreadPool.lockRes ds (b, ofs0)) eqn:AA; try reflexivity.
          inversion MATCH. specialize (mtch_locks (b,ofs0)).
          rewrite AA in mtch_locks.
          destruct (JSEM.ThreadPool.lockRes js (b, ofs0)) eqn:BB; inversion mtch_locks.
          destruct Hcompatible as [allj Hcompatible].
          inversion Hcompatible.
          unfold JSEM.ThreadPool.lockRes in BB.
          specialize (lset_in_juice (b, ofs0)). rewrite BB in lset_in_juice.
          destruct lset_in_juice as [sh' [psh [P MAP]]]; auto.
          assert (HH:= JSEM.compatible_threadRes_sub Hi juice_join).          assert (VALID:= phi_valid allj).
          specialize (VALID b ofs0).
          unfold "oo" in VALID.
          rewrite MAP in VALID.
          simpl in VALID.
          assert (ineq': 0 < Ptrofs.intval ofs - ofs0 < LKSIZE).
          { clear - ineq. simpl in ineq; destruct ineq. xomega. }
          apply VALID in ineq'.
          replace (ofs0 + (Ptrofs.intval ofs - ofs0)) with (Ptrofs.intval ofs) in ineq' by omega.
          apply resource_at_join_sub with (l:= (b,Ptrofs.intval ofs)) in HH.
          move: Hrmap => /=.
          rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2 H3.
          assert (adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, Ptrofs.unsigned ofs)).
          { split; auto.
            split; omega. }
          destruct H3 as [H3 Hg].
          move: (H3 _ H4)=> [] v [] sh [] Rsh [] HH1 [] Wsh HH2.
          rewrite HH1 in HH.
          destruct HH as [x HH].
          inversion HH.
          + move ineq' at bottom.
            rewrite -H10 in ineq'.
            inversion ineq'.
          + move ineq' at bottom.
            rewrite -H10 in ineq'.
            inversion ineq'.
        }

        { (*DryMachine.invariant ds' *)
          (*But first, a couple facts*)

          assert (H:forall j cntj, i<> j ->
                              joins phi' (@JTP.getThreadR j js (MTCH_cnt' MATCH cntj))).
          { (*Will use rmap_locking.rmap_makelock_join*)
            intros j cntj neq.
            assert (Hcmpt':=Hcmpt).
            apply compatible_threadRes_join  with
            (cnti:= Hi)(cntj:= (MTCH_cnt' MATCH cntj)) in Hcmpt'; auto.
              destruct Hcmpt' as [x thread_join].
              simpl in Hrmap.
              apply (rmap_locking.rmap_makelock_join
                       _ _ _ _
                       _ _ _
                       LKSIZE_pos
                       Hrmap) in thread_join.
              destruct thread_join as [X [_ THEY_JOIN]].
              exists X; assumption. }



          assert (H':forall (l : address)
                      pmap,
                     JTP.lockRes js l = Some (Some pmap) ->
                     joins phi' pmap).
          { (*Will use rmap_locking.rmap_makelock_join*)
            intros l pmap is_lock.
            assert (Hcmpt':=Hcmpt).
            apply compatible_threadRes_lockRes_join  with
            (cnti:= Hi)(l:=l)(phi:=pmap) in Hcmpt'; auto.
              destruct Hcmpt' as [x thread_lock_join].
              simpl in Hrmap.
              apply (rmap_locking.rmap_makelock_join
                       _ _ _ _
                       _ _ _
                       LKSIZE_pos
                       Hrmap) in thread_lock_join.
              destruct thread_lock_join as [X [_ THEY_JOIN]].
              exists X; assumption.

          }






          apply updThread_inv.
          - eassumption.
          - intros j cnt H1.
            split; apply permDisjoint_permMapsDisjoint=> b0 ofs0.
            + rewrite <- pmap_spec1.
              rewrite (MTCH_perm' _ MATCH).
              apply joins_permDisjoint.
              apply resource_at_joins; apply H; assumption.
            + rewrite <- pmap_spec2.
              rewrite (MTCH_perm2' _ MATCH).
              apply joins_permDisjoint_lock.
              apply resource_at_joins; apply H; assumption.
          - intros j cnt neq b0 ofs0.
            rewrite (MTCH_perm' _ MATCH).
            destruct (peq b b0);
              [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
            + rewrite setPermBlock_same; auto.

              move: Hrmap.
              rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
              assert (H3: adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { split; auto. }
              intros [X Hg]; destruct (X _ H3) as (val & sh & Rsh & H4 & Y & H5); clear X.
              (*replace (MTCH_cnt' MATCH cnt) with Hi by apply proof_irrelevance.*)
              assert (H0: joins (JTP.getThreadR (MTCH_cnt' MATCH cnt))
                            (JTP.getThreadR Hi)).
              { eapply JMS.JuicyMachineLemmas.compatible_threadRes_join;
                eauto. }
              apply resource_at_joins with (loc:=(b, ofs0))   in H0.
              rewrite Hpersonal_juice in H0.
              rewrite H4 in H0.
              destruct H0 as [x H0]; inversion H0; subst.
              -- rewrite - H7; simpl;
                 destruct (eq_dec sh1 Share.bot); constructor.
              -- rewrite -H7; simpl.
                 apply join_comm in RJ.
                 exfalso. eapply shares.join_writable_readable; eauto.
            + apply Intv.range_notin in n; simpl in n; try (pose proof LKSIZE_pos; simpl; omega).
              rewrite setPermBlock_other_1; auto.
              rewrite /pmap_tid.
              rewrite (MTCH_perm2' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
            + rewrite setPermBlock_other_2; auto.
              rewrite /pmap_tid.
              rewrite (MTCH_perm2' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.

          - intros j cnt neq b0 ofs0.
            rewrite (MTCH_perm2' _ MATCH).
            destruct (peq b b0);
              [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
            + rewrite setPermBlock_same; auto.

              move: Hrmap.
              rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
              assert (H3: adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { split; auto. }
              intros [X Hg]; destruct (X _ H3) as (val & sh & Rsh & H4 & Wsh & H5); clear X.
              assert (H0: joins (JTP.getThreadR (MTCH_cnt' MATCH cnt))
                            (JTP.getThreadR Hi)).
              { eapply JMS.JuicyMachineLemmas.compatible_threadRes_join;
                eauto. }
              apply resource_at_joins with (loc:=(b, ofs0))   in H0.
              rewrite Hpersonal_juice in H0.
              rewrite H4 in H0.
              destruct H0 as [x H0]; inversion H0; subst.
              -- rewrite - H7; simpl;
                 destruct (eq_dec sh1 Share.bot); constructor.
              -- rewrite -H7; simpl.
                 apply join_comm in RJ.
                 exfalso. eapply shares.join_writable_readable; eauto.
            + apply Intv.range_notin in n; simpl in n; try (pose proof LKSIZE_pos; simpl; omega).
              rewrite setPermBlock_other_1; auto.
              rewrite /pmap_tid.
              rewrite (MTCH_perm' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
            + rewrite setPermBlock_other_2; auto.
              rewrite /pmap_tid.
              rewrite (MTCH_perm' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply JMS.JuicyMachineLemmas.compatible_threadRes_join; eauto.
          - move=> l pmap is_lock.
            assert (is_lock': exists p, JTP.lockRes js l = Some p).
            { destruct (JSEM.ThreadPool.lockRes js l) eqn:is_lock'.
              + exists l0; reflexivity.
              + inversion MATCH. specialize (mtch_locks l).
                rewrite is_lock is_lock' in mtch_locks.
                inversion mtch_locks. }
            destruct is_lock' as [p is_lock'];
              destruct p.
            + assert (is_lock'':=is_lock').
              apply H' in is_lock''.
              split; apply permDisjoint_permMapsDisjoint=> b0 ofs0.
              * rewrite - pmap_spec1.
                inversion MATCH.
                erewrite <- mtch_locksRes; eauto.
                apply joins_permDisjoint.
                apply resource_at_joins.
                apply joins_comm.
                eapply H'; eauto.
              * rewrite - pmap_spec2.
                inversion MATCH.
                erewrite <- mtch_locksRes0; eauto.
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                apply joins_comm.
                eapply H'; eauto.
            + inversion MATCH.
              eapply mtch_locksEmpty in is_lock';
                eauto; rewrite is_lock'.
              split; first [apply empty_disjoint' | apply empty_disjoint].
          - move=> l pmap is_lock.
            assert (is_lock': exists p, JTP.lockRes js l = Some p).
            { destruct (JSEM.ThreadPool.lockRes js l) eqn:is_lock'.
              + exists l0; reflexivity.
              + inversion MATCH. specialize (mtch_locks l).
                rewrite is_lock is_lock' in mtch_locks.
                inversion mtch_locks. }
            destruct is_lock' as [p is_lock'];
              destruct p.
             + assert (is_lock'':=is_lock').
              apply H' in is_lock''.
              split; move=> b0 ofs0.
              * rewrite - pmap_spec2.
                inversion MATCH.
                erewrite <- mtch_locksRes; eauto.
                apply perm_coh_joins.
                apply resource_at_joins.
                apply joins_comm.
                eapply H'; eauto.
              * rewrite - pmap_spec1.
                inversion MATCH.
                erewrite <- mtch_locksRes0; eauto.
                apply perm_coh_joins.
                apply resource_at_joins.
                eapply H'; eauto.
            + inversion MATCH.
              eapply mtch_locksEmpty in is_lock';
                eauto; rewrite is_lock'.
              split;
                first [ apply permCoh_empty' | apply permCoh_empty].

              { move=> b0 ofs0.
                rewrite -pmap_spec2.
                apply perm_of_res_lock_not_Freeable. }
          - intros b0 ofs0.
            rewrite - pmap_spec2 - pmap_spec1.
            apply perm_coh_self.
        }


            (*

Here be dragons
                *)

      - (*rewrite Htp''; *)    unfold ds''.
                                apply MTCH_age.
                                apply MTCH_updLockN.
                                (*rewrite Htp';*) unfold ds'.
                                apply MTCH_update.
                                assumption.

                                intros b0 ofs0.
                                apply pmap_spec1.

                                intros b0 ofs0.
                                apply pmap_spec2.
      - econstructor 4. (*The step *)
        10: reflexivity.
        10: reflexivity.
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + eassumption.
        (*      + eapply MTCH_compat; eassumption. *)
        + reflexivity.
        + admit.
      (* Range of lock permisison, now it spans multiple locations given my LKSIZE *)
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
        + replace (MTCH_cnt MATCH Hi) with Htid' by
              apply proof_irrelevance; reflexivity.
        + replace (MTCH_cnt MATCH Hi) with Htid' by
              apply proof_irrelevance; reflexivity.
        + destruct (DTP.lockRes ds (b, Ptrofs.intval ofs)) eqn:AA; try reflexivity.
          inversion MATCH.
          specialize (mtch_locks (b, Ptrofs.intval ofs)).
          rewrite AA in mtch_locks.

          move: Hrmap.
          rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
          assert (H3: adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, Ptrofs.unsigned ofs)).
          { split; auto.
            pose proof LKSIZE_pos.
            split; omega. }
          intros [X Hg]; destruct (X _ H3) as (val & sh & Rsh & H4 & Y & H5); clear X.
          assert (Hcmpt':=Hcmpt).
          destruct Hcmpt as [jall Hcmpt].
          inversion Hcmpt.
          apply JSEM.compatible_threadRes_sub with (cnt:=Hi) in juice_join.
          apply resource_at_join_sub with (l:=(b, Ptrofs.unsigned ofs)) in juice_join.
          destruct juice_join as [X HH].
          simpl in H4.
          rewrite H4 in HH.
          move : mtch_locks => /lset_in_juice [] sh' [] psh' [] P H6.
          rewrite H6 in HH; inversion HH.
    }

        (* step_freelock *)
        { assert (Htid':= MTCH_cnt MATCH Hi).
          (* (Htp': tp' = updThread cnt0 (Kresume c) pmap_tid')
            (Htp'': tp'' = updLockSet tp' pmap_lp), *)
          Definition WorF (sh: share): permission:=
            if eq_dec sh Share.top then Freeable else Writable.
          pose (delta_b:=
                  fun ofs0 => if (Intv.In_dec ofs0 ( Ptrofs.intval ofs,  Ptrofs.intval ofs + LKSIZE)%Z) then
                             Some (perm_of_res (phi' @ (b, ofs0)))
                           else None).
          Definition empty_delta_map: delta_map:= PTree.empty (Z -> option (option permission)).
          pose (virtue:= PTree.set b delta_b empty_delta_map).

          pose (pmap_tid  := DTP.getThreadR Htid').
          pose (pdata:= fun i:nat =>
                          if (i > LKSIZE_nat)%N  then
                            None
                          else
                            perm_of_res (phi' @ (b, Ptrofs.intval ofs + Z.of_nat (i)-1))
               ).
          pose (pmap_tid' := (setPermBlock_var (*=setPermBlockfunc*)
                                pdata
                                b
                                (Ptrofs.intval ofs)
                                pmap_tid.1
                                LKSIZE_nat,
                              setPermBlock
                                None
                                b
                                (Ptrofs.intval ofs)
                                pmap_tid.2
                                LKSIZE_nat)).
          assert (pmap_spec1: forall b0 ofs0, perm_of_res (phi' @ (b0, ofs0)) =
                                         pmap_tid'.1 !! b0 ofs0).
          { move => b0 ofs0.
            rewrite /pmap_tid'.
            destruct (peq b b0);
              [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
            - rewrite setPermBlock_var_same; auto.
              unfold pdata.
              replace
                (Ptrofs.intval ofs + Z.of_nat (nat_of_Z (ofs0 - Ptrofs.intval ofs + 1)) -1)
              with
              ofs0.
              assert ((LKSIZE_nat < nat_of_Z (ofs0 - Ptrofs.intval ofs + 1) )%N = false).
              {
                move: i0. clear.
                move => [] /= A B.
                rewrite /LKSIZE_nat /nat_of_Z.
                apply /ltP => / lt_not_le HH.
                apply: HH.
                (* rewrite -Z2Nat.inj_succ .*)
                eapply Z2Nat.inj_le; eauto.
                xomega.
                xomega.
                xomega.
              }
              rewrite H.
              reflexivity.
              rewrite Coqlib.nat_of_Z_eq.
              xomega.

              unfold LKSIZE in i0; destruct i0 as [A B].
              simpl in A. simpl in B.
              assert (ofs0 - Ptrofs.intval ofs >= 0).
              omega.
              omega.
            - rewrite setPermBlock_var_other_1; auto.
              move: Hrmap  => [] [] H1 [].
              assert (H3: ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { move => [] AA BB.
                apply: n; auto. }
              move => /(_ _ H3) => <- _.

                rewrite (MTCH_perm' _ MATCH).
                replace (MTCH_cnt' MATCH Htid') with Hi by
                    apply proof_irrelevance.
                reflexivity.
                apply Intv.range_notin in n; auto.
                pose proof LKSIZE_pos; simpl; omega.
            - rewrite setPermBlock_var_other_2; auto.
              move: Hrmap  => [] [] H1 [].
              assert (H3: ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b0, ofs0)).
              { move => [] AA BB.
                apply: n; auto. }
              move => /(_ _ H3) => <- _.

                rewrite (MTCH_perm' _ MATCH).
                replace (MTCH_cnt' MATCH Htid') with Hi by
                    apply proof_irrelevance.
                reflexivity.
          }

          assert (pmap_spec2: forall b0 ofs0, perm_of_res_lock (phi' @ (b0, ofs0)) =
                                         pmap_tid'.2 !! b0 ofs0).
          {
            move => b0 ofs0.
            rewrite /pmap_tid'.
            destruct (peq b b0);
              [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
            - rewrite setPermBlock_same; auto.
              move: Hrmap  => [] [] H1 [] _.
              assert (H3: adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { split; auto. }
              intros [X Hg]; destruct (X _ H3) as (sh & Rsh & -> & Wsh & BB); clear X.
              reflexivity.
            - rewrite setPermBlock_other_1; auto.
               move: Hrmap  => [] [] H1 [].
              assert (H3: ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { move => [] AA BB.
                apply: n; auto. }
              move => /(_ _ H3) => <- _.


                rewrite (MTCH_perm2' _ MATCH).
                replace (MTCH_cnt' MATCH Htid') with Hi by
                    apply proof_irrelevance.
                reflexivity.
                apply Intv.range_notin in n; auto.
                pose proof LKSIZE_pos; simpl; omega.
            - rewrite setPermBlock_other_2; auto.
              move: Hrmap  => [] [] H1 [].
              assert (H3: ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b0, ofs0)).
              { move => [] AA BB.
                apply: n; auto. }
              move => /(_ _ H3) => <- _.


                rewrite (MTCH_perm2' _ MATCH).
                replace (MTCH_cnt' MATCH Htid') with Hi by
                    apply proof_irrelevance.
                reflexivity.
          }


          pose (ds':= DTP.updThread Htid' (Kresume c Vundef) pmap_tid').
          pose (ds'':= DTP.remLockSet ds' (b,(Ptrofs.intval ofs))).

          exists ds'', (JSEM.Events.freelock (b, Ptrofs.intval ofs)).
          split ; [|split].

          unfold ds''; rewrite DTP.remLock_updThread_comm.
          pose (ds0:= (DTP.remLockSet ds (b, (Ptrofs.intval ofs)))).

          - cut (DryMachine.invariant ds0).
            { (*DryMachine.invariant ds' *)
              (*But first, a couple facts*)

          assert (H:forall j cntj, i<> j ->
                              joins phi' (@JTP.getThreadR j js (MTCH_cnt' MATCH cntj))).
          { (*Will use rmap_locking.rmap_makelock_join*)
            move => j cntj neq.
            assert (Hcmpt':=Hcmpt).
            apply compatible_threadRes_join  with
            (cnti:= Hi)(cntj:= (MTCH_cnt' MATCH cntj)) in Hcmpt'; auto.
              destruct Hcmpt' as [x thread_join].
              simpl in Hrmap.
              apply (rmap_locking.rmap_freelock_join
                       _ _ _ _
                       _ _ _ _
                       LKSIZE_pos
                       Hrmap) in thread_join.
              destruct thread_join as [X [_ THEY_JOIN]].
              exists X; assumption. }

          assert (H':forall (l : address)
                      pmap,
                     JTP.lockRes js l = Some (Some pmap) ->
                     joins phi' pmap).
          { intros l pmap is_lock.
            assert (Hcmpt':=Hcmpt).
            apply compatible_threadRes_lockRes_join  with
            (cnti:= Hi)(l:=l)(phi:=pmap) in Hcmpt'; auto.
              destruct Hcmpt' as [x thread_lock_join].
              simpl in Hrmap.
              apply (rmap_locking.rmap_freelock_join
                       _ _ _ _
                       _ _ _ _
                       LKSIZE_pos
                       Hrmap) in thread_lock_join.
              destruct thread_lock_join as [X [_ THEY_JOIN]].
              exists X; assumption.
          }


          intros dinv0.
          apply updThread_inv.
          - eassumption.
          - intros.
            split; apply permDisjoint_permMapsDisjoint=> b0 ofs0.
            + rewrite -pmap_spec1.
              rewrite (MTCH_perm' _ MATCH).
              apply joins_permDisjoint.
              apply resource_at_joins.
              apply H; assumption.
            + rewrite -pmap_spec2.
              rewrite (MTCH_perm2' _ MATCH).
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              apply H; assumption.
          - move => j cntj neq b0 ofs0.
            rewrite -pmap_spec2.
            rewrite (MTCH_perm' _ MATCH).
            apply perm_coh_joins.
            apply resource_at_joins.
            apply joins_comm.
            eapply H; assumption.
          - intros j cntj neq b0 ofs0.
            rewrite <- pmap_spec1.
            rewrite (MTCH_perm2' _ MATCH).
            apply perm_coh_joins.
            apply resource_at_joins.
            eapply H; assumption.
          - move=> l pmap is_lock0.
            assert (is_lock: DryMachine.ThreadPool.lockRes ds l =  Some pmap).
            { destruct (AMap.E.eq_dec (b, Ptrofs.intval ofs) l).
                * subst l.
                  rewrite DMS.DTP.gsslockResRemLock in is_lock0; inversion is_lock0.
                * rewrite DMS.DTP.gsolockResRemLock in is_lock0; auto. }
            assert (is_lock': exists p, JTP.lockRes js l = Some p).
            { destruct (JSEM.ThreadPool.lockRes js l) eqn:is_lock'.
              + exists l0; reflexivity.
              + inversion MATCH. specialize (mtch_locks l).
                move mtch_locks at bottom.
                move is_lock at bottom.
                move is_lock' at bottom.
                  rewrite is_lock is_lock' in mtch_locks.
                  inversion mtch_locks. }
            destruct is_lock' as [p is_lock'];
              destruct p.
            + assert (is_lock'':=is_lock').
              apply H' in is_lock''.
              split; apply permDisjoint_permMapsDisjoint=> b0 ofs0.
              * rewrite - pmap_spec1.
                inversion MATCH.
                erewrite <- mtch_locksRes; eauto.
                apply joins_permDisjoint.
                apply resource_at_joins.
                apply joins_comm.
                eapply H'; eauto.
              * rewrite - pmap_spec2.
                inversion MATCH.
                erewrite <- mtch_locksRes0; eauto.
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                apply joins_comm.
                eapply H'; eauto.
            + inversion MATCH.
              eapply mtch_locksEmpty in is_lock';
                eauto; rewrite is_lock'.
              split; first [apply empty_disjoint'| apply permCoh_empty].
          - move=> l pmap is_lock0.
            assert (is_lock: DryMachine.ThreadPool.lockRes ds l =  Some pmap).
            { destruct (AMap.E.eq_dec (b, Ptrofs.intval ofs) l).
                * subst l.
                  rewrite DMS.DTP.gsslockResRemLock in is_lock0; inversion is_lock0.
                * rewrite DMS.DTP.gsolockResRemLock in is_lock0; auto. }
            assert (is_lock': exists p, JTP.lockRes js l = Some p).
            { destruct (JSEM.ThreadPool.lockRes js l) eqn:is_lock'.
              + exists l0; reflexivity.
              + inversion MATCH. specialize (mtch_locks l).
                rewrite is_lock is_lock' in mtch_locks.
                inversion mtch_locks. }
            destruct is_lock' as [p is_lock'];
              destruct p.
             + assert (is_lock'':=is_lock').
              apply H' in is_lock''.
              split; move=> b0 ofs0.
              * rewrite - pmap_spec2.
                inversion MATCH.
                erewrite <- mtch_locksRes; eauto.
                apply perm_coh_joins.
                apply resource_at_joins.
                apply joins_comm.
                eapply H'; eauto.
              * rewrite - pmap_spec1.
                inversion MATCH.
                erewrite <- mtch_locksRes0; eauto.
                apply perm_coh_joins.
                apply resource_at_joins.
                eapply H'; eauto.
            + inversion MATCH.
              eapply mtch_locksEmpty in is_lock';
                eauto; rewrite is_lock'.
              split; first [apply permCoh_empty'| apply permCoh_empty].

              { move=> b0 ofs0.
                rewrite -pmap_spec2.
                apply perm_of_res_lock_not_Freeable. }
          - intros b0 ofs0.
            rewrite - pmap_spec2 - pmap_spec1.
            apply perm_coh_self.
            }




(*
              Old proof was removed from here

*)
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
            apply pmap_spec1.
            apply pmap_spec2.

          - (*The step*)

            (*First get the lock rmap*)

            destruct (DTP.lockRes ds (b, Ptrofs.intval ofs)) eqn:is_lock.
            Focus 2.
            { inversion MATCH.
              specialize (mtch_locks (b, Ptrofs.intval ofs)).
              rewrite is_lock His_acq in mtch_locks.
              inversion mtch_locks.
            } Unfocus.


            econstructor 5. (*The step *)
            12: reflexivity.
            12: reflexivity.
            7: reflexivity.

            + instantiate (1:=pdata) => p.
              rewrite /pdata => -> //.
            + assumption.
            + eapply MTCH_getThreadC; eassumption.
            + eassumption.
            + eassumption.
            + move=> b0 ofs0.
              inversion MATCH;
                specialize (mtch_locksEmpty _ _ His_acq is_lock); rewrite mtch_locksEmpty.
              simpl; rewrite empty_map_spec; split; reflexivity.
            + intros ofs0 ineq.
              rewrite /Mem.perm.
              assert (HH:=@restrPermMap_Cur _ m' (DryMachine.compat_th (MTCH_compat js ds m' MATCH Hcmpt)
              (MTCH_cnt MATCH Hi)).2 b ofs0).
              unfold permission_at in HH. rewrite HH.
              rewrite -(MTCH_perm2 _ MATCH).
              move: Hrmap  => [] [] H1 [] AA.
              assert (H3: adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { split; auto. }
              intros [X Hg]; destruct (X _ H3) as (sh & Rsh & _ & Wsh & ->); clear X.
              if_tac.
              * simpl.
                rewrite perm_of_writable.
                (*1*) constructor.
                (*2*) eapply shares.writable_share_glb_Rsh; eauto.
                (*3*) apply glb_Rsh_not_top.
              * simpl.
                rewrite perm_of_writable.
                (*1*) constructor.
                (*2*) eapply shares.writable_share_glb_Rsh; eauto.
                (*3*) apply glb_Rsh_not_top.
            + replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
              reflexivity.
            + intros indx ineq.
              (* instantiate (1:=pdata). *)
              unfold pdata.
              assert ((LKSIZE_nat < indx.+1)%N = false).
              { destruct ineq.
                move: H0.
                simpl.
                destruct (LKSIZE_nat < indx.+1)%N eqn:NN; auto.
                assert ((LKSIZE_nat < indx.+1)%N) by
                (rewrite NN; auto).
                move: H0 => /ltP.
                intros. unfold LKSIZE_nat in *. apply Z2Nat.inj_lt in H0; try omega. rewrite Nat2Z.id in H0; omega. }
              rewrite H.

              move: Hrmap  => [] [] H1 [] AA.
              assert (H3: adr_range (b, Ptrofs.unsigned ofs)
                                    LKSIZE
                     (b, Ptrofs.unsigned ofs + Z.of_nat indx.+1 - 1)).
              { split; auto.
                unfold LKSIZE.
                move:  ineq.
                clear.
                rewrite /LKSIZE => [] [] /= A B.
                replace (Ptrofs.unsigned ofs + Z.pos (Pos.of_succ_nat indx) - 1)
                with
                (Ptrofs.unsigned ofs + Z.of_nat indx).
                split; simpl.
                replace (Ptrofs.unsigned ofs) with (Ptrofs.unsigned ofs + 0) at 1.
                apply Z.add_le_mono; omega.
                omega.
                omega.
                rewrite Zpos_P_of_succ_nat; omega. }
              unfold Ptrofs.unsigned in H3.
              intros [X Hg]; destruct (X _ H3) as (sh & ? & -> & Wsh & _); clear X; simpl.
              destruct (eq_dec sh Share.top); try subst.
              * rewrite perm_of_freeable; constructor.
              * rewrite perm_of_writable; auto; constructor.
            + replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
              reflexivity.
        }

        (* step_acqfail *)
        {
          exists ds, (JSEM.Events.failacq (b, Ptrofs.intval ofs)).
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
              + admit.
      (* Range of lock permisison, now it spans multiple locations given my LKSIZE *)
              + erewrite restrPermMap_ext.
                eassumption.
                intros b0.
                inversion MATCH; subst.
                extensionality x.
                rewrite -JSEM.juic2Perm_locks_correct.
                symmetry; apply mtch_perm2.
                apply JSEM.mem_compat_thread_max_cohere.
                assumption.
            }
        }

        Grab Existential Variables.
    Focus 4.
    { (*This is side condition [Hlt'] of acquire or relese *)
       intros b0 ofs0.
             move: (Hlt' b0 ofs0).
             (*Do the cases *)
             destruct (peq b b0);
               [subst b0;
                 destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
             - do 2 (rewrite setPermBlock_same; auto).
             - apply Intv.range_notin in n; [|simpl; pose proof LKSIZE_pos; omega].
               do 2 (rewrite setPermBlock_other_1; auto).

               destruct Hcmpt as [jall Hcmpt];
               inversion Hcmpt; inversion all_cohere.
               rewrite -JSEM.juic2Perm_locks_correct.
               rewrite -(MTCH_perm2 _ MATCH); auto.
               apply JMS.mem_access_coh_sub with (phi1:=jall).
               assumption.
               eapply JMS.compatible_threadRes_sub; eauto.
             - do 2 (rewrite setPermBlock_other_2; auto).
               destruct Hcmpt as [jall Hcmpt];
               inversion Hcmpt; inversion all_cohere.
               rewrite -JSEM.juic2Perm_locks_correct.
               rewrite -(MTCH_perm2 _ MATCH); auto.
               apply JMS.mem_access_coh_sub with (phi1:=jall).
               assumption.
               eapply JMS.compatible_threadRes_sub; eauto.
    }

  Admitted.



              Lemma step_decay_invariant:
                forall tp  (m : Mem.mem) i
                     (Hi : DTP.containsThread tp i) c m1 m1' c'
                     (Hinv: DryMachine.invariant tp)
                     (Hcompatible: DryMachine.mem_compatible tp m)
                     (Hrestrict_pmap :restrPermMap ((DryMachine.compat_th Hcompatible) Hi).1 = m1)
                     (Hdecay: decay m1 m1')
                     (Hcode: DTP.getThreadC Hi = Krun c),
                  DryMachine.invariant
                    (DTP.updThread Hi (Krun c')
                                   (getCurPerm m1', (DTP.getThreadR Hi).2)).
              Proof.
                intros.
                assert (CASES: forall b0 ofs0,
                           Mem.perm_order''
                             ((getCurPerm m1) !! b0 ofs0) ((getCurPerm m1') !! b0 ofs0) \/
                           ~ Mem.valid_block m b0).
                { move=> b ofs.
                  rewrite getCurPerm_correct getCurPerm_correct /permission_at /=.
                  destruct (Hdecay b ofs) as [_ VAL].
                  destruct (valid_block_dec m1 b); [left|right].
                  - move :( VAL v) => [] /(_ Cur).
                    move => [] -> -> //.
                    move => -> . apply po_refl.
                  - intros HH; apply n.
                    subst m1;
                    eapply restrPermMap_valid; eauto.
                }
                assert (m1_spec: forall b0 ofs0,
                           (getCurPerm m1) !! b0 ofs0 = (DTP.getThreadR Hi).1 !! b0 ofs0).
                { move=> b ofs.
                  subst m1.
                  rewrite getCurPerm_correct restrPermMap_Cur //. }

                apply updThread_inv.
                - assumption.
                - intros j cnt H; split;
                  apply permDisjoint_permMapsDisjoint=> b0 ofs0.
                  + destruct (CASES b0 ofs0) as [PO | NV].
                    * eapply permDisjointLT; eauto.
                      rewrite m1_spec.
                      apply permMapsDisjoint_permDisjoint.
                      inversion Hinv; apply no_race_thr; auto.
                    * move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
                      => [] /(_ j cnt) [] -> _ _.
                      apply permDisjoint_comm;
                        apply permDisjoint_None.
                  + apply permMapsDisjoint_permDisjoint.
                    inversion Hinv; apply no_race_thr; auto.
                - intros j cnt H.
                  inversion Hinv.
                  simpl. apply thread_data_lock_coh.
                - intros j cnt H b0 ofs0.
                  destruct (CASES b0 ofs0) as [PO | NV].
                  + eapply perm_coh_lower; [| apply po_refl | eauto].
                    rewrite m1_spec.
                    inversion Hinv.
                    apply thread_data_lock_coh.
                  + move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
                    => [] /(_ j cnt) [] _ -> _.
                    apply perm_coh_empty_1.
                - intros l pmap0 H; split;
                  apply permDisjoint_permMapsDisjoint=> b0 ofs0.
                  + destruct (CASES b0 ofs0) as [PO | NV].
                    * eapply permDisjoint_comm;
                      eapply permDisjointLT; eauto.
                      rewrite m1_spec.
                      apply permMapsDisjoint_permDisjoint.
                      inversion Hinv. eapply no_race; eauto.
                    * move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
                      => [] _ /(_ l pmap0 H) [] -> _.
                      apply permDisjoint_None.
                  + eapply permDisjoint_comm;
                    apply permMapsDisjoint_permDisjoint.
                    inversion Hinv; eapply no_race; eauto.
                - intros l pmap0 H; split=> b0 ofs0.
                  + inversion Hinv. eapply thread_data_lock_coh; eauto.
                  + destruct (CASES b0 ofs0) as [PO | NV].
                    * eapply perm_coh_lower; [| apply po_refl | eauto].
                      rewrite m1_spec.
                      inversion Hinv.
                      destruct (locks_data_lock_coh _ _ H).
                      eapply H0.
                    * move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
                      => [] _ /(_ l pmap0 H) [] _ -> .
                      apply perm_coh_empty_1.
                - move => b0 ofs0.
                  destruct (CASES b0 ofs0) as [PO | NV].
                    * eapply perm_coh_lower; [| apply po_refl | eauto].
                      rewrite m1_spec.
                      inversion Hinv.
                      destruct (thread_data_lock_coh i Hi).
                      eapply H.
                    * move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
                      => [] /(_ i Hi) [] _ -> _.
                      apply perm_coh_empty_1.

              Qed.

  Lemma core_diagram':
    forall (m : Mem.mem)  (U0 U U': schedule)
      (ds : dstate) (js js': jstate) rmap pmap
      (m' : Mem.mem) genv,
      match_st js ds ->
      DryMachine.invariant ds ->
      corestep (JMachineSem U0 rmap) genv (U,nil, js) m (U',nil, js') m' ->
      exists (ds' : dstate),
        DryMachine.invariant ds' /\
        match_st js' ds' /\
        corestep (DMachineSem U0 pmap) genv (U,nil, ds) m (U',nil, ds') m'.
          intros m U0 U U' ds js js' rmap pmap m' genv MATCH dinv.
          unfold JuicyMachine.MachineSemantics; simpl.
          unfold JuicyMachine.MachStep; simpl.
Proof.
          intros STEP;
            inversion STEP; subst.

*         (* start_step *)
          { inversion Htstep; subst.
            pose (ds':= (DTP.updThreadC (MTCH_cnt MATCH ctn) (Krun c_new))).
            exists ds'. split; [|split].
            - apply updThreadC_invariant. assumption.
            - apply MTCH_updt; assumption.
            - eapply (DryMachine.start_step tid) with (Htid0 := @MTCH_cnt js tid ds MATCH Htid).
              + assumption.
              + eapply MTCH_compat; eassumption.
              + { econstructor.
                  - eapply MTCH_getThreadC. eassumption. eassumption.
                  - eassumption.
                  - eassumption.
                  - reflexivity.
                }
          }

*          (* resume_step *)
          { inversion MATCH; subst.
            inversion Htstep; subst.
            exists (DTP.updThreadC (mtch_cnt _ ctn) (Krun c')).
            split;[|split].
            (*Invariant*)
            { apply updThreadC_invariant; assumption. }
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

*          (* core_step *)
          {
            inversion MATCH; subst.
            inversion Htstep; subst.
            assert (Htid':=mtch_cnt _ Htid).


            exists (DTP.updThread Htid'
                             (Krun c')
                             (permissions.getCurPerm (m_dry jm'),
              (DTP.getThreadR Htid').2
              (*JSEM.juice2Perm_locks (m_phi jm') m *) )).
            split ; [|split].
            {
              inversion Hcorestep.
              eapply ev_step_ax2 in H; destruct H as [T H].
              apply SEM.step_decay in H.

  eapply step_decay_invariant
  with (Hcompatible:= MTCH_compat _ _ _ MATCH Hcmpt); try eapply H; eauto.

  (*eapply DSEM.DryMachineLemmas.step_decay_invariant
              with (Hcompatible:= MTCH_compat _ _ _ MATCH Hcmpt); try eapply H; eauto. *)
  eapply MTCH_restrict_personal.
  auto.
  inversion MATCH. erewrite <- mtch_gtc0; eassumption.
  }
{
  apply MTCH_update.
  apply MTCH_age.
  assumption.
  - intros.
    assert (HH:= juicy_mem_access jm').
    rewrite <- HH.
    rewrite getCurPerm_correct.
    reflexivity.
  - intros.
    rewrite (MTCH_perm2' _ MATCH).
    (*is decay *)
    inversion Hcorestep.
    eapply ev_step_ax2 in H; destruct H as [T H].
    apply SEM.step_decay in H.
    { (*decay preserves lock permissions!!*)
      replace (MTCH_cnt' MATCH Htid') with Htid by apply proof_irrelevance.
      move: H0 => [] [] _ /(_ (b,ofs)) [] A B _.
      destruct B as [B| [B|B]].
      - rewrite - B; simpl.
        destruct ((JTP.getThreadR Htid @ (b, ofs))) eqn:HH;
          try rewrite HH; simpl; eauto.
      - destruct B as [rsh [Wsh [v [v' [B1 B2]]]] ].
        rewrite B2.
        simpl in B1.
        destruct (JSEM.ThreadPool.getThreadR Htid @ (b, ofs)) eqn:HH;
          try ( try destruct k; simpl in B1; inversion B1).
        rewrite HH; simpl; auto.
      - destruct B as [[M [v B]]|[v[pp [B1 B2]]]].
        + rewrite B; simpl.
          { (* address is not valid so it should be no... wiht mem compat.*)
            destruct Hcmpt as [jall Hcmpt].
            inversion Hcmpt.
            inversion all_cohere.

            symmetry.
            apply po_None1.
            eapply po_trans;
            [ |eapply perm_of_res_op2].
            replace None with (max_access_at m  (b, ofs)).
            eapply po_trans.
            eapply max_coh.
            eapply JMS.po_join_sub'.
            apply resource_at_join_sub.
            apply JMS.compatible_threadRes_sub; auto.
            apply nextblock_access_empty.
            apply M.
            }
        + rewrite B2 B1; auto. }
}
{  assert (Hcmpt': DryMachine.mem_compatible ds m) by
      (eapply MTCH_compat; eassumption).
   inversion Hcorestep.
   eapply ev_step_ax2 in H.
   destruct H as [T evSTEP].
    eapply DryMachine.thread_step; simpl.
   - eassumption.
   - econstructor; try eassumption.
      3: reflexivity.
     Focus 2. eapply (MTCH_getThreadC _ _ _ _ _ _ _ Hthread).
     instantiate(1:=Hcmpt').
     apply MTCH_restrict_personal.
     assumption.
}
  }

* (* suspend_step *)
inversion MATCH; subst.
  inversion Htstep; subst.
  exists (DTP.updThreadC (mtch_cnt _ ctn) (Kblocked c)).
  split;[|split].
  (*Invariant*)
  { apply updThreadC_invariant ; assumption. }
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

*  (*Conc step*)
  {
    destruct (conc_step_diagram m m' U js js' ds tid genv ev MATCH dinv Htid Hcmpt HschedN Htstep)
      as [ds' [ev' [dinv' [MTCH' step']]]]; eauto.
    exists ds'; split; [| split]; try assumption.
    econstructor 5; simpl; try eassumption.
    reflexivity.
  }

*  (* step_halted *)
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


*  (* schedfail *)
  { exists ds.
    split;[|split]; try eassumption.
    econstructor 7; try eassumption; try reflexivity.
    unfold not; simpl; intros.
    apply Htid. inversion MATCH; apply mtch_cnt'; assumption. }

  Grab Existential Variables.
  - simpl. apply mtch_cnt. assumption.
  - assumption.
  Qed.

  Lemma core_diagram:
    forall (m : Mem.mem)  (U0 U U': schedule) rmap pmap
      (ds : dstate) (js js': jstate)
      (m' : Mem.mem) genv,
      corestep (JMachineSem U0 rmap) genv (U,nil, js) m (U',nil, js') m' ->
      match_st js ds ->
      DryMachine.invariant ds ->
      exists (ds' : dstate),
        DryMachine.invariant ds' /\
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
