
(** Erasure Proof *)

(** This file contains the proof of erasure between 
    juicy and dry programs
 *)



(** *Imports*)

(* This file uses Proof Irrelevance: 
   forall (P : Prop) (p1 p2 : P), p1 = p2. *)
Require Import ProofIrrelevance.

(* CompCert imports *)
Require Import compcert.common.Memory.

(* VST imports *)
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(* Concurrency Imports *)
Require Import VST.concurrency.common.threadPool. Import addressFiniteMap.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.sync_preds.
(*The semantics*)
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.common.ClightMachine.
(*Erasure specification*)
Require Import VST.concurrency.juicy.erasure_signature.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.common.ssromega. (*omega in ssrnat *)
From mathcomp.ssreflect Require Import ssreflect seq.

Set Bullet Behavior "Strict Subproofs".

Module Parching <: ErasureSig.
  Import THE_JUICY_MACHINE.
  Import Clight_newMachine.
  Import DMS.
  Import ThreadPoolWF.

  Section Parching.

  Context (ge : genv).

  Instance Sem : Semantics := ClightSemanticsForMachines.Clight_newSem ge.

  Instance JR : Resources := LocksAndResources.
  Instance JTP : ThreadPool.ThreadPool := OrdinalPool.OrdinalThreadPool.
  Instance JMS : MachineSig := Concur.JuicyMachineShell.
  Instance DilMem : DiluteMem := HybridMachineSig.HybridCoarseMachine.DilMem.
  Instance scheduler : Scheduler := HybridCoarseMachine.scheduler.
  Instance JuicyMachine : HybridMachine := HybridCoarseMachine.HybridCoarseMachine.
  Definition jstate := jstate ge.

  Instance DR : Resources := DryHybridMachine.dryResources.
  Instance DTP : ThreadPool.ThreadPool := OrdinalPool.OrdinalThreadPool.
  Instance DMS : MachineSig := DryHybridMachine.DryHybridMachineSig.
  Instance DryMachine : HybridMachine := HybridCoarseMachine.HybridCoarseMachine.
  Definition dstate := ThreadPool.t
                         (ThreadPool := OrdinalPool.OrdinalThreadPool)
                         (*
                         @t dryResources DSem (@OrdinalPool.OrdinalThreadPool dryResources DSem)
                          *).
                         
  Definition dmachine_state:= MachState(ThreadPool := OrdinalPool.OrdinalThreadPool).

  Import event_semantics threadPool.ThreadPool.

  (** * Match relation between juicy and dry state : *)
  (* 1-2. Same threads are contained in each state:
     3.   Threads have the same c
     4-5.   Threads have the same permissions up to erasure
     6.   the locks are in the same addresses.
     7-8-9. Lock contents match up to erasure. *)
  Inductive match_st' : jstate ->  dstate -> Prop:=
    MATCH_ST: forall (js:jstate) (ds:dstate)
                (mtch_cnt: forall {tid},  containsThread js tid -> containsThread ds tid )
                (mtch_cnt': forall {tid}, containsThread ds tid -> containsThread js tid )
                (mtch_gtc: forall {tid} (Htid:containsThread js tid)(Htid':containsThread ds tid),
                    getThreadC Htid = getThreadC Htid' )
                (mtch_perm1: forall b ofs {tid} (Htid:containsThread js tid)(Htid':containsThread ds tid),
                    juicy_mem.perm_of_res (resource_at (getThreadR Htid) (b, ofs)) =
                    ((getThreadR Htid').1 !! b) ofs )
                (mtch_perm2: forall b ofs {tid} (Htid:containsThread js tid)(Htid':containsThread ds tid),
                    juicy_mem.perm_of_res_lock (resource_at (getThreadR Htid) (b, ofs)) =
                    ((getThreadR Htid').2 !! b) ofs )
                (mtch_locks: forall a,
                    ssrbool.isSome (lockRes js a) = ssrbool.isSome (lockRes ds a))
                (mtch_locksEmpty: forall lock dres,
                    lockRes js lock = Some (None) ->
                    lockRes ds lock = Some dres ->
                   dres = (empty_map, empty_map))
                (mtch_locksRes: forall lock jres dres,
                    lockRes js lock = Some (Some jres) ->
                    lockRes ds lock = Some dres ->
                     forall b ofs,
                       juicy_mem.perm_of_res (resource_at jres (b, ofs)) = (dres.1 !! b) ofs )
                (mtch_locksRes: forall lock jres dres,
                    lockRes js lock = Some (Some jres) ->
                    lockRes ds lock = Some dres ->
                     forall b ofs,
                    juicy_mem.perm_of_res_lock (resource_at jres (b, ofs)) = (dres.2 !! b) ofs )
                (*mtch_locks: AMap.map (fun _ => tt) (lockGuts js) = lockGuts ds*),
      match_st' js ds.
  Definition match_st:= match_st'.


  (** *Match lemmas*)
  Lemma MTCH_cnt: forall {js tid ds},
           match_st js ds ->
           containsThread js tid -> containsThread ds tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt. Qed.
  
  Lemma MTCH_cnt': forall {js tid ds},
           match_st js ds ->
           containsThread ds tid -> containsThread js tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt'. Qed.

  Lemma MTCH_perm: forall {js ds i},
      forall (cnt: containsThread js i)
      (MTCH: match_st js ds),
      forall b ofs,
        juicy_mem.perm_of_res ((getThreadR cnt) @ (b, ofs)) = ((getThreadR (MTCH_cnt MTCH cnt)).1 !! b) ofs.
  Proof. intros ? ? ? ? MTCH ? ?. inversion MTCH. apply mtch_perm1. Qed.

  Lemma MTCH_perm2: forall {js ds i},
      forall (cnt: containsThread js i)
      (MTCH: match_st js ds),
      forall b ofs,
        juicy_mem.perm_of_res_lock  ((getThreadR cnt) @ (b, ofs)) = ((getThreadR (MTCH_cnt MTCH cnt)).2 !! b) ofs.
  Proof. intros. inversion MTCH. apply mtch_perm2. Qed.

  Lemma MTCH_perm': forall {js ds i},
      forall (cnt: containsThread ds i)
      (MTCH: match_st js ds),
      forall b ofs,
        ((getThreadR cnt).1 !! b) ofs =
        juicy_mem.perm_of_res ((getThreadR (MTCH_cnt' MTCH cnt)) @ (b, ofs)).
  Proof. intros. inversion MTCH. symmetry. apply mtch_perm1; eauto. Qed.

  Lemma MTCH_perm2': forall {js ds i},
      forall (cnt: containsThread ds i)
      (MTCH: match_st js ds),
      forall b ofs,
        ((getThreadR cnt).2 !! b) ofs =
        juicy_mem.perm_of_res_lock ((getThreadR (MTCH_cnt' MTCH cnt)) @ (b, ofs)).
  Proof. intros. inversion MTCH. symmetry; apply mtch_perm2. Qed.

  Lemma cnt_irr: forall tid (ds : dstate) (cnt1 cnt2: containsThread ds tid),
      getThreadC cnt1 = getThreadC cnt2.
  Proof. intros.
         unfold getThreadC.
         destruct ds; simpl.
         f_equal; f_equal.
         eapply proof_irrelevance.
  Qed.

  Lemma MTCH_locks: forall ds js laddr rmap,
      match_st js ds ->
      lockRes ds laddr = Some rmap ->
      exists x, lockRes js laddr = Some x.
  Proof.
    move=> ? js laddr ? MTCH HH.
    destruct (lockRes js laddr) eqn:AA.
    - exists l; reflexivity.
    - inversion MTCH.
      specialize (mtch_locks laddr).
      rewrite HH AA in mtch_locks; inversion mtch_locks.
  Qed.

  Lemma MTCH_getThreadC: forall js ds tid c,
      forall (cnt: containsThread js tid)
        (cnt': containsThread ds tid)
        (M: match_st js ds),
        getThreadC cnt =  c ->
        getThreadC cnt'  =  c.
  Proof. intros ? ? ? ? ? MTCH; inversion MTCH; subst.
         intros HH; inversion HH; subst.
         intros AA; rewrite <- AA. symmetry; apply mtch_gtc.
  Qed.

  Lemma MTCH_lockSet: forall js ds,
      match_st js ds ->
      forall b ofs, (lockSet js) !! b ofs = (lockSet ds) !! b ofs.
  Proof.
    intros js ds MATCH b ofs.
    inversion MATCH. clear - mtch_locks.
    destruct (OrdinalPool.lockRes_range_dec ds b ofs).
    - destruct e as [z [ineq dLR]].
      specialize (mtch_locks (b, z)).
      destruct ( lockRes ds (b, z)) eqn:AA; inversion dLR.
      destruct (lockRes js (b, z)) eqn:BB; inversion mtch_locks.
      erewrite lockSet_spec_2; eauto.
      erewrite lockSet_spec_2; eauto.
      rewrite BB; constructor.
      setoid_rewrite AA in dLR; inversion dLR.
    - destruct (OrdinalPool.lockRes_range_dec js b ofs).
      + clear e.
        destruct e0 as [z [ineq dLR]].
        specialize (mtch_locks (b, z)).
        destruct (lockRes js (b, z)) eqn:AA; inversion dLR.
        * destruct ( lockRes ds (b, z)) eqn:BB; inversion mtch_locks.
          erewrite lockSet_spec_2; eauto.
          erewrite lockSet_spec_2; eauto.
          rewrite BB; constructor.
        * setoid_rewrite AA in dLR; inversion dLR.
      + erewrite lockSet_spec_3; eauto.
        erewrite lockSet_spec_3; eauto.
  Qed.

  Lemma MTCH_compat: forall js ds m,
      match_st js ds ->
      mem_compatible js m ->
      mem_compatible ds m.
  Proof.
    intros ? ? ? MTCH mc.
    inversion MTCH; subst.
    constructor.
    - intros tid cnt.
      assert (th_coh:= Concur.thread_mem_compatible mc).
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
      assert(HH: exists jres, lockRes js l = Some jres).
      { specialize (mtch_locks  l); rewrite H in mtch_locks.
      destruct (lockRes js l); try solve[inversion mtch_locks].
      exists l0; reflexivity. }
      destruct HH as [jres HH].
      destruct jres.
      + specialize (mtch_locksRes _ _ _ HH H).
        specialize (mtch_locksRes0 _ _ _ HH H).
        split; intros b ofs.
        * rewrite <- mtch_locksRes.
          eapply Concur.compat_lockLT; eauto.
          apply mc.
        * rewrite <- mtch_locksRes0.
          eapply po_trans.
          eapply Concur.compat_lockLT'; eauto.
          { apply mc. }
          eapply perm_of_res_op2.
      + specialize (mtch_locksEmpty _ _ HH H).
        rewrite mtch_locksEmpty.
        split; apply empty_LT.
   (* - intros b ofs.
      rewrite <- (MTCH_lockSet _ _ MTCH).
      apply compat_lt_m; assumption.*)
    - intros l rmap0 H.
      destruct (valid_block_dec m l.1); try assumption.
      eapply m with (ofs:=l.2) (k:=Max) in n.
      specialize (mtch_locks l).
      rewrite H in mtch_locks.
      destruct (lockRes js l) eqn:lock_in_l; try solve[inversion mtch_locks]; clear mtch_locks.
      destruct mc as [all_juice mc']; destruct mc'.
      move lset_in_juice at bottom.
      specialize (lset_in_juice l).
      setoid_rewrite lock_in_l in lset_in_juice. simpl in lset_in_juice.
      assert (HH:true) by auto; apply lset_in_juice in HH.
      destruct HH as [sh HH].
      destruct all_cohere.
      specialize (max_coh l).
      specialize (HH 0). spec HH. pose proof LKSIZE_pos; omega. destruct HH as [sh' [psh' [P [? HH]]]].
      rewrite fst_snd0 in HH.
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
      (cnt: containsThread js tid)
      (cnt': containsThread ds tid),
      match_st (updThreadC cnt c)
               (updThreadC cnt' c).
  Proof.
    intros. constructor; intros.
    - apply cntUpdateC.
      inversion H0; subst.
      apply mtch_cnt.
      eapply cntUpdateC'; apply H.
    - apply cntUpdateC.
      inversion H0; subst.
      apply mtch_cnt'.
        eapply cntUpdateC'; apply H.
    - destruct (eq_dec tid tid0) as [e|ine].
      + subst.
          rewrite gssThreadCC;
          rewrite gssThreadCC.
          reflexivity.
      + assert (cnt2:= cntUpdateC' _ _ Htid).
        rewrite <- (gsoThreadCC ine _ cnt2) by assumption.
        inversion H0; subst.
          (* pose (cnt':=(@MTCH_cnt js tid ds H0 cnt)). *)
          assert (cnt2':= cntUpdateC' _ _ Htid').
          (*fold cnt';*)
          rewrite <- (gsoThreadCC ine _ cnt2') by assumption.
          apply mtch_gtc; assumption.
    - inversion H0; apply mtch_perm1.
    - inversion H0; apply mtch_perm2.
    - inversion H0; apply mtch_locks.
    - rewrite gsoThreadCLPool in H; rewrite gsoThreadCLPool in H1.
      inversion H0; eapply mtch_locksEmpty; eauto.
    - rewrite gsoThreadCLPool in H; rewrite gsoThreadCLPool in H1.
      inversion H0; eapply mtch_locksRes; eauto.
    - rewrite gsoThreadCLPool in H; rewrite gsoThreadCLPool in H1.
      inversion H0; eapply mtch_locksRes0; eauto.
  Qed.

  Lemma MTCH_updt':
    forall js ds tid c m
      (H0:match_st js ds)
      (cnt: containsThread js tid)
      (cnt': containsThread ds tid)
      (Hcmpt : mem_compatible js m)
      (Hcmpt' : HybridMachineSig.mem_compatible ds m),
      match_st (updThread cnt c (add_block Hcmpt cnt (Concur.install_perm Hcmpt cnt)))
               (updThread cnt' c (HybridMachineSig.add_block Hcmpt' cnt' (Concur.install_perm Hcmpt cnt))).
  Proof.
    intros. constructor; intros.
    - apply cntUpdate.
      inversion H0; subst.
      apply mtch_cnt.
      eapply cntUpdate'; apply H.
    - apply cntUpdate.
      inversion H0; subst.
      apply mtch_cnt'.
        eapply cntUpdate'; apply H.
    - destruct (eq_dec tid tid0) as [e|ine].
      + subst.
          rewrite gssThreadCode;
          rewrite gssThreadCode.
          reflexivity.
      + assert (cnt2:= cntUpdate' _ _ _ Htid).
        rewrite (gsoThreadCode ine _ cnt2).
        inversion H0; subst.
          (* pose (cnt':=(@MTCH_cnt js tid ds H0 cnt)). *)
          assert (cnt2':= cntUpdate' _ _ _ Htid').
          (*fold cnt';*)
          rewrite (gsoThreadCode ine _ cnt2').
          apply mtch_gtc; assumption.
    - inversion H0.
      destruct (eq_dec tid tid0); [|rewrite !gsoThreadRes; auto].
      subst.
      rewrite !gssThreadRes.
      simpl.
      unfold Concur.add_block, Concur.install_perm.
      rewrite getCurPerm_correct.
      unfold permission_at.
      pose proof Concur.juicyRestrictCurEq (Concur.max_acc_coh_acc_coh (Concur.max_coh (Concur.thread_mem_compatible Hcmpt cnt)))
        (b, ofs); auto.
    - inversion H0.
      destruct (eq_dec tid tid0); [|rewrite !gsoThreadRes; auto].
      subst.
      rewrite !gssThreadRes.
      apply mtch_perm2.
    - inversion H0; apply mtch_locks.
    - rewrite gsoThreadLPool in H; rewrite gsoThreadLPool in H1.
      inversion H0; eapply mtch_locksEmpty; eauto.
    - rewrite gsoThreadLPool in H; rewrite gsoThreadLPool in H1.
      inversion H0; eapply mtch_locksRes; eauto.
    - rewrite gsoThreadLPool in H; rewrite gsoThreadLPool in H1.
      inversion H0; eapply mtch_locksRes0; eauto.
  Qed.

    Lemma MTCH_restrict_personal:
      forall ds js m i
        (MTCH: match_st js ds)
        (Hi: containsThread js i)
        (Hi': containsThread ds i)
        Hcmpt
        (Hcmpt': DryHybridMachine.mem_compatible ds m),
        restrPermMap (DryHybridMachine.compat_th _ _ Hcmpt' Hi').1 =
        m_dry (@Concur.personal_mem m (@getThreadR _ _ _ i js Hi) Hcmpt).
    Proof.
      intros.
      inversion MTCH; subst.
      unfold Concur.personal_mem; simpl; unfold Concur.juicyRestrict; simpl.
      apply restrPermMap_ext; intros.
      extensionality ofs;
      setoid_rewrite <- mtch_perm1.
      instantiate(1:=Hi).
      erewrite Concur.juic2Perm_correct. reflexivity.
      apply Concur.acc_coh; assumption.
    Qed.

(*    Lemma MTCH_halted:
      forall ds js i
        (cnt: containsThread  js i)
        (cnt': containsThread  ds i),
        match_st js ds->
        threadHalted cnt ->
        invariant ds ->
        threadHalted cnt'.
    Proof.
      intros.
      inversion H0; subst.
      econstructor.
     (* - assumption.*)
      - inversion H; subst. erewrite <- mtch_gtc. eassumption.
      - apply Hcant.
    Qed.*)

    Lemma MTCH_updLockS:
             forall js ds loc jres dres1 dres2,
               match_st js ds ->
             (forall b ofs, perm_of_res (jres @ (b, ofs)) = dres1 !! b ofs) ->
             (forall b ofs, perm_of_res_lock (jres @ (b, ofs)) = dres2 !! b ofs) ->
                      match_st
                        (updLockSet js loc (Some jres))
                        (updLockSet ds loc (dres1,dres2)).
    Proof. intros.
           constructor.
           + intros. apply cntUpdateL.
             destruct H; apply mtch_cnt.
             apply cntUpdateL' in H2; assumption.
           + intros. apply cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply cntUpdateL' in H2; assumption.
           + intros. rewrite gLockSetCode gLockSetCode.
             inversion H; subst. apply mtch_gtc.
           + intros. rewrite gLockSetRes gLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite gLockSetRes gLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite gsslockResUpdLock gsslockResUpdLock.
               reflexivity.
             * rewrite gsolockResUpdLock.
               rewrite gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
               assumption.
               assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite gsslockResUpdLock in H2; inversion H2.
             * rewrite gsolockResUpdLock in H2. rewrite gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksEmpty; eassumption.
               assumption. assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite gsslockResUpdLock in H2.
               rewrite gsslockResUpdLock in H3.
               inversion H2; inversion H3; subst.
               apply H0.
             * rewrite gsolockResUpdLock in H2. rewrite gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksRes; eassumption.
               assumption.
               assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite gsslockResUpdLock in H2.
               rewrite gsslockResUpdLock in H3.
               inversion H2; inversion H3; subst.
               apply H1.
             * rewrite gsolockResUpdLock in H2. rewrite gsolockResUpdLock in H3.
               inversion H. eapply mtch_locksRes0; eassumption.
               assumption.
               assumption.
    Qed.

    Lemma MTCH_updLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (updLockSet js loc None)
          (updLockSet ds loc (empty_map,empty_map)).
           intros.
           constructor.
           + intros. apply cntUpdateL.
             destruct H; apply mtch_cnt.
             apply cntUpdateL' in H0; assumption.
           + intros. apply cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply cntUpdateL' in H0; assumption.
           + intros. rewrite gLockSetCode gLockSetCode.
             inversion H; subst. apply mtch_gtc.
           + intros. rewrite gLockSetRes gLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite gLockSetRes gLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite gsslockResUpdLock gsslockResUpdLock.
               reflexivity.
             * rewrite gsolockResUpdLock.
               rewrite gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
               assumption. assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite gsslockResUpdLock in H1; inversion H1; reflexivity.
             * rewrite gsolockResUpdLock in H1.
               rewrite gsolockResUpdLock in H0.
               inversion H. eapply mtch_locksEmpty; eassumption.
               assumption.
               assumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite gsslockResUpdLock in H0.
               rewrite gsslockResUpdLock in H1.
               inversion H0.
             * rewrite gsolockResUpdLock in H0. 2: assumption.
               rewrite gsolockResUpdLock in H1. 2: assumption.
               inversion H. eapply mtch_locksRes; eassumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite gsslockResUpdLock in H0.
               rewrite gsslockResUpdLock in H1.
               inversion H0.
             * rewrite gsolockResUpdLock in H0. 2: assumption.
               rewrite gsolockResUpdLock in H1. 2: assumption.
               inversion H. eapply mtch_locksRes0; eassumption.
    Qed.

    Lemma MTCH_remLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (remLockSet js loc)
          (remLockSet ds loc).
           intros.
           constructor.
           + intros. apply cntRemoveL.
             destruct H; apply mtch_cnt.
             apply cntRemoveL' in H0; assumption.
           + intros. apply cntRemoveL.
             destruct H; apply mtch_cnt'.
             apply cntRemoveL' in H0; assumption.
           + intros. rewrite gRemLockSetCode gRemLockSetCode.
             inversion H; subst. apply mtch_gtc.
           + intros. rewrite gRemLockSetRes  gRemLockSetRes.
             inversion H; subst. apply mtch_perm1.
           + intros. rewrite gRemLockSetRes  gRemLockSetRes.
             inversion H; subst. apply mtch_perm2.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite gsslockResRemLock gsslockResRemLock.
               reflexivity.
             * rewrite gsolockResRemLock.
               2: exact NEQ.
               rewrite gsolockResRemLock.
               2: exact NEQ.
               inversion H. solve[apply mtch_locks].
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite gsslockResRemLock in H1; inversion H1; reflexivity.
             * rewrite gsolockResRemLock in H1.
               2: exact NEQ.
               rewrite gsolockResRemLock in H0.
               2: exact NEQ.
               inversion H. eapply mtch_locksEmpty; eassumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite gsslockResRemLock in H0.
               rewrite gsslockResRemLock in H1.
               inversion H0.
             * rewrite gsolockResRemLock in H0.
               2: exact NEQ.
               rewrite gsolockResRemLock in H1.
               2: exact NEQ.
               inversion H. eapply mtch_locksRes; eassumption.
           + intros.
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite gsslockResRemLock in H0.
               rewrite gsslockResRemLock in H1.
               inversion H0.
             * rewrite gsolockResRemLock in H0.
               2: exact NEQ.
               rewrite gsolockResRemLock in H1.
               2: exact NEQ.
               inversion H. eapply mtch_locksRes0; eassumption.
    Qed.

    Lemma MTCH_update:
      forall js ds Kc phi p1 p2 i
        (Hi : containsThread js i)
        (Hi': containsThread ds i),
        match_st js ds ->
        ( forall b ofs,
            perm_of_res (phi @ (b, ofs)) = p1 !! b ofs) ->
        ( forall b ofs,
            perm_of_res_lock (phi @ (b, ofs)) = p2 !! b ofs) ->
        match_st (updThread Hi  Kc phi)
                 (updThread Hi' Kc (p1,p2)).
    Proof.
      intros. inversion H; subst.
      constructor; intros.
      - apply cntUpdate. apply mtch_cnt.
        eapply cntUpdate'; eassumption.
      - apply cntUpdate. apply mtch_cnt'.
        eapply cntUpdate'; eassumption.
      - destruct (eq_dec i tid).
        + subst.
          rewrite gssThreadCode gssThreadCode; reflexivity.
        + assert (jcnt2:= @cntUpdateC' _ _ _ _ _ _ Kc Hi Htid).
          assert (dcnt2:= @cntUpdateC' _ _ _ _ _ _ Kc Hi' Htid').
          rewrite (gsoThreadCode n _ jcnt2); auto.
          rewrite (gsoThreadCode n _ dcnt2); auto.
      - destruct (eq_dec i tid).
        + subst.
          rewrite (gssThreadRes _ _ _ Htid); auto.
          rewrite (gssThreadRes _ _ _ Htid'); auto.
        + assert (jcnt2:= @cntUpdateC' _ _ _ _ _ _ Kc Hi Htid).
          assert (dcnt2:= @cntUpdateC' _ _ _ _ _ _ Kc Hi' Htid').
          rewrite (gsoThreadRes _ jcnt2); auto.
          rewrite (gsoThreadRes _ dcnt2); auto.
      - destruct (eq_dec i tid).
        + subst.
          rewrite (gssThreadRes _ _ _ Htid); auto.
          rewrite (gssThreadRes _ _ _ Htid'); simpl; auto.
        + assert (jcnt2:= @cntUpdateC' _ _ _ _ _ _ Kc Hi Htid).
          assert (dcnt2:= @cntUpdateC' _ _ _ _ _ _ Kc Hi' Htid').
          rewrite (gsoThreadRes _ jcnt2); auto.
          rewrite (gsoThreadRes _ dcnt2); auto.
      - simpl;  apply mtch_locks.
      - rewrite gsoThreadLPool in H2; rewrite gsoThreadLPool in H3.
        eapply mtch_locksEmpty; eassumption.
      - rewrite gsoThreadLPool in H2; rewrite gsoThreadLPool in H3.
        eapply mtch_locksRes; eassumption.
      - rewrite gsoThreadLPool in H2; rewrite gsoThreadLPool in H3.
        eapply mtch_locksRes0; eassumption.
    Qed.

    Lemma match_st_age_tp_to tp n ds :
      match_st tp ds -> match_st (Concur.age_tp_to n tp) ds.
    Proof.
      intros M.
      inversion M as [? ? A B C D E F G H I J]; subst.
      constructor; intros.
      - now apply A; (eapply Concur.cnt_age, H0).
      - apply Concur.cnt_age', B; auto.
      - now erewrite <-Concur.gtc_age; eauto.
      - erewrite <-D.
        erewrite <-Concur.getThreadR_age; eauto.
        erewrite Concur.perm_of_age.
        reflexivity.
      - erewrite <- E.
        erewrite <-Concur.getThreadR_age; eauto.
        erewrite Concur.perm_of_age_lock.
        reflexivity.
      - erewrite <-F.
        apply Concur.LockRes_age.
      - unshelve eapply G with (lock := lock); auto.
        simpl in *.
        unfold OrdinalPool.lockRes, OrdinalPool.lockGuts in *.
        rewrite lset_age_tp_to in H0.
        rewrite AMap_find_map_option_map in H0.
        simpl in *.
        destruct (AMap.find (elt:=option rmap) lock (OrdinalPool.lset tp))
          as [[o|]|]; simpl in *; congruence.
      - simpl in *.
        specialize (H lock).
        unfold OrdinalPool.lockRes in *.
        unfold OrdinalPool.lockGuts in *.
        rewrite lset_age_tp_to in H0.
        simpl in *.
        rewrite AMap_find_map_option_map in H0.
        destruct (AMap.find (elt:=option rmap) lock (OrdinalPool.lset tp))
          as [[o|]|]; simpl in *; try congruence.
        specialize (H o dres Logic.eq_refl ltac:(assumption)).
        rewrite <-H.
        injection H0 as <-.
        apply Concur.perm_of_age.
        (* again aging lset. *)
      - simpl in *.
        specialize (I lock).
        unfold OrdinalPool.lockRes in *.
        unfold OrdinalPool.lockGuts in *.
        rewrite lset_age_tp_to in H0.
        simpl in *.
        rewrite AMap_find_map_option_map in H0.
        destruct (AMap.find (elt:=option rmap) lock (OrdinalPool.lset tp))
          as [[o|]|]; simpl in *; try congruence.
        specialize (I o dres Logic.eq_refl ltac:(assumption)).
        rewrite <-I.
        injection H0 as <-.
        apply Concur.perm_of_age_lock.
        (* again aging lset. *)
        Unshelve. auto. auto. auto.
    Qed.

    Definition match_rmap_perm (rmap : rmap) (pmap: access_map * access_map): Prop:=
      (forall b ofs, perm_of_res (rmap @ (b, ofs)) = pmap.1 !! b ofs) /\
               pmap.2 = empty_map.

     Definition no_locks_perm (rmap : rmap): Prop:=
      forall b ofs, perm_of_res_lock (rmap @ (b, ofs)) = None.

    Lemma MTCH_initial:
      forall  c rmap pmap,
        match_rmap_perm rmap pmap ->
        no_locks_perm rmap ->
        match_st (Concur.initial_machine rmap c) (DryHybridMachine.initial_machine (*genv*) pmap.1 c).
    Proof.
      intros.
      constructor.
      - intro i. unfold containsThread, Concur.initial_machine; simpl.
        unfold containsThread, DryHybridMachine.initial_machine; simpl.
        trivial.
      - intro i. unfold containsThread, Concur.initial_machine; simpl.
        unfold containsThread, DryHybridMachine.initial_machine; simpl.
        trivial.
      - reflexivity.
      - intros.
        unfold getThreadR; unfold Concur.initial_machine; simpl.
        unfold getThreadR; unfold DryHybridMachine.initial_machine; simpl.
        unfold match_rmap_perm in H. apply H.
      - intros.
        unfold getThreadR; unfold Concur.initial_machine; simpl.
        rewrite empty_map_spec; apply H0.
      - unfold empty_rmap, "@"; simpl.
        reflexivity.
      - unfold lockRes, DryHybridMachine.initial_machine; simpl.
        intros. setoid_rewrite OrdinalPool.find_empty in H2; inversion H2.
      - unfold lockRes, DryHybridMachine.initial_machine; simpl.
        intros. setoid_rewrite OrdinalPool.find_empty in H2; inversion H2.
      - unfold lockRes, DryHybridMachine.initial_machine; simpl.
        intros. setoid_rewrite OrdinalPool.find_empty in H2; inversion H2.
    Qed.

    Lemma contains_iff_num:
      forall (js : jstate) (ds : dstate)
        (Hcnt: forall i, containsThread js i <-> containsThread ds i),
        OrdinalPool.num_threads js = OrdinalPool.num_threads ds.
    Proof.
      intros.
      simpl in *.
      unfold OrdinalPool.containsThread in *.
      remember (OrdinalPool.num_threads js).
      remember (OrdinalPool.num_threads ds).
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
        latestThread js = latestThread ds.
    Proof.
      intros js ds MATCH.
      simpl.
      unfold OrdinalPool.latestThread.
      erewrite contains_iff_num.
      - reflexivity.
      - split; generalize i; inversion MATCH; assumption.
    Qed.

    Lemma MTCH_addThread: forall js ds parg arg phi res lres,
        match_st js ds ->
        (forall b0 ofs0, perm_of_res (phi@(b0, ofs0)) = res !! b0 ofs0) ->
        (forall b0 ofs0, perm_of_res_lock (phi@(b0, ofs0)) = lres !! b0 ofs0) ->
        match_st
          (addThread js parg arg phi)
          (addThread ds parg arg (res,lres)).
    Proof.
      intros ? ? ? ? ? ? ? MATCH DISJ. constructor.
      - intros tid HH.
        apply cntAdd' in HH. destruct HH as [[HH ineq] | HH].
        + apply cntAdd. inversion MATCH. apply mtch_cnt. assumption.
        +
          erewrite MTCH_latestThread in HH.
          rewrite HH.
          apply OrdinalPool.contains_add_latest.
          assumption.
      - intros tid HH.
        apply cntAdd' in HH. destruct HH as [[HH ineq] | HH].
        + apply cntAdd. inversion MATCH. eapply  mtch_cnt'; assumption.
        + erewrite <- MTCH_latestThread in HH.
          rewrite HH.
          apply OrdinalPool.contains_add_latest.
          assumption.
      - intros.
        destruct (cntAdd' _ _ _ Htid) as [[jcnt jNLast]| jLast];
          destruct (cntAdd' _ _ _ Htid') as [[dcnt dNLast]| dLast].
        * erewrite !gsoAddCode; try eassumption.
          inversion MATCH. eapply mtch_gtc.
        * contradict jNLast.
          rewrite <- (MTCH_latestThread js ds) in dLast.
          rewrite dLast; reflexivity.
          assumption.
        * contradict dNLast.
          rewrite (MTCH_latestThread js ds) in jLast.
          rewrite jLast; reflexivity.
          assumption.
        * erewrite !gssAddCode; try eassumption.
          reflexivity.
      - intros.
        destruct (cntAdd' _ _ _ Htid) as [[jcnt jNLast]| jLast];
          destruct (cntAdd' _ _ _ Htid') as [[dcnt dNLast]| dLast].
        * erewrite !gsoAddRes; try eassumption.
          inversion MATCH. eapply mtch_perm1.
        * contradict jNLast.
          rewrite <- (MTCH_latestThread js ds) in dLast.
          rewrite dLast; reflexivity.
          assumption.
        * contradict dNLast.
          rewrite (MTCH_latestThread js ds) in jLast.
          rewrite jLast; reflexivity.
          assumption.
        * erewrite !gssAddRes; try eassumption.
          apply DISJ.
      - intros.
        destruct (cntAdd' _ _ _ Htid) as [[jcnt jNLast]| jLast];
          destruct (cntAdd' _ _ _ Htid') as [[dcnt dNLast]| dLast].
        * erewrite !gsoAddRes; try eassumption.
          inversion MATCH. eapply mtch_perm2.
        * contradict jNLast.
          rewrite <- (MTCH_latestThread js ds) in dLast.
          rewrite dLast; reflexivity.
          assumption.
        * contradict dNLast.
          rewrite (MTCH_latestThread js ds) in jLast.
          rewrite jLast; reflexivity.
          assumption.
        * erewrite !gssAddRes; try eassumption.
          simpl; apply H.
      - intros. rewrite gsoAddLPool gsoAddLPool.
        inversion MATCH. apply mtch_locks.
      - intros lock dres.
        rewrite gsoAddLPool gsoAddLPool.
        inversion MATCH. apply mtch_locksEmpty.
      - intros lock jres dres .
        rewrite gsoAddLPool gsoAddLPool.
        inversion MATCH. apply mtch_locksRes.
      - intros lock jres dres .
        rewrite gsoAddLPool gsoAddLPool.
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
        match_st (Concur.age_tp_to age js) ds.
    Proof.
      intros js ds age MATCH; inversion MATCH. constructor.
      -
        intros i HH. apply Concur.cnt_age in HH.
        apply mtch_cnt; assumption.
      - intros i HH. apply @Concur.cnt_age'.
        apply mtch_cnt'; assumption.
      - intros i cnt cnt'.
        simpl; setoid_rewrite <- Concur.gtc_age.
        eapply mtch_gtc.
      - intros.
        setoid_rewrite <- Concur.getThreadR_age. simpl.
        rewrite Concur.perm_of_age.
        apply mtch_perm1.
      - intros.
        erewrite <- Concur.getThreadR_age. simpl.
        rewrite Concur.perm_of_age_lock.
        apply mtch_perm2.
      - intros.
        rewrite Concur.LockRes_age. apply mtch_locks.
      - intros.

        apply Concur.LockRes_age_content1 in H1.
        eapply mtch_locksEmpty; eassumption.
      -
        intros. apply Concur.LockRes_age_content2 in H1.
        destruct H1 as [r [AA BB]].
        rewrite BB.
        rewrite Concur.perm_of_age.
        eapply mtch_locksRes; eassumption.
      -
        intros. apply Concur.LockRes_age_content2 in H1.
        destruct H1 as [r [AA BB]].
        rewrite BB.
        rewrite Concur.perm_of_age_lock.
        eapply mtch_locksRes0; eassumption.

        Grab Existential Variables.
        eapply Concur.cnt_age; eassumption.
        eapply Concur.cnt_age; eassumption.
        eapply Concur.cnt_age; eassumption.
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
        assert (containsThread js i) as cnt0 by (apply Hcnt; auto).
        specialize (Hget _ cnt0) as [Hget _].
        replace (proj2 _ _) with cnt in Hget by apply proof_irr.
        rewrite <- Hget; auto.
      - intros.
        assert (containsThread js tid) as cnt0 by (apply Hcnt; auto).
        specialize (Hget _ cnt0) as (_ & _ & Hget).
        replace (proj2 _ _) with Htid in Hget by apply proof_irr.
        rewrite <- Hget; auto.
      - intros.
        assert (containsThread js tid) as cnt0 by (apply Hcnt; auto).
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



(*    (** *Inital state simulation*)
    (* Erasure of the juicy initial_state is the dry initial_state AND
       the two are related by a Match relation. *)
    Lemma init_diagram:
      forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
        (vals : list Values.val) (m m' : Mem.mem) rmap pmap main h,
        init_inj_ok j m ->
        match_rmap_perm rmap pmap ->
        no_locks_perm rmap ->
        initial_core (JMachineSem U (Some rmap)) h m (U, nil, js) m' main vals ->
        exists (ds : dstate),
          initial_core (ClightMachineSem U (Some pmap)) h m (U, nil, ds) m' main vals /\
          invariant ds /\
          match_st js ds.
    Proof.
      intros.

      (* Build the structured injection*)
      (* exists (initial_SM (valid_block_dec m) (valid_block_dec m) (fun _ => false) (fun _ => false) j).*)

      (* Build the dry state *)
      simpl in H2.
      unfold Concur.init_mach in H2; simpl in *.
      destruct H2 as (_ & s & ? & ?); subst.
      exists (DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm m') s).
      destruct H0 as [Hperm ?]; destruct pmap; simpl in *; subst.

      split; [|split].

      (*Proofs*)
      - split; auto.
        split; auto.
        SearchAbout perm_of_
        unfold DryHybridMachine.init_mach.
        eexists; split; simpl; eauto.
      - eapply initial_invariant0.

      - eapply MTCH_initial with (pmap := (getCurPerm m', _)); auto; split; simpl; auto.
        destruct (H0 b ofs) as [-> _].
    Qed.*)

  Lemma perm_of_readable' : forall sh, shares.readable_share sh ->
    Mem.perm_order' (perm_of_sh (Share.glb Share.Rsh sh)) Readable.
  Proof.
    intros; unfold perm_of_sh.
    if_tac.
    - erewrite if_false by (apply shares.glb_Rsh_not_top); constructor.
    - erewrite if_true by (apply shares.readable_glb; auto); constructor.
  Qed.

  Lemma perm_of_writable' : forall sh, shares.writable_share sh ->
    Mem.perm_order' (perm_of_sh sh) Writable.
  Proof.
    intros; unfold perm_of_sh.
    erewrite if_true by auto.
    if_tac; constructor.
  Qed.

  Lemma lock_range_perm : forall m js ds (MATCH : match_st js ds) i (Hi : containsThread js i)
    (Hcmpt : mem_compatible js m) b ofs 
    sh R (HJcanwrite : Concur.lock_at_least sh R (getThreadR Hi) b (Ptrofs.intval ofs)),
    Mem.range_perm (Concur.juicyRestrict_locks (Concur.mem_compat_thread_max_cohere Hcmpt Hi)) b
      (Ptrofs.intval ofs) (Ptrofs.intval ofs + LKSIZE) Cur Readable.
  Proof.
    intros.
    intros j ?. specialize (HJcanwrite (j-Ptrofs.intval ofs)). spec HJcanwrite; [omega|].
    destruct HJcanwrite as [sh' [rsh' [? ?]]].
    replace (Ptrofs.intval ofs + (j - Ptrofs.intval ofs)) with j in H1 by omega.
    unfold Concur.juicyRestrict_locks, Mem.perm.
    setoid_rewrite restrPermMap_Cur.
    rewrite <- Concur.juic2Perm_locks_correct by (eapply Concur.mem_compat_thread_max_cohere; auto).
    rewrite H1. 
      apply perm_of_readable'; auto.
  Qed.
  
  (** *SyncStep simulation*)
  (** Proof of the step diagram when the step is a synchronization step.   
      TODO: Split the proof in each diagram.
   *)

  Inductive deltaMap_cases (dmap:delta_map) b ofs:=
  | DMAPS df p:  dmap ! b = Some df -> df ofs = Some p -> deltaMap_cases dmap b ofs
  | DNONE1 df:  dmap ! b = Some df -> df ofs = None -> deltaMap_cases dmap b ofs
  | DNONE2:  dmap ! b = None -> deltaMap_cases dmap b ofs.

  Lemma deltaMap_dec: forall dmap b ofs, deltaMap_cases dmap b ofs.
  Proof.
    intros. destruct (dmap ! b) eqn:H1; [destruct (o ofs) eqn:H2 | ]; econstructor; eassumption.
  Qed.
 
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
  
  Lemma po_None1: forall p, Mem.perm_order'' None p -> p = None.
  Proof. intros. simpl in H. destruct p; inversion H; reflexivity. Qed.

  (*Adding a thread preserves the invariant! *)
  Lemma addThrd_inv: forall (ds : dstate) vf arg new_perm,
      invariant ds  ->
      (forall i cnti,
          permMapsDisjoint2 new_perm (@getThreadR _ _ _ i ds cnti)) ->
      (forall l rm,  lockRes ds l = Some rm ->
                permMapsDisjoint2 new_perm rm) ->
      permMapCoherence new_perm.1 new_perm.2 ->
      (forall i cnti,
          permMapCoherence new_perm.1 (@getThreadR _ _ _ i ds cnti).2) ->
      (forall i cnti,
          permMapCoherence (@getThreadR _ _ _ i ds cnti).1 new_perm.2) ->
      (forall l rm,  lockRes ds l = Some rm ->
                permMapCoherence new_perm.1 rm.2) ->
      (forall l rm,  lockRes ds l = Some rm ->
                permMapCoherence rm.1 new_perm.2) ->
      invariant (addThread ds vf arg new_perm).
  Proof.
    move => ds vf arg new_perm dinv
              DISJ_RES DISJ_LOCK COH_SELF COH_RES1
              COH_RES2 COH_LOCK1 COH_LOCK2.
    constructor.
    - move => i j cnti cntj neq.
      assert (cntj':=cntj).
      assert (cnti':=cnti).
      apply cntAdd' in cnti'.
      apply cntAdd' in cntj'.
      destruct cntj' as [[H1 H2] | H1];
        destruct cnti' as [[H3 H4] | H3]; subst;
          try solve[exfalso; apply neq; reflexivity].
      + rewrite (gsoAddRes _ _ _ _ H1) .
        rewrite (gsoAddRes _ _ _ _ H3).
        inversion dinv; eauto.
      + rewrite (gsoAddRes _ _ _ _ H1).
        erewrite gssAddRes; auto.
      + rewrite (gsoAddRes _ _ _ _ H3).
        apply permMapsDisjoint2_comm.
        erewrite gssAddRes; auto.
    - move => l1 l2 mr1 mr2.
      rewrite gsoAddLPool.
      rewrite gsoAddLPool.
      inversion dinv; eauto.
    - move => i l cnti rm.
      rewrite gsoAddLPool.
      assert (cnti':=cnti).
      apply cntAdd' in cnti'.
      destruct cnti' as [[H1 H2] | H1].
      + rewrite (gsoAddRes _ _ _ _ H1).
        inversion dinv; eauto.
      + erewrite gssAddRes; eauto.
    - move => i cnti; split.
      + assert (cnti':=cnti).
        apply cntAdd' in cnti'.
        destruct cnti' as [[H1 H2] | H1].
        * inversion dinv.
          move: (thread_data_lock_coh0 i H1)=> [] AA _.
          move => j cntj.
          assert (cntj':=cntj).
          apply cntAdd' in cntj'.
          destruct cntj' as [[H3 H4] | H3].
          -- rewrite (gsoAddRes _ _ _ _ H1) .
             rewrite (gsoAddRes _ _ _ _ H3).
             eapply AA.
          -- rewrite (gsoAddRes _ _ _ _ H1) .
             rewrite (gssAddRes); auto.
        * move => j cntj.
          assert (cntj':=cntj).
          apply cntAdd' in cntj'.
          destruct cntj' as [[H3 H4] | H3].
          -- rewrite (gsoAddRes _ _ _ _ H3).
             rewrite (gssAddRes); auto.
          -- do 2 (rewrite (gssAddRes); auto).
      + assert (cnti':=cnti).
        apply cntAdd' in cnti'.
        destruct cnti' as [[H1 H2] | H1].
        * inversion dinv.
          move: (thread_data_lock_coh0 i H1)=> [] _ BB.
          move => l rm.
          rewrite (gsoAddRes _ _ _ _ H1).
          rewrite gsoAddLPool.
          eauto.
        * move => l rm.
          rewrite (gssAddRes); auto.
          rewrite gsoAddLPool.
          eauto.
    - move=> l rm;
              rewrite gsoAddLPool => isLock.
      inversion dinv.
      move: (locks_data_lock_coh0 l rm isLock)=> [] AA BB.
      split.
      + move => j cntj.
        assert (cntj':=cntj).
        apply cntAdd' in cntj'.
        destruct cntj' as [[H3 H4] | H3].
        -- rewrite (gsoAddRes _ _ _ _ H3).
           inversion dinv; eauto.
        -- (rewrite (gssAddRes); auto).
           eauto.
      + move => l2 rm2;
                 rewrite gsoAddLPool => isLock2.
        eauto.
    - move => b ofs.
      inversion dinv; simpl; eauto.
      apply lockRes_valid0.
  Qed.

  (* Proof of the step diagram when the step is a synchronization step *)
  Lemma sync_step_diagram:
    forall (m m':Memory.mem) (U:seq nat) js js' ds i ev
          (MATCH: match_st js ds)
          (dinv: invariant ds)
            (Hi: containsThread js i)
            (Hcmpt: mem_compatible js m)
            (HschedN: schedPeek U = Some i)
      (Htstep:  syncStep true Hi Hcmpt js' m' ev),
      exists ds' : dstate, exists ev',
        invariant ds' /\ match_st js' ds' /\
        syncStep true (MTCH_cnt MATCH Hi) (MTCH_compat _ _ _ MATCH Hcmpt) ds' m' ev'.
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

            assert (virtue_correct1: forall b ofs,
                       (computeMap (getThreadR Htid').1 virtue1)  !! b ofs
                       = perm_of_res (phi' @ (b, ofs))
                   ).
            { intros.
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
                move: juice_join => /Concur.compatible_lockRes_sub.
                move => /(_ _ _ His_unlocked) /(resource_at_join_sub _ _ (b0, ofs0)) .
                cut (x @ (b0, ofs0) = NO Share.bot shares.bot_unreadable).
                { move=> -> . elim=> X Join. inversion Join; subst.
                  apply permjoin.join_to_bot_l in RJ; subst sh1.
                  f_equal. apply proof_irr. }
                { inversion all_cohere.
                  specialize (max_coh (b0, ofs0)). move: isNO max_coh.
                  rewrite /max_access_at /access_at /getMaxPerm /PMap.get PTree.gmap1 /=.
                  destruct (((Mem.mem_access m).2) ! b0)=> HH; try solve[ inversion HH].
                  rewrite Concur.Mem_canonical_useful /=.
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
                       (computeMap (getThreadR Htid').2 virtue2)  !! b ofs
                       = perm_of_res_lock (phi' @ (b, ofs))
                   ).
            { intros.
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
                move: juice_join => /Concur.compatible_lockRes_sub.
                move => /(_ _ _ His_unlocked) /(resource_at_join_sub _ _ (b0, ofs0)) .
                cut (x @ (b0, ofs0) = NO Share.bot shares.bot_unreadable).
                { move=> -> . elim=> X Join. inversion Join; subst.
                  apply permjoin.join_to_bot_l in RJ.
                  subst. f_equal; apply proof_irr. }
                { inversion all_cohere.
                  specialize (max_coh (b0, ofs0)). move: isNO max_coh.
                  rewrite /max_access_at /access_at /getMaxPerm /PMap.get PTree.gmap1 /=.
                  destruct (((Mem.mem_access m).2) ! b0)=> HH; try solve[ inversion HH].
                  rewrite Concur.Mem_canonical_useful /=.
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


         pose (ds':= updThread Htid' (Kresume c Vundef)
                  (computeMap
                     (getThreadR Htid').1 virtue1,
              computeMap
                     (getThreadR Htid').2 virtue2)).
         pose (ds'':= updLockSet ds'
                      (b, Ptrofs.intval ofs) (empty_map,empty_map)).
                      SearchAbout Events.delta_content.
         exists ds'', (Events.acquire (b, Ptrofs.intval ofs) (Some (build_delta_content virtue1 m')) ).
         split; [|split].
    - { (* invariant ds''*)

        unfold ds''.
        rewrite updLock_updThread_comm.
        pose (ds0:= (updLockSet ds (b, (Ptrofs.intval ofs)) (empty_map,empty_map))).

        cut (invariant ds0).
        { (* Proving: invariant ds0' *)
          intros dinv0.
          apply updThread_inv.

          - assumption.
          - intros.
            assert (forall l, joins (phi' @ l) (getThreadR (MTCH_cnt' MATCH cnt) @ l)).
            {assert (Hcmpt':=Hcmpt).
              assert (Hcmpt'':=Hcmpt).
              eapply
                Concur.compatible_threadRes_join
                with (cnti:=Hi)(cntj:=(MTCH_cnt' MATCH cnt))
                in Hcmpt'; auto.
              eapply
                Concur.compatible_threadRes_lockRes_join
              with (cnti:=(MTCH_cnt' MATCH cnt))
                     (l:=(b, Ptrofs.intval ofs))
                     (phi:=d_phi)
                in Hcmpt''; auto.
              intro l; apply resource_at_joins with (loc := l) in Hcmpt';
                apply resource_at_joins with (loc := l) in Hcmpt'';
                apply resource_at_join with (loc := l) in Hadd_lock_res.
              eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
              eapply joins_comm; auto.
            }

            split;
            eapply permDisjoint_permMapsDisjoint; intros b0 ofs0; simpl.
            + rewrite virtue_correct1 (MTCH_perm' _ MATCH b0 ofs0).
              apply joins_permDisjoint; auto.
            + rewrite virtue_correct2 (MTCH_perm2' _ MATCH b0 ofs0).
              apply joins_permDisjoint_lock; auto.
          - intros; intros b0 ofs0.
            destruct (eq_dec i j).
            + subst j.
              rewrite virtue_correct2 (MTCH_perm' _ MATCH b0 ofs0).
              contradiction.
            + rewrite virtue_correct2 (MTCH_perm' _ MATCH b0 ofs0).
              assert (forall l, joins (phi' @ l) (getThreadR (MTCH_cnt' MATCH cnt) @ l)).
              {assert (Hcmpt':=Hcmpt).
               assert (Hcmpt'':=Hcmpt).
               eapply
                Concur.compatible_threadRes_join
                with (cnti:=Hi)(cntj:=(MTCH_cnt' MATCH cnt))
                in Hcmpt'; auto.
               eapply
                 Concur.compatible_threadRes_lockRes_join
                 with (cnti:=(MTCH_cnt' MATCH cnt))
                     (l:=(b, Ptrofs.intval ofs))
                     (phi:=d_phi)
                 in Hcmpt''; auto.
               intro l; apply resource_at_joins with (loc := l) in Hcmpt';
                 apply resource_at_joins with (loc := l) in Hcmpt'';
                 apply resource_at_join with (loc := l) in Hadd_lock_res.
               eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
               eapply joins_comm; auto.
             }


              apply perm_coh_joins.
              apply joins_comm; auto.

          - intros; intros b0 ofs0.
            destruct (eq_dec i j).
            + subst j.
              contradiction.
            + rewrite virtue_correct1 (MTCH_perm2' _ MATCH b0 ofs0).
              assert (forall l, joins (phi' @ l) (getThreadR (MTCH_cnt' MATCH cnt) @ l)).
              {assert (Hcmpt':=Hcmpt).
               assert (Hcmpt'':=Hcmpt).
               eapply
                Concur.compatible_threadRes_join
                with (cnti:=Hi)(cntj:=(MTCH_cnt' MATCH cnt))
                in Hcmpt'; auto.
               eapply
                 Concur.compatible_threadRes_lockRes_join
                 with (cnti:=(MTCH_cnt' MATCH cnt))
                     (l:=(b, Ptrofs.intval ofs))
                     (phi:=d_phi)
                 in Hcmpt''; auto.
               intro l; apply resource_at_joins with (loc := l) in Hcmpt';
                 apply resource_at_joins with (loc := l) in Hcmpt'';
                 apply resource_at_join with (loc := l) in Hadd_lock_res.
               eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
               eapply joins_comm; auto.
              }
              apply perm_coh_joins; auto.
          - intros l pmap0.
            destruct (AMap.E.eq_dec l (b, Ptrofs.intval ofs)).
            + subst l; rewrite gssLockRes; simpl; intros HH; inversion HH; simpl.
              split; apply empty_disjoint'.
            + rewrite gsoLockRes; auto; simpl; intros HH.
              assert (exists pmap1, lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                setoid_rewrite HH in mtch_locks.
                destruct (lockRes js l).
                - exists l0; reflexivity.
                - inversion mtch_locks.
              }
              destruct H as [pmap1 HH'].
              destruct pmap1.
              * assert (forall l, joins (r @ l) (phi' @ l)).
               { assert (Hcmpt':=Hcmpt).
                 assert (Hcmpt'':=Hcmpt).
                 eapply
                   Concur.compatible_threadRes_lockRes_join
                 with (cnti:=Hi)
                        (l0:=l)
                        (phi:=r)
                   in Hcmpt'; auto.
                 eapply
                   Concur.compatible_lockRes_join
                 with (l2:=(b, Ptrofs.intval ofs))
                        (l1:=l)
                        (phi2:=d_phi)
                        (phi1:=r)
                   in Hcmpt''; auto.
                 intro l0; apply resource_at_joins with (loc := l0) in Hcmpt';
                   apply resource_at_joins with (loc := l0) in Hcmpt'';
                   apply resource_at_join with (loc := l0) in Hadd_lock_res.
                 eapply joins_comm.
                 eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
                 eapply joins_comm; auto. }
               split;
                 eapply permDisjoint_permMapsDisjoint; intros b0 ofs0.
               -- rewrite virtue_correct1.
                inversion MATCH.
                erewrite <- mtch_locksRes; eauto.
                apply joins_permDisjoint; auto.
               -- rewrite virtue_correct2.
                  inversion MATCH.
                  erewrite <- mtch_locksRes0; eauto.
                  apply joins_permDisjoint_lock; auto.
              * inversion MATCH.
                specialize (mtch_locksEmpty l pmap0 HH' HH);
                  subst pmap0;
                  simpl; split; apply permDisjoint_permMapsDisjoint; intros b0 ofs0;
                rewrite empty_map_spec;
                apply permDisjoint_None.
          - intros l pmap0.
            destruct (AMap.E.eq_dec l (b, Ptrofs.intval ofs)).
            + subst l; rewrite gssLockRes; simpl; intros HH; inversion HH; simpl.
              (*here*)
              split; [apply permCoh_empty | apply permCoh_empty'].
              { move=> b0 ofs0;
                  rewrite virtue_correct2.
                apply perm_of_res_lock_not_Freeable. }

            + rewrite gsoLockRes; auto; simpl; intros HH.
              assert (HH':=HH).
              eapply MTCH_locks in HH'; eauto.
              destruct HH' as [x HH'].
              destruct x.
              * assert (forall l, joins (r @ l) (phi' @ l)).
               { assert (Hcmpt':=Hcmpt).
                 assert (Hcmpt'':=Hcmpt).
                 eapply
                   Concur.compatible_threadRes_lockRes_join
                 with (cnti:=Hi)
                        (l0:=l)
                        (phi:=r)
                   in Hcmpt'; auto.
                 eapply
                   Concur.compatible_lockRes_join
                 with (l2:=(b, Ptrofs.intval ofs))
                        (l1:=l)
                        (phi2:=d_phi)
                        (phi1:=r)
                   in Hcmpt''; auto.
                 intro l0; apply resource_at_joins with (loc := l0) in Hcmpt';
                   apply resource_at_joins with (loc := l0) in Hcmpt'';
                   apply resource_at_join with (loc := l0) in Hadd_lock_res.
                 eapply joins_comm.
                 eapply (juicy_mem_lemmas.components_join_joins _ _ _ _ Hadd_lock_res); eauto;
                 eapply joins_comm; auto. }
                split; intros b0 ofs0.
                -- rewrite virtue_correct2.
                   inversion MATCH.
                   erewrite <- mtch_locksRes; eauto.
                   apply perm_coh_joins; auto.
                -- rewrite virtue_correct1.
                   inversion MATCH.
                   erewrite <- mtch_locksRes0; eauto.
                   apply perm_coh_joins; apply joins_comm; auto.
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
                apply permMapsDisjoint2_empty.

              - intros.
                apply permMapsDisjoint2_comm.
                apply permMapsDisjoint2_empty.
              - intros.
                split; [apply permCoh_empty | apply permCoh_empty'].
                { move=> b0 ofs0.
                  apply (invariant_not_freeable) with (b1:=b0)(ofs1:= ofs0) in dinv.
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
                cut (lockRes js (b, ofs0) = None).
                { intros HH. inversion MATCH.
                  specialize (mtch_locks (b, ofs0)).
                  rewrite HH in mtch_locks.
                  clear - mtch_locks.
                  destruct (lockRes ds (b, ofs0)) eqn:AA; auto.
                  - inv mtch_locks.
                }
                {(*the cut*)
                  move HJcanwrite at bottom.
                  destruct Hcmpt as [all_juice Hcmpt].
                  inversion Hcmpt.
                  unfold Concur.juicyLocks_in_lockSet in jloc_in_set.
                  eapply Concur.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
                  destruct juice_join as [x H0].
                  assert (H0':= fun loc => resource_at_join _ _ _ loc H0).
                  apply resource_at_join with (loc:=(b, Ptrofs.intval ofs)) in H0.
                  rewrite <- (fst_snd0 (b, Ptrofs.intval ofs)) in H0.
                  destruct (HJcanwrite 0) as [sh' [rsh' [HJc1 HJc2]]]. pose proof LKSIZE_pos; omega.
                  rewrite HJc2 in H0.
                  simpl in H0; inversion H0.
                  - subst.
                    symmetry in H6.
                    assert (H1 := jloc_in_set (b, Ptrofs.intval ofs)).
                    spec H1. { intros. destruct (HJcanwrite _ H2) as [sh'' [rsh'' [HJc3 HJc4]]].
                            specialize (H0' (b, Ptrofs.intval ofs + i0)). rewrite HJc4 in H0'.
                            clear - H0'. inv H0'; eauto.
                    }
                    assert (VALID:= Concur.compat_lr_valid Hcompatible).
                    specialize (VALID b (Ptrofs.intval ofs)).
                    simpl in *.
                    unfold OrdinalPool.lockRes in *.
                    simpl in *.
                    destruct (AMap.find (elt:=option rmap)
                                        (b, Ptrofs.intval ofs) (OrdinalPool.lockGuts js)) eqn:AA;
                      rewrite AA in H1, VALID; try solve[inversion H1].
                    apply VALID. auto.
                  -
                    symmetry in H6.
                    assert (H1 := jloc_in_set (b, Ptrofs.intval ofs)).
                    spec H1. { intros. destruct (HJcanwrite _ H7) as [sh'' [rsh'' [HJc3 HJc4]]].
                            specialize (H0' (b, Ptrofs.intval ofs + i0)). rewrite HJc4 in H0'.
                            clear - H0'. inv H0'; eauto.
                    }
                    assert (VALID:= Concur.compat_lr_valid Hcompatible).
                    specialize (VALID b (Ptrofs.intval ofs)).
                    simpl in *.
                    unfold OrdinalPool.lockRes in *.
                    simpl in *.
                    destruct (AMap.find (elt:=option rmap)
                                        (b, Ptrofs.intval ofs) (OrdinalPool.lockGuts js)) eqn:AA;
                      rewrite AA in H1, VALID; try solve[inversion H1].
                    apply VALID. auto.
                }
              - simpl. intros ofs0 ineq. move HJcanwrite at bottom.
                cut ( lockRes js (b, ofs0) = None).
                { intros HH. inversion MATCH.
                  specialize (mtch_locks (b, ofs0)). rewrite HH in mtch_locks.
                  destruct (lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks; auto. }
                {
                  destruct (lockRes js (b, ofs0)) eqn:MAP; try reflexivity. exfalso.
                  move HJcanwrite at bottom.
                  destruct Hcmpt as [all_juice Hcmpt].
                  inversion Hcmpt.
                  unfold Concur.juicyLocks_in_lockSet in jloc_in_set.
                  eapply Concur.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
                  destruct juice_join as [x H0].
                  assert (H0':= fun loc => resource_at_join _ _ _ loc H0).
                  apply resource_at_join with (loc:=(b, Ptrofs.intval ofs)) in H0.
                  rewrite <- (fst_snd0 (b, Ptrofs.intval ofs)) in H0.
                  destruct (HJcanwrite 0) as [sh' [rsh' [HJc1 HJc2]]]. pose proof LKSIZE_pos; omega.
                  rewrite HJc2 in H0.
                  simpl in H0; inversion H0.
                  -
                    symmetry in H5.
                    assert (H8 := jloc_in_set (b, Ptrofs.intval ofs)).
                    spec H8. { intros. destruct (HJcanwrite _ H4) as [sh'' [rsh'' [HJc3 HJc4]]].
                            specialize (H0' (b, Ptrofs.intval ofs + i0)). rewrite HJc4 in H0'.
                            clear - H0'. inv H0'; eauto.
                    } 
                    assert (VALID:= Concur.compat_lr_valid Hcompatible).
                    specialize (VALID b ofs0).
                    rewrite MAP in VALID.
                    apply VALID in ineq.
                    move ineq at bottom.
                    setoid_rewrite ineq in H8.
                    inversion H8.
                  -
                    symmetry in H5.
                    assert (H8 := jloc_in_set (b, Ptrofs.intval ofs)).
                    spec H8. { intros. destruct (HJcanwrite _ H4) as [sh'' [rsh'' [HJc3 HJc4]]].
                            specialize (H0' (b, Ptrofs.intval ofs + i0)). rewrite HJc4 in H0'.
                            clear - H0'. inv H0'; eauto.
                   }
                    assert (VALID:= Concur.compat_lr_valid Hcompatible).
                    specialize (VALID b ofs0).
                    rewrite MAP in VALID.
                    apply VALID in ineq.
                    move ineq at bottom.
                    setoid_rewrite ineq in H8.
                    inversion H8.
                }
            }
      }
    - unfold ds''.
      apply match_st_age_tp_to.
      apply MTCH_updLockN.
      unfold ds'.
      apply MTCH_update; auto.

    - assert (H: exists l, lockRes ds (b, Ptrofs.intval ofs) = Some l).
      { inversion MATCH; subst.
        specialize (mtch_locks (b, (Ptrofs.intval ofs) )).
        rewrite His_unlocked in mtch_locks.
        destruct (lockRes ds (b, Ptrofs.intval ofs));
          try solve[inversion mtch_locks]. exists l; reflexivity. }
      destruct H as [l dlockRes].
      assert (Hlt'':  permMapLt (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
                                              (getThreadR
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
          rewrite -Concur.juic2Perm_locks_correct.
          rewrite -(MTCH_perm2 _ MATCH); auto.
          apply Concur.mem_access_coh_sub with (phi1:=jall).
          assumption.
          eapply Concur.compatible_threadRes_sub; eauto.
        - do 2 (rewrite setPermBlock_other_2; auto).
          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt; inversion all_cohere.
          rewrite -Concur.juic2Perm_locks_correct.
          rewrite -(MTCH_perm2 _ MATCH); auto.
          apply Concur.mem_access_coh_sub with (phi1:=jall).
          assumption.
          eapply Concur.compatible_threadRes_sub; eauto.
      }

      change virtue1 with (virtue1, virtue2).1.
      econstructor 1.

      15: reflexivity.
      15: now unfold ds'', ds'; repeat f_equal; apply proof_irr.
      8: eassumption.
      10: eassumption.
      + (*boundedness*)
        split.
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].

          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
          { move: (Concur.compat_lockLT
                        Hcmpt _ His_unlocked p b0).

            rewrite /PMap.get HH' is_none => /po_None1 //.
            }
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
          { move: (Concur.compat_lockLT
                        Hcmpt _ His_unlocked p b0).
            rewrite /PMap.get HH' is_none => /po_None1 //.
            }

          (*eapply treemap_sub_map.*)
      + assumption.
      + eapply MTCH_getThreadC; eassumption.
      + reflexivity.
      + eassumption.
      + unfold Concur.juicyRestrict_locks.
        apply restrPermMap_ext;
          intros b0.
        inversion MATCH; subst.
        extensionality ofs0.
        rewrite <- Concur.juic2Perm_locks_correct.
        symmetry. apply mtch_perm2.
        apply Concur.mem_compat_thread_max_cohere.
        assumption.
      + eapply lock_range_perm;  eauto.
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
          rewrite -Concur.juic2Perm_locks_correct.
          inversion MATCH. symmetry. eapply mtch_perm2.
          eapply Concur.mem_compat_thread_max_cohere; auto.
          simpl; pose proof LKSIZE_pos; xomega.
        * repeat (rewrite setPermBlock_other_2; auto).
          rewrite -Concur.juic2Perm_locks_correct.
          inversion MATCH. symmetry. eapply mtch_perm2.
          eapply Concur.mem_compat_thread_max_cohere; auto.
      + exact dlockRes.
      + intros b0 ofs0. inversion MATCH; subst.
        specialize (mtch_locksRes _ _ _ His_unlocked dlockRes).
        rewrite <- mtch_locksRes.
        rewrite <- mtch_perm1 with (Htid:=Hi).
        replace (MTCH_cnt MATCH Hi) with Htid' by eapply proof_irr.
        rewrite virtue_correct1.
        eapply permjoin.join_permjoin.
        eapply resource_at_join.
        apply join_comm.
        assumption.
      + intros b0 ofs0. inversion MATCH; subst.
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
    pose (ds':= updThread Htid' (Kresume c Vundef)
                                          (computeMap
                                             (getThreadR Htid').1 virtue1,
                                           computeMap
                                             (getThreadR Htid').2 virtue2)).
    pose (ds'':= updLockSet ds' (b, Ptrofs.intval ofs)
                                            (Concur.juice2Perm d_phi m, Concur.juice2Perm_locks d_phi m )).

    assert (virtue_spec1: forall b0 ofs0, perm_of_res (phi' @ (b0, ofs0)) =
                                    (computeMap (getThreadR Htid').1 virtue1) !! b0 ofs0).
    {
      intros b0 ofs0.
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
             replace ((getThreadR Htid').1 !! b0 ofs0) with
             (perm_of_res ((getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply Concur.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply Concur.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold Concur.access_cohere' in acc_coh.
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
                                    (computeMap (getThreadR Htid').2 virtue2) !! b0 ofs0).
    {
      intros b0 ofs0.
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
             replace ((getThreadR Htid').2 !! b0 ofs0) with
             (perm_of_res_lock ((getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply Concur.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply Concur.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold max_access_cohere in max_coh.
               specialize (max_coh (b0,ofs0)).
               unfold max_access_at, access_at in max_coh.
               unfold permission_at in the_cure.
               rewrite the_cure in max_coh.

               pose (HERE:= perm_of_res_op2 (getThreadR Hi @ (b0, ofs0))).
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
SearchAbout Events.delta_content.
SearchAbout access_map delta_map.
    eexists ds'', _.
    split; [|split].
    - unfold ds''.
      cut (invariant ds').
      { intros dinv'.
        apply updLock_inv.
        - assumption.
        - move=> laddr ramp0 laddr_neq .
          unfold ds'; rewrite gsoThreadLPool => get_lres.
          (*move this*)
          move: (get_lres) => /(MTCH_locks) /= /(_ _ MATCH) [] l.
          destruct l.
          + (*Some case: lock is not acquyired*)
            inversion MATCH => jget_lres.
            split.
            * apply permDisjoint_permMapsDisjoint;
              intros b0 ofs0.
              move : (mtch_locksRes _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite -Concur.juic2Perm_correct.
              apply joins_permDisjoint.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              -- exists phi'; eassumption.
              -- eapply Concur.compatible_threadRes_lockRes_join; eauto.
              -- apply Concur.max_acc_coh_acc_coh.
                 destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
            * apply permDisjoint_permMapsDisjoint;
              intros b0 ofs0.
              move : (mtch_locksRes0 _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite -Concur.juic2Perm_locks_correct.
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              -- exists phi'; eassumption.
              -- eapply Concur.compatible_threadRes_lockRes_join; eauto.
              -- destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
          + (*None case: lock was acquired before*)
            inversion MATCH.
            move => /(mtch_locksEmpty) // /(_ _ get_lres) ->.
            apply permMapsDisjoint2_comm;
            apply permMapsDisjoint2_empty.

        (*empty map disjoit!*)
        - rewrite /ds'=> i0.
          destruct (eq_dec i i0).
          + subst=> cnti.
            rewrite gssThreadRes; split=> /=;
              apply permDisjoint_permMapsDisjoint => b0 ofs0.
            * rewrite - virtue_spec1.
              rewrite - Concur.juic2Perm_correct.
              apply joins_permDisjoint.
              apply resource_at_joins.
              apply joins_comm.
              eexists; eassumption.

              apply Concur.max_acc_coh_acc_coh.
              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
            * rewrite - virtue_spec2.
              rewrite - Concur.juic2Perm_locks_correct.
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              apply joins_comm.
              eexists; eassumption.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
          + move => cnti. rewrite gsoThreadRes => //.
            split=> /=;
              apply permDisjoint_permMapsDisjoint => b0 ofs0.
            * rewrite (MTCH_perm' _ MATCH).
              rewrite - Concur.juic2Perm_correct.
              apply joins_permDisjoint.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply Concur.compatible_threadRes_join;
                eassumption.

              apply Concur.max_acc_coh_acc_coh.
              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
            * rewrite (MTCH_perm2' _ MATCH).
              rewrite - Concur.juic2Perm_locks_correct.
              apply joins_permDisjoint_lock.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply Concur.compatible_threadRes_join;
                eassumption.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
        - move=> laddr ramp0 laddr_neq .
          unfold ds'; rewrite gsoThreadLPool => get_lres.
          (*move this*)
          move: (get_lres) => /(MTCH_locks) /= /(_ _ MATCH) [] l.
          destruct l.
          + (*Some case: lock is not acquyired*)
            inversion MATCH => jget_lres.
            split.
            * intros b0 ofs0.
              move : (mtch_locksRes0 _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite - Concur.juic2Perm_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply Concur.compatible_threadRes_lockRes_join ; eassumption.

              apply Concur.max_acc_coh_acc_coh.
              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
            * intros b0 ofs0.
              move : (mtch_locksRes _ _ _ jget_lres get_lres b0 ofs0) =>  <- /=.
              rewrite - Concur.juic2Perm_locks_correct.
               apply perm_coh_joins.
               apply resource_at_joins.
               apply joins_comm.
              eapply join_sub_joins_trans.
              exists phi'; eassumption.
              eapply Concur.compatible_threadRes_lockRes_join ; eassumption.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.


          + (*None case: lock was acquired before*)
            inversion MATCH.
            move => /(mtch_locksEmpty) // /(_ _ get_lres) -> /=.
            split; first [apply permCoh_empty'| apply permCoh_empty].
            { move => b0 ofs0.
              rewrite -Concur.juic2Perm_locks_correct.
              apply perm_of_res_lock_not_Freeable.

              destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.

            }

        - move=> b0 ofs0 /=.
          assert ( max_access_cohere m d_phi).
          {
             destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption. }

          rewrite - Concur.juic2Perm_locks_correct.
          rewrite - Concur.juic2Perm_correct.
          apply perm_coh_self.

          + apply Concur.max_acc_coh_acc_coh; assumption.
          + assumption.
        - rewrite /ds'=> i0.
          destruct (eq_dec i i0).
          + subst=> cnti. rewrite gssThreadRes; split=> /= b0 ofs0.
            * rewrite - virtue_spec2.
              rewrite - Concur.juic2Perm_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              eexists; eassumption.

              apply Concur.max_acc_coh_acc_coh.
               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.

            * rewrite - virtue_spec1.
              rewrite - Concur.juic2Perm_locks_correct.
              apply perm_coh_joins.
              apply joins_comm.
              apply resource_at_joins.
              eexists; eassumption.

               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
          + move => cnti. rewrite gsoThreadRes => //.
            split=> /= b0 ofs0.
            * rewrite (MTCH_perm2' _ MATCH).
              rewrite - Concur.juic2Perm_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              eexists phi'; eassumption.
              eapply Concur.compatible_threadRes_join; eassumption.

               apply Concur.max_acc_coh_acc_coh.
               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.
            * rewrite (MTCH_perm' _ MATCH).
              rewrite - Concur.juic2Perm_locks_correct.
              apply perm_coh_joins.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              eexists phi'; eassumption.
              eapply Concur.compatible_threadRes_join; eassumption.

               destruct Hcmpt as [jall Hcmpt]; inversion Hcmpt.
                 apply Concur.mem_access_coh_sub with (phi1:= jall).
                  inversion  all_cohere; assumption.
                 apply join_sub_trans with (b1:=(getThreadR Hi)).
                 exists phi'; assumption.
                 apply Concur.compatible_threadRes_sub; assumption.

        - intros ofs0 ineq.
          rewrite gsoThreadLPool.
          cut (lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH. specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            destruct (lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks; auto.
          }
          { destruct Hcompatible as [allj Hcompatible].
            inversion Hcompatible.
            assert (VALID:= Concur.compat_lr_valid Hcmpt).
            specialize (VALID b (Ptrofs.intval ofs)).
            eapply Concur.compatible_threadRes_sub with (cnt:= Hi) in juice_join. 
            rewrite His_locked in VALID. apply VALID; auto.
           }
        - intros ofs0 ineq.
          rewrite gsoThreadLPool.
          cut (lockRes js (b, ofs0) = None).
          { intros HH. inversion MATCH. specialize (mtch_locks (b, ofs0)).
            rewrite HH in mtch_locks.
            destruct (lockRes ds (b, ofs0)) eqn:AA; inversion mtch_locks; auto.
          }
          { destruct (lockRes js (b, ofs0)) eqn:AA; try reflexivity. exfalso.
             destruct Hcompatible as [allj Hcompatible].
            inversion Hcompatible.
            assert (VALID:= Concur.compat_lr_valid Hcmpt).
            specialize (VALID b ofs0).
            rewrite AA in VALID.
            apply VALID in ineq.
            eapply Concur.compatible_threadRes_sub with (cnt:= Hi) in juice_join.
            specialize (jloc_in_set (b,Ptrofs.intval ofs)).
            spec jloc_in_set. { intros. simpl. 
                  apply resource_at_join_sub with (l:=(b,Ptrofs.intval ofs+i0)) in juice_join.
                  destruct (HJcanwrite _ H) as [sh' [rsh' [? ?]]]. rewrite H1 in juice_join.
                 destruct juice_join as [x HH].
                 inversion HH; eauto.
            }
           setoid_rewrite ineq in jloc_in_set. inv jloc_in_set.
          }

      }


      { (*Proof invariant ds'*) (*repeat lemma*)
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

      2:{
      inversion MATCH; subst.
      intros; apply Concur.juic2Perm_correct.
      inversion Hcompatible; inversion H; inversion all_cohere.
      apply Concur.max_acc_coh_acc_coh.
      assumption.
      (*
      eapply Concur.mem_access_coh_sub.
      - eassumption.
      - eapply join_sub_trans.
        + unfold join_sub. exists phi'. eassumption.
        + eapply Concur.compatible_threadRes_sub.
      assumption. *) }

      unfold ds'.
      apply MTCH_update; eauto.
      move=> b0 ofs0.
      apply Concur.juic2Perm_locks_correct.
      assumption.

      (*the cut*)
      { inversion Hcompatible; inversion H; inversion all_cohere.
        eapply Concur.mem_access_coh_sub.
         - eassumption.
         - eapply join_sub_trans.
           + unfold join_sub. exists phi'. eassumption.
           + eapply Concur.compatible_threadRes_sub.
             assumption.
      }


    - assert (H: exists l, lockRes ds (b, Ptrofs.intval ofs) = Some l).
      { inversion MATCH; subst.
        specialize (mtch_locks (b, (Ptrofs.intval ofs) )).
        rewrite His_locked in mtch_locks.
        destruct (lockRes ds (b, Ptrofs.intval ofs)); try solve[inversion mtch_locks]. exists l; reflexivity. }
           destruct H as [l dlockRes].
      econstructor 2.
      17: reflexivity.
      16: instantiate (2:= (virtue1, virtue2));
          instantiate (1 := (Concur.juice2Perm d_phi m, Concur.juice2Perm_locks d_phi m));
        unfold ds'; repeat f_equal; try reflexivity; try apply proof_irrelevance.
      9: eassumption.
      11: eassumption.
      9: reflexivity.
      + (*boundedness 1*)
        split.
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
          (* eapply treemap_sub_map. *)
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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


          (* eapply treemap_sub_map. *)
      + (*boundedness 2*)
        repeat split.
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
          (* eapply treemap_sub_map. *)
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
      + reflexivity.
      + eassumption.
      + apply restrPermMap_ext.
        intros b0.
        inversion MATCH; subst.
        extensionality ofs0.
        rewrite -Concur.juic2Perm_locks_correct.
        symmetry; apply mtch_perm2.
        inversion Hcompatible; inversion H; inversion all_cohere.
        eapply Concur.mem_access_coh_sub.
        * eassumption.
        *  eapply Concur.compatible_threadRes_sub.
           assumption.
      + eapply lock_range_perm; eauto.
      + apply restrPermMap_ext.
        intros b0.
        extensionality ofs0.
        destruct (peq b b0); [subst b0; destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, Ptrofs.intval ofs + lksize.LKSIZE)%Z ) | ].
        * unfold Intv.In in i0; simpl in i0.
          repeat rewrite setPermBlock_same; auto.
        * apply Intv.range_notin in n; auto.
          repeat rewrite setPermBlock_other_1; auto.
          rewrite -Concur.juic2Perm_locks_correct.
          symmetry; eapply MTCH_perm2.
          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt. inversion all_cohere.
          eapply Concur.mem_access_coh_sub; eauto.
          apply Concur.compatible_threadRes_sub; assumption.
          pose proof LKSIZE_pos; simpl; xomega.
        * repeat rewrite setPermBlock_other_2; auto.
          rewrite -Concur.juic2Perm_locks_correct.
          symmetry; eapply MTCH_perm2.
          destruct Hcmpt as [jall Hcmpt];
            inversion Hcmpt. inversion all_cohere.
          eapply Concur.mem_access_coh_sub; eauto.
          apply Concur.compatible_threadRes_sub; assumption.

      + exact dlockRes.
      + inversion MATCH.
        specialize (mtch_locksEmpty _ _ His_locked dlockRes).
        inversion mtch_locksEmpty; simpl.
        move=> b0 ofs0.
        rewrite empty_map_spec; tauto.
      + simpl; intros b0 ofs0.
        replace (MTCH_cnt MATCH Hi) with Htid'.
        rewrite -virtue_spec1.
        rewrite -Concur.juic2Perm_correct.
        rewrite (MTCH_perm' _ MATCH b0 ofs0).
        apply permjoin.join_permjoin.
        move Hrem_lock_res at bottom.
        eapply resource_at_join; apply join_comm.
        replace (MTCH_cnt' MATCH Htid') with Hi.
        assumption.
        apply proof_irrelevance.
        2:
        apply proof_irrelevance.
        apply Concur.max_acc_coh_acc_coh.
        inversion Hcompatible; inversion H; inversion all_cohere.
        eapply Concur.mem_access_coh_sub.
        * eassumption.
        *  eapply join_sub_trans.
           -- unfold join_sub. exists phi'. eassumption.
           -- eapply Concur.compatible_threadRes_sub.
              assumption.
      + simpl; intros b0 ofs0.
        replace (MTCH_cnt MATCH Hi) with Htid'.
        rewrite -virtue_spec2.
        rewrite -Concur.juic2Perm_locks_correct.
        rewrite (MTCH_perm2' _ MATCH b0 ofs0).
        apply permjoin.join_permjoin_lock.
        apply resource_at_join.
        apply join_comm.
        replace (MTCH_cnt' MATCH Htid') with Hi by apply proof_irrelevance.
        assumption.
        2:
        apply proof_irrelevance.
        inversion Hcompatible; inversion H; inversion all_cohere.
        eapply Concur.mem_access_coh_sub.
        * eassumption.
        *  eapply join_sub_trans.
           -- unfold join_sub. exists phi'. eassumption.
           -- eapply Concur.compatible_threadRes_sub.
              assumption.
      + replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
        reflexivity.
    }




    (*step_create*)
    {


      (*First two deltas correspond to the two access maps removed from the thread:
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
                 (computeMap (getThreadR (MTCH_cnt MATCH Hi)).1 virtue11) !! b0 ofs0 =
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
             replace ((getThreadR (MTCH_cnt MATCH Hi)).1 !! b0 ofs0) with
             (perm_of_res ((getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply Concur.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply Concur.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold Concur.access_cohere' in acc_coh.
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
                 (computeMap (getThreadR (MTCH_cnt MATCH Hi)).2 virtue12) !! b0 ofs0 =
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
             replace ((getThreadR (MTCH_cnt MATCH Hi)).2 !! b0 ofs0) with
             (perm_of_res_lock ((getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply Concur.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               (*apply Concur.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold Concur.access_cohere' in acc_coh.*)
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
                 (perm_of_res_op2 (getThreadR Hi @ (b0, ofs0))).

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
             replace ((getThreadR (MTCH_cnt MATCH Hi)).1 !! b0 ofs0) with
             (perm_of_res ((getThreadR Hi)@ (b0, ofs0))).
             + assert (Hcohere':= Hcompatible).
               apply Concur.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               apply Concur.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold Concur.access_cohere' in acc_coh.
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
             replace ((getThreadR (MTCH_cnt MATCH Hi)).2 !! b0 ofs0) with
             (perm_of_res_lock ((getThreadR Hi)@ (b0, ofs0))).
          + assert (Hcohere':= Hcompatible).
               apply Concur.compatible_threadRes_cohere with (cnt:=Hi) in Hcohere'.
               inversion Hcohere'.
               (*apply Concur.max_acc_coh_acc_coh in max_coh as acc_coh.
               unfold Concur.access_cohere' in acc_coh.*)
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
                 (perm_of_res_op2 (getThreadR Hi @ (b0, ofs0))).

               rewrite max_coh => /po_None1 is_none.
               rewrite empty_map_spec.
               rewrite is_none in HH.
               apply po_None1 in HH. symmetry; assumption.
             + inversion MATCH.  apply mtch_perm2.

      }







      (*Having computed and specified the virtues, we can prove the create step.*)



      pose (ds_upd:= updThread
                       (MTCH_cnt MATCH Hi)
                       (Kresume c Vundef)
                       (computeMap (getThreadR (MTCH_cnt MATCH Hi)).1 virtue11,
                        computeMap (getThreadR (MTCH_cnt MATCH Hi)).2 virtue12)).

      pose (ds':= addThread
                    ds_upd
                    (Vptr b ofs)
                    arg
                    (computeMap empty_map virtue21,
                     computeMap empty_map virtue22)).
      exists ds'.
      eexists.
      split ;[|split].
      { (* invariant *)
        cut (invariant ds_upd).
        { (*This is a new lemma that is missing.*)
          intro HH; apply addThrd_inv.
          - assumption.
          - move=> j cntj .
            split;
              apply permDisjoint_permMapsDisjoint => b0 ofs0.
            + rewrite virtue_spec21.
              destruct (eq_dec i j).
              * subst. rewrite gssThreadRes.
                rewrite virtue_spec11.
                apply joins_permDisjoint.
                apply resource_at_joins.
                eexists; eassumption.
              * rewrite gsoThreadRes; auto.
                rewrite (MTCH_perm' _ MATCH).
                apply joins_permDisjoint.
                apply resource_at_joins.
                eapply join_sub_joins_trans; eauto.
                exists phi'; eauto.
                simpl.
                eapply Concur.compatible_threadRes_join; eauto.
            + rewrite virtue_spec22.
              destruct (eq_dec i j).
              * subst. rewrite gssThreadRes.
                rewrite virtue_spec12.
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                eexists; eassumption.
              * rewrite gsoThreadRes; auto.
                rewrite (MTCH_perm2' _ MATCH).
                apply joins_permDisjoint_lock.
                apply resource_at_joins.
                eapply join_sub_joins_trans; eauto.
                exists phi'; eauto.
                simpl.
                eapply Concur.compatible_threadRes_join; eauto.
          - move => l rm.
            rewrite gsoThreadLPool => isLock2.
            split; apply permDisjoint_permMapsDisjoint=> b0 ofs0 /=.
            + rewrite virtue_spec21.

              assert (exists pmap1, lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock2 in mtch_locks.
                destruct (lockRes js l).
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
                eapply Concur.compatible_threadRes_lockRes_join;
                  eauto.
              * inversion MATCH.
                specialize (mtch_locksEmpty _ _ H isLock2).
                inversion mtch_locksEmpty.
                rewrite empty_map_spec.
                eapply permDisjoint_comm.
                eapply permDisjoint_None.
            + rewrite virtue_spec22.

              assert (exists pmap1, lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock2 in mtch_locks.
                destruct (lockRes js l).
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
                eapply Concur.compatible_threadRes_lockRes_join;
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
            destruct (eq_dec i j).
            * subst. rewrite gssThreadRes.
              rewrite virtue_spec12.
              apply perm_coh_joins.
              apply resource_at_joins.
              eexists; eauto.
            * rewrite gsoThreadRes; auto.
              rewrite (MTCH_perm2' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply join_sub_joins_trans.
              -- eexists; eauto.
              --  eapply Concur.compatible_threadRes_join; eauto.
          - move=> j cntj b0 ofs0.
            rewrite virtue_spec22.
            destruct (eq_dec i j).
            * subst. rewrite gssThreadRes.
              rewrite virtue_spec11.
              apply perm_coh_joins.
              apply resource_at_joins.
              eexists; eauto.
            * rewrite gsoThreadRes; auto.
              rewrite (MTCH_perm' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              apply joins_comm.
              eapply join_sub_joins_trans.
              -- eexists; eauto.
              --  eapply Concur.compatible_threadRes_join; eauto.
          - move => l rm .
            rewrite gsoThreadLPool => isLock b0 ofs0.
            rewrite virtue_spec21.
             assert (exists pmap1, lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock in mtch_locks.
                destruct (lockRes js l).
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
                eapply Concur.compatible_threadRes_lockRes_join;
                  eauto.
              + inversion MATCH.
                specialize (mtch_locksEmpty _ _ H isLock).
                inversion mtch_locksEmpty.
                rewrite empty_map_spec.
                eapply perm_coh_empty_1.
          - move => l rm .
            rewrite gsoThreadLPool => isLock b0 ofs0.
            rewrite virtue_spec22.
             assert (exists pmap1, lockRes js l = Some pmap1).
              { inversion MATCH.
                specialize (mtch_locks l).
                rewrite isLock in mtch_locks.
                destruct (lockRes js l).
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
                eapply Concur.compatible_threadRes_lockRes_join;
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
                      (Concur.personal_mem
                         (Concur.thread_mem_compatible Hcompatible Hi)))
            with
            (getThreadR Hi) in Hrem_fun_res by reflexivity.
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
        eapply DryHybridMachine.step_create with
        (virtue1:=(virtue11,virtue12))
          (virtue2:=(virtue21,virtue22)).
        - (*boundedness 1*)
          split.
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p0 f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p0, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
          (* eapply treemap_sub_map. *)
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p0 f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p0, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
          (* eapply treemap_sub_map. *)
        * eapply sub_map_and_shape;
          [eapply same_shape_map|].
          move=> p f1 HH.
          assert (HH':= HH).
          eapply map_leq_apply in HH';
            try apply treemap_sub_map.
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
                    (getThreadR Hi @ (p, b0))) = None).
            intros to_rewrite;
              eapply po_None1; rewrite -to_rewrite; eauto.

            move: (Concur.mem_compat_thread_max_cohere
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
        - reflexivity.
        - eassumption.
        - eassumption.
        - move => b0 ofs0.
          rewrite virtue_spec11.
          rewrite virtue_spec21.
          inversion MATCH. erewrite <- MTCH_perm.
          eapply permjoin.join_permjoin.
          apply resource_at_join.
          move Hrem_fun_res at bottom.
            replace
              (m_phi
                      (Concur.personal_mem
                         (Concur.thread_mem_compatible Hcompatible Hi)))
            with
            (getThreadR Hi) in Hrem_fun_res by reflexivity.
            assumption.
        -move => b0 ofs0.
          rewrite virtue_spec12.
          rewrite virtue_spec22.
          inversion MATCH. erewrite <- MTCH_perm2.
          eapply permjoin.join_permjoin_lock. (*for _locks *)
          apply resource_at_join.
          move Hrem_fun_res at bottom.
            replace
              (m_phi
                      (Concur.personal_mem
                         (Concur.thread_mem_compatible Hcompatible Hi)))
            with
            (getThreadR Hi) in Hrem_fun_res by reflexivity.
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
      pose (pmap_tid  := getThreadR Htid').
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
     - rewrite setPermBlock_same; auto.

       assert (HH':adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
       { split; auto. }

       move: Hrmap => /=.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2.
       intros [X Hg]; destruct (X _ HH') as (val & sh & Rsh & sh_before & Wsh & sh_after); clear X.
       rewrite sh_after.
       reflexivity.
     - rewrite setPermBlock_other_1.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
        { intros [ H1 [H2 H2']]; apply n; split; auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm' _ MATCH); simpl; repeat f_equal;
       apply proof_irrelevance.

       apply Intv.range_notin in n; auto.
       pose proof LKSIZE_pos; simpl. xomega.
     - rewrite setPermBlock_other_2.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b0,ofs0)).
        { intros [ H1 [H2 H2']]; apply n. auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm' _ MATCH); simpl; repeat f_equal;
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
       apply perm_of_writable;
         try apply shares.writable_share_glb_Rsh; eauto;
           apply shares.glb_Rsh_not_top.
       auto.

     - rewrite setPermBlock_other_1.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b,ofs0)).
        { intros [ H1 [H2 H2']]; apply n; split; auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm2' _ MATCH); simpl; repeat f_equal;
       apply proof_irrelevance.

       apply Intv.range_notin in n; auto.
       pose proof LKSIZE_pos; simpl. xomega.
     - rewrite setPermBlock_other_2.

       assert (HH': ~ adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b0,ofs0)).
        { intros [ H1 [H2 H2']]; apply n. auto.  }
        move: Hrmap.
       rewrite /rmap_locking.rmap_makelock => [] [] H1 [].
       move=> /(_ _ HH') => <- _ /=.
       rewrite (MTCH_perm2' _ MATCH); simpl; repeat f_equal;
       apply proof_irrelevance.

       auto.

       }



      (*HERE*)
      (*pose (pmap_lp   := setPerm (Some Writable) b (Ptrofs.intval ofs)
                                               (lockSet ds)).*)
      pose (ds':= updThread Htid' (Kresume c Vundef) (pmap_tid')).
      pose (ds'':= updLockSet ds' (b, Ptrofs.intval ofs) (empty_map,empty_map)).
      exists ds'',  (Events.mklock (b, Ptrofs.intval ofs)).
      split ; [|split].
      - (*invariant ds''*)
        cut (invariant ds').
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
              apply (invariant_not_freeable) with (b1:=b0)(ofs1:= ofs0) in dinv.
              destruct dinv as [AA BB].
              eapply BB in H0.
              destruct ((rmap'0.2) # b0 ofs0); try constructor.
              destruct p; try constructor.
              exfalso; apply H0; reflexivity. }
          - intros i0 cnti; apply permCoh_empty'.
          - intros i0 cnti; split;
            first [ apply permCoh_empty | apply permCoh_empty'].
            { move=> b0 ofs0.
              destruct (eq_dec i0 i).
              - subst i0.
                rewrite gssThreadRes.
                rewrite <- pmap_spec2.
                apply perm_of_res_lock_not_Freeable.
              - rewrite gsoThreadRes; auto.

                rewrite (MTCH_perm2' _ MATCH).

              apply perm_of_res_lock_not_Freeable. }
          - intros ofs0  ineq.
            rewrite gsoThreadLPool.

          destruct (lockRes ds (b, ofs0)) eqn:AA;  auto.

          inversion MATCH. specialize (mtch_locks (b,ofs0)).
          rewrite AA in mtch_locks.
          destruct (lockRes js (b, ofs0)) eqn:BB; inversion mtch_locks.
          destruct Hcompatible as [allj Hcompatible].
          inversion Hcompatible.
          specialize (lset_in_juice (b, ofs0)). setoid_rewrite BB in lset_in_juice.
          spec lset_in_juice; auto.
          destruct lset_in_juice as [sh' MAP]; auto.
          assert (HH:= Concur.compatible_threadRes_sub Hi juice_join).
          apply resource_at_join_sub with (l:= (b,ofs0)) in HH.
          assert (MAP0 := MAP 0). spec MAP0; [pose proof LKSIZE_pos; omega|]. 
            simpl in MAP0. destruct MAP0 as [shx [pshx [P [MAPx MAP0]]]]. rewrite Z.add_0_r in MAP0.
          rewrite MAP0 in HH.

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
          rewrite gsoThreadLPool.
          destruct (lockRes ds (b, ofs0)) eqn:AA; auto.
          inversion MATCH. specialize (mtch_locks (b,ofs0)).
          rewrite AA in mtch_locks.
          destruct (lockRes js (b, ofs0)) eqn:BB; inversion mtch_locks.
          destruct Hcompatible as [allj Hcompatible].
          inversion Hcompatible.
          specialize (lset_in_juice (b, ofs0)). setoid_rewrite BB in lset_in_juice.
          destruct lset_in_juice as [sh' MAP]; auto.
          assert (HH:= Concur.compatible_threadRes_sub Hi juice_join).
          assert (ineq': 0 <= Ptrofs.intval ofs - ofs0 < LKSIZE).
          { clear - ineq. simpl in ineq; destruct ineq. xomega. }
          apply resource_at_join_sub with (l:= (b,Ptrofs.intval ofs)) in HH.
          specialize (MAP _ ineq'). destruct MAP as [shx [pshx [P [MAPx MAP]]]]. simpl in MAP.
          replace (ofs0 + (Ptrofs.intval ofs - ofs0)) with (Ptrofs.intval ofs) in MAP by omega.
          move: Hrmap => /=.
          rewrite /rmap_locking.rmap_makelock => [] [] H1 [] H2 H3.
          assert (adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, Ptrofs.unsigned ofs)).
          { split; auto.
            split; omega. }
          destruct H3 as [H3 Hg].
          move: (H3 _ H4)=> [] v [] sh [] Rsh [] HH1 [] Wsh HH2.
          rewrite HH1 in HH.
          destruct HH as [x HH]. simpl in HH2. rewrite Z.sub_diag in HH2.
          clear - MAP HH. rewrite MAP in HH. inv HH.
        }

        { (*invariant ds' *)
          (*But first, a couple facts*)

          assert (H:forall j cntj, i<> j ->
                              joins phi' (@getThreadR _ _ _ j js (MTCH_cnt' MATCH cntj))).
          { (*Will use rmap_locking.rmap_makelock_join*)
            intros j cntj neq.
            assert (Hcmpt':=Hcmpt).
            apply Concur.compatible_threadRes_join  with
            (cnti:= Hi)(cntj0:= (MTCH_cnt' MATCH cntj)) in Hcmpt'; auto.
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
                     lockRes js l = Some (Some pmap) ->
                     joins phi' pmap).
          { (*Will use rmap_locking.rmap_makelock_join*)
            intros l pmap is_lock.
            assert (Hcmpt':=Hcmpt).
            apply Concur.compatible_threadRes_lockRes_join  with
            (cnti:= Hi)(l0:=l)(phi:=pmap) in Hcmpt'; auto.
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
              assert (H0: joins (getThreadR (MTCH_cnt' MATCH cnt))
                            (getThreadR Hi)).
              { eapply Concur.compatible_threadRes_join;
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
              eapply Concur.compatible_threadRes_join; eauto.
            + rewrite setPermBlock_other_2; auto.
              rewrite /pmap_tid.
              rewrite (MTCH_perm2' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply Concur.compatible_threadRes_join; eauto.

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
              assert (H0: joins (getThreadR (MTCH_cnt' MATCH cnt))
                            (getThreadR Hi)).
              { eapply Concur.compatible_threadRes_join;
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
              eapply Concur.compatible_threadRes_join; eauto.
            + rewrite setPermBlock_other_2; auto.
              rewrite /pmap_tid.
              rewrite (MTCH_perm' _ MATCH).
              apply perm_coh_joins.
              apply resource_at_joins.
              eapply Concur.compatible_threadRes_join; eauto.
          - move=> l pmap is_lock.
            assert (is_lock': exists p, lockRes js l = Some p).
            { destruct (lockRes js l) eqn:is_lock'.
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
            assert (is_lock': exists p, lockRes js l = Some p).
            { destruct (lockRes js l) eqn:is_lock'.
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
        11: reflexivity.
        11: reflexivity.
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + reflexivity.
        + eassumption.
        + reflexivity.
        + destruct Hrmap as (_ & _ & Hl & _).
          intros ??.
          specialize (Hl (b, ofs0)) as (? & sh & ? & Hl & ? & _); [split; auto|].
          simpl in Hl.
          unfold Mem.perm; setoid_rewrite restrPermMap_Cur.
          replace (MTCH_cnt _ _) with Htid' by apply proof_irr.
          inv MATCH.
          erewrite <- mtch_perm1; setoid_rewrite Hl; simpl.
          apply perm_of_writable'; auto.
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
        + destruct (lockRes ds (b, Ptrofs.intval ofs)) eqn:AA; auto.
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
          apply Concur.compatible_threadRes_sub with (cnt:=Hi) in juice_join.
          apply resource_at_join_sub with (l:=(b, Ptrofs.unsigned ofs)) in juice_join.
          destruct juice_join as [X HH].
          simpl in H4.
          rewrite H4 in HH.
          hnf in lset_in_juice.
          specialize (lset_in_juice (b, Ptrofs.intval ofs)).
          spec lset_in_juice; auto. destruct lset_in_juice as [sh' ?].
          destruct (H6 0). pose proof LKSIZE_pos; omega. simpl in H7.
          destruct H7 as [psh [P [H7' H7]]].
          rewrite Z.add_0_r in H7; rewrite H7 in HH; inv HH.
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

          pose (pmap_tid  := getThreadR Htid').
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


          pose (ds':= updThread Htid' (Kresume c Vundef) pmap_tid').
          pose (ds'':= remLockSet ds' (b,(Ptrofs.intval ofs))).

          exists ds'', (Events.freelock (b, Ptrofs.intval ofs)).
          split ; [|split].

          unfold ds''; rewrite remLock_updThread_comm.
          pose (ds0:= (remLockSet ds (b, (Ptrofs.intval ofs)))).

          - cut (invariant ds0).
            { (*invariant ds' *)
              (*But first, a couple facts*)

          assert (H:forall j cntj, i<> j ->
                              joins phi' (@getThreadR _ _ _ j js (MTCH_cnt' MATCH cntj))).
          { (*Will use rmap_locking.rmap_makelock_join*)
            move => j cntj neq.
            assert (Hcmpt':=Hcmpt).
            apply Concur.compatible_threadRes_join  with
            (cnti:= Hi)(cntj0:= (MTCH_cnt' MATCH cntj)) in Hcmpt'; auto.
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
                     lockRes js l = Some (Some pmap) ->
                     joins phi' pmap).
          { intros l pmap is_lock.
            assert (Hcmpt':=Hcmpt).
            apply Concur.compatible_threadRes_lockRes_join  with
            (cnti:= Hi)(l0:=l)(phi:=pmap) in Hcmpt'; auto.
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
            assert (is_lock: lockRes ds l =  Some pmap).
            { destruct (AMap.E.eq_dec (b, Ptrofs.intval ofs) l).
                * subst l.
                  rewrite gsslockResRemLock in is_lock0; inversion is_lock0.
                * rewrite gsolockResRemLock in is_lock0; auto. }
            assert (is_lock': exists p, lockRes js l = Some p).
            { destruct (lockRes js l) eqn:is_lock'.
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
            assert (is_lock: lockRes ds l =  Some pmap).
            { destruct (AMap.E.eq_dec (b, Ptrofs.intval ofs) l).
                * subst l.
                  rewrite gsslockResRemLock in is_lock0; inversion is_lock0.
                * rewrite gsolockResRemLock in is_lock0; auto. }
            assert (is_lock': exists p, lockRes js l = Some p).
            { destruct (lockRes js l) eqn:is_lock'.
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

            destruct (lockRes ds (b, Ptrofs.intval ofs)) eqn:is_lock.
            2:{ inversion MATCH.
              specialize (mtch_locks (b, Ptrofs.intval ofs)).
              rewrite is_lock His_acq in mtch_locks.
              inversion mtch_locks.
            }


            econstructor 5. (*The step *)
            13: reflexivity.
            13: reflexivity.
            8: reflexivity.

            + instantiate (1:=pdata) => p.
              rewrite /pdata => -> //.
            + assumption.
            + eapply MTCH_getThreadC; eassumption.
            + reflexivity.
            + eassumption.
            + eassumption.
            + move=> b0 ofs0.
              inversion MATCH;
                specialize (mtch_locksEmpty _ _ His_acq is_lock); rewrite mtch_locksEmpty.
              simpl; rewrite empty_map_spec; split; reflexivity.
            + intros ofs0 ineq.
              rewrite /Mem.perm.
              assert (HH:=@restrPermMap_Cur _ m' (DryHybridMachine.compat_th _ _ (MTCH_compat js ds m' MATCH Hcmpt)
              (MTCH_cnt MATCH Hi)).2 b ofs0).
              unfold permission_at in HH. rewrite HH.
              rewrite -(MTCH_perm2 _ MATCH).
              move: Hrmap  => [] [] H1 [] AA.
              assert (H3: adr_range (b, Ptrofs.unsigned ofs) LKSIZE (b, ofs0)).
              { split; auto. }
              intros [X Hg]; destruct (X _ H3) as (sh & Rsh & _ & Wsh & Heq); clear X.
              rewrite Heq.
              simpl.
                rewrite perm_of_writable.
                (*1*) constructor.
                (*2*) eapply shares.writable_share_glb_Rsh; eauto.
                (*3*) apply shares.glb_Rsh_not_top.
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
          exists ds, (Events.failacq (b, Ptrofs.intval ofs)).
          split ; [|split].
          + assumption.
          + assumption.
          + { econstructor 6.
              + assumption.
              + inversion MATCH; subst.
                rewrite <- (mtch_gtc i Hi).
                eassumption.
              + reflexivity.
              + eassumption.
              + reflexivity.
              + eapply lock_range_perm in HJcanwrite; eauto.
                intros ? H; specialize (HJcanwrite _ H).
                unfold Mem.perm in *; setoid_rewrite restrPermMap_Cur.
                inversion MATCH.
                setoid_rewrite <- mtch_perm2.
                erewrite Concur.juic2Perm_locks_correct
                  by (apply Concur.mem_compat_thread_max_cohere; eauto).
                setoid_rewrite restrPermMap_Cur in HJcanwrite; eauto.
              + erewrite restrPermMap_ext.
                eassumption.
                intros b0.
                inversion MATCH; subst.
                extensionality x.
                rewrite -Concur.juic2Perm_locks_correct.
                symmetry; apply mtch_perm2.
                apply Concur.mem_compat_thread_max_cohere.
                assumption.
            }
        }

        Grab Existential Variables.
        auto.
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
               rewrite -Concur.juic2Perm_locks_correct.
               rewrite -(MTCH_perm2 _ MATCH); auto.
               apply Concur.mem_access_coh_sub with (phi1:=jall).
               assumption.
               eapply Concur.compatible_threadRes_sub; eauto.
             - do 2 (rewrite setPermBlock_other_2; auto).
               destruct Hcmpt as [jall Hcmpt];
               inversion Hcmpt; inversion all_cohere.
               rewrite -Concur.juic2Perm_locks_correct.
               rewrite -(MTCH_perm2 _ MATCH); auto.
               apply Concur.mem_access_coh_sub with (phi1:=jall).
               assumption.
               eapply Concur.compatible_threadRes_sub; eauto.
    }
  Qed.


  (* 'Decaying memory' preserves invariant.
     Note that the invariant doesnt depend on the "core" c.
     so we can cahnge it to any c' 
  *)
  Lemma step_decay_invariant:
    forall (tp : dstate)  (m : Mem.mem) i
      (Hi : containsThread tp i) m1 m1' c'
      (Hinv: invariant tp)
      (Hcompatible: DryHybridMachine.mem_compatible tp m)
      (Hrestrict_pmap :restrPermMap ((DryHybridMachine.compat_th _ _ Hcompatible) Hi).1 = m1)
      (Hdecay: decay m1 m1'),
      invariant
        (updThread Hi (Krun c')
                   (getCurPerm m1', (getThreadR Hi).2)).
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
               (getCurPerm m1) !! b0 ofs0 = (getThreadR Hi).1 !! b0 ofs0).
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
      simpl. apply thread_data_lock_coh0.
    - intros j cnt H b0 ofs0.
      destruct (CASES b0 ofs0) as [PO | NV].
      + eapply perm_coh_lower; [| apply po_refl | eauto].
        rewrite m1_spec.
        inversion Hinv.
        apply thread_data_lock_coh0.
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
      + inversion Hinv. eapply thread_data_lock_coh0; eauto.
      + destruct (CASES b0 ofs0) as [PO | NV].
        * eapply perm_coh_lower; [| apply po_refl | eauto].
          rewrite m1_spec.
          inversion Hinv.
          destruct (locks_data_lock_coh0 _ _ H).
          eapply H0.
        * move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
          => [] _ /(_ l pmap0 H) [] _ -> .
          apply perm_coh_empty_1.
    - move => b0 ofs0.
      destruct (CASES b0 ofs0) as [PO | NV].
      * eapply perm_coh_lower; [| apply po_refl | eauto].
        rewrite m1_spec.
        inversion Hinv.
        destruct (thread_data_lock_coh0 i Hi).
        eapply H.
      * move: (mem_compatible_invalid_block ofs0 Hcompatible NV)
        => [] /(_ i Hi) [] _ -> _.
        apply perm_coh_empty_1.

  Qed.

  Lemma mtch_install_perm:
    forall js ds m m' tid (MATCH : match_st js ds)
      (Hcmpt : mem_compatible js m) (Htid : containsThread js tid)
      (Hperm : install_perm Hcmpt Htid m'),
      DryHybridMachine.install_perm _ _ _ (MTCH_compat _ _ _ MATCH Hcmpt) (MTCH_cnt MATCH Htid) m'.
  Proof.
    simpl; intros; hnf.
    subst.
    unshelve erewrite MTCH_restrict_personal; eauto; simpl.
    { apply Concur.compatible_threadRes_cohere; auto. }
    unfold Concur.install_perm; simpl; f_equal.
    apply proof_irr.
  Qed.

  (* Proof of the smallstep diagram *)
  Lemma core_diagram':
    forall (m : Mem.mem)  (U0 U U': schedule)
      (ds : dstate) dtr (js js': jstate) jtr jtr' rmap pmap
      (m' : Mem.mem),
      match_st js ds ->
      invariant ds ->
      corestep (JMachineSem U0 rmap) (U, jtr, js) m (U', jtr', js') m' ->
      exists (ds' : dstate),
        invariant ds' /\
        match_st js' ds' /\
        exists dtr', corestep (ClightMachineSem U0 pmap) (U, dtr, ds) m (U', dtr ++ dtr', ds') m'.
  Proof.
    intros m U0 U U' ds dtr js js' jtr jtr' rmap pmap m' MATCH dinv.
    unfold JuicyMachine.MachineSemantics; simpl.
    unfold JuicyMachine.MachStep; simpl.
    intros STEP;
      inversion STEP; subst.

    *         (* start_step *)
      { inversion Htstep; subst.
        pose proof MTCH_updt' _ _ _ (Krun c_new) _ MATCH ctn (MTCH_cnt MATCH ctn) Hcmpt (MTCH_compat js ds m MATCH Hcmpt) as MATCH'.
        pose (ds':= (updThread (MTCH_cnt MATCH ctn) (Krun c_new)
          (HybridMachineSig.add_block (MTCH_compat js ds m MATCH Hcmpt) (MTCH_cnt MATCH ctn) m'0))).
        exists ds'.
        assert (DryHybridMachine.invariant ds').
        { eapply step_decay_invariant with (Hcompatible := MTCH_compat _ _ _ MATCH Hcmpt); auto.
          destruct Hinitial as (? & Harg & ?); subst.
          hnf in Hperm; subst.
          split; intros.
          + right; intro. contradiction H0. 
          + apply restrPermMap_valid in H0.
            right; intro. (*rewrite <- Haccess by (right; omega). *)
            unfold Concur.install_perm; destruct k.
            * pose proof restrPermMap_max ((MTCH_compat js ds m MATCH Hcmpt) tid (MTCH_cnt MATCH ctn)).1
                as Hmax1.
              apply equal_f with (b, ofs) in Hmax1.
              pose proof Concur.juicyRestrictMax (Concur.max_acc_coh_acc_coh (Concur.max_coh (Concur.thread_mem_compatible Hcmpt ctn)))
                (b, ofs) as Hmax2.
              unfold max_access_at, access_at in Hmax1, Hmax2; rewrite Hmax1 -Hmax2; auto.
            * destruct (restrPermMap_correct ((MTCH_compat js ds m MATCH Hcmpt) tid (MTCH_cnt MATCH ctn)).1 b ofs) as [_ Hcur1].
              unfold permission_at in Hcur1; rewrite Hcur1.
              pose proof Concur.juicyRestrictCurEq (Concur.max_acc_coh_acc_coh (Concur.max_coh (Concur.thread_mem_compatible Hcmpt ctn)))
                (b, ofs) as Hcur2.
              unfold access_at in Hcur2; rewrite Hcur2.
              inversion MATCH.
              symmetry; apply mtch_perm1. }
        split; auto; split.
        - hnf in Hperm; destruct Hinitial as (? & ? & ?); subst; auto.
        - exists nil; rewrite <- app_nil_end.
          eapply (HybridMachineSig.start_step tid) with (Htid0 := @MTCH_cnt js tid ds MATCH Htid).
          + assumption.
          + { simpl in Hperm; subst.
              econstructor.
              - eapply MTCH_getThreadC. eassumption. eassumption.
              - reflexivity.
              - simpl in *.
                destruct Hinitial as (? & ? & ?); split; eauto.
                split; auto.
                replace Htid with ctn by apply proof_irr.
                remember (Concur.install_perm _ _) as m1.
                apply mtch_install_perm with (ds := ds)(MATCH := MATCH) in Heqm1; hnf in Heqm1.
                rewrite Heqm1 in e; rewrite e; simpl.
                replace Htid with ctn by apply proof_irr; reflexivity.
              - eassumption.
              - replace Htid with ctn by apply proof_irr; reflexivity.
            }
      }

    *          (* resume_step *)
      { inversion MATCH; subst.
        inversion Htstep; subst.
        exists (updThreadC (mtch_cnt _ ctn) (Krun c')).
        split;[|split].
        (*Invariant*)
        { apply updThreadC_invariant; assumption. }
        (*Match *)
        { apply MTCH_updt; assumption.
        }
        (*Step*)
        { exists nil; rewrite <- app_nil_end.
          econstructor 2; try eassumption.
          - simpl. econstructor; try eassumption.
            + apply mtch_install_perm; eauto.
            + setoid_rewrite <- Hcode. symmetry. apply mtch_gtc.
            + reflexivity.
        }
      }

    *          (* core_step *)
      {
        inversion MATCH; subst.
        inversion Htstep; subst.
        assert (Htid':=mtch_cnt _ Htid).


        exists (updThread Htid'
                     (Krun c')
                     (permissions.getCurPerm (m_dry jm'),
                      (getThreadR Htid').2
          (*juice2Perm_locks (m_phi jm') m *) )).
        split ; [|split].
        {
          inversion Hcorestep.
          eapply ev_step_ax2 in H; destruct H as [T H].
          apply ClightSemanticsForMachines.CLN_step_decay in H.
          
          eapply step_decay_invariant
            with (Hcompatible:= MTCH_compat _ _ _ MATCH Hcmpt); try eapply H; eauto.

  (*eapply DSEM.DryHybridMachineLemmas.step_decay_invariant
              with (Hcompatible:= MTCH_compat _ _ _ MATCH Hcmpt); try eapply H; eauto. *)
  eapply MTCH_restrict_personal.
  auto.
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
    apply ClightSemanticsForMachines.CLN_step_decay in H.
    { (*decay preserves lock permissions!!*)
      replace (MTCH_cnt' MATCH Htid') with Htid by apply proof_irrelevance.
      move: H0 => [] [] _ /(_ (b,ofs)) [] A B _.
      destruct B as [B| [B|B]].
      - rewrite - B; simpl.
        destruct ((getThreadR Htid @ (b, ofs))) eqn:HH;
          try rewrite HH; simpl; eauto.
      - destruct B as [rsh [Wsh [v [v' [B1 B2]]]] ].
        rewrite B2.
        simpl in B1.
        destruct (OrdinalPool.getThreadR Htid @ (b, ofs)) eqn:HH;
          try ( try destruct k; simpl in B1; inversion B1).
        rewrite HH; simpl; auto.
      - destruct B as [[M [v B]]|[v[pp [B1 B2]]]].
        + rewrite B; simpl.
          { (* address is not valid so it should be no... with mem compat.*)
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
            eapply Concur.po_join_sub'.
            apply resource_at_join_sub.
            apply Concur.compatible_threadRes_sub; auto.
            apply nextblock_access_empty.
            apply M.
            }
        + rewrite B2 B1; auto. }
}
{  assert (Hcmpt': DryHybridMachine.mem_compatible ds m) by
      (eapply MTCH_compat; eassumption).
   inversion Hcorestep.
   eapply ev_step_ax2 in H.
   destruct H as [T evSTEP].
   exists (map (Events.internal tid) T).
   eapply HybridMachineSig.thread_step; simpl.
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
  exists (updThreadC (mtch_cnt _ ctn) (Kblocked c)).
  split;[|split].
  (*Invariant*)
  { apply updThreadC_invariant ; assumption. }
  (*Match *)
  { apply MTCH_updt; assumption.        }
  (*Step*)
  { exists nil; rewrite <- app_nil_end.
    econstructor 4; try eassumption.
    - simpl. reflexivity.
    - simpl. econstructor; try eassumption.
      + setoid_rewrite <- Hcode. symmetry. apply mtch_gtc.
      + apply mtch_install_perm; eauto.
      + reflexivity.
  }

*  (*Conc step*)
  {
    destruct (sync_step_diagram m m' U js js' ds tid ev MATCH dinv Htid Hcmpt HschedN Htstep)
      as [ds' [ev' [dinv' [MTCH' step']]]]; eauto.
    exists ds'; split; [| split]; try assumption.
    eexists; econstructor 5; simpl; try eassumption.
    reflexivity.
  }

(* *  (* step_halted *)
  exists ds.
  split; [|split].
  { assumption. }
  { assumption. }
  { inversion MATCH; subst.
    assert (Htid':=Htid); apply mtch_cnt in Htid'.
    exists nil; rewrite <- app_nil_end.
    econstructor 6; try eassumption.
    simpl; reflexivity.
    simpl. eapply MTCH_compat; eassumption; instantiate(1:=Htid').
    eapply MTCH_halted; eassumption.
  }*)


*  (* schedfail *)
  { exists ds.
    split;[|split]; try eassumption.
    exists nil; rewrite <- app_nil_end.
    econstructor 6; try eassumption; try reflexivity.
    unfold not; simpl; intros.
    apply Htid. inversion MATCH; apply mtch_cnt'; assumption.
    { eapply MTCH_compat; eassumption. } }

  Grab Existential Variables.
(*  - simpl. apply mtch_cnt. assumption.*)
  - assumption.
  - assumption.
  - assumption.
  Qed.

  Lemma core_diagram:
    forall (m : Mem.mem)  (U0 U U': schedule) rmap pmap
      (ds : dstate) dtr (js js': jstate) jtr jtr'
      (m' : Mem.mem),
      corestep (JMachineSem U0 rmap) (U, jtr, js) m (U', jtr', js') m' ->
      match_st js ds ->
      invariant ds ->
      exists (ds' : dstate),
        invariant ds' /\
        match_st js' ds' /\
        exists dtr', corestep (ClightMachineSem U0 pmap) (U, dtr, ds) m (U', dtr ++ dtr', ds') m'.
  Proof.
    intros. destruct (core_diagram' m U0 U U' ds dtr js js' jtr jtr' rmap0 pmap m' H0 H1 H) as [ds' [A[B C]]].
    exists ds'; split;[|split]; try assumption.
  Qed.


  Lemma halted_diagram:
    forall U ds js rmap pmap,
      fst (fst js) = fst (fst ds) ->
      halted (JMachineSem(ge := ge) U rmap) js = halted (ClightMachineSem(ge := ge) U pmap) ds.
        intros until pmap. destruct ds as [dp ?], js as [jp ?]; destruct dp, jp; simpl; intros HH; rewrite HH.
        reflexivity.
  Qed.

  End Parching.

End Parching.
(*Export Parching.*)
