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
Require Import concurrency.lksize.
Require Import concurrency.permissions.

(*The simulations*)
Require Import sepcomp.wholeprog_simulations.

(*General erasure*)
Require Import concurrency.erasure.

From mathcomp.ssreflect Require Import ssreflect seq.

Import addressFiniteMap.

(* I will import this from CLight once we port it*)
(*Module ClightSEM<: Semantics.
  Definition G:= nat.
  Definition C:= nat.
  Definition M:= Mem.mem.
  Definition  
End ClightSEM.*)

Module ClightParching <: ErasureSig.

  Declare Module ClightSEM: Semantics. (*This will be imported from Clight wonce we port it*)
  Module SCH:= ListScheduler NatTID.            
  Module SEM:= ClightSEM.
  Import SCH SEM.

  Module JSEM:= JuicyMachineShell SEM. (* JuicyMachineShell : Semantics -> ConcurrentSemanticsSig *)
  Module JuicyMachine:= CoarseMachine SCH JSEM. (* CoarseMachine : Schedule -> ConcurrentSemanticsSig -> ConcurrentSemantics *)
  Notation JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=JuicyMachine.SIG.ThreadPool.
  
  Module DSEM:= DryMachineShell SEM.
  Module DryMachine:= CoarseMachine SCH DSEM.
  Notation DMachineSem:= DryMachine.MachineSemantics. 
  Notation dstate:= DryMachine.SIG.ThreadPool.t.
  Notation dmachine_state:= DryMachine.MachState.
  Module DTP:=DryMachine.SIG.ThreadPool.

  (*Parameter parch_state : jstate ->  dstate.*)
  Inductive match_st' : jstate ->  dstate -> Prop:=
    MATCH_ST: forall (js:jstate) ds
                (mtch_cnt: forall {tid},  JTP.containsThread js tid -> DTP.containsThread ds tid )
                (mtch_cnt': forall {tid}, DTP.containsThread ds tid -> JTP.containsThread js tid )
                (mtch_gtc: forall {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    JTP.getThreadC Htid = DTP.getThreadC Htid' )
                (mtch_perm: forall b ofs {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    juicy_mem.perm_of_res (resource_at (JTP.getThreadR Htid) (b, ofs)) = ((DTP.getThreadR Htid') !! b) ofs )
                (mtch_locks: forall a,
                    ssrbool.isSome (JSEM.ThreadPool.lockRes js a) = ssrbool.isSome (DSEM.ThreadPool.lockRes ds a))
                (mtch_locksEmpty: forall lock dres,
                    JSEM.ThreadPool.lockRes js lock = Some (None) -> 
                    DSEM.ThreadPool.lockRes ds lock = Some dres ->
                   dres = empty_map )
                (mtch_locksRes: forall lock jres dres,
                    JSEM.ThreadPool.lockRes js lock = Some (Some jres) -> 
                    DSEM.ThreadPool.lockRes ds lock = Some dres ->
                     forall b ofs,
                    juicy_mem.perm_of_res (resource_at jres (b, ofs)) = (dres !! b) ofs )
                (*mtch_locks: AMap.map (fun _ => tt) (JTP.lockGuts js) = DTP.lockGuts ds*),
      match_st' js ds.
  
  Definition match_st:= match_st'.

  
  (*match axioms*)
  Lemma MTCH_cnt: forall {js tid ds},
           match_st js ds ->
           JTP.containsThread js tid -> DTP.containsThread ds tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt. Qed.
  Lemma MTCH_cnt': forall {js tid ds},
           match_st js ds ->
           DTP.containsThread ds tid -> JTP.containsThread js tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt'. Qed.


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
       
  Lemma MTCH_compat: forall js ds m,
      match_st js ds ->
      JSEM.mem_compatible js m ->
      DSEM.mem_compatible ds m.
  Proof. 
    intros ? ? ? MTCH mc;
    inversion MTCH; subst.
    constructor.
    -intros tid cnt.
     unfold permMapLt; intros b ofs.
     assert (th_coh:= JSEM.thread_mem_compatible mc).
     eapply po_trans.
     specialize (th_coh tid (mtch_cnt' _ cnt)).
     inversion th_coh.
     specialize (acc_coh (b, ofs)).
     rewrite getMaxPerm_correct;
       apply acc_coh.
     
     rewrite (mtch_perm _ _ _ (mtch_cnt' tid cnt) cnt).
     unfold DTP.getThreadR.
     apply po_refl.

    - intros.
      assert(HH: exists jres, JSEM.ThreadPool.lockRes js l = Some jres).
      { specialize (mtch_locks  l); rewrite H in mtch_locks.
      destruct (JSEM.ThreadPool.lockRes js l); try solve[inversion mtch_locks].
      exists l0; reflexivity. }
      destruct HH as [jres HH].
      destruct jres.
      +  specialize (mtch_locksRes _ _ _ HH H).
         intros b ofs.
         rewrite <- mtch_locksRes.
         eapply JSEM.compat_lockLT;
           eassumption.
      + specialize (mtch_locksEmpty _ _ HH H).
         rewrite mtch_locksEmpty.
         apply empty_LT.
    - intros b ofs.
      rewrite DSEM.ThreadPool.lockSet_spec.
      rewrite <- mtch_locks.
      rewrite <- JSEM.ThreadPool.lockSet_spec.
      apply JSEM.compat_lt_m; assumption.
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
      - inversion H0; apply mtch_perm.
      - inversion H0; apply mtch_locks.
      - inversion H0; eapply mtch_locksEmpty; eauto.
      - inversion H0; eapply mtch_locksRes; eauto.
    Qed.

    Lemma restrPermMap_irr:
      forall p1 p2 m1 m2
        (P1: permMapLt p1 (getMaxPerm m1))
        (P2: permMapLt p2 (getMaxPerm m2)),
        p1 = p2 -> m1 = m2 ->
        restrPermMap P1 = restrPermMap P2.
    Proof.
      intros; subst.
      replace P1 with P2.
      reflexivity.
      apply proof_irrelevance.
    Qed.
    Lemma restrPermMap_ext:
      forall p1 p2 m
        (P1: permMapLt p1 (getMaxPerm m))
        (P2: permMapLt p2 (getMaxPerm m)),
        (forall b, (p1 !! b) = (p2 !! b)) ->
        restrPermMap P1 = restrPermMap P2.
    Proof.
      intros; subst.
      remember (restrPermMap P1) as M1.
      remember (restrPermMap P2) as M2.
      assert (Mem.mem_contents M1 = Mem.mem_contents M2) by
          (subst; reflexivity).
      assert (Mem.nextblock M1 = Mem.nextblock M2) by
          (subst; reflexivity).
      assert (Mem.mem_access M1 = Mem.mem_access M2).
      {
        subst. simpl.
        f_equal. f_equal.
        simpl.
        do 4 (apply functional_extensionality; intro).
        destruct x2; try rewrite H; reflexivity. 
      }
      subst.
      destruct (restrPermMap P1);
        destruct (restrPermMap P2); simpl in *.
      subst. f_equal;
      apply proof_irrelevance.
    Qed.
    Print Assumptions restrPermMap_ext.
    
    Lemma MTCH_restrict_personal:
      forall ds js m i
        (MTCH: match_st js ds)
        (Hi: JTP.containsThread js i)
        (Hi': DTP.containsThread ds i)
        (Hcmpt: JSEM.mem_compatible js m)
        (Hcmpt': DSEM.mem_compatible ds m),
        restrPermMap (DSEM.compat_th Hcmpt' Hi') =
        m_dry (JSEM.personal_mem Hi Hcmpt).
    Proof.
      intros.
      inversion MTCH; subst.
      unfold JSEM.personal_mem; simpl; unfold JSEM.juicyRestrict; simpl.
      apply restrPermMap_ext; intros.
      extensionality ofs;
        erewrite <- mtch_perm.
      instantiate(1:=Hi).
      erewrite JSEM.juic2Perm_correct. reflexivity.
      destruct (@JSEM.thread_mem_compatible _ _ Hcmpt _ Hi); assumption.
    Qed.
      
    Lemma MTCH_halted:
      forall ds js i
        (cnt: JTP.containsThread  js i)
        (cnt': DTP.containsThread  ds i),
        match_st js ds->
        JSEM.threadHalted cnt ->
        DSEM.threadHalted cnt'.
    Proof.
      intros.
      inversion H0; subst.
      econstructor.
      admit. (*Do we need this?*)
      inversion H; subst. erewrite <- mtch_gtc. eassumption.
      apply Hcant.
    Admitted.
    
    Lemma MTCH_updLockS:
             forall js ds loc jres dres,
               match_st js ds ->
             (forall b ofs, perm_of_res (jres @ (b, ofs)) = dres !! b ofs) ->
                      match_st
                        (JSEM.ThreadPool.updLockSet js loc (Some jres))
                        (DSEM.ThreadPool.updLockSet ds loc dres).
    Proof. intros.
           constructor.
           + intros. apply DTP.cntUpdateL.
             destruct H; apply mtch_cnt.
             apply JTP.cntUpdateL' in H1; assumption.
           + intros. apply JTP.cntUpdateL.
             destruct H; apply mtch_cnt'.
             apply DTP.cntUpdateL' in H1; assumption.
           + intros. rewrite JSEM.ThreadPool.gLockSetCode DSEM.ThreadPool.gLockSetCode.
             inversion H; subst. apply mtch_gtc. 
           + intros. rewrite JSEM.ThreadPool.gLockSetRes DSEM.ThreadPool.gLockSetRes.
             inversion H; subst. apply mtch_perm.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock DSEM.ThreadPool.gsslockResUpdLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock DSEM.ThreadPool.gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock in H1; inversion H1. 
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H1. rewrite DSEM.ThreadPool.gsolockResUpdLock in H2.
               inversion H. eapply mtch_locksEmpty; eassumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H1.
               rewrite DSEM.ThreadPool.gsslockResUpdLock in H2.
               inversion H1; inversion H2; subst.
               apply H0.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H1. rewrite DSEM.ThreadPool.gsolockResUpdLock in H2.
               inversion H. eapply mtch_locksRes; eassumption.
    Qed.
    
    Lemma MTCH_updLockN:
      forall js ds loc,
        match_st js ds ->
        match_st
          (JSEM.ThreadPool.updLockSet js loc None)
          (DSEM.ThreadPool.updLockSet ds loc empty_map).
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
             inversion H; subst. apply mtch_perm.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResUpdLock DSEM.ThreadPool.gsslockResUpdLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResUpdLock DSEM.ThreadPool.gsolockResUpdLock.
               inversion H. solve[apply mtch_locks].
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite DSEM.ThreadPool.gsslockResUpdLock in H1; inversion H1; reflexivity. 
             * rewrite DSEM.ThreadPool.gsolockResUpdLock in H1.
               rewrite JSEM.ThreadPool.gsolockResUpdLock in H0.
               inversion H. eapply mtch_locksEmpty; eassumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResUpdLock in H0.
               rewrite DSEM.ThreadPool.gsslockResUpdLock in H1.
               inversion H0. 
             * rewrite JSEM.ThreadPool.gsolockResUpdLock in H0. rewrite DSEM.ThreadPool.gsolockResUpdLock in H1.
               inversion H. eapply mtch_locksRes; eassumption.
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
             inversion H; subst. apply mtch_perm.
           + intros.
             destruct (AMap.E.eq_dec loc a) as [EQ | NEQ].
             * subst loc. rewrite JSEM.ThreadPool.gsslockResRemLock DSEM.ThreadPool.gsslockResRemLock.
               reflexivity.
             * rewrite JSEM.ThreadPool.gsolockResRemLock DSEM.ThreadPool.gsolockResRemLock.
               inversion H. solve[apply mtch_locks].
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc. rewrite DSEM.ThreadPool.gsslockResRemLock in H1; inversion H1; reflexivity. 
             * rewrite DSEM.ThreadPool.gsolockResRemLock in H1.
               rewrite JSEM.ThreadPool.gsolockResRemLock in H0.
               inversion H. eapply mtch_locksEmpty; eassumption.
           + intros. 
             destruct (AMap.E.eq_dec loc lock) as [EQ | NEQ].
             * subst loc.
               rewrite JSEM.ThreadPool.gsslockResRemLock in H0.
               rewrite DSEM.ThreadPool.gsslockResRemLock in H1.
               inversion H0. 
             * rewrite JSEM.ThreadPool.gsolockResRemLock in H0. rewrite DSEM.ThreadPool.gsolockResRemLock in H1.
               inversion H. eapply mtch_locksRes; eassumption.
    Qed.
    
    Lemma MTCH_update:
      forall js ds Kc phi p i
        (Hi : JTP.containsThread js i)
        (Hi': DTP.containsThread ds i),
        match_st js ds ->
        ( forall b ofs,
            perm_of_res (phi @ (b, ofs)) = p !! b ofs) -> 
        match_st (JSEM.ThreadPool.updThread Hi  Kc phi)
                 (DSEM.ThreadPool.updThread Hi' Kc p).
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
      - simpl; apply mtch_locks.
      - simpl. eapply mtch_locksEmpty; eassumption.
      - simpl; eapply mtch_locksRes; eassumption.
    Qed.

    Lemma MTCH_initial:
      forall genv c,
        match_st (JSEM.initial_machine c) (DSEM.initial_machine genv c).
    Proof.
      intros.
      constructor.
      - intro i. unfold JTP.containsThread, JSEM.initial_machine; simpl.
        unfold DTP.containsThread, DSEM.initial_machine; simpl.
        trivial.
      - (*Here*)
        intro i. unfold JTP.containsThread, JSEM.initial_machine; simpl.
        unfold DTP.containsThread, DSEM.initial_machine; simpl.
        trivial.
      - reflexivity.
      - intros.
        unfold JTP.getThreadR; unfold JSEM.initial_machine; simpl.
        unfold DTP.getThreadR; unfold DSEM.initial_machine; simpl.
        unfold empty_rmap, "@"; simpl.
        rewrite compcert_rmaps.R.unsquash_squash; simpl.
        destruct (eq_dec Share.bot Share.bot); try solve[exfalso; apply n; reflexivity].
        unfold DSEM.compute_init_perm.
        rewrite empty_map_spec; reflexivity.
      - reflexivity.
      - unfold DSEM.ThreadPool.lockRes, DSEM.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H0; inversion H0.
      - unfold DSEM.ThreadPool.lockRes, DSEM.initial_machine; simpl.
        intros. rewrite threadPool.find_empty in H0; inversion H0.
    Qed.
    
    Variable genv: G.
    Variable main: Values.val.
    Lemma init_diagram:
      forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
        (vals : list Values.val) (m : mem),
        init_inj_ok j m ->
        initial_core (JMachineSem U) genv main vals = Some (U, js) ->
        exists (mu : SM_Injection) (ds : dstate),
          as_inj mu = j /\
          initial_core (DMachineSem U) genv main vals = Some (U, ds) /\
          DSEM.invariant ds /\
          match_st js ds.
    Proof.
      intros.

      (* Build the structured injection*)
      exists (initial_SM (valid_block_dec m) (valid_block_dec m) (fun _ => false) (fun _ => false) j).

      (* Build the dry state *)
      simpl in H0.
      unfold JuicyMachine.init_machine in H0.
      unfold JSEM.init_mach in H0. simpl in H0.
      destruct ( initial_core JSEM.ThreadPool.SEM.Sem genv main vals) eqn:C; try solve[inversion H0].
      inversion H0.
      exists (DSEM.initial_machine genv c).

      split; [|split;[|split]].
      
      (*Proofs*)
      - apply initial_SM_as_inj.
      - simpl.
        unfold DryMachine.init_machine.
        unfold DSEM.init_mach.
        rewrite C.
        f_equal.
      - Lemma initial_invariant: forall genv c,
          DSEM.invariant (DSEM.initial_machine genv c).
            unfold  DSEM.invariant.
            constructor.
            - unfold DSEM.race_free, DSEM.initial_machine; simpl.
              unfold DSEM.ThreadPool.containsThread; simpl.
              intros.
              apply empty_disjoint.
            - intros.
              unfold DSEM.initial_machine; simpl.
              unfold permMapsDisjoint; intros.
              exists ((DSEM.compute_init_perm genv) !! b ofs).
              unfold empty_map.
              unfold PMap.get at 1; simpl. rewrite PTree.gempty.
              reflexivity.
            - unfold DSEM.initial_machine, DSEM.ThreadPool.lockRes, DSEM.ThreadPool.containsThread ; simpl.
              intros. rewrite threadPool.find_empty in H; inversion H.
            - unfold DSEM.initial_machine, DSEM.ThreadPool.lockRes, DSEM.ThreadPool.containsThread ; simpl.
              intros. rewrite threadPool.find_empty in H; inversion H.
        Qed.
        apply initial_invariant.
      - 
        apply MTCH_initial.
    Qed.
            
  Lemma updCinvariant: forall {tid} ds c (cnt: DTP.containsThread ds tid),
      DSEM.invariant ds ->
      DSEM.invariant (DTP.updThreadC cnt c).
        intros ? ? ? ? INV; inversion INV.
        constructor.
        - generalize no_race; unfold DSEM.race_free.
          simpl. intros.
          apply no_race0; auto.
        - simpl; assumption.
        - simpl; assumption.
        - simpl; assumption.
  Qed.
  
  Lemma conc_step_diagram:
    forall m m' U js js' ds i genv
      (MATCH: match_st js ds)
      (dinv: DSEM.invariant ds)
      (Hi: JSEM.ThreadPool.containsThread js i)
      (Hcmpt: JSEM.mem_compatible js m)
      (HschedN: schedPeek U = Some i)
      (Htstep:  JSEM.syncStep genv Hi Hcmpt js' m'),
      exists ds' : dstate,
        DSEM.invariant ds' /\
        match_st js' ds' /\
        DSEM.syncStep genv (MTCH_cnt MATCH Hi) (MTCH_compat _ _ _ MATCH Hcmpt) ds' m'.
  Proof.

    intros.
    inversion Htstep; try subst.
    
    (* step_acquire  *)
    {
    assert (Htid':= MTCH_cnt MATCH Hi).
    pose (inflated_delta:=
            fun loc => match (d_phi @ loc ) with
                      NO s => if Share.EqDec_share s Share.bot then None else Some ( perm_of_res ((m_phi jm') @ loc))
                    | _ => Some (perm_of_res ((m_phi jm') @ loc))
                    end).
         pose (virtue:= PTree.map
                                      (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                                         (inflated_delta (block, ofs))) (snd (getCurPerm m)) ).
         pose (ds':= DSEM.ThreadPool.updThread Htid' (Kresume c Vundef)
                  (computeMap
                     (DSEM.ThreadPool.getThreadR Htid') virtue)).
         pose (ds'':= DSEM.ThreadPool.updLockSet ds'
                      (b, Int.intval ofs) empty_map).
         exists ds''.
         split; [|split].
    - Require Import dry_machine_lemmas.
      unfold ds''.
      Definition permDisjoint p1 p2:=
        exists pu : option permission,
          perm_union p1 p2 = Some pu.
      
      Lemma updLock_inv: forall ds a pmap,
        DSEM.invariant ds ->
        (forall i (cnt: DSEM.ThreadPool.containsThread ds i),
            permDisjoint (Some Writable) ((DTP.getThreadR cnt) # (fst a) (snd a)) ) ->
        (forall i (cnt : DSEM.ThreadPool.containsThread ds i),
            permMapsDisjoint pmap (DSEM.ThreadPool.getThreadR cnt)) ->
        (permMapsDisjoint (DSEM.ThreadPool.lockSet ds) pmap) ->
        (permDisjoint (Some Writable) (pmap # (fst a) (snd a))) ->
        (forall l pmap0, DSEM.ThreadPool.lockRes ds l = Some pmap0 ->
              permDisjoint (Some Writable) (pmap0 # (fst a) (snd a)))->
        DSEM.invariant (DSEM.ThreadPool.updLockSet ds a pmap).
      Proof.
        intros ? ? ? INV A B C D E. constructor.
        - Lemma updLock_raceFree: forall ds a pmap,
            DSEM.race_free ds ->
            DSEM.race_free (DSEM.ThreadPool.updLockSet ds a pmap).
          Proof.
            unfold DSEM.race_free; intros.
            rewrite DTP.gLockSetRes. rewrite DTP.gLockSetRes.
            apply H; assumption.
          Qed.
          apply updLock_raceFree. inversion INV; assumption.
        - intros. rewrite DTP.gLockSetRes.
          Search access_map.
          Lemma lockSet_upd: forall ds b ofs pmap,
              DSEM.ThreadPool.lockSet (DSEM.ThreadPool.updLockSet ds (b, ofs) pmap) =
              setPerm (Some Writable) b ofs (DSEM.ThreadPool.lockSet ds).
          Proof.
            intros.
          Admitted.
          destruct a as [b ofs]; rewrite lockSet_upd.

          Lemma disjoint_add:
            forall p1 p2 b ofs,
              permMapsDisjoint p1 p2 ->
             permDisjoint (Some Writable) ((p2) # b ofs) ->
              permMapsDisjoint ( setPerm (Some Writable) b ofs p1) p2.
          Proof.
            intros. unfold permMapsDisjoint; intros.
          Admitted.
          apply disjoint_add.
          inversion INV; apply lock_set_threads.
          apply A.
        - intros.
          destruct (AMap.E.eq_dec a l).
          + subst.
            rewrite DTP.gssLockRes in H; inversion H; subst.
            rewrite DTP.gLockSetRes. apply B.
          + rewrite DTP.gsoLockRes in H; try solve[assumption].
            inversion INV. eapply lock_res_threads. apply H.
        - intros.
          destruct (AMap.E.eq_dec a l); destruct a.
          + subst.
            rewrite DTP.gssLockRes in H; inversion H; subst.
            rewrite lockSet_upd.
            apply permMapsDisjoint_comm; apply disjoint_add.
            apply C0.
            apply D.
          + rewrite lockSet_upd.
            apply permMapsDisjoint_comm.
              apply disjoint_add.
            * inversion INV. apply permMapsDisjoint_comm. eapply lock_res_set.
              rewrite <- H. symmetry.
              apply DTP.gsoLockRes; assumption.
            * eapply E. rewrite <- H.
              rewrite DTP.gsoLockRes. reflexivity.
              assumption.
      Qed.

      cut (DSEM.invariant ds').
      { intros dinv'.
        apply updLock_inv.
        - assumption. (*Another lemma for invariant.*)
        - cut ( exists p, DSEM.ThreadPool.lockRes ds' (b, Int.intval ofs) = Some p).
          {
            intros HH i0 cnt . destruct HH as [p HH].
          inversion dinv'.
          unfold permMapsDisjoint in lock_set_threads.
          specialize (lock_set_threads i0 cnt b (Int.intval ofs)).
          destruct lock_set_threads as [pu lst].
          rewrite DSEM.ThreadPool.lockSet_spec in lst.
          rewrite HH in lst; simpl in lst.
          generalize lst.
          destruct ((DSEM.ThreadPool.getThreadR cnt) # b (Int.intval ofs)) as [perm|] eqn:AA;
            rewrite AA;  [destruct perm; intros H; try solve[ inversion H] | ]; exists (Some Writable); reflexivity. }
          { inversion MATCH; subst. specialize (mtch_locks (b,Int.intval ofs)).
          rewrite His_unlocked in mtch_locks.
          destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)) eqn: AA; try solve[inversion mtch_locks].
          exists l; assumption. }
        - Lemma empty_disjoint':
            forall pmap,
              permMapsDisjoint empty_map pmap.
                intros pmap b ofs. exists (pmap # b ofs). rewrite empty_map_spec; reflexivity.
          Qed.
          intros. apply empty_disjoint'.
        - apply permMapsDisjoint_comm; apply empty_disjoint'.
        - rewrite empty_map_spec. exists (Some Writable); reflexivity.
        - intros. simpl. inversion dinv'. apply lock_res_set in H.
          apply permMapsDisjoint_comm in H.
          specialize (H b (Int.intval ofs)).
          rewrite DSEM.ThreadPool.lockSet_spec in H.
          cut ( ssrbool.isSome
                  (DSEM.ThreadPool.lockRes ds' (b, Int.intval ofs)) = true ).
          { intros HH. rewrite HH in H. destruct H as [pu H].
            exists (pu); assumption. }
          { inversion MATCH; subst. specialize (mtch_locks (b, Int.intval ofs)).
            rewrite His_unlocked in mtch_locks. 
            rewrite DTP.gsoThreadLPool.
            rewrite <- mtch_locks; reflexivity. }
      }
      { (* Proving: invariant ds*)
        unfold ds'.
        Lemma updThread_inv: forall ds i (cnt: DTP.containsThread ds i) c pmap,
            DSEM.invariant ds ->
            (forall j (cnt: DTP.containsThread ds j),
                i<>j -> permMapsDisjoint pmap (DTP.getThreadR cnt))->
            (permMapsDisjoint (DTP.lockSet ds) pmap) ->
            (forall l pmap0, DTP.lockRes ds l = Some pmap0 -> permMapsDisjoint pmap0 pmap) ->
        DSEM.invariant (DSEM.ThreadPool.updThread cnt c pmap).
        Proof.
          intros ? x ? ? ? INV A B C.
          constructor.
          - unfold DSEM.race_free; intros.
            destruct (NatTID.eq_tid_dec x i); [|destruct (NatTID.eq_tid_dec x j)].
            + subst i.
              rewrite DTP.gssThreadRes.
              rewrite DTP.gsoThreadRes; try solve[assumption].
              assert (cntj':=cntj).
              apply DSEM.ThreadPool.cntUpdate' in cntj'.
              eapply (A); assumption.
            + subst j.
              apply permMapsDisjoint_comm.
              rewrite DTP.gssThreadRes.
              rewrite DTP.gsoThreadRes; try solve[assumption].
              apply A; assumption.
            + rewrite DTP.gsoThreadRes; try solve[assumption].
              rewrite DTP.gsoThreadRes; try solve[assumption].
              inversion INV. apply no_race; assumption.
          - intros. rewrite DTP.gsoThreadLock.
            destruct (NatTID.eq_tid_dec x i).
            + subst x. rewrite DTP.gssThreadRes. apply B.
            + rewrite DTP.gsoThreadRes; try solve[assumption].
              inversion INV. apply lock_set_threads.
          - intros. rewrite DTP.gsoThreadLPool in H.
            destruct (NatTID.eq_tid_dec x i).
            + subst x. rewrite DTP.gssThreadRes. 
              apply (C _ _ H).
            + rewrite DTP.gsoThreadRes; try solve[assumption].
              inversion INV. eapply lock_res_threads; eassumption.
          - intros. rewrite DTP.gsoThreadLPool in H.
            rewrite DTP.gsoThreadLock.
            inversion INV. eapply lock_res_set. eassumption.
        Qed.
        apply updThread_inv.
        - assumption.
        - intros. admit. (*virtue is disjoint from other threads. *)
        - intros. admit. (*virtue is disjoint from lockSet. *)
        - intros. admit. (*virtue disjoint from other lock resources.*)
      }
      - unfold ds''.
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
               unfold max_access_at, PMap.get  in acc_coh; simpl in acc_coh.
               rewrite valb0MEM in acc_coh.
               simpl in acc_coh.
               rewrite mtch_perm in acc_coh.
               rewrite JSEM.Mem_canonical_useful in acc_coh. destruct (o ofs0); try solve[inversion acc_coh].
               + (*Some 1.1*)
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
                 unfold max_access_at, PMap.get  in acc_coh0; simpl in acc_coh0.
                 rewrite valb0MEM in acc_coh0.
                 rewrite JSEM.Mem_canonical_useful in acc_coh0.
                 destruct (perm_of_res (d_phi @ (b0, ofs0))); try solve[inversion acc_coh0].
                 reflexivity.

               + (*None 1.2*)
                 Lemma threads_canonical:
                   forall ds m i (cnt:DSEM.ThreadPool.containsThread ds i),
                     DSEM.mem_compatible ds m ->  
                     isCanonical (DSEM.ThreadPool.getThreadR cnt).
                       intros.
                       inversion H; clear compat_lp compat_ls.
                       specialize (compat_th i cnt); apply canonical_lt in compat_th.
                       assumption.
                 Qed.
                 apply (MTCH_compat _ _ _ MATCH) in Hcompatible.
                 rewrite (threads_canonical _ m _ Htid'); [|eapply MTCH_compat; eassumption].
                 replace (m_phi jm' @ (b0, ofs0)) with (NO Share.bot).
                 simpl.
                 rewrite if_true; reflexivity.
                 apply (resource_at_join _ _ _ (b0, ofs0)) in Hadd_lock_res.
                 replace (JSEM.ThreadPool.getThreadR Hi @ (b0, ofs0)) with (NO Share.bot) in Hadd_lock_res.
                 replace (d_phi @ (b0, ofs0)) with (NO Share.bot) in Hadd_lock_res.
                 - apply join_unit1_e in Hadd_lock_res.
                 assumption.
                 apply NO_identity.
                 - clear Hadd_lock_res.
                   symmetry.
                   Lemma compatible_lockRes_cohere: forall js m l phi,
                       JSEM.ThreadPool.lockRes js l = Some (Some phi) ->
                       JSEM.mem_compatible js m ->
                       JSEM.mem_cohere' m phi .
                   Proof.
                     Lemma compatible_lockRes_sub: forall js m l phi,
                       JSEM.ThreadPool.lockRes js l = Some (Some phi) ->
                       forall compat:JSEM.mem_compatible js m,
                       join_sub phi 
                   
                   unfold d_phi.
                 unfold sepalg.join in Hadd_lock_res.
                 ShareMap.join_lifted.
                 res_option_join

                   Focus 2. reflexivity.
                         
                 
                 unfold sepalg.join, Join_rmap in Hadd_lock_res. 
                       
                 admit. (*We know both sides are None, because of mem_compatible, the join and because 
                         mem is None at that point, so it tricles down. *)
           }
           
           assert (H: exists l, DSEM.ThreadPool.lockRes ds (b, Int.intval ofs) = Some l).
           { inversion MATCH; subst.
             specialize (mtch_locks (b, (Int.intval ofs) )).
             rewrite His_unlocked in mtch_locks.
             destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)); try solve[inversion mtch_locks]. exists l; reflexivity. }
           destruct H as [l dlockRes].
         - econstructor 1.
           + assumption.
           + eapply MTCH_getThreadC; eassumption.
           + eassumption.
           + eapply MTCH_compat; eassumption.
           + instantiate(1:=(restrPermMap
               (JSEM.mem_compatible_locks_ltwritable Hcompatible))). 
             apply restrPermMap_ext.
             intros b0.
             inversion MATCH; subst.
             admit. (*This should follow from mtch_locks*)
           + assumption.
           + assumption.
           + exact dlockRes.
           + Focus 2. reflexivity.
           + Focus 2. unfold ds'', ds'.
             replace (MTCH_cnt MATCH Hi) with Htid'.
             reflexivity.
             apply proof_irrelevance.
           + admit. (*angelSpec!!! *)
    }  
    
    (* step_release *)
    {
      
    assert (Htid':= MTCH_cnt MATCH Hi).
    pose (inflated_delta:=
            fun loc => match (d_phi @ loc ) with
                      NO s => if Share.EqDec_share s Share.bot then None else Some ( perm_of_res ((m_phi jm') @ loc))
                    | _ => Some (perm_of_res ((m_phi jm') @ loc))
                    end).
         pose (virtue:= PTree.map
                                      (fun (block : positive) (_ : Z -> option permission) (ofs : Z) =>
                                         (inflated_delta (block, ofs))) (snd (getCurPerm m)) ).
         pose (ds':= DSEM.ThreadPool.updThread Htid' (Kresume c Vundef)
                  (computeMap
                     (DSEM.ThreadPool.getThreadR Htid') virtue)).
         pose (ds'':= DSEM.ThreadPool.updLockSet ds' (b, Int.intval ofs)
              (JSEM.juice2Perm d_phi m)).
         exists ds''.
         split; [|split].
    - admit. (*Nick has this proof somewhere. *)
    - unfold ds''.
      apply MTCH_updLockS.
      Focus 2. inversion MATCH; subst.
      intros; apply JSEM.juic2Perm_correct.
      admit. (*lock resources cohere. We know this.*)
      unfold ds'.
      apply MTCH_update; auto.
      intros.
      (*This is going tot ake some work. If its false the definitions can easily change. *)
      admit.

      assert (H: exists l, DSEM.ThreadPool.lockRes ds (b, Int.intval ofs) = Some l).
      { inversion MATCH; subst.
        specialize (mtch_locks (b, (Int.intval ofs) )).
        rewrite His_locked in mtch_locks.
        destruct (DSEM.ThreadPool.lockRes ds (b, Int.intval ofs)); try solve[inversion mtch_locks]. exists l; reflexivity. }
           destruct H as [l dlockRes].
    - econstructor 2.
      + assumption.
      + eapply MTCH_getThreadC; eassumption.
      + eassumption.
(*      + eapply MTCH_compat; eassumption. *)
      + instantiate(1:=(restrPermMap
               (JSEM.mem_compatible_locks_ltwritable Hcompatible))). 
             apply restrPermMap_ext.
             intros b0.
             inversion MATCH; subst.
             admit. (*This should follow from mtch_locks*)
      + assumption.
      + assumption.
      + exact dlockRes.
      + Focus 2. reflexivity.
      + Focus 2. unfold ds'', ds'. 
        replace (MTCH_cnt MATCH Hi) with Htid'.
        reflexivity.
        apply proof_irrelevance.
      + admit. (*angelSpec!!!*)
    }

    (* step_create *)
    { 

      (* This step needs a complete overhaul!*)
      (* Will work on this once all other steps are 'reliably' proven. *)
      admit.
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

      exists ds''.
      split ; [|split].
      - admit. (*Nick has this proof somewhere. *)
      - rewrite Htp''; unfold ds''.
        apply MTCH_updLockN.
        rewrite Htp'; unfold ds'.
        apply MTCH_update.
        assumption.

        (* Now I prove the map construction is correct*)
        {
          inversion MATCH; subst js0 ds0.
          unfold pmap_tid', pmap_tid.
          intros.
          (*unfold setPerm.*)
          destruct (ident_eq b0 b). rewrite e.
          + (*I consider three cases:
             * ofs = ofs0 
             * 0 < ofs0 - ofs < LOCKSIZE 
             * ~ 0 < ofs0 - ofs <= LOCKSIZE
             *)
            admit. (*This should come from the specification of setPermBlock. *)
            (* destruct (Intv.In_dec (ofs0 - (Int.intval ofs))%Z (0, LKSIZE));
              [ destruct (zeq (Int.intval ofs) ofs0)| ].
            * (* ofs = ofs0 *)
              rewrite e0 in Hlock. 
              rewrite Hlock; reflexivity.
            * (* n0 < ofs0 - ofs < LOCKSIZE *)
              move Hct at bottom. 
              rewrite Hct.
              simpl.
              { 
                destruct i0 as [lineq rineq]; simpl in lineq, rineq.
                split; try assumption.
                apply Z.le_neq; split; [assumption  |].
                unfold not; intros HH; apply n; symmetry.
                apply Zminus_eq; symmetry.
                exact HH. }
            
          * erewrite <- Hj_forward. *)
          + admit. (*again this comes from the specification of setPermBlock with b<>b0*)
        }
        
      - econstructor 4. (*The step *)
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + eassumption.
        (*      + eapply MTCH_compat; eassumption. *)
        + instantiate(1:= m_dry jm).
          subst tp''.
          rewrite <- Hpersonal_perm.
          erewrite <- (MTCH_restrict_personal ).
          reflexivity.
          assumption.
        + rewrite <- Hright_juice; assumption.
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
      pose (pmap_tid  := DTP.getThreadR Htid').
       pose (pmap_tid' := setPermBlock (Some (WorF sh)) b (Int.intval ofs) pmap_tid LKSIZE_nat).
(*      pose (pmap_tid' := (setPermBlock (Some (WorF sh)) b (Int.intval ofs)
           (DSEM.ThreadPool.getThreadR Htid') LKSIZE_nat)))*)
      
      
      pose (ds':= DTP.updThread Htid' (Kresume c Vundef) pmap_tid').
      pose (ds'':= DTP.remLockSet ds' (b,(Int.intval ofs))).

      exists ds''.
      split ; [|split].
      - admit. (*Nick has this proof somewhere. *)
      - unfold ds''.
        apply MTCH_remLockN.
        unfold ds'.
        apply MTCH_update.
        assumption.

        (* Now I prove the map construction is correct*)
        {
          admit.
        }
        
      - econstructor 5. (*The step *)
        
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + eassumption.
        (*      + eapply MTCH_compat; eassumption. *)
        + instantiate(2:= Some (WorF sh) ). reflexivity.
        + reflexivity.
        + unfold ds'',  ds'.
        + replace (MTCH_cnt MATCH Hi) with Htid'.
          reflexivity. 
          apply proof_irrelevance.
          assumption.
    }

    (* step_acqfail *)
    {
      exists ds.
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
            admit. (*This should follow from mtch_locks. Just like in release*)
        }
    }
  Admitted.

    

  
  Lemma core_diagram':
    forall (m : mem)  (U0 U U': schedule) 
     (ds : dstate) (js js': jstate) 
     (m' : mem),
   match_st js ds ->
   DSEM.invariant ds ->
   corestep (JMachineSem U0) genv (U, js) m (U', js') m' ->
   exists (ds' : dstate),
     DSEM.invariant ds' /\
     match_st js' ds' /\
     corestep (DMachineSem U0) genv (U, ds) m (U', ds') m'.
       intros m U0 U U' ds js js' m' MATCH dinv.
       unfold JuicyMachine.MachineSemantics; simpl.
       unfold JuicyMachine.MachStep; simpl.
       intros STEP;
         inversion STEP; subst.
      
       (* start_step *)
       admit.
       
       (* resume_step *)
       inversion MATCH; subst.
       inversion Htstep; subst.
       exists (DTP.updThreadC (mtch_cnt _ ctn) (Krun c')).
       split;[|split].
       (*Invariant*)
       { apply updCinvariant; assumption. }
       (*Match *)
       { (*This should be a lemma *)
         constructor.
         - intros. apply DTP.cntUpdateC. apply mtch_cnt. eapply JTP.cntUpdateC'. eassumption.
         - intros. apply JTP.cntUpdateC. apply mtch_cnt'. eapply DTP.cntUpdateC'. eassumption.
         - intros. destruct (NatTID.eq_tid_dec tid0 tid).
           + subst. rewrite JTP.gssThreadCC DTP.gssThreadCC. reflexivity.
           +  assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
              assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
             rewrite <- (JTP.gsoThreadCC (not_eq_sym n) ctn jcnt2 _  Htid0) by auto.
             rewrite <- (DTP.gsoThreadCC (not_eq_sym n) _   dcnt2 _  Htid') by auto.
             apply mtch_gtc.
         - intros.
           assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
           assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
           rewrite (JTP.gThreadCR _ jcnt2).
           rewrite (DTP.gThreadCR _ dcnt2).
           apply mtch_perm.
         -  admit. (*Locks 1*)
         -  admit. (*Locks 1*) 
       }
       
       (*Step*)
       { econstructor 2; try eassumption.
         - simpl. eapply MTCH_compat; eassumption.
         - simpl. econstructor; try eassumption.
           + rewrite <- Hcode. symmetry. apply mtch_gtc.
           + reflexivity.
       }

       
       (* core_step *)
       {
         inversion MATCH; subst.
         inversion Htstep; subst.
         assert (Htid':=mtch_cnt _ Htid).
         exists (DTP.updThread Htid' (Krun c') (permissions.getCurPerm (m_dry jm'))).
         split ; [|split].
         { generalize dinv.
           (*Nick has this proof somewhere. *)
           admit.
         }
         { apply MTCH_update.
           assumption.
           intros.
           assert (HH:= juicy_mem_access jm').
           rewrite <- HH.
           rewrite getCurPerm_correct.
           reflexivity.
         }
         {  assert (Hcmpt': DSEM.mem_compatible ds m) by
               (eapply MTCH_compat; eassumption).

           econstructor; simpl.
           - eassumption.
           - econstructor; try eassumption.
             Focus 4. reflexivity.
             Focus 2. eapply (MTCH_getThreadC _ _ _ _ _ _ _ Hthread).
             Focus 2.
             simpl.
             inversion Hcorestep. apply H.
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
       { constructor.
         - intros. apply DTP.cntUpdateC. apply mtch_cnt. eapply JTP.cntUpdateC'. eassumption.
         - intros. apply JTP.cntUpdateC. apply mtch_cnt'. eapply DTP.cntUpdateC'. eassumption.
         - intros. destruct (NatTID.eq_tid_dec tid0 tid).
           + subst.
             rewrite JTP.gssThreadCC DTP.gssThreadCC; reflexivity.
           + assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
             assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
             rewrite <- (JTP.gsoThreadCC (not_eq_sym n) ctn jcnt2 _  Htid0) by auto.
             rewrite <- (DTP.gsoThreadCC (not_eq_sym n) (mtch_cnt tid ctn) dcnt2 _ Htid') by auto.
             apply mtch_gtc.
         - intros.
           assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
           assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
           rewrite (JTP.gThreadCR _ jcnt2).
           rewrite (DTP.gThreadCR _ dcnt2).
           apply mtch_perm.
         - admit. (* Locks1*)
         - admit. (* Locks2*)
       }
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
         destruct (conc_step_diagram m m' U js js' ds tid genv MATCH dinv Htid Hcmpt HschedN Htstep)
           as [ds' [dinv' [MTCH' step']]]; eauto.
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
  Admitted.

  Lemma core_diagram:
    forall (m : mem)  (U0 U U': schedule) 
     (ds : dstate) (js js': jstate) 
     (m' : mem),
   corestep (JMachineSem U0) genv (U, js) m (U', js') m' ->
   match_st js ds ->
   DSEM.invariant ds ->
   exists (ds' : dstate),
     DSEM.invariant ds' /\
     match_st js' ds' /\
     corestep (DMachineSem U0) genv (U, ds) m (U', ds') m'.
  Proof.
    intros. destruct (core_diagram' m U0 U U' ds js js' m' H0 H1 H) as [ds' [A[B C]]].
    exists ds'; split;[|split]; try assumption.
  Qed.

  
  Lemma halted_diagram:
    forall U ds js,
      fst js = fst ds ->
      halted (JMachineSem U) js = halted (DMachineSem U) ds.
        intros until js. destruct ds, js; simpl; intros HH; rewrite HH.
        reflexivity.
  Qed.

End ClightParching.
Export ClightParching.

Module ClightErasure:= ErasureFnctr ClightParching.


(** BEHOLD THE THEOREM :) *)
(*Just to be explicit*)


Theorem clight_erasure:
  forall U : DryMachine.Sch,
       Wholeprog_sim.Wholeprog_sim (JMachineSem U) 
         (DMachineSem U) ClightParching.genv ClightParching.genv ClightParching.main ClightErasure.ge_inv
         ClightErasure.init_inv ClightErasure.halt_inv.
Proof.
  Proof. apply ClightErasure.erasure. Qed.
