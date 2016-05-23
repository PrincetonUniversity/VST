Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import concurrency.concurrent_machine.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.dry_machine. Import Concur.

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
                (mtch_locks: forall b ofs, ssrbool.isSome (AMap.find (b,ofs) (JTP.lockSet js) ) = ssrbool.isSome ((DTP.lockSet ds) !! b ofs ) ),
      match_st' js ds. (*Missing match locked/unlockde locks. Do we need?*)
  
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
     unfold permissions.permMapLt; intros b ofs.
     assert (th_coh:= JSEM.thread_mem_compatible mc).
     eapply po_trans.
     specialize (th_coh tid (mtch_cnt' _ cnt)).
     inversion th_coh.
     specialize (acc_coh (b, ofs)).
     rewrite permissions.getMaxPerm_correct;
       apply acc_coh.
     
     rewrite (mtch_perm _ _ _ (mtch_cnt' tid cnt) cnt).
     unfold DTP.getThreadR.
     apply permissions.po_refl.

    - inversion mc.
      admit.
  Admitted.
      
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
    Qed.

    Lemma restrPermMap_irr:
      forall p1 p2 m1 m2
        (P1: permissions.permMapLt p1 (permissions.getMaxPerm m1))
        (P2: permissions.permMapLt p2 (permissions.getMaxPerm m2)),
        p1 = p2 -> m1 = m2 ->
        permissions.restrPermMap P1 = permissions.restrPermMap P2.
    Proof.
      intros; subst.
      replace P1 with P2.
      reflexivity.
      apply proof_irrelevance.
    Qed.
    Lemma restrPermMap_ext:
      forall p1 p2 m
        (P1: permissions.permMapLt p1 (permissions.getMaxPerm m))
        (P2: permissions.permMapLt p2 (permissions.getMaxPerm m)),
        (forall b, (p1 !! b) = (p2 !! b)) ->
        permissions.restrPermMap P1 = permissions.restrPermMap P2.
    Proof.
      intros; subst.
      remember (permissions.restrPermMap P1) as M1.
      remember (permissions.restrPermMap P2) as M2.
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
      destruct (permissions.restrPermMap P1);
        destruct (permissions.restrPermMap P2); simpl in *.
      subst. f_equal;
      apply proof_irrelevance.
    Qed.
    
    Lemma MTCH_restrict_personal:
      forall ds js m i
        (MTCH: match_st js ds)
        (Hi: JTP.containsThread js i)
        (Hi': DTP.containsThread ds i)
        (Hcmpt: JSEM.mem_compatible js m)
        (Hcmpt': DSEM.mem_compatible ds m),
        permissions.restrPermMap (DSEM.compat_th Hcmpt' Hi') =
        m_dry (JSEM.personal_mem Hi Hcmpt).
    Proof.
      intros.
      inversion MTCH; subst.
      unfold JSEM.personal_mem; simpl; unfold JSEM.juicyRestrict; simpl.
      apply restrPermMap_ext; intros.
      extensionality ofs;
        erewrite <- mtch_perm.
      instantiate(1:=Hi).
      Lemma juic2Perm_correct:
        forall r m b ofs,
          JSEM.access_cohere' m r ->
          perm_of_res (r @ (b,ofs)) = (JSEM.juice2Perm r m) !! b ofs.
      Proof.
        intros.
        unfold JSEM.juice2Perm, JSEM.mapmap.
        unfold PMap.get; simpl.
        rewrite PTree.gmap. 
        rewrite PTree.gmap1; simpl.
        destruct ((snd (Mem.mem_access m)) ! b) eqn:search; simpl.
        - auto.
        - generalize (H (b, ofs)).
          unfold max_access_at, PMap.get; simpl.
          rewrite search. rewrite JSEM.Mem_canonical_useful.
          unfold perm_of_res. destruct ( r @ (b, ofs)).
          destruct (eq_dec t Share.bot); auto; simpl.
          intros HH. contradiction HH.
          destruct k;  try solve [intros HH;inversion HH].
          destruct (perm_of_sh t (pshare_sh p)); auto.
          intros HH;inversion HH.
          intros HH;inversion HH.
      Qed.
      erewrite juic2Perm_correct. reflexivity.
      destruct (@JSEM.thread_mem_compatible _ _ Hcmpt _ Hi); assumption.
    Qed.
      
    Lemma MTCH_halted:
      forall ds js i
        (cnt: JTP.containsThread  js i)
        (cnt': DTP.containsThread  ds i),
        match_st js ds->
        JSEM.threadHalted cnt ->
        DSEM.threadHalted cnt'.
    Admitted.

    Lemma MTCH_updLock:
      forall js ds loc r, 
        match_st js ds ->
        (AMap.In loc (JTP.lockSet js)) ->
        match_st (JTP.updLockSet js (AMap.add loc r (JTP.lockSet js))) ds.
          intros. inversion H; subst.
          constructor; auto.
          - intros.
            simpl.
            Lemma mem_find_add: forall elt (t: AMap.t elt) k x,
                AMap.In k t ->
                ssrbool.isSome
                  (AMap.find k (AMap.add k x t))=
                ssrbool.isSome
                  (AMap.find k t).
            Proof.
              intros. destruct (AMap.find (elt:=elt) k t) eqn:XX.
              apply AMap.find_2 in XX.
              assert (Hx: k = k); auto.
              pose (HH:=@AMap.add_1 _ t k k x Hx).
              apply AMap.find_1 in HH.
              rewrite HH. reflexivity.
              Import AMap.
              unfold AMap.In in H.
              unfold Raw.PX.In in H.
              destruct H as [e MT].
              rewrite (AMap.find_1 MT) in XX. inversion XX.
            Qed.
            Lemma mem_find_add': forall elt (t: AMap.t elt) k1 k2 x,
                k1 <> k2 ->
                AMap.In k1 t ->
                ssrbool.isSome
                  (AMap.find k2 (AMap.add k1 x t))=
                ssrbool.isSome
                  (AMap.find k2 t).
            Proof.
              intros ? t ? ?  ? ? ?.
              destruct (AMap.find (elt:=elt) k2 t) eqn:XX.
              apply AMap.find_2 in XX.
              pose (HH:=@AMap.add_2 _ t k1 k2 e x H).
              apply AMap.find_1 in HH.
              rewrite HH. reflexivity.
              auto.

              destruct (find k2 (add k1 x t)) eqn:B; try reflexivity.
              apply find_2 in B. apply add_3 in B; auto.
              apply find_1 in B; rewrite B in XX.
              inversion XX.
            Qed.
            destruct (EqDec_address loc (b,ofs)).
          - subst. rewrite mem_find_add; auto.
          - rewrite mem_find_add'; auto.
    Qed.
    Lemma MTCH_addLock:
      forall js ds b ofs r, 
        match_st js ds ->
        match_st (JTP.updLockSet js (AMap.add (b, ofs) r (JTP.lockSet js)))
         (DTP.updLockSet ds (permissions.setPerm (Some Writable) b ofs (DTP.lockSet ds))).
    intros. inversion H; subst.
    constructor; auto.
    - intros.
      simpl.
      admit.
    Admitted.
    Lemma MTCH_remLock:
      forall js ds b ofs, 
        match_st js ds ->
        match_st (JTP.updLockSet js (AMap.remove (b, ofs) (JTP.lockSet js)))
         (DTP.updLockSet ds (permissions.setPerm None b ofs (DTP.lockSet ds))).
    intros. inversion H; subst.
    constructor; auto.
    - intros.
      simpl.
      admit.
    Admitted.
            
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
    Qed.
    
    Variable genv: G.
    Variable main: Values.val.
    Lemma init_diagram:
      forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
        (vals : list Values.val) (m : M),
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
      - unfold  DSEM.invariant.
        constructor.
        + unfold DSEM.race_free, DSEM.initial_machine; simpl.
          unfold DSEM.ThreadPool.containsThread; simpl.
          intros.
          admit. (*This will change once [compute_init_perm] is well defined. *)
        (*apply permissions.empty_disjoint.*)
        + (*Again, this might change*)
          intros.
          unfold DSEM.initial_machine; simpl.
          unfold permissions.permMapsDisjoint; intros.
          exists ((DSEM.compute_init_perm genv) !! b ofs).
          unfold permissions.empty_map.
          unfold PMap.get at 1; simpl. rewrite PTree.gempty.
        reflexivity.
      - (*This should be easy, but it will slightly change once we fix MATCH and initial*)
      admit.
  Admitted.

  Lemma updCinvariant: forall {tid} ds c (cnt: DTP.containsThread ds tid),
      DSEM.invariant ds ->
      DSEM.invariant (DTP.updThreadC cnt c).
        intros ? ? ? ? INV; inversion INV.
        constructor.
        - generalize no_race; unfold DSEM.race_free.
          simpl. intros.
          apply no_race0; auto.
        - intros; simpl. apply lock_pool.
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
    inversion Htstep; subst.
    
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
                                          (inflated_delta (block, ofs))) (snd (permissions.getCurPerm m)) ).
         exists (DSEM.ThreadPool.updThread Htid' (Kresume c)
                  (permissions.computeMap
                     (DSEM.ThreadPool.getThreadR Htid') virtue)).
         split; [|split].
         
         - admit. (*Nick has this proof somewh
ere. *)
         - apply MTCH_updLock.
           apply MTCH_update; auto.
           intros.
           (*This is going to take some work. If its false the definitions can easily change. *)
           admit.
           destruct Hcmpt.
           unfold JSEM.locks_correct in loc_set_ok.
           apply (JSEM.join_geq(all_juice:=all_juice)) in HJcanwrite; auto.
           apply loc_set_ok in HJcanwrite.
           clear -HJcanwrite.
           destruct (find (b, Int.intval ofs)
                          (JSEM.ThreadPool.lockSet js)) eqn:B.
           + apply (find_2 ) in B.
             exists o; auto.
           + inversion HJcanwrite.
         - econstructor 1.
           + assumption.
           + eapply MTCH_getThreadC; eassumption.
           + eassumption.
           + eapply MTCH_compat; eassumption.
           + inversion MATCH; subst.
             rewrite <- mtch_locks.
             destruct Hcmpt.
             unfold JSEM.locks_correct in loc_set_ok.
             eapply loc_set_ok.
             eapply JSEM.join_geq; eassumption.
           + reflexivity.
           + assumption.
           + assumption.
           + instantiate(1:=virtue).
             replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
             reflexivity.
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
                                          (inflated_delta (block, ofs))) (snd (permissions.getCurPerm m)) ).
         exists (DSEM.ThreadPool.updThread Htid' (Kresume c)
                  (permissions.computeMap
                     (DSEM.ThreadPool.getThreadR Htid') virtue)).
         split; [|split].
    - admit. (*Nick has this proof somewhere. *)
    - apply MTCH_updLock.
      apply MTCH_update; auto.
      intros.
      (*This is going tot ake some work. If its false the definitions can easily change. *)
      admit.

      destruct Hcmpt.
      unfold JSEM.locks_correct in loc_set_ok.
      
      
      (*HERE *)
      apply (JSEM.join_geq(all_juice:=all_juice)) in HJcanwrite; auto.
      apply loc_set_ok in HJcanwrite.
      clear -HJcanwrite.
      destruct (find (b, Int.intval ofs)
                     (JSEM.ThreadPool.lockSet js)) eqn:B.
      + apply (find_2 ) in B.
        exists o; auto.
      + inversion HJcanwrite.
    - econstructor 2.
      + assumption.
      + eapply MTCH_getThreadC; eassumption.
      + eassumption.
(*      + eapply MTCH_compat; eassumption. *)
      + inversion MATCH; subst.
        rewrite <- mtch_locks.
        destruct Hcmpt.
        unfold JSEM.locks_correct in loc_set_ok.
        eapply loc_set_ok.
        eapply JSEM.join_geq; eassumption.
      + reflexivity.
      + assumption.
      + assumption.
      + instantiate(1:=virtue).
        replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
        reflexivity.
    }

    (* step_create *)
    { (* This step needs a complete overhaul!*)
      (* Will work on this once all other steps are 'reliably' proven. *)
      admit.
    }

    
    (* step_mklock *)
    { 
      assert (Htid':= MTCH_cnt MATCH Hi).
     (* (Htp': tp' = updThread cnt0 (Kresume c) pmap_tid')
            (Htp'': tp'' = updLockSet tp' pmap_lp), *)
      pose (pmap_tid  := DTP.getThreadR Htid').
      pose (pmap_tid' := permissions.setPerm (Some Nonempty) b (Int.intval ofs) pmap_tid).
      pose (pmap_lp   := permissions.setPerm (Some Writable) b (Int.intval ofs)
                                               (DTP.lockSet ds)).
      
      
      exists (DTP.updLockSet (DTP.updThread Htid' (Kresume c) pmap_tid' ) pmap_lp).
      split ; [|split].
      - admit. (*Nick has this proof somewhere. *)
      - unfold pmap_lp.
        erewrite <- DTP.gsoThreadLock.
        apply MTCH_addLock. 
        apply MTCH_update; auto.
        intros.
        
        (*This is going tot ake some work. If its false the definitions can easily change. *)
        admit.
      - econstructor 4. (*The step *)
        + assumption.
        + eapply MTCH_getThreadC; eassumption.
        + eassumption.
        (*      + eapply MTCH_compat; eassumption. *)
        + inversion MATCH; subst.
          rewrite <- mtch_locks.
          destruct Hcmpt.
          unfold JSEM.locks_correct in loc_set_ok.
          eapply loc_set_ok.
          eapply JSEM.join_geq; eassumption.
        + reflexivity.
        + assumption.
        + assumption.
        + instantiate(1:=virtue).
          replace (MTCH_cnt MATCH Hi) with Htid' by apply proof_irrelevance.
          reflexivity.
    }

    (* step_freelock *)
    { admit. }

    (* step_acqfail *)
    { admit. }
  Admitted.

    

  
  Lemma core_diagram':
    forall (m : M)  (U0 U U': schedule) 
     (ds : dstate) (js js': jstate) 
     (m' : M),
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
      
       
       (* resume_step *)
       inversion MATCH; subst.
       inversion Htstep; subst.
       exists (DTP.updThreadC (mtch_cnt _ ctn) (Krun c')).
       split;[|split].
       (*Invariant*)
       { apply updCinvariant; assumption. }
       (*Match *)
       { constructor.
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
         -  admit. (*Locks cohere*)
       }
       (*Step*)
       { econstructor 1; try eassumption.
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
         { constructor.
           - simpl; intros.
             apply DTP.cntUpdate. apply mtch_cnt.
             eapply JTP.cntUpdate'; eassumption.
           - simpl; intros.
             apply JTP.cntUpdate. apply mtch_cnt'.
             eapply DTP.cntUpdate'; eassumption.
           - intros. destruct (NatTID.eq_tid_dec tid0 tid).
             + subst. rewrite JTP.gssThreadCode DTP.gssThreadCode; reflexivity.
             + assert (jcnt2:= JTP.cntUpdateC' (Krun c') Htid Htid0).
               assert (dcnt2:= DTP.cntUpdateC' (Krun c') Htid' Htid'0).
               assert (Hn: tid <> tid0) by auto.
             rewrite (JTP.gsoThreadCode Hn Htid jcnt2 _ _ Htid0); auto.
             rewrite (DTP.gsoThreadCode Hn Htid' dcnt2 _ _ Htid'0); auto.
             (*apply mtch_gtc.*)

           -  intros. destruct (NatTID.eq_tid_dec tid0 tid).
              + subst. rewrite JTP.gssThreadRes DTP.gssThreadRes.
                simpl. rewrite permissions.getCurPerm_correct.
                unfold perm_of_res.
                inversion Hcorestep.
                (*m_phi = cur *)
                admit.
              + assert (jcnt2:= JTP.cntUpdateC' (Krun c') Htid Htid0).
                assert (dcnt2:= DTP.cntUpdateC' (Krun c') Htid' Htid'0).
                assert (Hn: tid <> tid0) by auto.
                rewrite (JTP.gsoThreadRes Htid jcnt2 Hn _ _ Htid0); auto.
                rewrite (DTP.gsoThreadRes Htid' dcnt2 Hn _ _ Htid'0); auto.
                (*apply mtch_perm.*)
           - admit. (* Locks cohere *)
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
       exists (DTP.updThreadC (mtch_cnt _ ctn) (Kstop c)).
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
         - admit. (* Locks cohere *)
       }
       (*Step*)
       { econstructor 3; try eassumption.
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
         econstructor 4; simpl; try eassumption.
         reflexivity.
       }
       
       (* step_halted *)
       exists ds.
       split; [|split]. 
       { assumption. }
       { assumption. }
       { inversion MATCH; subst. 
         assert (Htid':=Htid); apply mtch_cnt in Htid'.
         econstructor 5; try eassumption.
         simpl; reflexivity.
         simpl. eapply MTCH_compat; eassumption; instantiate(1:=Htid').

         eapply MTCH_halted; eassumption.
       }
       
           
       (* schedfail *)
       exists ds.
       split;[|split]; try eassumption.
       econstructor 6; try eassumption.
       inversion MATCH; subst.
       unfold not; simpl; intros.
       apply Htid. apply mtch_cnt'; assumption.
       reflexivity.

       Grab Existential Variables.
       - simpl. apply mtch_cnt. assumption.
       - assumption.
  Admitted.

  Lemma core_diagram:
    forall (m : M)  (U0 U U': schedule) 
     (ds : dstate) (js js': jstate) 
     (m' : M),
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









(** STOP HERE *)

  
(*
THIS PART COMES FROM THE erasure.v FILE.
WILL EVENTUALLY BE INCLUDE FULLY ABOVE

 (* HERE ENDS THE NEW PART *)
  
 Definition perm_of_res (r: compcert_rmaps.RML.R.resource): shares.share. (*This must exists somwehre*)
 Admitted.
  
  Definition erase_state (js:jstate) (m:mem): dstate.
  Proof.
    destruct js.
    eapply (ThreadPool.mk num_threads).
    - exact pool.
    - intros. (*specialize (perm_comp X). inversion perm_comp. *)
      unfold permissions.share_map.
      pose (mp:= Mem.mem_access m).
      destruct mp as [default TREE].
      pose (f:= fun (p: BinNums.positive) (A: BinNums.Z -> perm_kind -> option permission) =>
           fun (ofs: BinNums.Z) => perm_of_res (compcert_rmaps.RML.R.resource_at (juice X)  (p,ofs))).
      eapply (Maps.PTree.map f TREE).
  Defined.

  
    
  Inductive match_st : jstate ->  dstate -> Prop:=
    MATCH_ST: forall (js:jstate) ds
      (size_eq: juicy_machine.ThreadPool.num_threads js = compcert_threads.ThreadPool.num_threads ds),
      forall tid, juicy_machine.ThreadPool.pool js tid = compcert_threads.ThreadPool.pool ds (size_change size_eq tid) ->
             match_st js ds.
  
  Axiom parch_match: forall (js: jstate) (ds: dstate),
      match_st js ds <-> ds = parch_state js.

  (*Init diagram*)
  Axiom parch_initi: forall genv main vals U jms,
      initial_core JMachineSem genv main vals = Some (U, jms) ->
      initial_core DMachineSem genv main vals = Some (U, parch_state jms).
  
  (*Core Diagram*)
  Axiom parched_diagram: forall genv U U' m m' jst jst',  
      corestep JMachineSem genv (U, jst) m (U', jst') m' ->
      corestep DMachineSem genv (U, parch_state jst) m (U', parch_state jst') m'.

  (*Halted diagram*)
  Axiom parched_halted: forall U js v1,
          halted JMachineSem (U, js) = Some v1 ->
          halted DMachineSem (U, parch_state js) = Some v1.

  Module JSEM:= JuicyMachineSig SEM.
  Module JuicyMachine:= CoarseMachine NatTID SCH JSEM.
  Definition JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JSEM.machine_state.
  
  Module DSEM:= ShareMachineSig SEM.
  Module DryMachine:= CoarseMachine NatTID SCH DSEM.
  Definition DMachineSem:= DryMachine.MachineSemantics.
  Notation dstate:= DSEM.machine_state.

  Definition parch_perm (juice: compcert_rmaps.RML.R.rmap): permissions.share_map.
  Admitted.

  Definition parch_perms (n: pos.pos)(Juice: fintype.ordinal (pos.n n) -> compcert_rmaps.RML.R.rmap):  fintype.ordinal (pos.n n) -> permissions.share_map.
  Proof.                                                                                      
    intros X.
    eapply parch_perm; apply Juice; apply X.
  Defined.
  
  Definition parch_state (js: jstate) : dstate :=
    let n:= juicy_machine.ThreadPool.num_threads js in
    ThreadPool.mk
      n
      (juicy_machine.ThreadPool.pool js)
      (parch_perms n (juicy_machine.ThreadPool.juice js))
  .
  

  Record t (cT : Type) : Type := mk
  { num_threads : pos.pos;
    pool : fintype.ordinal (pos.n num_threads) -> ctl;
    juice : fintype.ordinal (pos.n num_threads) ->
            compcert_rmaps.RML.R.rmap;
    lpool : LockPool } 


*)