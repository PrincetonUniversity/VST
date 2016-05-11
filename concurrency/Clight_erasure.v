Add LoadPath "../concurrency" as concurrency.

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

  Module JSEM:= JuicyMachineShell SEM .
  Module JuicyMachine:= CoarseMachine SCH JSEM.
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
                    juicy_mem.perm_of_res (resource_at (JTP.getThreadR Htid) (b, ofs)) = ((DTP.getThreadR Htid') !! b) ofs ),
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
  Qed.
      
    Lemma MTCH_updt:
      forall js ds tid c
        (H0:match_st js ds)  (cnt: JTP.containsThread js tid),
        match_st (JTP.updThreadC cnt c)
                 (DTP.updThreadC (MTCH_cnt H0 cnt) c).
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
          rewrite JTP.getThreadUpdateC1;
            rewrite DTP.getThreadUpdateC1.
          reflexivity.
        + assert (cnt2:= JTP.cntUpdateC' _ cnt Htid).
          rewrite <- (JTP.getThreadUpdateC2 c cnt cnt2 Htid) by assumption.
          inversion H0; subst.
          pose (cnt':=(@MTCH_cnt js tid ds H0 cnt)).
          assert (cnt2':= DTP.cntUpdateC' _ cnt' Htid').
          fold cnt'; rewrite <- (DTP.getThreadUpdateC2 c cnt' cnt2' Htid') by assumption.
          apply mtch_gtc; assumption.
      - inversion H0; apply mtch_perm.
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
        f_equal.
        apply Logic.eq_refl.
        f_equal.
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
  Qed.

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
       exists (DTP.updThreadC (mtch_cnt _ ctn) (Krun c)).
       split;[|split].
       (*Invariant*)
       { apply updCinvariant; assumption. }
       (*Match *)
       { constructor.
         - intros. apply DTP.cntUpdateC. apply mtch_cnt. eapply JTP.cntUpdateC'. eassumption.
         - intros. apply JTP.cntUpdateC. apply mtch_cnt'. eapply DTP.cntUpdateC'. eassumption.
         - intros. destruct (NatTID.eq_tid_dec tid0 tid).
           + subst. rewrite JTP.getThreadUpdateC1, DTP.getThreadUpdateC1; reflexivity.
           + assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
             assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
             rewrite <- (JTP.getThreadUpdateC2 _ ctn jcnt2  Htid0) by auto.
             rewrite <- (DTP.getThreadUpdateC2 _ _   dcnt2  Htid') by auto.
             apply mtch_gtc.
         - intros.
           assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
           assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
           rewrite (JTP.gThreadCR _ jcnt2).
           rewrite (DTP.gThreadCR _ dcnt2).
           apply mtch_perm.
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
             + subst. rewrite JTP.gssThreadCode, DTP.gssThreadCode; reflexivity.
             + assert (jcnt2:= JTP.cntUpdateC' (Krun c') Htid Htid0).
               assert (dcnt2:= DTP.cntUpdateC' (Krun c') Htid' Htid'0).
               assert (Hn: tid <> tid0) by auto.
             rewrite <- (JTP.gsoThreadCode _ _ Htid jcnt2 Htid0) by auto.
             rewrite <- (DTP.gsoThreadCode _ _ Htid' dcnt2 Htid'0) by auto.
             apply mtch_gtc.

           -  intros. destruct (NatTID.eq_tid_dec tid0 tid).
              + subst. rewrite JTP.gssThreadRes, DTP.gssThreadRes.
                simpl. rewrite permissions.getCurPerm_correct.
                unfold perm_of_res.
                inversion Hcorestep.
                (*m_phi = cur *)
                admit.
              + assert (jcnt2:= JTP.cntUpdateC' (Krun c') Htid Htid0).
                assert (dcnt2:= DTP.cntUpdateC' (Krun c') Htid' Htid'0).
                assert (Hn: tid <> tid0) by auto.
                rewrite (JTP.gsoThreadRes Htid jcnt2 Hn _ _ Htid0) by auto.
                rewrite (DTP.gsoThreadRes Htid' dcnt2 Hn _ _ Htid'0) by auto.
                apply mtch_perm.
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
           + subst. rewrite JTP.getThreadUpdateC1, DTP.getThreadUpdateC1; reflexivity.
           + assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
             assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
             rewrite <- (JTP.getThreadUpdateC2 _ ctn jcnt2  Htid0) by auto.
             rewrite <- (DTP.getThreadUpdateC2 _ _   dcnt2  Htid') by auto.
             apply mtch_gtc.
         - intros.
           assert (jcnt2:= JTP.cntUpdateC' _ _ Htid0).
           assert (dcnt2:= DTP.cntUpdateC' _ _ Htid').
           rewrite (JTP.gThreadCR _ jcnt2).
           rewrite (DTP.gThreadCR _ dcnt2).
           apply mtch_perm.
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
         inversion Htstep; subst.

         (* step_lock  *)
         assert (Htid':= MTCH_cnt MATCH Htid).
         assert (virtue: permissions.delta_map). admit.
         exists (DSEM.ThreadPool.updThread Htid' (Kresume c)
                  (permissions.computeMap
                     (DSEM.ThreadPool.getThreadR Htid') virtue)).
         split; [|split].
         
         - admit. (*Nick has this proof somewhere. *)
         - Search match_st. 
           
       admit.
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
  Qed.

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

(*Just to be explicit*)
Theorem clight_erasure:
  forall U : DryMachine.Sch,
       Wholeprog_sim.Wholeprog_sim (JMachineSem U) 
         (DMachineSem U) genv genv main ClightErasure.ge_inv
         ClightErasure.init_inv ClightErasure.halt_inv.
Proof.
  Proof. apply ClightErasure.erasure. Qed.




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