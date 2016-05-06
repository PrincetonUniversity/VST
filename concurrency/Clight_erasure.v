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
  Inductive match_st : jstate ->  dstate -> Prop:=
    MATCH_ST: forall (js:jstate) ds
                (mtch_cnt: forall {tid},  JTP.containsThread js tid -> DTP.containsThread ds tid )
                (mtch_cnt': forall {tid}, DTP.containsThread ds tid -> JTP.containsThread js tid )
                (mtch_gtc: forall {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    JTP.getThreadC Htid = DTP.getThreadC Htid' )
                (mtch_perm: forall b ofs {tid} (Htid:JTP.containsThread js tid)(Htid':DTP.containsThread ds tid),
                    juicy_mem.perm_of_res (resource_at (JTP.getThreadR Htid) (b, ofs)) = ((DTP.getThreadR Htid') !! b) ofs ),
      match_st js ds.
  
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
        (M: match_st js ds),
        JTP.getThreadC cnt =  c ->
        DTP.getThreadC (MTCH_cnt M cnt) =  c.
  Proof. intros ? ? ? ? ? MTCH; inversion MTCH; subst.
         intros HH; rewrite <- HH.
         symmetry.
         apply mtch_gtc.
  Qed.
       
  Lemma MTCH_compat: forall js ds m,
      match_st js ds ->
      JSEM.mem_compatible js m ->
      DSEM.mem_compatible ds m.
  Proof. 
    intros ? ? ? MTCH mc;
    inversion MTCH; inversion mc; subst.
    unfold DSEM.mem_compatible.
    constructor.
    -intros tid cnt.
     unfold permissions.permMapLt; intros b ofs.
     eapply po_trans.
     specialize (perm_comp tid (mtch_cnt' _ cnt)).
     inversion perm_comp.
     specialize (acc_coh (b, ofs)).
     rewrite permissions.getMaxPerm_correct.
     apply acc_coh.

     rewrite (mtch_perm _ _ _ (mtch_cnt' tid cnt) cnt).
     unfold DTP.getThreadR.
     apply permissions.po_refl.
    - unfold JSEM.mem_compatible in mc.
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
      + intros.
        unfold DSEM.ThreadPool.getThreadC.
        unfold DSEM.initial_machine; simpl.
        admit.
    - admit.
        (*constructor.*)
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
       inversion H3; subst.
       
       
       eapply (MTCH_getThreadC _ ds tid _ cnt H1) in HC.
       exists (U, DSEM.updThreadC (MTCH_cnt H1 cnt) (Krun c)).
       split.
       { destruct jmst'.
         simpl in Hms'; rewrite <- Hms'.
         simpl in H; rewrite <- H.
         constructor.
         admit. (* invariant updateC*)
         apply MTCH_updt.
       }
       { econstructor 1.
         - eassumption.
         - simpl.
         - simpl in Hcmpt.
           eapply (MTCH_compat _ _ _ H1 Hcmpt).
         - simpl.
           econstructor; try eassumption; reflexivity. }
       (* core_step *)
       {
         inversion MATCH; subst.
         inversion H3; subst.
         inversion Hcorestep.
         Search dstate.
         Axiom get_permMap: mem -> permissions.share_map.
         exists (U, updThread (MTCH_cnt H1 (Htid))
                         (Krun c') (get_permMap (juicy_mem.m_dry jm'))).
         split.
         - destruct jmst' as [U' js'].
         simpl in *; subst.
         constructor.
         simpl.
         Axiom upd_MATCH: forall js ds tid (Htid: JSEM.containsThread js tid) c new_jm
                            (MATCH: match_st js ds),
             match_st
               (juicy_machine.updThread js (cont2ord Htid) c (juicy_mem.m_phi new_jm))
               (updThread (MTCH_cnt MATCH Htid) c (get_permMap (juicy_mem.m_dry new_jm))).
         admit. (*invariant step *)
         - apply upd_MATCH.
         - pose (Hcompatible:= @MTCH_compat js _ _ H1 Hcmpt).
           assert (Hcnt : ThreadPool.containsThread ds tid) by (apply (@MTCH_cnt js); auto).
           econstructor 2; try eassumption.
           unfold DSEM.cstep.
           eapply (@step_dry _ _ Sem _ tid ds m2 (MTCH_cnt H1 Htid) _  _ c).
           reflexivity.
           inversion MATCH0; try eassumption.
           apply MTCH_getThreadC; eassumption.
           simpl in *. unfold JSEM.Sem in H2; unfold DSEM.Sem.
           instantiate(1:=c'); instantiate(1:=Hcompatible).
           Lemma MTCH_personal_mem:
             forall tid ds js m
               (MTCH: match_st js ds)
               (Htid: JSEM.containsThread js tid)
               (Hcmpt: JSEM.mem_compatible js m),
               (juicy_mem.m_dry (personal_mem Htid Hcmpt)) = 
               (restrPermMap
                  (permMapsInv_lt (perm_comp (MTCH_compat _ _ _ MTCH Hcmpt)) (MTCH_cnt MTCH Htid))).
           Admitted.
           unfold Hcompatible.
           rewrite <- MTCH_personal_mem.
           assumption.
         - simpl. f_equal.
           admit. (*This will change with the updated semantics of juicy_machine. *)
       }
           
       (* suspend_step *)
       inversion MATCH0; subst.
       inversion H; subst.
       eapply (MTCH_getThreadC _ ds tid _ cnt H1) in HC.
       exists (SCH.schedSkip U, DSEM.updThreadC (MTCH_cnt H1 cnt) (Kstop c)).
       split.
       { destruct jmst'.
         simpl in Hms'; rewrite <- Hms'.
         simpl in HschedS. rewrite <- HschedS.
         constructor.
         admit. (*invariant update. *)
         apply MTCH_updt.
       }
       { econstructor 3.
         - eassumption.
         - reflexivity.
         - simpl in Hcmpt.
           eapply (MTCH_compat _ _ _ H1 Hcmpt).
         - simpl.
           econstructor; try eassumption; reflexivity. }
       (* conc_step *)
       {
         (*Have to go through the cases*)
         inversion MATCH.
         inversion Hconc; subst.
         - (*Lock*)
           exists (fst jmst',updThread (MTCH_cnt H0 (Htid))
                         (Krun c') (get_permMap (juicy_mem.m_dry jm'))).
           simpl; split.
           + destruct jmst' as [U' jm''].
             simpl in *; subst.
             econstructor.
             admit. (* invariant on update. *)
             admit. (* match on update . probably need a new axiom *)
             simpl.
             unfold DryMachine.MachStep; simpl.
             econstructor 4;
               try eassumption.
             econstructor 1;
               try eassumption.
           + eapply MTCH_getThreadC; eassumption.
           + 
               
         - (*Unlock*)
         - (*Create*)
         - (*MkLock*)
         - (*Freelock*)
         - (*LockFail*)

         
       admit.
       }
       (* step_halted *)
       exists (SCH.schedSkip (fst dmst), snd dmst).
       split. 
       { destruct jmst'.
         simpl in H4; rewrite <- H4.
         simpl in HschedS; rewrite <- HschedS.
         inversion MATCH0; subst.
         simpl; constructor.
         assumption.
       }
       { destruct dmst.
         unfold DryMachine.MachStep; simpl.
         inversion MATCH0; subst.
         inversion Hhalted; subst.
         cut (DSEM.threadHalted (MTCH_cnt H7 cnt)).
         { intros HH; eapply (DryMachine.step_halted tid _ _ _ _ _ _ _ _ HH). }
         { inversion Hhalted; subst.
           econstructor.
           - apply (MTCH_getThreadC). eapply Hthread. 
           - cut (c = c0).
             { intros; subst c;  assumption. }
             { simpl in cnt0.
               Lemma getTC_proof_indep:
                 forall {js tid} (cnt1 cnt2: JSEM.containsThread js tid),
                   JSEM.getThreadC cnt1 =JSEM.getThreadC cnt2.
               Admitted.
               rewrite (getTC_proof_indep cnt cnt0) in Hthread.
               rewrite Hthread in Hthread0; inversion Hthread0; reflexivity. }
         }
         }
           
       (* schedfail *)
       exists (fst jmst', snd dmst).
       split.
       - destruct jmst' as [U' jst'];  econstructor.
         destruct jmst as [U jst]; simpl in H4. 
         inversion MATCH0; subst; assumption.
       -  inversion MATCH0; subst. econstructor 6. simpl. exact HschedN.
          simpl.
          unfold not; intros NOWAY; apply Htid.
          eapply MTCH_cnt' in NOWAY;  eassumption.
          simpl. exact HschedS. 

          (* Fix this in place*)
          Grab Existential Variables.
          - simpl in Hcmpt. inversion MATCH0; subst. eapply MTCH_compat; eassumption.
          - reflexivity.
          - simpl. assumption.
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
       
       
  Lemma halted_diagram:
    forall c, halted JMachineSem c = None.
  










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