Add LoadPath "../concurrency" as concurrency.

Require Import compcert.common.Memory.

(* The concurrent machinery*)
Require Import concurrency.concurrent_machine.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.compcert_threads. Import Concur.

(*The simulations*)
Require Import sepcomp.wholeprog_simulations. 

Module Type Parching (SCH: Scheduler NatTID)(SEM: Semantics).
  
  Import SEM.
    
  Module JSEM:= JuicyMachineSig SEM.
  Module JuicyMachine:= CoarseMachine NatTID SCH JSEM.
  Definition JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JSEM.machine_state.
  
  Module DSEM:= ShareMachineSig SEM.
  Module DryMachine:= CoarseMachine NatTID SCH DSEM.
  Definition DMachineSem:= DryMachine.MachineSemantics.
  Notation dstate:= DSEM.machine_state.

  (*Parameter parch_state : jstate ->  dstate.*)
  Parameter match_st : jstate ->  dstate -> Prop.
  
  (*match axioms*)
  Axiom MTCH_ctn: forall {js tid ds},
           match_st js ds ->
           JSEM.containsThread js tid -> DSEM.containsThread ds tid.
  Axiom MTCH_ctn': forall {js tid ds},
           match_st js ds ->
           DSEM.containsThread ds tid -> JSEM.containsThread js tid.
        
       Axiom MTCH_getThreadC: forall js ds tid c,
           forall (ctn: JSEM.containsThread js tid)
           (M: match_st js ds),
           JSEM.getThreadC ctn =  c ->
           DSEM.getThreadC (MTCH_ctn M ctn) =  c.
        
       Axiom MTCH_compat: forall js ds m,
           match_st js ds ->
         JSEM.mem_compatible js m ->
         DSEM.mem_compatible ds m.
        
       Axiom MTCH_updt:
           forall js ds tid c
             (H0:match_st js ds)  (ctn: JSEM.containsThread js tid),
             match_st (JSEM.updThreadC ctn c)
                       (DSEM.updThreadC (MTCH_ctn H0 ctn) c).
          

  (*Axiom parch_match: forall (js: jstate) (ds: dstate),
      match_st js ds <-> ds = parch_state js.*)
  
  (*Init diagram*)
  Axiom match_init: forall c, match_st (JSEM.initial_machine (Kresume c)) (DSEM.initial_machine (Kresume c)).

  
  
  (*Core Diagram*)
  Axiom parched_diagram: forall genv U U' m m' jst jst' ds ds',  
      corestep JMachineSem genv (U, jst) m (U', jst') m' ->
      match_st jst ds -> match_st jst ds -> 
      corestep DMachineSem genv (U, ds)  m (U', ds') m'.

End Parching.
  
  
Module Erasure (SCH: Scheduler NatTID)(SEM: Semantics)(PC: Parching SCH SEM).
  Import SEM.
  Import PC.
  Parameter genv: G.
  Parameter main: Values.val.
    
  (*Module JSEM:= JuicyMachineSig SEM.
  Module JuicyMachine:= CoarseMachine NatTID SCH JSEM.
  Definition JMachineSem:= JuicyMachine.MachineSemantics.*)
  Notation jmachine_state:= JuicyMachine.MachState.
  
  (*Module DSEM:= ShareMachineSig SEM.
  Module DryMachine:= CoarseMachine NatTID SCH DSEM.
  Definition DMachineSem:= DryMachine.MachineSemantics.*)
  Notation dmachine_state:= DryMachine.MachState.
  

  (* The main erasure theorem is stated with Wholeprog_sim
     which might change, but will escentially have the same
     structure: match, init_clause, core_diagram, etc...  *)
  Definition ge_inv (g1 g2: SEM.G):= g1 = g2.
  Inductive init_inv:  Values.Val.meminj ->
                       G -> list Values.val -> mem ->
                       G -> list Values.val -> mem -> Prop:=
  |InitEq: forall j g1 args1 m1 g2 args2 m2,
      g1 = g2 ->
      args1 = args2 ->
      m1 = m2 ->
      init_inv j g1 args1 m1 g2 args2 m2.

  Inductive halt_inv:  SM_Injection ->
                       G -> Values.val -> mem ->
                       G -> Values.val -> mem -> Prop:=
  |HaltEq: forall j g1 args1 m1 g2 args2 m2,
      g1 = g2 ->
      args1 = args2 ->
      m1 = m2 ->
      halt_inv j g1 args1 m1 g2 args2 m2.

  Definition core_data:= unit.
  Import Mem.
  Import Maps.PTree.
  (*Record m_equiv (m1 m2: Mem.mem):=
    {
      contents_eq: Mem.mem_contents m1 = Mem.mem_contents m2 ;
      mas_access_eq: forall b ofs, Maps.PMap.get b (Mem.mem_access m1) ofs Max =
                              Maps.PMap.get b (Mem.mem_access m2) ofs Max ;
      nextblock_eq: nextblock m1 = nextblock m2
      
    }.
  Lemma m_eq_eqv: forall m1, m_equiv m1 m1.
  Proof. constructor; reflexivity. Qed. *)
  Inductive match_state :  core_data ->  SM_Injection -> jmachine_state ->  mem -> dmachine_state -> mem -> Prop:=
    MATCH: forall d j js ds U m1 m2,
      match_st js ds ->
      
      invariant(the_sem:=Sem) ds -> (* this could be carried inside the state. But it will sufice to put it here*)
      m1 m2 ->
      match_state d j  (U, js) m1 (U, ds) m2.
  (*Definition parch_machine (jms: jmachine_state): dmachine_state:=
    match jms with (U, jm) => (U, parch_state jm) end.*)
  
  Definition core_ord: unit-> unit -> Prop := fun _ _ => False.
  Definition core_ord_wf:  well_founded core_ord.
      constructor; intros y H; inversion H.
  Defined.
  Lemma core_initial (j: Values.Val.meminj)
             (JS: JuicyMachine.MachState)(vals1:list Values.val)(m1: mem)
             (vals2:list Values.val)(m2: mem)
             : initial_core JMachineSem genv main vals1 = Some JS ->
                   init_inv j genv vals1 m1 genv vals2 m2 ->
                   exists (mu : SM_Injection) (cd : core_data) 
                   (DS : DryMachine.MachState),
                     as_inj mu = j /\
                     initial_core DMachineSem genv main vals2 = Some DS /\
                     match_state cd mu JS m1 DS m2.
  Proof.
    intros INIT_C INIT_INV.
    inversion INIT_INV; subst.
    pose (mu:=(initial_SM
         (fun _ : block => false)(fun _ : block => false)
         (fun b:block => match j b with Some _ => true | None => false end)
         (fun b:block => match j b with Some _ => true | None => false end)
         j)).
    
    exists mu, tt.
    simpl in INIT_C; unfold JuicyMachine.init_machine in INIT_C.
    simpl JSEM.init_mach in INIT_C.
(*    unfold JSEM.init_mach, JSEM.Sem in INIT_C. *)
    unfold JSEM.init_mach, JSEM.Sem in INIT_C.
    destruct (@initial_core G C M Sem genv main vals2) eqn:initc; inversion INIT_C.
    exists (DryMachine.U, DSEM.initial_machine (Kresume c)).
    split; [|split].
    - unfold mu; apply initial_SM_as_inj.
    - simpl.
      unfold DryMachine.init_machine.
      unfold DSEM.init_mach.
      unfold DSEM.Sem.
      rewrite initc; reflexivity.
    - assert (same_sch: JuicyMachine.U = DryMachine.U). admit. (* This should be proven elswhere. The same SCHEDULE *)
      rewrite same_sch; constructor. 
      apply match_init.
      admit. (*init invariant*)
      apply m_eq_eqv.
  Qed.

  Lemma core_step' :
    forall (st1 : JuicyMachine.MachState) (m1 : mem)
     (st1' : JuicyMachine.MachState) (m1' : mem),
   corestep JMachineSem genv st1 m1 st1' m1' ->
   forall (cd : core_data) (st2 : DryMachine.MachState)
     (mu : SM_Injection) (m2 : mem),
   match_state cd mu st1 m1 st2 m2 ->
   exists  (m2' : mem) (cd' : core_data)  (mu' : SM_Injection)
      (st2' : DryMachine.MachState),
     match_state cd' mu' st1' m1' st2' m2' /\
     (corestep DMachineSem genv st2 m2 st2' m2').
       intros jmst m1 jmst' m1' STEP cd dmst mu m2 MATCH.
       unfold corestep, JMachineSem,
       JuicyMachine.MachineSemantics, JuicyMachine.MachStep in STEP.
       inversion STEP; subst.

       
       (* resume_step *)
       exists  m2, tt, mu.
       inversion MATCH0; subst.
       inversion H3; subst.
       eapply (MTCH_getThreadC _ ds tid _ ctn H0) in HC.
       exists (U, DSEM.updThreadC (MTCH_ctn H0 ctn) (Krun c)).
       split.
       { destruct jmst'.
         simpl in Hms'; rewrite <- Hms'.
         simpl in H; rewrite <- H.
         constructor.
         apply MTCH_updt.
         admit. (*invariant on updateC*)
         assumption.
       }
       { econstructor 1.
         - eassumption.
         - simpl.
         - simpl in Hcmpt.
           Lemma compat_equiv: forall ds m1 m2,
               m_equiv m1 m2 ->
               DSEM.mem_compatible ds m1 ->
               DSEM.mem_compatible ds m2.
           Admitted.
           apply (compat_equiv _ m1' m2); try assumption.
           apply (MTCH_compat _ _ _ H0 Hcmpt).
         - simpl.
           econstructor; try eassumption; reflexivity. }
       (* core_step *)
       {
         inversion MATCH; subst.
         inversion H3; subst.
         inversion Hcorestep.
         destruct H5 as [rdecay rageable].
         Axiom get_permMap: mem -> permissions.share_map.
         Parameter parch_perm : juicy_mem.juicy_mem -> permissions.access_map -> Prop.
           Lemma parch_perm_lt: forall {jm p},
               parch_perm jm p -> permissions.permMapLt p (permissions.getMaxPerm (juicy_mem.m_dry jm)).
           Admitted.
           Lemma erasureSingleThread:
             forall jm jm' genv c c' p,
               corestep Sem genv c (juicy_mem.m_dry jm) c' (juicy_mem.m_dry jm') ->
               juicy_mem.resource_decay (Mem.nextblock (juicy_mem.m_dry jm)) (juicy_mem.m_phi jm) (juicy_mem.m_phi jm') ->
               forall (pape: parch_perm jm p),
               exists m',
                 corestep Sem genv c (restrPermMap (parch_perm_lt pape)) c' m' /\
                 parch_perm jm' (permissions.getCurPerm m').
           Admitted.
           simpl in Hcmpt.
           Definition p: permissions.access_map. Admitted.
           assert (pape: parch_perm (personal_mem Htid Hcmpt) p). admit.
           
           eapply erasureSingleThread in H4; try assumption. (*Have to prove parche_perm and choose the perm_map*)
           generalize H4. instantiate(1:=pape).
           clear H4; intros H4.
           destruct H4 as [m2' [DSTEP pape']].
           exists  m2', tt, mu.  
           exists (U, updThread (MTCH_ctn H0 (Htid))
                         (Krun c') (get_permMap (m2'))).
           split.
           (*
           { destruct jmst' as [U' jst']; simpl in *; subst.
             simpl. econstructor.
             
           } *)
           Focus 2.
           simpl.
           unfold DryMachine.MachStep; simpl.
           assert (Htid0: DSEM.containsThread ds tid).
           { eapply MTCH_ctn; eassumption. }
           pose (Htid0':= (MTCH_ctn H0 Htid)).
           assert (Hcmpt0: DSEM.mem_compatible ds m2). admit.
           eapply (DryMachine.core_step tid U ds _ m2 m2' _ Htid0' Hcmpt0 ); try eassumption.
         - simpl.
           unfold DSEM.cstep.
           eapply (@step_dry _ _ _ genv tid ds _ _ Hcmpt0  _ c
                  (restrPermMap (permMapsInv_lt (perm_comp Hcmpt0) Htid0')) _ c').
           + reflexivity.
           + assumption.
           + apply MTCH_getThreadC; eassumption.
           + Set Printing All.
             erewrite (restrPermMap_irr (permMapsInv_lt (perm_comp Hcmpt0) Htid0')
                                        _ ); try reflexivity.
             unfold DSEM.Sem.
             erewrite restrPermMap_irr; try reflexivity.
             exact DSTEP.

             (* MISMACH IN MEMORIES! *)
                     try reflexivity; try eassumption.
             unfold DSEM.Sem.
             instantiate(1:=(parch_perm_lt pape)).
             apply DSTEP. (* Or a different memory*)
             
             unfold DSEM.Sem.
             unfold JSEM.mem_compatible in Hcmpt.
             unfold juicy_machine.mem_compatible in Hcmpt.
             simpl in Hcmpt.
             simpl in Hcmpt.
             erewrite restrPermMap_irr .
             
             unfold DSEM.Sem.
             
             eapply DSTEP.
             Lemma equiv_blah:
               forall p m,
               forall (P1 P2: permissions.permMapLt p (permissions.getMaxPerm m)),
                 restrPermMap P1 = restrPermMap P2.
                   intros. 
                   unfold restrPermMap.
                   
                   
               (restrPermMap
                  (permMapsInv_lt (perm_comp a) (MTCH_ctn(ds:=ds) b Htid)))
                 = (restrPermMap (parch_perm_lt c)).

             assert (Hcompatible:mem_compatible ds m2) by (apply (@MTCH_compat js _ _ H0 Hcmpt)).
           assert (Hcnt : ThreadPool.containsThread ds tid) by (apply (@MTCH_ctn js); auto).
           econstructor 2; try eassumption.
           unfold DSEM.cstep.
           econstructor.
           - reflexivity.
           - assumption.
           - apply MTCH_getThreadC; eassumption.
           - unfold DSEM.Sem.
             Focus 2.
             simpl.
           eapply (@step_dry _ _ Sem _ tid ds m2 (MTCH_ctn H0 Htid) Hcompatible  _ c); try eassumption; simpl.
           
           
               
               
                                        
           + 
             
             Require Import veric.jstep.
             assert (JSTEP:= (FSem.step _ _ JuicyFSem.t) _ _ JSEM.Sem). simpl in JSTEP.
             simpl in H2.*)
             unfold personal_mem. destruct Hcmpt. destruct (perm_comp (cont2ord Htid)); simpl.
             
             admit. (* This is wrong!!!*)
             (* The cur permission on the on the memory is definetly not the same,
              because the juicy machine doesn't update it! *)
           
                  (restrPermMap (permMapsInv_lt (perm_comp Hcompatible) (MTCH_ctn H0 Htid) ))).
           
           try eassumption. Focus 4. simpl in *. unfold JSEM.Sem in H1; unfold DSEM.Sem. eassumption; simpl.
           Focus 3. apply MTCH_getThreadC; eassumption.
           unfold personal_mem. destruct Hcmpt.
           destruct (perm_comp (cont2ord Htid)) eqn:pcmpt.
           simpl.
         unfold match_state.
       (* suspend_step *)
       exists  m1', tt, mu.
       inversion MATCH0; subst.
       inversion H; subst.
       eapply (MTCH_getThreadC _ ds tid _ ctn H0) in HC.
       exists (SCH.schedSkip U, DSEM.updThreadC (MTCH_ctn H0 ctn) (Kstop c)).
       split.
       { destruct jmst'.
         simpl in Hms'; rewrite <- Hms'.
         simpl in HschedS. rewrite <- HschedS.
         constructor.
         apply MTCH_updt.
       }
       { econstructor 3.
         - eassumption.
         - reflexivity.
         - simpl in Hcmpt.
           eapply (MTCH_compat _ _ _ H0 Hcmpt).
         - simpl.
           econstructor; try eassumption; reflexivity. }
       (* conc_step *)
       exists  m1', tt, mu. (* ? *)
       admit.
       (* step_halted *)
       exists  m1', tt, mu.
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
         cut (DSEM.threadHalted (MTCH_ctn H7 cnt)).
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
       exists  m1', tt, mu.
       exists (fst jmst', snd dmst).
       split.
       - destruct jmst' as [U' jst'];  econstructor.
         destruct jmst as [U jst]; simpl in H4. 
         inversion MATCH0; subst; assumption.
       -  inversion MATCH0; subst. econstructor 6. simpl. exact HschedN.
          simpl.
          unfold not; intros NOWAY; apply Htid.
          eapply MTCH_ctn' in NOWAY;  eassumption.
          simpl. exact HschedS. 

          (* Fix this in place*)
          Grab Existential Variables.
          - simpl in Hcmpt. inversion MATCH0; subst. eapply MTCH_compat; eassumption.
          - reflexivity.
          - simpl. assumption.
  Qed.
  
  Lemma core_step :
    forall (st1 : JuicyMachine.MachState) (m1 : mem)
     (st1' : JuicyMachine.MachState) (m1' : mem),
   corestep JMachineSem genv st1 m1 st1' m1' ->
   forall (cd : core_data) (st2 : DryMachine.MachState)
     (mu : SM_Injection) (m2 : mem),
   match_state cd mu st1 m1 st2 m2 ->
   exists
     (st2' : DryMachine.MachState) (m2' : mem) (cd' : core_data) 
   (mu' : SM_Injection),
     match_state cd' mu' st1' m1' st2' m2' /\
     (semantics_lemmas.corestep_plus DMachineSem genv st2 m2 st2' m2' \/
      semantics_lemmas.corestep_star DMachineSem genv st2 m2 st2' m2' /\
      core_ord cd' cd).
       intros jmst m1 jmst' m1' STEP cd dmst mu m2 MATCH.
       destruct (core_step' jmst m1 jmst' m1' STEP cd dmst mu m2 MATCH)
         as [m2' [cd' [mu' [st2' [MATCH' STEP']]]]].
       exists st2', m2', cd', mu'.
       split; [ | left ; apply semantics_lemmas.corestep_plus_one]; assumption.
  Qed.

  Lemma core_halted:
     forall (cd : core_data) (mu : SM_Injection)
     (c1 : JuicyMachine.MachState) (m1 : mem) (c2 : DryMachine.MachState)
     (m2 : mem) (v1 : Values.val),
   match_state cd mu c1 m1 c2 m2 ->
   halted JMachineSem c1 = Some v1 ->
   exists (j : SM_Injection) (v2 : Values.val),
     halt_inv j genv v1 m1 genv v2 m2 /\ halted DMachineSem c2 = Some v2.
  Proof.
    intros cd mu jmst m1 dmst m2 v1 MATCH HALT.
    exists mu, v1.
    inversion MATCH; subst.
    split.
    - constructor; try reflexivity.
    - inversion HALT.
  Qed.

  
  Theorem erasure:
    Wholeprog_sim.Wholeprog_sim
      JMachineSem DMachineSem
      genv genv
      main
      ge_inv init_inv halt_inv.
  Proof.
    apply (Wholeprog_sim.Build_Wholeprog_sim
             JMachineSem DMachineSem
             genv genv
             main
             ge_inv init_inv halt_inv
             core_data match_state core_ord core_ord_wf).
    - reflexivity.
    - apply core_initial.
    - apply core_step.
    - apply core_halted.
  Qed.
    
End Erasure.

  
