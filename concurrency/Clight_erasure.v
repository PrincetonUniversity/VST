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
                (mtch_gtc: forall {tid} (Htid:JTP.containsThread js tid), JTP.getThreadC Htid = DTP.getThreadC (mtch_cnt Htid) )
                (mtch_perm: forall b ofs {tid} (Htid:JTP.containsThread js tid),
                    juicy_mem.perm_of_res (resource_at (JTP.getThreadR Htid) (b, ofs)) = ((DTP.getThreadR (mtch_cnt Htid)) !! b) ofs ),
      match_st js ds.
  
  (*match axioms*)
  Lemma MTCH_ctn: forall {js tid ds},
           match_st js ds ->
           JTP.containsThread js tid -> DTP.containsThread ds tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt. Qed.
  Lemma MTCH_ctn': forall {js tid ds},
           match_st js ds ->
           DTP.containsThread ds tid -> JTP.containsThread js tid.
  Proof. intros ? ? ? MTCH. inversion MTCH. apply mtch_cnt'. Qed.


  Lemma ctn_irr: forall tid ds (cnt1 cnt2: DTP.containsThread ds tid),
      DTP.getThreadC cnt1 = DTP.getThreadC cnt2.
  Proof. intros.
         
         unfold DTP.getThreadC.
         destruct ds; simpl.
         f_equal; f_equal.
         eapply proof_irrelevance.
  Qed.

  Lemma MTCH_getThreadC: forall js ds tid c,
      forall (ctn: JTP.containsThread js tid)
        (M: match_st js ds),
        JTP.getThreadC ctn =  c ->
        DTP.getThreadC (MTCH_ctn M ctn) =  c.
  Proof. intros ? ? ? ? ? MTCH; inversion MTCH; subst.
         intros HH; rewrite <- HH.
         rewrite mtch_gtc.
         apply ctn_irr.
  Qed.
       
  Lemma MTCH_compat: forall js ds m,
      match_st js ds ->
      JSEM.mem_compatible js m ->
      DSEM.mem_compatible ds m.
  Proof. 
    intros ? ? ? MTCH mc;
    inversion MTCH; inversion mc; subst.
    constructor.
    - unfold DSEM.perm_compatible. intros tid cnt.
      unfold permissions.permMapLt; intros b ofs.
      eapply po_trans.
      specialize (perm_comp tid (mtch_cnt' _ cnt)).
      inversion perm_comp.
      specialize (acc_coh (b, ofs)).
      rewrite permissions.getMaxPerm_correct.
      apply acc_coh.

      
      
      rewrite <- permissions.restrPermMap_max.
      specialize (acc_coh b).
      
      unfold max_accDess_cohere in max_coh.
      
      
    Lemma MTCH_updt:
      forall js ds tid c
        (H0:match_st js ds)  (ctn: JTP.containsThread js tid),
        match_st (JTP.updThreadC ctn c)
                 (DTP.updThreadC (MTCH_ctn H0 ctn) c).
          

  (*Lemma parch_match: forall (js: jstate) (ds: dstate),
      match_st js ds <-> ds = parch_state js.*)

       (*
  (*Init diagram*)
  Lemma match_init: forall c, match_st (JSEM.initial_machine c) (DSEM.initial_machine c).

  (*Core Diagram*)
  Lemma parched_diagram: forall genv U U' m m' jst jst' ds ds',  
      corestep JMachineSem genv (U, jst) m (U', jst') m' ->
      match_st jst ds -> match_st jst ds -> 
      corestep DMachineSem genv (U, ds)  m (U', ds') m'.
        *)

       
  Variable genv: G.
  Variable main: Values.val.
  Lemma init_diagram:
    forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
     (vals : list Values.val) (m : M),
   initial_core JMachineSem genv main vals = Some (U, js) ->
   exists (mu : SM_Injection) (ds : dstate),
     as_inj mu = j /\
     initial_core DMachineSem genv main vals = Some (U, ds) /\
     DSEM.invariant ds /\
     match_st js ds.

  Lemma core_diagram:
    forall (m : M)  (U U': schedule) 
     (ds : dstate) (js js': jstate) 
     (m' : M),
   corestep JMachineSem genv (U, js) m (U', js') m' ->
   match_st js ds ->
   DSEM.invariant ds ->
   exists (ds' : dstate) (mu' : SM_Injection),
     DSEM.invariant ds' /\
     match_st js' ds' /\
     corestep DMachineSem genv (U, ds) m (U', ds') m'.

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