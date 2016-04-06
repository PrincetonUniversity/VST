
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

  Parameter parch_state : jstate ->  dstate.
  Parameter match_st : jstate ->  dstate -> Prop.
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
  Inductive match_state :  core_data ->  SM_Injection -> jmachine_state ->  mem -> dmachine_state -> mem -> Prop:=
  MATCH: forall d j js ds U m, match_st js ds -> match_state d j  (U, js) m (U, ds) m.
  Definition parch_machine (jms: jmachine_state): dmachine_state:=
    match jms with (U, jm) => (U, parch_state jm) end.
  
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
    exists (parch_machine JS).
    split; [|split].
    - unfold mu; apply initial_SM_as_inj.
    - destruct JS as [U jms]. unfold parch_machine.
      apply parch_initi; assumption.
    - destruct JS as [U js]; constructor.
      apply parch_match; reflexivity.
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
       exists (parch_machine jmst'), m1', tt, mu.
       destruct jmst' as [U' jst'].
       split; [|left].
       - constructor.
         apply parch_match; reflexivity.
       - inversion MATCH; subst.
         apply semantics_lemmas.corestep_plus_one.
         apply parch_match in H; subst ds.
         unfold parch_machine. apply parched_diagram; assumption.
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
    - apply parch_match in H; subst ds.
      apply parched_halted; assumption.
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

  
