
Add LoadPath "../concurrency" as concurrency.

Require Import Memory.

(* The concurrent machinery*)
Require Import concurrent_machine.
Require Import juicy_machine. Import Concur.
Require Import compcert_threads. Import Concur.

(*The simulations*)
Require Import wholeprog_simulations. 

Module Erasure (SCH: Scheduler NatTID)(SEM: Semantics).
  Import SEM.
  Parameter genv: G.
  Parameter main: Values.val.
    
  Module JSEM:= JuicyMachineSig SEM.
  Module JuicyMachine:= CoarseMachine NatTID SCH JSEM.
  Definition JMachineSem:= JuicyMachine.MachineSemantics.
  
  Module DSEM:= ShareMachineSig SEM.
  Module DryMachine:= CoarseMachine NatTID SCH DSEM.
  Definition DMachineSem:= DryMachine.MachineSemantics.

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
  Definition match_state (d: core_data) (j: SM_Injection)
             (JS: JuicyMachine.MachState)(M1: mem)
             (DS: DryMachine.MachState)(M2: mem):= True.
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
    admit.
    (*eexists. (* Fill in! *)
    split.
    unfold mu; apply initial_SM_as_inj.
    split.
    unfold initial_core, DMachineSem,  DryMachine.MachineSemantics.
    unfold DryMachine.init_machine.
     *)
    Qed.
    
    Theorem erasure:
    Wholeprog_sim.Wholeprog_sim
      JMachineSem DMachineSem
      genv genv
      main
      ge_inv init_inv halt_inv.
      apply (Wholeprog_sim.Build_Wholeprog_sim
            JMachineSem DMachineSem
            genv genv
            main
            ge_inv init_inv halt_inv
            core_data match_state core_ord core_ord_wf).
      - reflexivity.
      - apply core_initial.                                                         -          

  
