From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.

Require Import VST.msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Export VST.concurrency.semantics.
Require Export VST.concurrency.lksize.
Require Import VST.concurrency.threadPool. Export threadPool.

Require Import VST.concurrency.machine_semantics.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.bounded_maps.
Require Import VST.concurrency.addressFiniteMap.

Require Import VST.concurrency.scheduler.
Require Import Coq.Program.Program.

Require Import VST.concurrency.safety.

Require Import VST.concurrency.coinductive_safety.


Require Import VST.concurrency.HybridMachineSig_rec.

Require Import VST.veric.res_predicates.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.ccc26x86.Asm_coop.
Require Import VST.ccc26x86.Asm_event.

Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.HybridMachine.

Require Import VST.concurrency.CoreSemantics_sum.

Require Import compcert.common.Smallstep.

Require Import VST.concurrency.machine_semantics_lemmas.


Section HybridSimulation.

  Variable (Sems Semt : Semantics_rec).
  Variable (hb1 hb2: option nat).
  Variable (Resources : Resources_rec).
  Variable (MatchCAsm: meminj -> corestate -> mem -> Asm_coop.state -> mem -> Prop).
  
  Definition HM1:=HybridMachine hb1 Sems Semt.
  Definition HM2:=HybridMachine hb2 Sems Semt.

  Notation Sem1:=(ConcurMachineSemantics HM1).
  Notation Sem2:=(ConcurMachineSemantics HM2).
  
  Notation C1:= (MachState HybridMachine.Resources
                          (Sem hb1 Sems Semt) (ThreadPool hb1 Sems Semt)).
  Notation C2:= (MachState HybridMachine.Resources
                          (Sem hb2 Sems Semt) (ThreadPool hb2 Sems Semt)).
  Notation G1:= (semG (Sem hb1 Sems Semt)).
  Notation G2:= (semG (Sem hb2 Sems Semt)).
  Variable ge1:G1.
  Variable ge2:G2.
  Variable (ge_inv: G1 -> G2 -> Prop). 
  Record HybridMachine_simulation main init_inv:=
    { core_data : Type
      ; match_state : core_data -> (*SM_Injection*)meminj -> C1 -> mem -> C2 -> mem -> Prop
      ; core_ord : core_data -> core_data -> Prop
      ; core_ord_wf : well_founded core_ord
      ; genv_inv : ge_inv ge1 ge2
    (*  ; core_initial :
          forall j c1 vals1 m1 vals2 m2,
            initial_machine hb1 Sem1 Sem2 ge1 main vals1 = Some c1 ->
            init_inv j ge1 vals1 m1 ge2 vals2 m2 ->
    exists (*mu*) cd c2,
      (*as_inj mu = j*
      /\*) initial_machine Sem2 ge2 main vals2 = Some c2
           /\ match_state cd j c1 m1 c2 m2*)
      ; thread_diagram :
          forall U st1 m1 st1' m1',
            thread_step hb1 Sem1 Sem2 ge1 U st1 m1 st1' m1' ->
            forall cd st2 mu m2,
              match_state cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      match_state cd' mu' st1' m1' st2' m2'
                      /\ (thread_step_plus Sem2 ge2 U st2 m2 st2' m2'
               \/ (thread_step_star Sem2 ge2 U st2 m2 st2' m2' /\ core_ord cd' cd))
      ; machine_diagram :
          forall U tr st1 m1 U' tr' st1' m1',
            machine_step hb1 Sem1 Sem2 U tr st1 m1 U' tr' st1' m1' ->
            forall cd st2 mu m2,
              match_state cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      match_state cd' mu' st1' m1' st2' m2'
                      /\ machine_step Sem2 ge2 U tr st2 m2 U' tr' st2' m2'
      ; thread_halted :
          forall cd mu U c1 m1 c2 m2 v1,
            match_state cd mu c1 m1 c2 m2 ->
            conc_halted Sem1 U c1 = Some v1 ->
            exists j v2,
              halt_inv j ge1 v1 m1 ge2 v2 m2
              /\ conc_halted Sem2 U c2 = Some v2
      ; thread_running:
          forall cd mu c1 m1 c2 m2 ,
            match_state cd mu c1 m1 c2 m2 ->
            forall i, runing_thread Sem1 c1 i <-> runing_thread Sem2 c2 i
            (* runing_thread Sem1 c1 = runing_thread Sem2 c2 *)
 }.
                                      
