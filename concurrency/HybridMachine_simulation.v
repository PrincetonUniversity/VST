From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import Coqlib.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.

Require Import msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import sepcomp.semantics.
Require Import sepcomp.event_semantics.
Require Export concurrency.semantics.
Require Export concurrency.lksize.
Require Import concurrency.threadPool. Export threadPool.

Require Import concurrency.machine_semantics.
Require Import concurrency.permissions.
Require Import concurrency.bounded_maps.
Require Import concurrency.addressFiniteMap.

Require Import concurrency.scheduler.
Require Import Coq.Program.Program.

Require Import concurrency.safety.

Require Import concurrency.coinductive_safety.


Require Import concurrency.concurrent_machine_rec.

Require Import veric.res_predicates.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import Asm_core.
Require Import ccc26x86.Asm_event.

Require Import concurrency.HybridMachineSig.
Require Import concurrency.HybridMachine.

Require Import concurrency.CoreSemantics_sum.

Require Import compcert.common.Smallstep.

Require Import concurrency.machine_semantics_lemmas.


Set Bullet Behavior "Strict Subproofs".

Section HybridSimulation.

  Variable (Sems Semt : Semantics_rec).
  Variable (hb1 hb2: option nat).

  Variable U: seq.seq nat.

  (*I use none, but it should be the initial memory. FIX. *)
  Definition HCSem Sems Semt hb U:=
    (ConcurMachineSemantics _ _ _ (HybridMachine hb Sems Semt) U None).
  Notation Sem1:= (HCSem Sems Semt hb1 U).
  Notation Sem2:= (HCSem Sems Semt hb2 U).
  
  Notation C1:= (t_ (ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (ThreadPool hb2 Sems Semt)).
  Notation G:= (semG Sems * semG Semt)%type.
  Variable ge:G.

  Variable core_data: Type.
  Variable core_ord : core_data -> core_data -> Prop.
  Variable core_ord_wf : well_founded core_ord.
  
  Record HybridMachine_simulation
         (concur_match: core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
         main:=
    { Hybfsim_order_wf: well_founded core_ord
      ; core_initial :
          forall j c1 vals1 m1 vals2 m2,
            machine_semantics.initial_machine Sem1 ge main vals1 = Some c1 ->
            exists cd c2,
              machine_semantics.initial_machine Sem2 ge main vals2 = Some c2
           /\ concur_match cd j c1 m1 c2 m2
      ; thread_diagram :
          forall U st1 m1 st1' m1',
            machine_semantics.thread_step Sem1 ge U st1 m1 st1' m1' ->
            forall (cd:core_data) st2 mu m2,
              concur_match cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      concur_match cd' mu' st1' m1' st2' m2'
                      /\ (thread_step_plus Sem2 ge U st2 m2 st2' m2'
                         \/ (thread_step_star Sem2 ge U st2 m2 st2' m2' /\ core_ord cd' cd))
      ; machine_diagram :
          forall U tr st1 m1 U' tr' st1' m1',
            machine_semantics.machine_step Sem1 ge U tr st1 m1 U' tr' st1' m1' ->
            forall cd st2 mu m2,
              concur_match cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd',
                    concur_match cd' mu st1' m1' st2' m2'
                    /\ machine_semantics.machine_step Sem2 ge U tr st2 m2 U' tr' st2' m2'
      ; thread_halted :
          forall cd mu U c1 m1 c2 m2 v1,
            concur_match cd mu c1 m1 c2 m2 ->
            conc_halted Sem1 U c1 = Some v1 ->
            exists v2,
              conc_halted Sem2 U c2 = Some v2
      ; thread_running:
          forall cd mu c1 m1 c2 m2 ,
            concur_match cd mu c1 m1 c2 m2 ->
            forall i, runing_thread Sem1 c1 i <-> runing_thread Sem2 c2 i
            (* runing_thread Sem1 c1 = runing_thread Sem2 c2 *)
    }.
  
End HybridSimulation.

Inductive HM_forward_sim Sems Semt hb1 hb2 U G v:=
| Build_HM_forward_sim: forall core_data core_order match_states,
    HybridMachine_simulation Sems Semt hb1 hb2 U G
                             core_data core_order match_states v ->
    HM_forward_sim Sems Semt hb1 hb2 U G v.
Section HybridListComposition.

  
  Variable (Sems Semt : Semantics_rec).
  Variable (hb1 hb2 hb3: option nat).

  Variable U: seq.seq nat.

  (*I use none, but it should be the initial memory. FIX. *)
  Notation Sem1:= (HCSem Sems Semt hb1 U).
  Notation Sem2:= (HCSem Sems Semt hb2 U).
  Notation Sem3:= (HCSem Sems Semt hb3 U).
  
  Notation C1:= (t_ (ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (ThreadPool hb2 Sems Semt)).
  Notation C3:= (t_ (ThreadPool hb3 Sems Semt)).
  Notation G:= (semG Sems * semG Semt)%type.
  Variable ge:G.
  
  Variable data : Type.
  Notation ls_data:=(list data).
  Variable order: data -> data -> Prop.
  Parameter ls_order : (data -> data -> Prop) -> list data -> list data -> Prop.
  Parameter ls_ord_wf : forall order, well_founded order -> well_founded (ls_order order).
  Notation ls_order':=(ls_order order).

  Notation HybridMachine_simulation hb1 hb2:=
    (HybridMachine_simulation Sems Semt hb1 hb2 U ge ).

  Variable v:val.
  
  Variable (match12 : list data -> meminj -> C1 -> mem -> C2 -> mem -> Prop).
  Hypothesis Hsimulation12:
      HybridMachine_simulation hb1 hb2 ls_data ls_order' match12 v.

  Variable (match23 : data -> meminj -> C2 -> mem -> C3 -> mem -> Prop).
  Hypothesis Hsimulation23:
      HybridMachine_simulation hb2 hb3 data order match23 v.

  Definition ls_compose_match
             (d123:list data)
             (f:meminj)
             (c1:C1) (m1:mem) (c3:C3)(m3:mem): Prop:= 
    exists c2 m2 f12 f23,
      exists d12 d23, d123 = d23::d12 /\
      match12 d12 f12 c1 m1 c2 m2 /\
      match23 d23 f23 c2 m2 c3 m3 /\
      f = compose_meminj f12 f23.
      
  Lemma Hsim_ls_composition:
    HybridMachine_simulation hb1 hb3
                             ls_data
                             ls_order'
                             ls_compose_match v. 
  Proof.
    constructor.
    - admit. (*wf of list order*)
    - admit. (*Initial*)
    - admit. (*Thread step*)
    - intros ? ? ? ? ? tr3 ? ? ? ? st3 ? m3 ?.
      destruct H0 as
          (c2 & m2 & f12 & f23 & d12 & d23 & D & M12 & M23 & inj_comp).
      eapply Hsimulation12 in H; eauto. 
      destruct H as
          (c2' & m2' & cd'' & M12' & STEP2).
      eapply Hsimulation23 in STEP2; eauto.
      destruct STEP2 as (c3' & m3' & cd3 & M23' & STEP3).
      exists c3', m3', (cd3::cd''); split; eauto.
      exists c2', m2', f12, f23, cd'', cd3; split; eauto.
    - admit. (*Halted step*)
    - admit. (*Running step*)
  Admitted.


End HybridListComposition.

Section HybridComposition.

  
  Variable (Sems Semt : Semantics_rec).
  Variable (hb1 hb2 hb3: option nat).

  Variable U: seq.seq nat.

  (*I use none, but it should be the initial memory. FIX. *)
  Notation Sem1:= (HCSem Sems Semt hb1 U).
  Notation Sem2:= (HCSem Sems Semt hb2 U).
  Notation Sem3:= (HCSem Sems Semt hb3 U).
  
  Notation C1:= (t_ (ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (ThreadPool hb2 Sems Semt)).
  Notation C3:= (t_ (ThreadPool hb3 Sems Semt)).
  Notation G:= (semG Sems * semG Semt)%type.
  Variable ge:G.
  
  Variable data12 data23: Type.
  Variable ord12 : data12 -> data12 -> Prop.
  Variable ord23 : data23 -> data23 -> Prop.
  Variable ord_wf12 : well_founded ord12.
  Variable ord_wf23 : well_founded ord23.

  Notation HybridMachine_simulation hb1 hb2:=
    (HybridMachine_simulation Sems Semt hb1 hb2 U ge ).

  Variable v:val.
  
  Variable (match12 : data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop).
  Hypothesis Hsimulation12:
      HybridMachine_simulation hb1 hb2 data12 ord12 match12 v.

  Variable (match23 : data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop).
  Hypothesis Hsimulation23:
      HybridMachine_simulation hb2 hb3 data23 ord23 match23 v.

  Definition compose_match
             (d123:data23 * data12)
             (f:meminj)
             (c1:C1) (m1:mem) (c3:C3)(m3:mem): Prop:= 
    exists c2 m2 f12 f23, 
      match12 (snd d123) f12 c1 m1 c2 m2 /\
      match23 (fst d123) f23 c2 m3 c3 m3 /\
      f = compose_meminj f12 f23.
      
  Lemma Hsim_composition:
    HybridMachine_simulation hb1 hb3
                             (data23 * data12)
                             (lex_ord (clos_trans _ ord23) ord12)
                             compose_match v. 
  Proof.
    constructor.
    - apply wf_lex_ord. apply Transitive_Closure.wf_clos_trans.
      eapply Hybfsim_order_wf; eauto.
      eapply Hybfsim_order_wf; eauto.
    - admit. (*Initial*)
    - admit. (*Thread step*)
    - admit. (*Machine step*)
    - admit. (*Halted step*)
    - admit. (*Running step*)
  Admitted.


End HybridComposition.