Require Import concurrency.DryMachineSourceCore.
Require Import concurrency.x86_context.

Require Import concurrency.CoreSemantics_sum.
Require Import concurrency.HybridMachine.

(*Import the dry CPM for Clight_core*)
Import DMS.
Import DryMachine.

(*Build the hybrid context*)
Notation hb:=(Some 0).
Definition Hybrid_resources:=
  Build_Resources_rec
    dry_machine.LocksAndResources.res
    dry_machine.LocksAndResources.lock_info.
Definition Sems:= Build_Semantics_rec SEM.G SEM.C SEM.CLC_evsem.
Definition Semt:= X86SEM_rec. (*Need both for hybrid*)
Definition Hybrid_Sem:= CoreSem_Sum hb Sems Semt.
Definition Hybrid_MachineSem U r := new_MachineSemantics hb Sems Semt U r.
Definition Hybrid_new_machine U r:=
(HybridMachineSig.ConcurMachineSemantics _ _ _ (HybridMachine hb Sems Semt) U r).
Definition Hybrid_Thread_pool_context:=
  OrdinalThreadPool_rec Hybrid_resources Hybrid_Sem.

(* Hybrid ThreadPool *)
Definition make_hybrid_thread_pool (tp:thread_pool): t_ Hybrid_Thread_pool_context.
  destruct tp.
  econstructor; eauto.
  intros.
  eapply pool in X; destruct X;
    [eapply Krun|eapply Kblocked| eapply Kresume | eapply Kinit]; auto;
  apply SState; auto.
Defined.

(* Hybrid trace*)
Definition make_hybrid_event (ev:ErasedMachine.Events.machine_event): 
  HybridMachineSig.machine_event.
  destruct ev.
  - constructor ; eauto.
  - constructor 2; eauto.
    inversion s;
      [eapply HybridMachineSig.release|
       eapply HybridMachineSig.acquire|
       eapply HybridMachineSig.mklock|
       eapply HybridMachineSig.freelock|
       eapply HybridMachineSig.spawn|
       eapply HybridMachineSig.failacq]; eauto.
Qed.
  
Fixpoint make_hybrid_trace (tr: SC.event_trace): list HybridMachineSig.machine_event.
  induction tr.
  - exact nil.
  - apply cons; auto.
    exact (make_hybrid_event a).
Qed.

(* Initial simulation *)
(*This lemma is under construction*)
(*Lemma Hcore_initial :
    forall j c1 vals1 m1 m1' vals2 m2 m2' main,
    initial_machine Sem1 ge1 m1 main vals1 = Some (c1, m1') ->
    exists cd c2,
      HybridMachine.initial_machine hb Hybrid_Sems Hybrid_Semt main vals2 = Some (c2, m2')
      /\ MSmatch_states cd j c1 (option_proj m1 m1') c2 (option_proj m2 m2').*)

(* Thread step 1to1 simulation*)
Lemma thread_step_diagram:
    forall U0 gs gt st1 m st1' m' U r,
    machine_semantics.thread_step (new_DMachineSem U0 r) gs U st1 m st1' m' ->
    machine_semantics.thread_step (Hybrid_new_machine U0 r) (gs,gt) U
                                  ( make_hybrid_thread_pool st1) m
                                  (make_hybrid_thread_pool st1') m'.
Admitted.
(* Machine step 1to1 simulation*)
(* Note the traces should be nil...*)
Lemma machine_step_diagram:
    forall U0 gs gt st1 m st1' tr tr' m' U U' r,
    machine_semantics.machine_step (new_DMachineSem U0 r) gs U tr st1 m U' tr' st1' m' ->
    machine_semantics.machine_step (Hybrid_new_machine U0 r) (gs,gt) U (make_hybrid_trace tr)
                                  ( make_hybrid_thread_pool st1) m U' (make_hybrid_trace tr')
                                  (make_hybrid_thread_pool st1') m'.
Admitted.

(* Same halted states *) 
Lemma same_halted :
    forall U0 U c1 v1 r,
    machine_semantics.conc_halted (new_DMachineSem U0 r) U c1 = Some v1 ->
    machine_semantics.conc_halted (Hybrid_new_machine U0 r) U ( make_hybrid_thread_pool c1) = Some v1.
Admitted.

Lemma same_thread_running:
    forall U0 r c i,
      machine_semantics.runing_thread (new_DMachineSem U0 r) c i <->
      machine_semantics.runing_thread (Hybrid_new_machine U0 r) ( make_hybrid_thread_pool c) i.
Admitted.