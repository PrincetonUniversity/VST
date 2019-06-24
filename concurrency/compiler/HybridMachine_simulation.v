Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.

Require Import VST.msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Export VST.concurrency.common.semantics.
Require Export VST.concurrency.common.lksize.
Require Import VST.concurrency.common.threadPool. Export threadPool.

Require Import VST.concurrency.common.machine_semantics.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.addressFiniteMap.

Require Import VST.concurrency.common.scheduler.
Require Import Coq.Program.Program.

Require Import VST.concurrency.compiler.safety.

Require Import VST.concurrency.compiler.coinductive_safety.


Require Import VST.concurrency.common.HybridMachineSig.

Require Import VST.veric.res_predicates.

Require Import VST.concurrency.common.HybridMachine.

Require Import VST.concurrency.compiler.CoreSemantics_sum.

Require Import compcert.common.Smallstep.

Require Import VST.concurrency.common.machine_semantics_lemmas.

Import Events event_semantics Values.

Set Implicit Arguments.

Section HybridSimulation. 

  (*
  Variable (Sems Semt : semantics.Semantics).
  Variable (hb1 hb2: option nat).
  (*Variable (Resources : Resources_rec).
  Variable (MatchCAsm: meminj -> corestate -> mem -> Asm_coop.state -> mem -> Prop).*)
  
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
  Variable (ge_inv: G1 -> G2 -> Prop). *)

  Context (SG TG TID SCH SC TC R1 R2 (*s_thread_type t_thread_type*): Type).
  Variable SourceHybridMachine: @ConcurSemantics SG TID SCH (list machine_event) SC mem R1.
  Variable TargetHybridMachine: @ConcurSemantics TG TID SCH (list machine_event) TC mem R2.
  (* 
     Variable opt_init_mem_source : option Memory.Mem.mem.
     Variable opt_init_mem_target : option Memory.Mem.mem.
  *)

  (* Inductive inject_address (f : meminj) : address -> address -> Prop :=
  | inj_addr : forall b1 delt b2 ofs, f b1 = Some (b2, ofs) ->
      inject_address f (b1, ofs) (b2, ofs + delt). *)

  Inductive inject_address f: address -> address -> Prop :=
  | build_inject_address:
      forall b1 b2 ofs1 ofs2 delt,
        f b1 = Some (b2, delt) ->
        ofs2 = ofs1 + delt ->
        inject_address f (b1, ofs1) (b2,ofs2).
  Lemma inject_address_incr:
    forall f f' l1 l2,
      inject_incr f f' ->  
      inject_address f l1 l2 ->
      inject_address f' l1 l2.
  Proof.
    intros * Hincr Hinj. inv Hinj.
    econstructor; auto.
    eapply Hincr; assumption.
  Qed.
  Definition inject_delta_content: meminj -> delta_content -> delta_content -> Prop:=
    fun f dc1 dc2 =>
    True.
  (* Same as memories that are injected...
     but, we should reconsider if we really want sync_events.
   *)
  
  Inductive inject_sync_event (f : meminj) : sync_event -> sync_event -> Prop :=
  | inj_release : forall l1 l2 r1 r2, inject_address f l1 l2 ->
      match r1, r2 with
      | Some (a1), Some (a2) => inject_delta_content f a1 a2
      | None, None => True
      | _, _ => False
      end ->
      inject_sync_event f (release l1 r1) (release l2 r2)
  | inj_acquire : forall l1 l2 r1 r2, inject_address f l1 l2 ->
      match r1, r2 with
      | Some (a1), Some (a2) => inject_delta_content f a1 a2
      | None, None => True
      | _, _ => False
      end ->
      inject_sync_event f (acquire l1 r1) (acquire l2 r2)
  | inj_mklock : forall l1 l2, inject_address f l1 l2 ->
      inject_sync_event f (mklock l1) (mklock l2)
  | inj_freelock : forall l1 l2, inject_address f l1 l2 ->
      inject_sync_event f (freelock l1) (freelock l2)
  | inj_spawn : forall l1 l2 r1 r1' r2 r2', inject_address f l1 l2 ->
      match r1, r2 with
      | Some a1, Some a2 =>
          inject_delta_content f a1 a2
      | None, None => True
      | _, _ => False
      end ->
      match r1', r2' with
      | Some a1', Some a2' =>
          inject_delta_content f a1' a2'
      | None, None => True
      | _, _ => False
      end ->
      inject_sync_event f (spawn l1 r1 r1') (spawn l2 r2 r2')
  | inj_failacq : forall l1 l2, inject_address f l1 l2 ->
      inject_sync_event f (failacq l1) (failacq l2).
  Inductive inj_free (f:meminj): block * Z * Z -> block * Z * Z -> Prop:=
  | build_inj_free:  forall b1 b2 lo1 lo2 hi1 hi2 delt,
      f b1 = Some (b2, delt) ->
      lo2 = lo1 + delt ->
      hi2 = hi1 + delt ->
      inj_free f (b1,lo1,hi1) (b2,lo2,hi2).
  Lemma inj_free_incr:
    forall f f' ls1 ls2,
      inject_incr f f' ->
      inj_free f  ls1 ls2 ->
      inj_free f' ls1 ls2.
  Proof. intros; inv H0; econstructor; eauto. Qed.
    
  Inductive inject_mem_event : meminj -> mem_event -> mem_event -> Prop:=
  | inject_Write: forall f b1 b2 ofs1 ofs2 delt ls1 ls2,
      f b1 = Some (b2, delt) ->
      ofs2 = ofs1 + delt ->
      list_memval_inject f ls1 ls2 ->
      inject_mem_event f (Write b1 ofs1 ls1) (Write b2 ofs2 ls2)
  | inject_Read: forall f b1 b2 ofs1 ofs2 delt ls1 ls2 n,
      f b1 = Some (b2, delt) ->
      ofs2 = ofs1 + delt ->
      list_memval_inject f ls1 ls2 ->
      inject_mem_event f (Read b1 ofs1 n ls1)(Read b2 ofs2 n ls2)
  | inject_Alloc: forall f b1 b2 lo1 lo2 hi1 hi2 delt,
      f b1 = Some (b2, delt) ->
      lo2 = lo1 + delt ->
      hi2 = hi1 + delt ->
      inject_mem_event f (Alloc b1 lo1 hi1) (Alloc b2 lo2 hi2)
  | inject_Free: forall f ls1 ls2,
      List.Forall2 (inj_free f) ls1 ls2 ->
      inject_mem_event f (Free ls1) (Free ls2).
  Lemma list_memval_inject_incr:
        forall f f' ls1 ls2,
          inject_incr f f' ->
          list_memval_inject f  ls1 ls2 ->
          list_memval_inject f' ls1 ls2.
  Proof.
    intros.
    eapply list_map_rel_ind; eauto.
    - constructor.
    - constructor; eauto.
      eapply memval_inject_incr; eassumption.
  Qed.
  
  Lemma Forall2_impl: forall {A B} (P Q : A -> B -> Prop) l1 l2,
      (forall a b, P a b -> Q a b) -> List.Forall2 P l1 l2 -> List.Forall2 Q l1 l2.
  Proof.
    induction 2; constructor; auto.
  Qed.
  Lemma inject_mem_event_incr:
    forall f f' a b,
      inject_incr f f' ->
      inject_mem_event f a b ->
      inject_mem_event f' a b.
  Proof.
    intros.
    inv H0; [econstructor 1
            |econstructor 2
            |econstructor 3
            |econstructor 4]; eauto.
    - eapply list_memval_inject_incr; eauto.
    - eapply list_memval_inject_incr; eauto.
    - eapply Forall2_impl.
      2: apply H1.
      intros. eapply inj_free_incr; eauto.
  Qed.
  
  Inductive inject_mevent (f : meminj) : machine_event -> machine_event -> Prop :=
  | inj_internal : forall n me1 me2, inject_mem_event f me1 me2 ->
      inject_mevent f (internal n me1) (internal n me2)
  | inj_external : forall n se1 se2, inject_sync_event f se1 se2 ->
                                inject_mevent f (external n se1) (external n se2).

  Lemma inject_sync_event_incr:
    forall f f' a b,
      inject_incr f f' ->
      inject_sync_event f a b ->
      inject_sync_event f' a b.
  Proof.
    intros. inv H0;
              [constructor 1
              |constructor 2
              |constructor 3
              |constructor 4
              |constructor 5
              |constructor 6]; auto;
                eapply inject_address_incr; eassumption.
  Qed.
  
  Lemma inject_mevent_incr:
        forall f f' a b,
          inject_incr f f' ->
          inject_mevent f a b ->
          inject_mevent f' a b.
      Proof.
        intros.
        inv H0; simpl; [left | right].
        - eapply inject_mem_event_incr; eauto.
        - eapply inject_sync_event_incr; eauto.
      Qed.
  Lemma inject_incr_trace:
    forall (tr1 tr2 : list Events.machine_event) (mu f' : meminj),
      inject_incr mu f' ->
      List.Forall2 (inject_mevent mu) tr1 tr2 ->
      List.Forall2 (inject_mevent f') tr1 tr2.
  Proof.
    intros. eapply Forall2_impl; try eassumption.
    - intros; eapply inject_mevent_incr; eassumption.
  Qed.

  Record HybridMachine_simulation_properties
         (index: Type)(match_state : index -> meminj -> SC -> mem -> TC -> mem -> Prop) :=
    { core_ord : index -> index -> Prop
      ; core_ord_wf : well_founded core_ord

      (* This is the match relation for initial state of the initial core:*)
      (* That is property given by sequential theorem about inital_states *)
      (*; initial_source_thread:
          mem -> s_thread_type -> val -> seq.seq val -> Prop
      ; initial_target_thread:
          mem -> t_thread_type -> val -> seq.seq val -> Prop *)
      ; initial_setup :
          forall (*s_init_thread*) s_mem s_mem' main main_args s_mach_state r1,
            (*initial_source_thread s_mem s_init_thread main main_args -> *)
            machine_semantics.initial_machine SourceHybridMachine r1 s_mem s_mach_state s_mem' main main_args ->
            exists j cd t_mach_state t_mem t_mem' r2,
              machine_semantics.initial_machine TargetHybridMachine r2 t_mem t_mach_state t_mem' main main_args
           /\ match_state cd j s_mach_state s_mem' t_mach_state t_mem'
      ; thread_diagram :
          forall sge tge U tr1 st1 m1 st1' m1',
            thread_step SourceHybridMachine sge U st1 m1 st1' m1' ->
            forall cd tr2 st2 mu m2,
              match_state cd mu st1 m1 st2 m2 ->
              Forall2 (inject_mevent mu) tr1 tr2 ->
              exists st2', exists m2', exists cd', exists mu',
                      match_state cd' mu' st1' m1' st2' m2'
                      /\ Forall2 (inject_mevent mu') tr1 tr2
                      /\ (thread_step_plus (TargetHybridMachine) tge U st2 m2 st2' m2'
               \/ (thread_step_star (TargetHybridMachine) tge U st2 m2 st2' m2' /\ core_ord cd' cd))
      ; machine_diagram :
          forall sge tge U tr1 st1 m1 U' tr1' st1' m1',
            machine_step SourceHybridMachine sge U tr1 st1 m1 U' tr1' st1' m1' ->
            forall cd tr2 st2 mu m2,
              match_state cd mu st1 m1 st2 m2 ->
              Forall2 (inject_mevent mu) tr1 tr2 ->
              exists tr2', exists st2', exists m2', exists cd', exists mu',
                      match_state cd' mu' st1' m1' st2' m2'
                      /\ Forall2 (inject_mevent mu') tr1' tr2'
                      /\ machine_step (TargetHybridMachine) tge U tr2 st2 m2 U' tr2' st2' m2'
      ; thread_halted :
          forall cd mu U c1 m1 c2 m2 v1,
            match_state cd mu c1 m1 c2 m2 ->
            conc_halted SourceHybridMachine U c1 = Some v1 ->
            exists v2,
              conc_halted TargetHybridMachine U c2 = Some v2
      ; thread_running:
          forall cd mu c1 m1 c2 m2 ,
            match_state cd mu c1 m1 c2 m2 ->
            forall i, running_thread SourceHybridMachine c1 i <-> running_thread TargetHybridMachine c2 i
    }.

  Record HybridMachine_simulation:=
    { index: Type
      ; match_state : index -> meminj -> SC -> mem -> TC -> mem -> Prop
      ; SIM:> @HybridMachine_simulation_properties index match_state}.

End HybridSimulation.
