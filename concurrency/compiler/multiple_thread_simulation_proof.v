Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.Compcert_lemmas.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.list_order.
Require Import VST.concurrency.compiler.Asm_lemmas.
Require Import VST.concurrency.compiler.synchronisation_symulations.
Require Import VST.concurrency.compiler.single_thread_simulation_proof.



Require Import VST.concurrency.lib.Coqlib3.

Require Import VST.concurrency.memsem_lemmas.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.compiler.concur_match.
Require Import VST.concurrency.lib.Coqlib3.


Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import bounded_maps.


Import HybridMachineSig.


Section ThreadedSimulation.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  
  (*Module MySyncSimulation:= SyncSimulation CC_correct Args.
  Import MySyncSimulation.*)
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  (* Module MyConcurMatch := ConcurMatch CC_correct Args.*)

  

  
  Section ThreadedSimulation.
    (*Import MySimulationTactics.MyConcurMatch.*)
    
    Section CompileNThreads.
      
      Definition nth_index:= (list (option compiler_index)).
      Definition list_lt: nth_index -> nth_index -> Prop:=
        list_ord (opt_rel' (InjorderX compiler_sim)).

      Lemma list_lt_wf: well_founded list_lt.
      Proof. eapply list_ord_wf, option_wf, Injfsim_order_wfX. Qed.
      
      Inductive match_state:
        forall n, nth_index ->
             Values.Val.meminj ->
             ThreadPool (Some 0)%nat -> Memory.Mem.mem ->
             ThreadPool (Some n) -> Memory.Mem.mem -> Prop:=
      | refl_match: forall tp m,
          (* mem_compatible tp m -> *)
          match_state 0 nil (Mem.flat_inj (Mem.nextblock m)) tp m tp m
      | step_match_state:
          forall n ocd ils jn jSn tp0 m0 tpn mn tpSn mSn,
            match_state n ils jn tp0 m0 tpn mn ->
            concur_match n ocd jSn tpn mn tpSn mSn ->
            match_state (S n) (cons ocd ils) (compose_meminj jn jSn) tp0 m0 tpSn mSn.
      Lemma thread_step_mem_fwd:
        forall hb m sge U st1 m1 st1' m1',
          machine_semantics.thread_step (HybConcSem hb m) sge U st1 m1 st1' m1' ->
          ((Mem.nextblock m1) <= (Mem.nextblock m1'))%positive.
      Proof.
        intros.
        inv H; simpl in *.
        inv Htstep.
        eapply event_semantics.event_semantics_mem_fw in Hcorestep.
        simpl in Hcorestep; auto.
      Qed.
      Lemma machine_step_mem_fwd:
        forall hb m sge U tr1 st1 m1 U' tr1' st1' m1',
          machine_semantics.machine_step (HybConcSem hb m)
                                         sge U tr1 st1 m1 U' tr1' st1' m1'->
          ((Mem.nextblock m1) <= (Mem.nextblock m1'))%positive.
      Proof. Admitted.
      
      Lemma machine_step_trace_wf:
        forall hb m sge U tr1 st1 m1 U' x st1' m1',
          machine_semantics.machine_step (HybConcSem hb m)
                                         sge U tr1 st1 m1 U' (tr1++x) st1' m1'->
          Forall2 (inject_mevent (Mem.flat_inj (Mem.nextblock m1'))) x x.
      Proof.
      Admitted. (*This comes from self injection? *)

      (*This should probably go soewhere else? *)
      Lemma flat_inj_lt:
        forall b b', (b <= b')%positive ->
                inject_incr (Mem.flat_inj b) (Mem.flat_inj b').
      Proof.
        unfold Mem.flat_inj.
        intros ** ??? HH.
        match_case in HH. rewrite <- HH.
        match_case.
        xomega.
      Qed.
      
      Local Ltac inv_match0:=
        match goal with
          H: match_state 0 _ _ _ _ _ _ |- _ =>
          inversion H; subst_sig; try clear H
        end.
      Lemma Forall_cat:
        forall {A B} (f: A -> B -> Prop) a1 a2 b1 b2,
          Forall2 f a1 b1 ->
          Forall2 f a2 b2 ->
          Forall2 f (a1 ++  a2) (b1 ++ b2).
      Proof.
        intros A B f a1.
        induction a1.
        - intros. inv H.
          do 2 rewrite seq.cat0s; auto.
        - simpl; intros.
          inv H. econstructor; auto.
      Qed.
      Lemma machine_step_traces:
        forall hb m sge U tr1 st1 m1 U' tr1' st1' m1',
          machine_semantics.machine_step (HybConcSem hb m)
                                         sge U tr1 st1 m1 U' tr1' st1' m1'->
          exists tr_tail, tr1' = tr1 ++ tr_tail /\
                     forall tr2, machine_semantics.machine_step
                              (HybConcSem hb m)
                              sge U tr2 st1 m1 U' (tr2 ++ tr_tail) st1' m1'.
      Admitted.
      
      Lemma trivial_self_injection:
        forall m : option mem,
          simulation_properties_exposed
            (HybConcSem (Some 0)%nat m)
            (HybConcSem (Some 0)%nat m)
            invariant
            mem_compatible
            (match_state 0)
            list_lt.
      Proof.
        simpl; intros.
        unshelve econstructor; [econstructor|].
        - eapply list_lt_wf.
        - intros; normal; eauto.
          + econstructor.
        - intros; normal_hyp.
          assert (inject_incr mu (Mem.flat_inj (Mem.nextblock m1'))).
            { inv_match0; eapply flat_inj_lt.
              eapply thread_step_mem_fwd; apply H. }
          normal.
          + econstructor.
          + eapply inject_incr_trace; try eassumption.  
          + left. exists 0%nat; inv_match0.
            do 2 eexists; split; try reflexivity; eauto.
          + assumption.
        - intros; inv_match0.
          eapply machine_step_traces in H; normal_hyp; subst.
          do 5 econstructor; repeat weak_split.
          + econstructor.
          + eapply Forall_cat.
            eapply inject_incr_trace; try eassumption.
            apply flat_inj_lt.
            eapply machine_step_mem_fwd; eauto.
            eapply machine_step_trace_wf; eapply H2.
          + eapply H2.
          + specialize (H2 tr2); apply machine_step_mem_fwd in H2.
            apply flat_inj_lt; eauto.
        - intros; inv_match0; normal; eauto.
        - intros; inv_match0; reflexivity.
        - reflexivity.
          
          Unshelve.
          all: eauto.
      Qed.
      
      
      Lemma step_diagram_helper:
        forall mu (ord: relation nth_index) tr1 tr2 m U hb cd m1' st1' tge st2 m2, 
          (exists (st2' : ThreadPool (Some hb)) (m2' : mem) (cd' : nth_index) 
             (mu' : meminj),
              match_state hb cd' mu' st1' m1' st2' m2' /\
              Forall2 (inject_mevent mu') tr1 tr2 /\
              (machine_semantics_lemmas.thread_step_plus
                 (HybConcSem (Some hb) m) 
                 tge U st2 m2 st2' m2' \/
               machine_semantics_lemmas.thread_step_star
                 (HybConcSem (Some hb) m) 
                 tge U st2 m2 st2' m2' /\ ord cd' cd) /\
          inject_incr mu mu')
          <->
          exists (st2' : ThreadPool (Some hb)) (m2' : mem) (cd' : nth_index) 
            (mu' : meminj),
            match_state hb cd' mu' st1' m1' st2' m2' /\
            Forall2 (inject_mevent mu') tr1 tr2 /\
            (machine_semantics_lemmas.thread_step_plus
               (HybConcSem (Some hb) m) 
               tge U st2 m2 st2' m2' \/  m2=m2' /\ st2=st2' /\ ord cd' cd) /\
          inject_incr mu mu'.
      Proof.
        intros.
        split; intros; normal; eauto.
        - destruct H1; auto.
          destruct H1 as [[n H1] Hord]; destruct n.
          + inv H1; auto.
          + left; exists n; auto.
        - destruct H1; [left| right]; auto.
          normal; subst; auto.
          exists 0%nat. constructor.
      Qed.
      
      Lemma inject_mem_event_interpolation:
        forall jn jSn ev1 ev3,
          (inject_mem_event (compose_meminj jn jSn)) ev1 ev3 ->
          exists ev2,
            inject_mem_event jn ev1 ev2 /\
            inject_mem_event jSn ev2 ev3 .
      Proof.
        intros.
        destruct ev1.
        - inv H.
      Admitted.
      Lemma inject_mem_sync_interpolation:
        forall jn jSn ev1 ev3,
          (inject_sync_event (compose_meminj jn jSn)) ev1 ev3 ->
          exists ev2,
            inject_sync_event jn ev1 ev2 /\
            inject_sync_event jSn ev2 ev3 .
      Proof.
        intros.
        destruct ev1.
        - inv H.
      Admitted.
      Lemma inject_mevent_interpolation:
        forall jn jSn ev1 ev3,
          (inject_mevent (compose_meminj jn jSn)) ev1 ev3 ->
          exists ev2,
            inject_mevent jn ev1 ev2 /\
            inject_mevent jSn ev2 ev3 .
      Proof.
        intros.
        destruct ev1.
        - inv H.
          eapply inject_mem_event_interpolation in H3.
          normal_hyp; repeat (econstructor; eauto).
        - inv H.
          eapply inject_mem_sync_interpolation in H3.
          normal_hyp; repeat (econstructor; eauto).
      Qed.
      
      
      Lemma list_inject_mevent_interpolation:
        forall jn jSn tr1 tr3,
          Forall2 (inject_mevent (compose_meminj jn jSn)) tr1 tr3 ->
          exists tr2,
            Forall2 (inject_mevent jn) tr1 tr2 /\
            Forall2 (inject_mevent jSn) tr2 tr3 .
      Proof.
        intros ?? tr1.
        induction tr1.
        - intros tr3 HH; inv HH.
          econstructor; eauto.
        - intros tr3 HH; inv HH.
          eapply IHtr1 in H3.
          eapply inject_mevent_interpolation in H1.
          normal_hyp.
          eexists; repeat (econstructor; eauto).
      Qed.            
      Lemma inject_mevent_compose:
        forall j1 j2 t1 t2 t3,
          inject_mevent j1 t1 t2->
          inject_mevent j2 t2 t3->
          inject_mevent (compose_meminj j1 j2) t1 t3.
      Admitted.
      Lemma forall_inject_mevent_compose:
        forall j1 j2 t1 t2 t3,
          Forall2 (inject_mevent j1) t1 t2->
          Forall2 (inject_mevent j2) t2 t3->
          Forall2 (inject_mevent (compose_meminj j1 j2)) t1 t3.
      Proof.
        intros ?? t1.
        induction t1.
        - intros. inv H. inv H0. constructor.
        - intros. inv H. inv H0. constructor; eauto.
          eapply inject_mevent_compose; eauto.
      Qed.
      Lemma match_state_invariant:
              forall n x3 x4 st1' m1' x1 x2,
                invariant st1' ->
                match_state n x3 x4 st1' m1' x1 x2 ->
                invariant x1.
            Proof.
              induction n.
              - intros. inv H0; auto.
              - intros. inv H0. subst_sig.
                eapply H8.
            Qed.
            Lemma match_state_cmpt:
              forall n x3 x4 st1' m1' x1 x2,
                mem_compatible st1' m1' ->
                match_state n x3 x4 st1' m1' x1 x2 ->
                mem_compatible x1 x2.
            Proof.
              induction n.
              - intros. inv H0; auto.
              - intros. inv H0. subst_sig.
                eapply H8.
            Qed.
            
      
      (* Not this lemma can be generalized away from 
         splicit index and orders (given here by list_lt).
         Since it's only used once, we live this form for now.
       *)
      
      Lemma simulation_inductive_case:
        forall n : nat,
          (forall m : option mem,
              simulation_properties_exposed
                (HybConcSem (Some 0)%nat m)
                (HybConcSem (Some n) m)
                invariant
                mem_compatible
                (match_state n)
                list_lt) ->
          (forall m : option mem,
              simulation_properties_exposed
                (HybConcSem (Some n) m)
                (HybConcSem (Some (S n)) m)
                invariant
                mem_compatible
                (concur_match n)
                 (opt_rel' (InjorderX compiler_sim))) ->
          forall m : option mem,
            simulation_properties_exposed
              (HybConcSem (Some 0)%nat m)
              (HybConcSem (Some (S n)) m)
              invariant
              mem_compatible
              (match_state (S n))
                list_lt.
      Proof.
        intros n Hsim0 Hsimn m.
        specialize (Hsim0 m). destruct Hsim0 as [Hsim0 Hordr0].
        specialize (Hsimn m). destruct Hsimn as [Hsimn Hordrn].
        unshelve econstructor;
          [econstructor| ].
        - !goal (well_founded _).
          eapply list_ord_part_wf.
          eapply Hsimn.
          eapply Hsim0.
        - intros.
          eapply Hsim0 in H; normal_hyp.
          eapply Hsimn in H; eauto.
          normal; eauto.
          !goal(match_state _ _ _ _ _ _ _). econstructor; eauto.
        - intros.
          inv H0. subst_sig.
          eapply Hsim0 in H; eauto.
          apply step_diagram_helper in H.
          apply step_diagram_helper.
          normal_hyp. destruct H2.
          + revert H H0.
            admit.
          + normal_hyp; subst.
            assert (Forall2 (inject_mevent (compose_meminj x2 jSn)) tr1 tr2).
            { eapply inject_incr_trace; try eassumption.
              eapply compose_meminj_inject_incr; eauto. }
            clear H1.
            normal_goal; eauto.
            * econstructor; eauto.
            * right; repeat weak_split auto.
              constructor; auto.
            * eapply compose_meminj_inject_incr; eauto.
        - intros.
          inv H2; subst_sig.
          eapply list_inject_mevent_interpolation in H3; normal_hyp.
          eapply Hsim0 in H.
          normal_hyp.
          eapply Hsimn in H5; eauto.
          normal.
          + econstructor; eauto.
          + instantiate(1:= x5).
            eapply forall_inject_mevent_compose; eauto.
          + auto.
          + eapply compose_meminj_inject_incr; eauto.
          + (* add match_state _ st1 m1 st2 m2 -> invariant st2 *)
            eapply match_state_invariant; eauto.
                
          + (* add match_state _ st1 m1 st2 m2 -> mem_compat st2 m2 *)
            eapply match_state_cmpt; eauto.
          + eauto.
          + eauto.
          + eauto.
          + eauto.
        - econstructor; simpl in *.
          unfold halted_machine in *; simpl in *.
          match_case in H0.
          (* - intros * Hmatch i. inv Hmatch.
          (eapply thread_running with (i:=i) in Hsimn); eauto. 
          (eapply thread_running with (i:=i)  in Hsim0); eauto.
          split; intros HH; eauto.
          + eapply Hsimn; eapply Hsim0; assumption.
          + eapply Hsim0; eapply Hsimn; assumption. *)

          Unshelve.
          all: assumption.
      Admitted. (* Just one silly admit. *)

      
      Context (Hexterns_have_events: Asm_externals_have_events Asm_g).
      Lemma compile_n_threads:
        forall n m,
          simulation_properties_exposed
            (HybConcSem (Some 0)%nat m)
            (HybConcSem (Some n) m)
            invariant
            mem_compatible
            (match_state n) list_lt.
      Proof.
        induction n.
        - (*trivial reflexive induction*)
          apply trivial_self_injection.
        - eapply simulation_inductive_case; eauto.
          eapply compile_one_thread; auto.
      Qed.

    End CompileNThreads.

    Section Lift.
      (* We lift states to a different semantics: 
         The state content is exactly the same, 
         but the type is of a hybrid machine of higher order.
       *)

      
      (* Create a database for eauto and autorewrite
       *)
      Create HintDb lift.
      Tactic Notation "lift":= eauto with lift.
      Tactic Notation "rw_lift":= autorewrite with lift.


      (** *Definitions*)
      Definition lift_state': forall {on on'},
          ThreadPool on -> ThreadPool on'.
      Proof.  intros; inv X; econstructor; eauto. Defined.
      Inductive lift_state: forall on, ThreadPool on -> forall on', ThreadPool on' -> Prop:=
      | build_lift_state: forall on on' st st',
          st' = lift_state' st -> lift_state on st on' st'.
      Hint Constructors lift_state: lift.


      (** *Core lemmas *)
      Lemma lift_state_refl:
        forall n st, @lift_state' n n st = st.
      Proof. intros; destruct st; simpl. f_equal. Qed.
      Hint Resolve lift_state_refl: lift.
      Lemma lift_contains:
        forall {on on'} st j,
          OrdinalPool.containsThread st j <->
          OrdinalPool.containsThread (@lift_state' on on' st) j.
      Proof.
        intros. simpl.
        unfold OrdinalPool.containsThread; simpl.
        destruct st; simpl. reflexivity.
      Qed.
      Lemma lift_contains1:
        forall {on on'} st j,
          OrdinalPool.containsThread st j ->
          OrdinalPool.containsThread (@lift_state' on on' st) j.
      Proof. intros; eapply lift_contains in H; eauto. Qed.
      Hint Resolve lift_contains1: lift.
      (* this version is better to use in statement of lemmas to rewrite*)
      Lemma unlift_cnt:
        forall on on' {st j},
          OrdinalPool.containsThread (@lift_state' on on' st) j ->
          OrdinalPool.containsThread st j.
      Proof. intros; eapply lift_contains in H; eauto. Qed.
      Lemma lift_contains2:
        forall {on on'} st j,
          OrdinalPool.containsThread (@lift_state' on on' st) j ->
          OrdinalPool.containsThread st j.
      Proof. intros; eapply lift_contains in H; eauto. Qed.
      Lemma lift_getC:
        forall on on' st tid
          (Htid: OrdinalPool.containsThread st tid)
          (Htid': OrdinalPool.containsThread (@lift_state' on on' st) tid),
          OrdinalPool.getThreadC Htid' = OrdinalPool.getThreadC Htid.
      Proof.
        intros. destruct st; simpl in *.
        replace Htid' with Htid by apply Axioms.proof_irr; auto.
      Qed.
      Lemma lift_getC':
        forall on on' st tid
          (Htid': OrdinalPool.containsThread (@lift_state' on on' st) tid),
          OrdinalPool.getThreadC Htid' = OrdinalPool.getThreadC (unlift_cnt on on' Htid').
      Proof. intros; eapply lift_getC; auto. Qed.
      Hint Rewrite lift_getC': lift.
      Lemma lift_getR:
        forall on on' st tid
          (Htid: OrdinalPool.containsThread st tid)
          (Htid': OrdinalPool.containsThread (@lift_state' on on' st) tid),
          OrdinalPool.getThreadR Htid' = OrdinalPool.getThreadR Htid.
      Proof.
        intros. destruct st; simpl in *.
        replace Htid' with Htid by apply Axioms.proof_irr; auto.
      Qed.
      Lemma lift_getR':
        forall on on' st tid
          (Htid': OrdinalPool.containsThread (@lift_state' on on' st) tid),
          OrdinalPool.getThreadR Htid' = OrdinalPool.getThreadR (unlift_cnt on on' Htid').
      Proof. intros; eapply lift_getR; auto. Qed.
      Hint Rewrite lift_getR': lift.
      Lemma lift_lockRes:
        forall on on' st l,
          OrdinalPool.lockRes (@lift_state' on on' st) l =
          OrdinalPool.lockRes st l.
      Proof.
        intros; destruct st; simpl.
        unfold OrdinalPool.lockRes; simpl; reflexivity.
      Qed.
      Hint Rewrite lift_lockRes: lift.
      
      
      
      
      Lemma lift_invariant:
        forall hb1 hb2 st st',
          lift_state hb1 st hb2 st' ->
          invariant st -> invariant st'.
      Admitted.
      Lemma lift_invariant':
        forall hb1 hb2 st,
          invariant st -> invariant (@lift_state' hb1 hb2 st).
      Proof.
        intros. eapply lift_invariant; eauto.
        econstructor; eauto.
      Qed.
      Hint Resolve lift_invariant': lift.
      Lemma lift_cmpt:
        forall hb1 hb2 st m,
          mem_compatible st m ->
          mem_compatible (@lift_state' hb1 hb2 st) m.
      Proof.
        intros. inv H; simpl in *.
        econstructor; simpl;
          intros; simpl; autorewrite with lift in *;
            clean_proofs_goal; eauto.
      Qed.
      Hint Resolve lift_cmpt: lift.
      
      Lemma lift_state_idempotent:
        forall base n top st,
          @lift_state' (Some n) top
                       (@lift_state' base (Some n) st) =
          @lift_state' base top st.
      Proof. intros. destruct st; eauto. Qed.
      Hint Rewrite lift_state_idempotent: lift.

      
      (* for some reason, getC doesn't autorewrite
         it seems like it unifies on = on' before rewriteting,
         unless given explicitly...
       *)
      Ltac rewrite_getC:=
        match goal with
          |- @OrdinalPool.getThreadC
              _ _ ?i
              (@lift_state' ?on ?on'  ?st) ?cnt
            = _ =>
          rewrite (lift_getC' on on');
          clean_proofs_goal; lift
        end.
      
      Ltac lift_tac:=
        autorewrite with lift in *;
        try rewrite_getC; 
        clean_proofs_goal; lift.
      
      
      Lemma unlift_permMapLt:
        forall on on' {st tid m}
          {Htid': ThreadPool.containsThread
                    (@lift_state' on on' st) tid}
          (Hlt': permMapLt
                   (thread_perms (lift_state' st) tid Htid')
                   (getMaxPerm m)),
          permMapLt
            (thread_perms st tid (unlift_cnt _ _ Htid'))
            (getMaxPerm m).
      Proof. intros; lift_tac. Qed.
      Hint Resolve @unlift_permMapLt: lift.
      Lemma unlift_permMapLt_lock:
        forall on on' {st tid m}
               {Htid': ThreadPool.containsThread
                         (@lift_state' on on' st) tid}
               (Hlt': permMapLt
                        (lock_perms (lift_state' st) tid Htid')
                        (getMaxPerm m)),
          permMapLt
            (lock_perms st tid (unlift_cnt _ _ Htid'))
            (getMaxPerm m).
      Proof. intros; lift_tac. Qed.
      Hint Resolve @unlift_permMapLt_lock: lift.
      
      Lemma lift_restrPermMap:
        forall on on' st tid m
               (Htid': ThreadPool.containsThread
                         (@lift_state' on on' st) tid)
               (Hlt': permMapLt
                        (thread_perms (lift_state' st) tid Htid')
                        (getMaxPerm m)),
          restrPermMap Hlt' =
          restrPermMap (unlift_permMapLt _ _ Hlt').
      Proof.
        intros.
        eapply restre_equiv_eq; lift_tac;
          reflexivity.
      Qed.
      Hint Rewrite lift_restrPermMap: lift.
      
      Lemma lift_restrPermMap_lk:
        forall on on' st tid m
          (Htid': ThreadPool.containsThread
                    (@lift_state' on on' st) tid)
          (Hlt': permMapLt
                   (lock_perms (lift_state' st) tid Htid')
                   (getMaxPerm m)),
          restrPermMap Hlt' =
          restrPermMap (unlift_permMapLt_lock _ _ Hlt').
      Proof.
        intros.
        eapply restre_equiv_eq; lift_tac;
          reflexivity.
      Qed.
      Hint Rewrite lift_restrPermMap_lk: lift.

      
      
      
      (** *Regular lemmas
          i.e. don't go in the database 
       *)
      Lemma lift_unique_Krun:
        forall {on on'} st i,
          HybridMachineSig.unique_Krun st i <->
          HybridMachineSig.unique_Krun (@lift_state' on on' st) i.
      Proof.
        intros; split; intros ** ? **; simpl in *.
        - unshelve eapply H; eauto; simpl.
          eapply lift_contains2; eauto.
          destruct st; simpl in *.
          rewrite <- H0; f_equal.
          clean_proofs_goal; reflexivity.
        - unshelve eapply H; eauto; simpl.
          lift.
          destruct st; simpl in *.
          rewrite <- H0; f_equal.
          clean_proofs_goal; reflexivity.
      Qed.

      Lemma lift_updThread:
        forall on on' st tid
          (Htid: ThreadPool.containsThread st tid)
          (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid)
          c res st',
          OrdinalPool.updThread Htid c res = st' ->
          OrdinalPool.updThread Htid' c res = lift_state' st'.
      Proof.
        intros.
        subst st'. destruct st; simpl.
        unfold OrdinalPool.updThread; simpl.
        f_equal.
      Qed.
      Lemma lift_updThread':
        forall on on' st tid
               (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid)
               c res st',
          OrdinalPool.updThread (unlift_cnt on on' Htid') c res = st' ->
          OrdinalPool.updThread Htid' c res = lift_state' st'.
      Proof.
        intros.
        subst st'. destruct st; simpl.
        unfold OrdinalPool.updThread; simpl.
        f_equal.
      Qed.
      Hint Resolve lift_updThread: lift.
      Hint Rewrite lift_updThread' using eauto: lift.

      Lemma lift_updThreadC:
        forall on on' st tid
               (Htid: ThreadPool.containsThread st tid)
               (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid)
               res st',
          OrdinalPool.updThreadC Htid res = st' ->
          OrdinalPool.updThreadC Htid' res = lift_state' st'.
      Proof.
        intros.
        subst st'. destruct st; simpl in *.
        unfold lift_state' in *.
        unfold OrdinalPool.updThreadC; simpl.
        f_equal.
      Qed.
      Hint Resolve lift_updThreadC: lift.
      Hint Rewrite lift_updThreadC: lift.
      
      Notation MachineSig_n on:= (@DryHybridMachineSig
                                    (@HybridSem CC_correct Args on) (TP on)).
      
      Lemma lift_install_perm:
        forall on on' st tid m m'
          (Htid: ThreadPool.containsThread st tid)
          (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid)
          (Hcmpt : HybridMachineSig.mem_compatible st m)
          (Hcmpt' : HybridMachineSig.mem_compatible (@lift_state' on on' st) m),
          @HybridMachineSig.install_perm _ _ _
                                         (MachineSig_n on)  _ _ _ Hcmpt Htid m' ->
          @HybridMachineSig.install_perm _ _ _
                                         (MachineSig_n on')  _ _ _ Hcmpt' Htid' m'.
      Proof.
        simpl in *. 
        unfold HybridMachineSig.install_perm, install_perm; simpl;
          unfold install_perm; intros.
        clean_proofs_goal.
        subst m'; f_equal.
        simpl.
        eapply synchronisation_lemmas.restrPermMap_access_equiv.
        unfold thread_perms; simpl.
        remember (OrdinalPool.getThreadR Htid) as X.
        symmetry in HeqX.
        erewrite lift_getR; auto.
        subst X; reflexivity.
      Qed.
      Lemma lift_install_perm':
        forall on on' (st: OrdinalPool.t) tid m  m'
          (Htid: OrdinalPool.containsThread st tid)
          (Htid': OrdinalPool.containsThread (@lift_state' on on' st) tid)
          (Hcmpt : @mem_compatible _ (@OrdinalPool.OrdinalThreadPool
                                        _
                                        (@HybridSem CC_correct Args on)) st m)
          (Hcmpt' : mem_compatible (@lift_state' on on' st) m),
          install_perm _ _ _ Hcmpt Htid m' ->
          install_perm  _ _ _ Hcmpt' Htid' m'.
      Proof. eapply lift_install_perm. Qed.
      Hint Resolve lift_install_perm': lift.
      Hint Resolve lift_install_perm: lift.
      
      Definition hb_le (hb1 hb2: option nat):=
        match hb1, hb2 with
        | Some n1, Some n2 => (n1 <= n2)%nat
        | _, None => True
        | _ , _ => False
        end.
      Lemma  lt_op_hb_le:
        forall tid on1 on2,
          lt_op tid on1 ->
          hb_le on1 on2 ->
          lt_op tid on2.
      Proof.
        intros. unfold hb_le in H0.
        repeat match_case in H0; subst; simpl in *.
        omega.
      Qed.
      
      Lemma lift_initial_core:
        forall on on' tid m c m' vf arg,
          lt_op tid on -> hb_le on on' ->
          initial_core (sem_coresem (HybridSem on)) tid m c m' vf arg ->
          initial_core (sem_coresem (HybridSem on')) tid m
                       c m' vf arg.
      Proof.
        unfold HybridSem; simpl.
        intros. simpl in H1.
        unfold initial_core_sum in H1.
        match_case in H1.
        - normal. contradict H1; apply H.
        - simpl. normal; eauto.
          eapply lt_op_hb_le; eauto.
      Qed.
      Hint Resolve lift_initial_core: lift.
      
      Definition ThreadPool_num_threads {hb1} (st:ThreadPool hb1): nat.
        apply pos.n.
        eapply @OrdinalPool.num_threads.
        simpl in st. eauto.
      Defined.
      
      Lemma  lt_op_lt:
        forall tid x on2,
          lt_op x on2 ->
          (tid < x)%nat ->
          lt_op tid on2.
      Proof.
        intros. unfold lt_op in *.
        match_case; eauto.
        omega.
      Qed.
      Lemma cnt_pos_threads_lt:
        forall hb (st: ThreadPool (hb)) tid, 
          ThreadPool.containsThread st tid ->
          (tid < ThreadPool_num_threads st)%nat.
      Proof.
        unfold ThreadPool_num_threads in *.
        intros. 
        apply (Nat.lt_le_trans _ (S tid)); try omega.
        exploit (@ssrnat.leP (S tid) (pos.n (OrdinalPool.num_threads st))). 
        hnf in H. intros HH; inv HH; auto.
        rewrite H in H0; congruence.
      Qed.
      Lemma lift_start_thread:
        forall on on' m st st' m' tid
          (Htid: ThreadPool.containsThread st tid)
          (Htid': ThreadPool.containsThread (lift_state' st) tid)
          (Hltop: lt_op (ThreadPool_num_threads st) on)
          (Hhb_le: hb_le on on'),
          start_thread(machineSig:=MachineSig_n on)
                      m Htid st' m' ->
          start_thread(machineSig:=MachineSig_n on')
                      m Htid' (lift_state' st') m'.
      Proof.
        intros.
        inv H; econstructor; simpl in *;
          lift_tac.
        - instantiate (1:= c_new).
          hnf in Hinitial.
          match_case in Hinitial.
          normal_hyp.
          contradict H.
          + eapply lt_op_lt; eauto.
            eapply cnt_pos_threads_lt; auto.
          + simpl. normal; eauto.
            eapply lt_op_hb_le; eassumption.
        - unfold add_block; simpl.
          autorewrite with lift; simpl.
          erewrite lift_updThread; eauto; simpl.
          autorewrite with lift in *;
            clean_proofs_goal; lift.

          Unshelve.
          simpl; lift.
      Qed.
      Lemma lift_resume_thread:
        forall on on' m st st' tid
          (Htid: ThreadPool.containsThread st tid)
          (Htid': ThreadPool.containsThread (lift_state' st) tid)
          (Hltop: lt_op (ThreadPool_num_threads st) on)
          (Hhb_le: hb_le on on'),
          resume_thread(machineSig:=MachineSig_n on)
                       m Htid st' ->
          resume_thread(machineSig:=MachineSig_n on')
                       m Htid' (lift_state' st').
      Proof.
        intros.
        inv H; econstructor; simpl in *; lift_tac.
        erewrite lift_updThreadC; eauto; reflexivity.

        Unshelve.
        all: simpl; lift.
        
      Qed.
      
      Lemma lift_suspend_thread:
        forall on on' m st st' tid
          (Htid: ThreadPool.containsThread st tid)
          (Htid': ThreadPool.containsThread (lift_state' st) tid)
          (Hltop: lt_op (ThreadPool_num_threads st) on)
          (Hhb_le: hb_le on on'),
          suspend_thread(machineSig:=MachineSig_n on)
                        m Htid st' ->
          suspend_thread(machineSig:=MachineSig_n on')
                        m Htid' (lift_state' st').
      Proof.
        intros.
        inv H; econstructor; simpl in *;lift_tac.
        erewrite lift_updThreadC; eauto; reflexivity.

        Unshelve.
        all: simpl; lift.
      Qed.
      Lemma lift_syncStep:
        forall on on' m st m' st' tid ev
          (Htid: ThreadPool.containsThread st tid)
          (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid)
          (Hltop: lt_op (ThreadPool_num_threads st) on)
          (Hcmpt : @mem_compatible _ (@OrdinalPool.OrdinalThreadPool
                                        _
                                        (@HybridSem CC_correct Args on)) st m)
          (Hcmpt' : mem_compatible (lift_state' st) m),
          syncStep true Htid Hcmpt st' m' ev ->
          syncStep true Htid' Hcmpt' (lift_state' st') m' ev.
      Proof.
        intros.
        inv H;
          [ econstructor 1 |
            econstructor 2 |
            econstructor 3 |
            econstructor 4 |
            econstructor 5 |
            econstructor 6]; eauto;
            simpl in *; lift_tac; (* 7! goals *)
              try solve[destruct st; simpl; eauto];
              clean_proofs; eauto.
        1,2: rewrite <- Hstore; f_equal;
          eapply restre_equiv_eq; lift_tac;
            reflexivity.

        Unshelve.
        all: simpl in *; lift_tac. 
      Qed.
      Lemma lift_thread_step:
        forall on on' tge U st st' m2 x1 m,
          machine_semantics.thread_step
            (HybConcSem on m) tge U st m2 st' x1 ->
          machine_semantics.thread_step
            (HybConcSem on' m) tge U (@lift_state' on on' st) m2
            (@lift_state' on on' st') x1.
      Proof.
        intros.
        unshelve (inv H; econstructor; eauto);
                  try eapply lift_contains1; eauto;
                    simpl in *; lift.
        inv Htstep; simpl in *;
          econstructor; simpl in *; lift_tac.
        clean_proofs_goal. lift.
        simpl.
        unfold OrdinalPool.updThread; simpl in *.
        rw_lift. destruct st; f_equal.
      Qed.
      Lemma lift_thread_Nstep:
        forall on on' tge x
          (U : list nat) (st st' : ThreadPool on) (m2 x1 : mem) (m : option mem),
          machine_semantics_lemmas.thread_stepN (HybConcSem on m) tge x U st m2 st' x1 ->
          machine_semantics_lemmas.thread_stepN (HybConcSem on' m) tge x U 
                                                (lift_state' st) m2 (lift_state' st') x1.
        intros until x. induction x.
        
        - intros. inv H; simpl. reflexivity.
        - intros.
          simpl in H; normal_hyp.
          do 2 eexists; split; eauto.
          simpl; eauto.
          eapply lift_thread_step; eauto.

          Unshelve.
          all: auto.
      Qed.
      Lemma lift_thread_step_star:
        forall on on' tge U st st' m2 x1 m,
          machine_semantics_lemmas.thread_step_star
            (HybConcSem on m) tge U st m2 st' x1 ->
          machine_semantics_lemmas.thread_step_star
            (HybConcSem on' m) tge U (@lift_state' on on' st) m2
            (@lift_state' on on' st') x1.
      Proof.
        intros. inv H. exists x.
        apply lift_thread_Nstep; auto.
      Qed.
      
      Lemma lift_thread_step_plus:
        forall on on' tge U st st' m2 x1 m,
          machine_semantics_lemmas.thread_step_plus
            (HybConcSem on m) tge U st m2 st' x1 ->
          machine_semantics_lemmas.thread_step_plus
            (HybConcSem on' m) tge U (@lift_state' on on' st) m2
            (@lift_state' on on' st') x1.
      Proof.
        intros. inv H. exists x.
        eapply lift_thread_Nstep; auto.
      Qed.
        
      Lemma lift_machine_step:
        forall on on' tge U tr2 st st' m2 U' x x1 m
          (Hhb_le: hb_le on on')
          (Hltop: lt_op (ThreadPool_num_threads st) on),
          machine_semantics.machine_step
            (HybConcSem on m) tge U tr2 st m2 U' x st' x1 ->
          machine_semantics.machine_step
            (HybConcSem on' m) tge U tr2 (@lift_state' on on' st) m2 U' x
            (@lift_state' on on' st') x1.
      Proof.
        intros. unshelve (inv H;
                          [ econstructor 1 |
                            econstructor 2 |
                            econstructor 3 |
                            econstructor 4 |
                            econstructor 5]; eauto);
                  try eapply lift_contains1; eauto;
                    simpl in *; lift.
        - eapply lift_start_thread; eauto.
        - eapply lift_resume_thread; eauto.
        - eapply lift_suspend_thread; eauto.
        - eapply lift_syncStep; eauto.
          
        - destruct Htid; [left|right].
          + intros HH; apply H; eapply unlift_cnt; eauto.
          + normal; lift_tac.
            
            Unshelve.
            all: lift.
      Qed.
      
    End Lift.
    
    Section CompileInftyThread.
      Context {Hasm_externals: Asm_externals_have_events Asm_g}.

      
      Definition self_simulates:
        forall n, ThreadPool (Some n) -> mem -> Prop:=
        fun _ _ _ => True.
      
      Inductive infty_match:
        nth_index -> meminj ->
        ThreadPool (Some 0)%nat -> mem ->
        ThreadPool None -> mem -> Prop:=
      | Build_infty_match:
          forall n cd j st0 m0 stn mn st
            (Hself_inj:  self_simulates n stn mn)
            (Hhb_bound: (0 < ThreadPool_num_threads st0 < n)%nat),
            match_state n cd j st0 m0 stn mn ->
            lift_state (Some n) stn None st ->
            infty_match cd j st0 m0 st mn.


      Lemma initial_infty:
        forall (m : option mem) (s_mem s_mem' : mem) 
          (main : val) (main_args : list val)
          (s_mach_state : ThreadPool (Some 0)%nat) (r1 : option res),
          machine_semantics.initial_machine (HybConcSem (Some 0)%nat m) r1
                                            s_mem s_mach_state s_mem' main main_args ->
          exists
            (j : meminj) (cd : nth_index) (t_mach_state : ThreadPool None) 
            (t_mem t_mem' : mem) (r2 : option res),
            machine_semantics.initial_machine (HybConcSem None m) r2 t_mem
                                              t_mach_state t_mem' main main_args /\
            infty_match cd j s_mach_state s_mem' t_mach_state t_mem'.
      Proof.
      (* Follows from any initial diagram and a missing lemma showing that the initial state
        can be "lifted" (lift_state) *)
      Admitted.
      
      Lemma self_simulates_match:
        forall hb1 (st:ThreadPool (Some hb1)) m,
          (ThreadPool_num_threads st < hb1)%nat ->  
          self_simulates hb1 st m ->
          concur_match hb1 None (Mem.flat_inj (Mem.nextblock m)) st m (lift_state' st) m.
      Proof.
      Admitted.
      Lemma lift_self_simulates:
        forall hb1 hb2 st m, 
          self_simulates hb1 st m ->
          (ThreadPool_num_threads st < hb1)%nat -> 
          (hb1 <= hb2)%nat ->
          self_simulates hb2 (lift_state' st) m.
      Admitted.
      Lemma machine_step_preserves_self_simulates:
        forall n m0 ge U tr st m U' tr' st' m',
          self_simulates n st m ->
          machine_semantics.machine_step (HybConcSem (Some n) m0)
                                         ge U tr st m U' tr' st' m' ->
          self_simulates n st' m'.
      Proof.
      Admitted.
      Fixpoint Nones {A} (n:nat):=
        match n with
          O => nil
        | S n' => @None A :: (Nones n')
        end.
      
      Definition mappedblocks f m2:=
        forall (b b' : block) (delta : Z),
          f b = Some (b', delta) -> Mem.valid_block m2 b'.
      Lemma mappedblocks_compose_meminj:
        forall f m2,
          mappedblocks f m2 ->
          f = (compose_meminj f (Mem.flat_inj (Mem.nextblock m2))).
      Proof.
        intros.
        unfold compose_meminj.
        unfold Mem.flat_inj,compose_meminj.
        intros.
        extensionality b; simpl.
        repeat match_case. subst.
        - match_case in Heqo0; subst.
          inv Heqo0. repeat f_equal; omega.
        - match_case in Heqo0; subst.
          apply H in Heqo.
          clear Heqs.
          contradict n. apply Heqo.
      Qed.
      Lemma match_state_num_threads:
        forall n ocd mu st1 m1 st2 m2,
          match_state n ocd mu st1 m1 st2 m2 ->
          ThreadPool_num_threads st1 =
          ThreadPool_num_threads st2.
      Proof.
        induction n.
        - intros. inv H. subst_sig; reflexivity.
        - intros * H. inv H. subst_sig.
          etransitivity.
          eapply IHn; eauto.
          unfold ThreadPool_num_threads.
          apply same_length in H7.
          f_equal.
          destruct tpn, st2; simpl in *; auto.
      Qed.
      Lemma mappedblocks_flat:
        forall m2, 
          mappedblocks (Mem.flat_inj (Mem.nextblock m2)) m2.
      Proof.
        intros ** ? ** . 
        unfold Mem.flat_inj in *.
        match_case in H.
      Qed.
      Lemma concur_match_mappedblocks:
        forall n ocd mu st1 m1 st2 m2,
          (0 < ThreadPool_num_threads st1)%nat -> 
          concur_match n ocd mu st1 m1 st2 m2 ->
          mappedblocks mu m2.
      Proof.
        intros.
        assert (Hcnt1:ThreadPool.containsThread st1 0).
        { unfold ThreadPool.containsThread; simpl.
          unfold OrdinalPool.containsThread.
          unfold ThreadPool_num_threads in *.
          destruct st1; subst; simpl.
          clear - H.
          pose proof (@ssrnat.leP 1 (pos.n num_threads)).
          inv H0; auto. }
        assert (Hcnt2:ThreadPool.containsThread st2 0).
        { eapply contains12; eauto. }

        assert (Hlt1:permMapLt (fst (ThreadPool.getThreadR Hcnt1)) (getMaxPerm m1)).
        { eapply memcompat1 in H0. apply H0. }
        assert (Hlt2:permMapLt (fst (ThreadPool.getThreadR Hcnt2)) (getMaxPerm m2)).
        { eapply memcompat2 in H0. apply H0. }

        unshelve eapply INJ_threads in H0; try eapply Hcnt1; eauto.
        intros ? **.
        eapply Mem.mi_mappedblocks in H0; eauto.
      Qed.
      Lemma match_state_mappedblocks:
        forall n ocd mu st1 m1 st2 m2,
          (0 < ThreadPool_num_threads st1)%nat ->
          match_state n ocd mu st1 m1 st2 m2 ->
          mappedblocks mu m2.
      Proof.
        intros. inv H0; subst_sig.
        - 
          eapply mappedblocks_flat.
        - intros ? **.
          unfold compose_meminj in H0.
          repeat match_case in H0. inv H0.
          eapply concur_match_mappedblocks; try eapply H10; eauto.
          erewrite <- match_state_num_threads; eauto.
      Qed.
      
      Lemma pump_match_state:
        forall m n ocd mu st1 m1 st2 m2
          (Hpos: (0 < ThreadPool_num_threads st1)%nat),
          match_state n ocd mu st1 m1 st2 m2 ->
          self_simulates _ st2 m2 ->
          (ThreadPool_num_threads st2 < n)%nat -> 
          (n <= m)%nat ->
          match_state m ((Nones (m-n)) ++ ocd) mu st1 m1 (lift_state' st2) m2.
      Proof.
        intros. 
        assert (exists x, m = x + n)%nat.
        { exists (m - n)%nat. omega. }
        normal_hyp; subst.
        clear H2.
        replace (x + n - n)%nat with x by omega.
        revert n mu ocd st1 st2 m1 m2 Hpos H H1 H0.
        induction x.
        - simpl.
          intros; rewrite lift_state_refl; auto.
        - intros.
          exploit IHx; eauto. clear IHx.
          intros HH.
          simpl.
          replace mu with (compose_meminj mu (Mem.flat_inj (Mem.nextblock m2))).
          2: { symmetry; apply mappedblocks_compose_meminj.
               eapply match_state_mappedblocks; eauto. }

          simpl.
          eapply step_match_state; eauto.
          erewrite <- (lift_state_idempotent (Some n) (x + n) (Some (S (x + n)))).
          + eapply self_simulates_match; eauto.
            destruct st2; unfold ThreadPool_num_threads in *; simpl in *.
            omega.
      Qed.

            Lemma thread_step_preserves_self_simulates:
              forall n m0 ge U st m st' m',
                self_simulates n st m ->
                machine_semantics.thread_step (HybConcSem (Some n) m0)
                                               ge U st m st' m' ->
                self_simulates n st' m'.
            Proof.
            Admitted.
            Lemma thread_step_star_preserves_self_simulates:
              forall n m0 ge U st m st' m',
                self_simulates n st m ->
                machine_semantics_lemmas.thread_step_star (HybConcSem (Some n) m0)
                                               ge U st m st' m' ->
                self_simulates n st' m'.
            Proof.
              intros. inv H0.
              revert dependent m.
              revert U st st' m'.
              induction x.
              - simpl. intros. inv H1; assumption.
              - simpl; intros. normal_hyp.
                eapply IHx; try eapply H1.
                eapply thread_step_preserves_self_simulates; eauto.
                simpl; eassumption.

                Unshelve.
                all: eauto.
            Qed.
            
            Lemma thread_step_plus_preserves_self_simulates:
              forall n m0 ge U st m st' m',
                self_simulates n st m ->
                machine_semantics_lemmas.thread_step_plus (HybConcSem (Some n) m0)
                                               ge U st m st' m' ->
                self_simulates n st' m'.
            Proof.
              intros. eapply thread_step_star_preserves_self_simulates; eauto.
              apply machine_semantics_lemmas.thread_step_plus_star; eassumption.
            Qed.
      Lemma infinite_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G)
          (U : list nat) tr1 (st1 : ThreadPool (Some 0)%nat) 
          (m1 : mem) (st1' : ThreadPool (Some 0)%nat) 
          (m1' : mem),
          machine_semantics.thread_step (HybConcSem (Some 0)%nat m) sge U st1
                                        m1 st1' m1' ->
          forall (cd : nth_index) tr2 (st2 : ThreadPool None) 
            (mu : meminj) (m2 : mem),
            infty_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            exists
              (st2' : ThreadPool None) (m2' : mem) (cd' : nth_index) 
              (mu' : meminj),
              infty_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1 tr2 /\
              (machine_semantics_lemmas.thread_step_plus 
                 (HybConcSem None m) tge U st2 m2 st2' m2' \/
               machine_semantics_lemmas.thread_step_star 
                 (HybConcSem None m) tge U st2 m2 st2' m2' /\ 
               list_lt cd' cd) /\ inject_incr mu mu' .
      Proof.
      (*Proof sketch:
            infty_match defines an intermediate machine Mn at level n, matching the 0 machine.
            All threads of machine Mn are in Asm. A lemma should show that all hier machines 
            (Mk, for k>n) also match the machine at 0. 
            lemma [compile_n_threads] shows that machine M(S n) can step and reestablish 
            [match_states]. Since we increased the hybrid bound (n -> S n) then the new thread 
            is in Asm and [match_states] can be lifted to [infty_match].
       *)
        intros. inv H0.
        assert (Hsame_num: ThreadPool_num_threads st1' = ThreadPool_num_threads st1).
        { unfold ThreadPool_num_threads; inv H; simpl; eauto.
          inv Htstep; simpl; eauto. }
        
        pose proof (compile_n_threads Hasm_externals n m) as HH.
        destruct HH as [HH HHorder]; destruct HH; simpl in HHorder.
        clear thread_running thread_halted machine_diagram initial_setup.
        eapply thread_diagram in H; eauto.
        normal_hyp.
        normal; eauto.
        - econstructor; swap 1 3.
          + eassumption.
          + rewrite Hsame_num; split; eauto.
          + destruct H4 as [ ?| [? ?] ];
              [ eapply thread_step_plus_preserves_self_simulates |
                eapply thread_step_star_preserves_self_simulates]; eauto.
          + econstructor; eauto.
        - inv H3; repeat subst_sig.
          destruct H4 as [ H4| [H4 ?] ];
            [ left;eapply lift_thread_step_plus |
              right; split; try eapply lift_thread_step_star]; eauto.
      Qed.

      Lemma cnt_pos_threads:
        forall hb (st: ThreadPool (hb)) tid, 
          ThreadPool.containsThread st tid ->
          (0 < ThreadPool_num_threads st)%nat.
      Proof.
        unfold ThreadPool_num_threads in *.
        intros. 
        apply (Nat.lt_le_trans _ (S tid)); try omega.
        exploit (@ssrnat.leP (S tid) (pos.n (OrdinalPool.num_threads st))). 
        hnf in H. intros HH; inv HH; auto.
        rewrite H in H0; congruence.
      Qed.
      
      Lemma lift_ThreadPool_num_threads:
        forall  hb cd mu st1 m1 st2 m2,
          match_state hb cd mu st1 m1 st2 m2 ->
          ThreadPool_num_threads st2 = ThreadPool_num_threads st1.
      Proof.
        unfold ThreadPool_num_threads.
        induction hb.
        - simpl; intros; auto. inv H; subst_sig; auto.
        - intros. inv H; subst_sig.
          etransitivity; swap 1 2.
          eapply IHhb; eauto.
          apply same_length in H7; rewrite H7; reflexivity.
      Qed.
      
      
      Lemma machine_step_has_threads:
        forall n m0 ge U tr st m U' tr' st' m',
          (0 < ThreadPool_num_threads st)%nat ->
          machine_semantics.machine_step (HybConcSem (Some n) m0)
                                         ge U tr st m U' tr' st' m' ->
          (0 < ThreadPool_num_threads st')%nat.
      Proof.
        intros. unfold ThreadPool_num_threads in *.
        inv H0; eauto;
          inv Htstep; simpl; auto.
      Qed.  
      Lemma infinite_machine_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G)
          (U : list nat) (tr1 : HybridMachineSig.event_trace)
          (st1 : ThreadPool (Some 0)%nat) (m1 : mem) (U' : list nat)
          (tr1' : HybridMachineSig.event_trace)
          (st1' : ThreadPool (Some 0)%nat) (m1' : mem),
          machine_semantics.machine_step (HybConcSem (Some 0)%nat m) sge U tr1
                                         st1 m1 U' tr1' st1' m1' ->
          
          forall (cd : nth_index) tr2 (st2 : ThreadPool None) 
            (mu : meminj) (m2 : mem)
            (Hinv1': invariant st1')
            (Hcmpt1': mem_compatible st1' m1'),
            infty_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            exists
              tr2' (st2' : ThreadPool None) (m2' : mem) (cd' : nth_index) 
              (mu' : meminj),
              infty_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1' tr2' /\
              machine_semantics.machine_step (HybConcSem None m) tge U tr2 st2
                                             m2 U' tr2' st2' m2' /\
              inject_incr mu mu'.
      Proof.
        intros. inv H0.
        (* We will move the bound up "pump" 
           to ensure that it's higher than the number
           of threads AFTER the step
         *)
        set (new_hb:= max n (S (ThreadPool_num_threads st1'))).
        assert (Hnew_hb_spec1: (n <= new_hb)%nat) by apply Nat.le_max_l.
        
        rename stn into old_stn.
        exploit (pump_match_state new_hb); eauto.
        { apply Hhb_bound. }
        { erewrite lift_ThreadPool_num_threads; eauto.
          apply Hhb_bound. }
        remember (lift_state' old_stn) as stn.

        rename H3 into H3'.
        assert (H3: lift_state _ stn None st2).
        { econstructor; subst.
          erewrite lift_state_idempotent.
          inv H3'; repeat subst_sig; auto. }
        clear H3'.

        eapply (lift_self_simulates n new_hb) in Hself_inj; eauto.
        2:{ erewrite lift_ThreadPool_num_threads; eauto. apply Hhb_bound. }
        rewrite <- Heqstn in Hself_inj.
        clear H2 Heqstn old_stn; intros H2.

        (* Now everything is the same, but with a larger bound!*)
        
        pose proof (compile_n_threads Hasm_externals new_hb m) as HH.
        destruct HH as [HH _].
        eapply machine_diagram in HH; eauto.
        normal_hyp.
        normal; eauto.
        - econstructor; swap 1 3.
          + eassumption.
          + split. 2: apply Nat.le_max_r.
            eapply machine_step_has_threads; eassumption.
          + eapply machine_step_preserves_self_simulates; eauto.
          + econstructor; eauto.
        - inv H3; repeat subst_sig.
          instantiate(1:=tge) in H5.
          unshelve eapply lift_machine_step; try exact None;
            try assumption.
          simpl.
          !goal ((ThreadPool_num_threads stn < new_hb)%nat).
          { erewrite lift_ThreadPool_num_threads; eauto.
            omega. }
      Qed.
      

      Lemma infinite_halted:
        forall (m : option mem) (cd : nth_index) (mu : meminj)
          (U : list nat) (c1 : ThreadPool (Some 0)%nat) 
          (m1 : mem) (c2 : ThreadPool None) (m2 : mem) 
          (v1 : val),
          infty_match cd mu c1 m1 c2 m2 ->
          machine_semantics.conc_halted (HybConcSem (Some 0)%nat m) U c1 =
          Some v1 ->
          exists v2 : val,
            machine_semantics.conc_halted (HybConcSem None m) U c2 =
            Some v2.
      Proof.
        intros. inv H.
        exploit thread_halted; eauto.
        eapply compile_n_threads, Hasm_externals.
      Qed.
      
      Lemma infinite_running:
        forall (m : option mem) (cd : nth_index) (mu : meminj)
          (c1 : ThreadPool (Some 0)%nat) (m1 : mem) (c2 : ThreadPool None)
          (m2 : mem),
          infty_match cd mu c1 m1 c2 m2 ->
          forall i : nat,
            machine_semantics.running_thread (HybConcSem (Some 0)%nat m) c1 i <->
            machine_semantics.running_thread (HybConcSem None m) c2 i.
      Proof.
        intros. inv H.
        inv H1.
        subst_sig.
        etransitivity.
        instantiate(1:= machine_semantics.running_thread
                          (HybConcSem (Some n%nat) m)
                          stn i).
        - clear H st Hself_inj Hhb_bound. revert n mu cd i m c1 m1 stn m2 H0.
          induction n.
          + intros. inv H0. subst_sig; reflexivity.
          + intros. inv H0. etransitivity.
            * eapply IHn; eauto.
            * eapply concur_match_same_running; eauto.
        - eauto; subst_sig.
          simpl.
          apply lift_unique_Krun.
      Qed.
      Lemma compile_all_threads':
        forall m,
          simulation_properties_exposed
            (HybConcSem (Some 0)%nat m)
            (HybConcSem None m)
            invariant
            mem_compatible
            infty_match list_lt.
      Proof.
        intros. 
        (*All the proofs use the following lemma*)
        pose proof compile_n_threads as HH.
        
        unshelve econstructor;
          [econstructor| ].
        - eapply list_lt_wf.
        - apply initial_infty.
        - apply infinite_step_diagram.
        - intros; eapply infinite_machine_step_diagram;
            eauto.
        - apply infinite_halted.
        - apply infinite_running.
        - reflexivity.
      Qed.
      
      Lemma infty_match_invariant:
        forall cd mu st1 m1 st2 m2,
          infty_match cd mu st1 m1 st2 m2 ->
          invariant st1 ->
          invariant st2.
      Proof with eauto.
        intros. inv H.
        assert (invariant stn) by
        (eapply match_state_invariant; eauto). 
        eapply lift_invariant; eauto.
      Qed.
      Lemma infty_match_cmpt:
        forall cd mu st1 m1 st2 m2,
          infty_match cd mu st1 m1 st2 m2 ->
          mem_compatible st1 m1 ->
          mem_compatible st2 m2.
      Proof.
        intros. inv H.
        assert (mem_compatible stn m2) by
            (eapply match_state_cmpt; eauto).
        inv H2; repeat subst_sig.
        eapply lift_cmpt; assumption.
      Qed.
      Lemma compile_all_threads:
        forall m,
          HybridMachine_simulation'
            (HybConcSem (Some 0)%nat m)
            (HybConcSem None m)
            invariant
            invariant
            mem_compatible
            mem_compatible.
      Proof.
        intros. econstructor; swap 1 3; swap 2 3.
        { eapply compile_all_threads'. }
        - intros; eapply infty_match_invariant; eauto.
        - intros; eapply infty_match_cmpt; eauto.
      Qed. 

    End CompileInftyThread.
    
    
  End ThreadedSimulation.
End ThreadedSimulation.
