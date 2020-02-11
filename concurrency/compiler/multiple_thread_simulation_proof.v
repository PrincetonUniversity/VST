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
          ThreadPool (Some 0)%nat -> Memory.Mem.mem -> ThreadPool (Some n) -> Memory.Mem.mem -> Prop:=
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
                     forall tr2, machine_semantics.machine_step (HybConcSem hb m)
                         sge U tr2 st1 m1 U' (tr2 ++ tr_tail) st1' m1'.
      Admitted.
      Lemma trivial_self_injection:
        forall m : option mem,
          HybridMachine_simulation_properties
            (HybConcSem (Some 0)%nat m)
            (HybConcSem (Some 0)%nat m)
            invariant
            mem_compatible
            (match_state 0).
      Proof.
        simpl; intros.
        econstructor.
        - eapply list_lt_wf.
        - intros; normal; eauto.
          + econstructor.
        - intros; normal.
          + econstructor.
          + eapply inject_incr_trace; try eassumption.
            inv_match0; eapply flat_inj_lt.
            eapply thread_step_mem_fwd; apply H.
          + left. exists 0%nat; inv_match0.
            do 2 eexists; split; try reflexivity; eauto.
        - intros; inv_match0.
          eapply machine_step_traces in H; normal; subst; eauto.
          + econstructor.
          + eapply Forall_cat.
            eapply inject_incr_trace; try eassumption.
            apply flat_inj_lt.
            eapply machine_step_mem_fwd; eauto.
            eapply machine_step_trace_wf; eapply H2.
          + eapply H2.
        - intros; inv_match0; normal; eauto.
        - intros; inv_match0; reflexivity. 
          Unshelve.
          all: eauto.
      Qed.
      
      
      Lemma step_diagram_helper:
        forall (ord: relation nth_index) tr1 tr2 m U hb cd m1' st1' tge st2 m2, 
          (exists (st2' : ThreadPool (Some hb)) (m2' : mem) (cd' : nth_index) 
             (mu' : meminj),
              match_state hb cd' mu' st1' m1' st2' m2' /\
              Forall2 (inject_mevent mu') tr1 tr2 /\
              (machine_semantics_lemmas.thread_step_plus
                 (HybConcSem (Some hb) m) 
                 tge U st2 m2 st2' m2' \/
               machine_semantics_lemmas.thread_step_star
                 (HybConcSem (Some hb) m) 
                 tge U st2 m2 st2' m2' /\ ord cd' cd))
          <->
          exists (st2' : ThreadPool (Some hb)) (m2' : mem) (cd' : nth_index) 
            (mu' : meminj),
            match_state hb cd' mu' st1' m1' st2' m2' /\
            Forall2 (inject_mevent mu') tr1 tr2 /\
            (machine_semantics_lemmas.thread_step_plus
               (HybConcSem (Some hb) m) 
               tge U st2 m2 st2' m2' \/  m2=m2' /\ st2=st2' /\ ord cd' cd).
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
      Lemma simulation_inductive_case:
        forall n : nat,
          (forall m : option mem,
              HybridMachine_simulation_properties
                (HybConcSem (Some 0)%nat m)
                (HybConcSem (Some n) m)
                invariant
                mem_compatible
                (match_state n)) ->
          (forall m : option mem,
              HybridMachine_simulation_properties
                (HybConcSem (Some n) m)
                (HybConcSem (Some (S n)) m)
                invariant
                mem_compatible
                (concur_match n)) ->
          forall m : option mem,
            HybridMachine_simulation_properties
              (HybConcSem (Some 0)%nat m)
              (HybConcSem (Some (S n)) m)
              invariant
                mem_compatible
                (match_state (S n)).
      Proof.
        intros n Hsim0 Hsimn m.
        specialize (Hsim0 m).
        specialize (Hsimn m).
        econstructor.
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
            { admit. (*Need an inject_incr or something about x2. *)
            }
            clear H1.
            normal_goal; eauto.
            * econstructor; eauto.
            * right; repeat weak_split auto.
              constructor; auto.
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
          + (* add match_state _ st1 m1 st2 m2 -> invariant st2 *)
            admit.
          + (* add match_state _ st1 m1 st2 m2 -> mem_compat st2 m2 *)
            admit.
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
      Admitted.

      
      Context (Hexterns_have_events: Asm_externals_have_events Asm_g).
      Lemma compile_n_threads:
        forall n m,
          HybridMachine_simulation.HybridMachine_simulation_properties
            (HybConcSem (Some 0)%nat m)
            (HybConcSem (Some n) m)
            invariant
            mem_compatible
            (match_state n).
      Proof.
        induction n.
        - (*trivial reflexive induction*)
          apply trivial_self_injection.
        - eapply simulation_inductive_case; eauto.
          eapply compile_one_thread; auto.
      Qed.

    End CompileNThreads.

    Section CompileInftyThread.
      Context {Hasm_externals: Asm_externals_have_events Asm_g}.
      
      Definition lift_state': forall {on on'},
          ThreadPool on -> ThreadPool on'.
      Proof.
        intros; inv X; econstructor; eauto.
      Defined.
      
      Inductive lift_state: forall on, ThreadPool on -> forall on', ThreadPool on' -> Prop:=
      | build_lift_state: forall on on' st st',
          st' = lift_state' st -> lift_state on st on' st'.
      Lemma lift_contains:
        forall {on on'} st j,
          ThreadPool.containsThread st j <->
          ThreadPool.containsThread (@lift_state' on on' st) j.
      Proof.
        intros. simpl.
        unfold OrdinalPool.containsThread; simpl.
        destruct st; simpl. reflexivity.
      Qed.
      Lemma lift_contains1:
        forall {on on'} st j,
          ThreadPool.containsThread st j ->
          ThreadPool.containsThread (@lift_state' on on' st) j.
      Proof. intros; eapply lift_contains in H; eauto. Qed.
      Lemma lift_contains2:
        forall {on on'} st j,
          ThreadPool.containsThread (@lift_state' on on' st) j ->
          ThreadPool.containsThread st j.
      Proof. intros; eapply lift_contains in H; eauto. Qed.
      Lemma lift_unique_Krun:
        forall {on on'} st i,
          HybridMachineSig.unique_Krun st i <->
          HybridMachineSig.unique_Krun (@lift_state' on on' st) i.
      Proof.
        intros; split; intros ** ? **.
        - unshelve eapply H; eauto.
          eapply (@lift_contains on on' st j); auto.
          simpl. match_case; simpl.
          clear - H0.
          destruct st; simpl in *.
          replace (c0 cnti) with cnti by apply Axioms.proof_irr.
          rewrite H0.
          reflexivity.
        - unshelve eapply H; eauto.
          eapply (@lift_contains on on' st j); auto.
          simpl. match_case; simpl.
          clear - H0.
          destruct st; simpl in *.
          replace (c cnti) with (cnti) by apply Axioms.proof_irr.
          rewrite H0.
          reflexivity.
      Qed.

      
      Lemma lift_invariant:
        forall hb1 hb2 st st',
          lift_state hb1 st hb2 st' ->
          invariant st ->
          invariant st'.
      Admitted.
      Lemma lift_cmpt:
        forall hb1 hb2 st st' m,
          lift_state hb1 st hb2 st' ->
          mem_compatible st m ->
          mem_compatible st' m.
      Admitted.

      
      Inductive infty_match:
        nth_index -> meminj ->
        ThreadPool (Some 0)%nat -> mem ->
        ThreadPool None -> mem -> Prop:=
      | Build_infty_match:
          forall n cd j st0 m0 stn mn st,
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
               list_lt cd' cd).
      Proof.
      (*Proof sketch:
            infty_match defines an intermediate machine Mn at level n, matching the 0 machine.
            All threads of machine Mn are in Asm. A lemma should show that all hier machines 
            (Mk, for k>n) also match the machine at 0. 
            lemma [compile_n_threads] shows that machine M(S n) can step and reestablish 
            [match_states]. Since we increased the hybrid bound (n -> S n) then the new thread 
            is in Asm and [match_states] can be lifted to [infty_match].
       *)
      Admitted.
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
                                             m2 U' tr2' st2' m2'.
      Proof.
        intros. inv H0.
        pose proof (compile_n_threads Hasm_externals n m) as HH.
        eapply machine_diagram in HH; eauto.
        normal_hyp.
        normal; eauto.
        - econstructor; eauto. econstructor; eauto.
        - Lemma lift_machine_step:
            forall on on' tge U tr2 st st' m2 U' x x1 m,
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
                        simpl in *.
            - eapply lift_cmpt; eauto.
              econstructor; auto.
            -
              Notation MachineSig_n on:= (@DryHybridMachineSig
                                  (@HybridSem CC_correct Args on) (TP on)).
              Lemma lift_getC:
                forall on on' st tid X
                  (Htid: ThreadPool.containsThread st tid)
                  (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid),
                  ThreadPool.getThreadC Htid = X ->
                  ThreadPool.getThreadC Htid' = X.
              Proof.
                intros. destruct st; simpl in *.
                replace Htid' with Htid by apply Axioms.proof_irr; auto.
              Qed.
              Lemma lift_getR:
                forall on on' st tid X
                  (Htid: ThreadPool.containsThread st tid)
                  (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid),
                  ThreadPool.getThreadR Htid = X ->
                  ThreadPool.getThreadR Htid' = X.
              Proof.
                intros. destruct st; simpl in *.
                replace Htid' with Htid by apply Axioms.proof_irr; auto.
              Qed.
              Lemma lift_getR':
                forall on on' st tid
                  (Htid: ThreadPool.containsThread st tid)
                  (Htid': ThreadPool.containsThread (@lift_state' on on' st) tid),
                  ThreadPool.getThreadR Htid' = 
                  ThreadPool.getThreadR Htid.
              Proof.
                intros. destruct st; simpl in *.
                replace Htid' with Htid by apply Axioms.proof_irr; auto.
              Qed.
              Lemma lift_start_thread:
                forall on on' m st m' tid
                (Htid: ThreadPool.containsThread st tid)
                (Htid': ThreadPool.containsThread (lift_state' st) tid),
                  start_thread(machineSig:=MachineSig_n on)
                              m Htid st m' ->
                start_thread(machineSig:=MachineSig_n on')
                            m Htid' (lift_state' st) m'.
              Proof.
                intros.
                inv H; econstructor; eauto.
                eapply lift_getC; eauto.
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
                  unfold HybridMachineSig.install_perm, install_perm; simpl;
                    unfold install_perm; intros.
                  clean_proofs.
                  subst m'; f_equal.
                  simpl.
                  eapply synchronisation_lemmas.restrPermMap_access_equiv.
                  unfold thread_perms; simpl.
                  remember (OrdinalPool.getThreadR Htid) as X.
                  symmetry in HeqX.
                  unshelve eapply lift_getR in HeqX; auto.
                  subst X; reflexivity.
                Qed.
                eapply lift_install_perm; eauto.
                Lemma lift_initial_core:
                  forall on on' tid m c m' vf arg,
                  initial_core (sem_coresem (HybridSem on)) tid m c m' vf arg ->
                  initial_core (sem_coresem (HybridSem on')) tid m
                               c m' vf arg.
                Proof.
                  unfold HybridSem; simpl.
                  intros. 
                  unfold initial_core in H.
                  unfold sem_coresem in *.
                  unfold initial_core.
                  
              
              eapply Hcmpt.
            
                      try eapply lift_invariant; 
                      try eapply lift_cmpt; eauto.
            eapply lift_cmpt.
            Lemma lift_start_thread:
              start_thread m2 Htid st' m' ->
              start_thread m2 ?Htid (lift_state' st') m'.
            
        (* Same as the other step diagram.*)
      Admitted.

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
        - clear H st. revert n mu cd i m c1 m1 stn m2 H0.
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
          HybridMachine_simulation.HybridMachine_simulation_properties
            (HybConcSem (Some 0)%nat m)
            (HybConcSem None m)
            invariant
            mem_compatible
            infty_match.
      Proof.
        intros. 
        (*All the proofs use the following lemma*)
        pose proof compile_n_threads as HH.
        econstructor.
        - eapply list_lt_wf.
        - apply initial_infty.
        - apply infinite_step_diagram.
        - intros; eapply infinite_machine_step_diagram;
            eauto.
        - apply infinite_halted.
        - apply infinite_running.
      Qed.
      
      Lemma infty_match_invariant:
        forall cd mu st1 m1 st2 m2,
          infty_match cd mu st1 m1 st2 m2 ->
          invariant st1 ->
          invariant st2.
      Proof.
        intros. inv H.
        assert (invariant stn).
        { clear H2; revert n st1 m1 st2 m2 cd mu stn H1 H0. clear.
          induction n; intros.
          - inv H1; auto.
          - inv H1; eauto. subst_sig.
            eapply H8.
        }
        eapply lift_invariant; eauto.
      Qed.
      Lemma infty_match_cmpt:
        forall cd mu st1 m1 st2 m2,
          infty_match cd mu st1 m1 st2 m2 ->
          mem_compatible st1 m1 ->
          mem_compatible st2 m2.
      Proof.
        intros. inv H.
        assert (mem_compatible stn m2).
        { revert n  st1 m1 H0  st2 m2 cd mu stn H2 H1. clear.
          induction n; intros.
          - inv H1; auto.
          - inv H1; eauto. subst_sig.
            eapply H9.
        }
        eapply lift_cmpt; eauto.
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
