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


Import HybridMachineSig.HybridMachineSig.


(* LIFT:
   We define a lifting operator that moves a Hybrid machine state
   to a higher hybrid bound. Note that the "content" of the state 
   is the same (as long as the number of threads is lower than the
   bound; however the semantics is different.
 *)


Section Lift.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.

  
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridCoarseMachine.DilMem.
  
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