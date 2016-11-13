Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import concurrency.scheduler.
Require Import concurrency.TheSchedule.

Require Import concurrency.concurrent_machine.
Require Import concurrency.semantics.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.dry_machine. Import Concur.
(*Require Import concurrency.dry_machine_lemmas. *)
Require Import concurrency.lksize.
Require Import concurrency.permissions.

Require Import concurrency.dry_context.
Require Import concurrency.dry_machine_lemmas.
Require Import concurrency.erased_machine.

(*Semantics*)
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import sepcomp.event_semantics.
Require Import veric.Clight_sim.
Require Import concurrency.ClightSemantincsForMachines.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import concurrency.ssromega. (*omega in ssrnat *)
Set Bullet Behavior "Strict Subproofs".

Import Concur threadPool.

Module THE_DRY_MACHINE_SOURCE.
  Module SCH:= THESCH.         
  Module SEM:= ClightSEM.
  (*Import SCH SEM.*)

  (*Module DSEM := DryMachineShell SEM.
  Module DryMachine <: ConcurrentMachine:= CoarseMachine SCH DSEM.
  Notation DMachineSem:= DryMachine.MachineSemantics. 
  Notation new_DMachineSem:= DryMachine.new_MachineSemantics. 
  Notation dstate:= DryMachine.SIG.ThreadPool.t.
  Notation dmachine_state:= DryMachine.MachState.
  (*Module DTP:= DryMachine.SIG.ThreadPool.*)
  Import DSEM.DryMachineLemmas event_semantics.*)

  Module DMS  <: MachinesSig with Module SEM := ClightSEM.
     Module SEM:= ClightSEM .

     About mySchedule.
     (*Old DSEM*)
     Module DryMachine <: DryMachineSig SEM := DryMachineShell SEM.
     Module ErasedMachine :=  ErasedMachineShell SEM.

     Module DryConc <: ConcurrentMachine :=
      CoarseMachine SCH DryMachine.
     Notation DMachineSem:= DryConc.MachineSemantics. 
     Notation new_DMachineSem:= DryConc.new_MachineSemantics. 

     Module FineConc := concurrent_machine.FineMachine SCH DryMachine.
     (** SC machine*)
     Module SC := concurrent_machine.FineMachine SCH ErasedMachine.
     Module DTP<: ThreadPoolSig:= DryConc.SIG.ThreadPool.
     
     Import DryMachine DTP.
     
  End DMS.
  Module DryMachineLemmas := ThreadPoolWF SEM DMS.

  Module FiniteBranching.
    
  (** *Finite Branching*)
    (* Probably need to assume something about memory.
     Such as:
     1. Next block increases at most by one
     2. semantics is deterministic, so we know all possible changes to memory.
     3. it's finitely branching *)
    Lemma finite_branching_fixed_thread: forall ds ge i,
          safety.finite_on_x
            (@safety.possible_image
               DMS.DryConc.new_state
               DMS.DryConc.Sch
               (fun x y x' => exists y', (DMS.DryConc.new_step ge x y x' y'))
               (fun st y => SCH.schedPeek y = Some i /\ DMS.DryConc.new_valid st y)
               ds).
    Proof.
      move=> [] [] tr dm m  prog i. 
      rewrite /safety.finite_on_x /safety.possible_image /=.
      rewrite /DMS.DryConc.new_step /DMS.DryConc.new_valid /=.
      rewrite /DMS.DryConc.valid /DMS.DryConc.correct_schedule.
      rewrite /DMS.DryConc.unique_Krun /DMS.DryMachine.ThreadPool.containsThread.
      rewrite /DMS.DryConc.mk_ostate /=.

      (*Preliminary lemmas*)
      Lemma schedule_not_halted: forall y i,
          SCH.schedPeek y = Some i ->
          forall ge tr dm m y' tr' dm' m',
            DMS.DryConc.sem_with_halt ge (y, tr, dm) m (y', tr', dm') m' ->
            DMS.DryConc.MachStep ge (y, tr, dm) m (y', tr', dm') m'.
      Proof.
        intros.
        inversion H0; auto; simpl in *; subst.
        unfold DMS.DryConc.halted in H7.
        rewrite H in H7; inversion H7.
      Qed.
      Lemma no_thread_halted: forall i ds cnti,
          ~ @DMS.DryMachine.threadHalted i ds cnti.
      Proof. intros i ds cnti halted. inversion halted; subst.
             move: Hcant.
             rewrite /semantics.halted
                     /DMS.DryMachine.ThreadPool.SEM.Sem
                     /DMS.SEM.Sem SEM.CLN_msem //.
      Qed.

      (*First check if it's mem_compatible. If not, it can't step! *)
      pose (mem_compat_dec:=
              DMS.DryMachine.mem_compatible dm m).
      destruct (Classical_Prop.classic mem_compat_dec) as [Hcmpt|NHcmpt].
      Focus 2. (*it can't step! *)
      { 
        exists 1%nat, (fun _ => (tr, dm, m)).
        move => x y [] val [] y' stp.
        inversion stp; subst.
        - exists O; split.
          + compute; reflexivity.
          + destruct x as [[ ? ?] ?]; reflexivity.
        - inversion H; destruct x as [[a b] c]; simpl in *; subst;
          try solve [exfalso; apply NHcmpt; exact Hcmpt].
          (*only the schedule fail is left*)
          exists O; split.
          + compute; reflexivity.
          + reflexivity.
      } Unfocus.

      (*Second, check the thread is contained *)
      destruct (i < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N eqn:cnti'.
      Focus 2. {
        assert (cnti: (~ i < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N).
        rewrite cnti'; auto. clear cnti'.
        
        pose (st0 := (tr,dm,m)).
        exists 1%nat, (fun _ => st0).
        move => x y [] [] PEEK; rewrite PEEK.
        move => HH [] y' /(schedule_not_halted y i PEEK) STEP.
        inversion STEP; simpl in *; subst;
        match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try solve [exfalso; apply cnti; auto].
        exists 0%nat; split; auto.
        destruct x as [[? ?] ?]; simpl in *; subst; auto.
      } Unfocus.

      assert (cnti: (i < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N).
      rewrite cnti'; auto. clear cnti'.

      
      (*Third check the state of the thread: Krun Kblock. Kresume Kinit*)
      destruct (DMS.DTP.getThreadC cnti) eqn:Hruning.
      { (* Krun *)
        rename Hruning into is_running.

        (*If the schedule is empty, it's halted so the same state 
         * notice this case is impossible, but it's easier to 
         *consider it *)
        pose (st0 := (tr,dm,m)).
        (* Make a fake schedule, standing in for the real one *)
        pose (sch0:= i::nil).
        (*Step suspending would go to: *)
        pose (st1 := (tr,DMS.DryMachine.ThreadPool.updThreadC cnti (Kblocked c),m)).
        (*Otherwise it will take a step*)
        pose (m1:= restrPermMap (DMS.DryMachine.compat_th Hcmpt cnti).1).
        pose (step_dec:=
                exists c' m',
                  veric.Clight_new.cl_step prog c m1 c' m').
        destruct (Classical_Prop.classic step_dec) as [steps | steps]; move: steps.
      - move=> [] c' [] m' steps.
        pose (st2 := (tr,
                      DMS.DryMachine.ThreadPool.updThread
                        cnti
                        (Krun c')
                        (getCurPerm m',
                         (DMS.DryMachine.ThreadPool.getThreadR cnti).2)
                      ,m')).
        exists 4%nat.
        exists (fun i => match i with
                 | O => st0
                 | 1%nat => st1
                 | _ => st2
                         end).
        move => x y [] [] PEEK VAL [] y' steps2.
        inversion steps2; subst.
        + (* if halted *)
          exists O; split.
          * compute; reflexivity.
          * destruct x as [[? ?] ?]; reflexivity.
        + (*its a machine step*)
          simpl in VAL.
          rewrite PEEK in VAL.
         (*If not halted, the running thread is i*)
          (*specialize (VAL _ _ _ is_running ltac:(eapply no_thread_halted; eauto));
            destruct (SCH.TID.eq_tid_dec); inversion VAL.*)
          inversion H; (*Lets go through all possible steps*)
            simpl in *; subst;
          match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end) .
          * (*Thread step*)
            subst.
            apply ev_step_ax1 in Hcorestep.
            move: Hcorestep.
            rewrite /DMS.DryMachine.ThreadPool.SEM.Sem SEM.CLN_msem /= => steps'.
            (*We use that CLight is deterministic: *)
            Lemma CLight_Deterministic: forall ge c m c1 m1 c2 m2,
                veric.Clight_new.cl_step ge c m c2 m2 ->
                veric.Clight_new.cl_step ge c m c1 m1 ->
                c1 = c2 /\ m1 = m2.
                    
            Admitted.
            move: steps'.
            replace Hcmpt0 with Hcmpt by apply proof_irrelevance;
              replace Htid with cnti by apply proof_irrelevance .
            move => steps'.
            destruct (CLight_Deterministic _ _ _ _ _ _ _ steps steps').
            exists 2%nat; split.
            -- compute; reflexivity.
            -- destruct x as [[? ?]?]; simpl in *; subst.
               unfold st2; simpl.
               replace Htid with cnti by apply proof_irrelevance.
               reflexivity.
          * (*suspend_step *)
            exists 1%nat.
            split.
            -- compute; reflexivity.
            -- destruct x as [[? ?]?]; simpl in *; subst.
               unfold st1; simpl.
               replace Htid with cnti by apply proof_irrelevance.
               reflexivity.
          * (*Halted*)
            exfalso.
            eapply no_thread_halted.
            eassumption.
          * (*Schedule fail*)
            exfalso.
            apply Htid.
            assumption.
      - (*Other cases when can't step*)
        exists 3%nat.
        exists (fun i => match i with
                 | O => st0
                 | _ => st1
                 end) => x y /=.
        move => [] [] PEEK VAL [] y' steps2.
        inversion steps2; subst.
        + (* if halted *)
          exists O; split.
          * compute; reflexivity.
          * destruct x as [[? ?] ?]; reflexivity.
        + (*its a machine step*)
          simpl in VAL; rewrite PEEK in VAL.
          (*If not halted, the running thread is i*)
          (*specialize (VAL _ _ _ is_running ltac:(eapply no_thread_halted; eauto));
            destruct (SCH.TID.eq_tid_dec); inversion VAL. *)
          subst.
          inversion H; (*Lets go through all possible steps*)
            simpl in *; try subst;
          try match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try subst;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end) ;
          try subst.
          * (*Thread step*)
            subst.
            apply ev_step_ax1 in Hcorestep.
            exfalso; apply steps.
            rewrite /step_dec.
            exists c', x.2.
            unfold m1.
            replace Hcmpt with Hcmpt0 by apply proof_irrelevance.
            replace cnti with Htid by apply proof_irrelevance.
            unfold DMS.DryMachine.ThreadPool.SEM.Sem in Hcorestep.
            rewrite ClightSEM.CLN_msem in Hcorestep.
            simpl in Hcorestep.
            assumption.
          * (*suspend step*)
            simpl in *;
            subst.
            exists 1%nat; split.
            -- compute; reflexivity.
            -- destruct x as [[xa xb] xc]; simpl in *.
               simpl.
               replace ctn with cnti in Hms' by apply proof_irrelevance.
               unfold st1.
               rewrite Hms'.
               subst.
               reflexivity.
          * exfalso; eapply no_thread_halted .
            eassumption.
          * exfalso; apply Htid.
            assumption.
      }

      { (*Kblocked*)
        rename Hruning into Hblocked.
        admit.
      }

      { (*Kresume*)
        (*then it must be after external*) 
        destruct (after_external DMS.DryMachine.ThreadPool.SEM.Sem None c) eqn:AftEx.
        Focus 2. {
          exists 0%nat, (fun _  => (tr, dm, m)).
          move => x y [] [] PEEK; rewrite PEEK.
        move=> _ [] y' /(schedule_not_halted y i PEEK) STEP.
        
        inversion STEP; (*Lets go through all possible steps*)
          simpl in *; try subst;
          try match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try subst;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end).
          - subst. rewrite AftEx in Hafter_external; congruence.
          - exfalso; eapply no_thread_halted; eassumption.
          - exfalso; apply Htid; assumption.
        } Unfocus.

          
        exists 1%nat.
        exists (fun _ => (tr,
                  @DMS.DryMachine.ThreadPool.updThreadC i dm cnti (Krun c0),
                  m)).
        move => x y [] [] PEEK; rewrite PEEK.
        move=> _ [] y' /(schedule_not_halted y i PEEK) STEP.
        
        inversion STEP; (*Lets go through all possible steps*)
          simpl in *; try subst;
          try match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try subst;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end).
        - (* Resume *)
          exists 0%nat; split; auto.
          destruct x as [[? ?] ?]; simpl in *; subst.
          replace ctn with cnti by apply proof_irrelevance.
          rewrite AftEx in Hafter_external; inversion Hafter_external; auto.
        - exfalso; eapply no_thread_halted; eassumption.
        - exfalso; apply Htid; assumption.
      }

      { (*Kinit*)

        (*then it must be ready to start*) 
        destruct (initial_core DMS.DryMachine.ThreadPool.SEM.Sem prog v [:: v0]) eqn:Hinit.
        Focus 2. {
          exists 0%nat, (fun _  => (tr, dm, m)).
          move => x y [] [] PEEK; rewrite PEEK.
        move=> _ [] y' /(schedule_not_halted y i PEEK) STEP.
        
        inversion STEP; (*Lets go through all possible steps*)
          simpl in *; try subst;
          try match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try subst;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end).
          - subst. rewrite Hinit in Hinitial; congruence.
          - exfalso; eapply no_thread_halted; eassumption.
          - exfalso; apply Htid; assumption.
        } Unfocus.

        exists 1%nat.
        exists (fun _ => (tr,
                  @DMS.DryMachine.ThreadPool.updThreadC i dm cnti (Krun c),
                  m)).
        move => x y [] [] PEEK; rewrite PEEK.
        move=> _ [] y' /(schedule_not_halted y i PEEK) STEP.
        
        inversion STEP; (*Lets go through all possible steps*)
          simpl in *; try subst;
          try match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try subst;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end).
          - exists 0%nat; split; auto.
          destruct x as [[? ?] ?]; simpl in *; subst.
          replace ctn with cnti by apply proof_irrelevance.
          rewrite Hinit in Hinitial; inversion Hinitial; auto.
          - exfalso; eapply no_thread_halted; eassumption.
          - exfalso; apply Htid; assumption.
      }
      Admitted.



    
  Lemma finite_branching: forall ds ge,
          safety.finite_on_x
            (@safety.possible_image
               DMS.DryConc.new_state
               DMS.DryConc.Sch
               (fun x y x' => exists y', (DMS.DryConc.new_step ge x y x' y'))
               DMS.DryConc.new_valid ds).
  Proof.
    move=> [] [] tr dm m  prog.
    rewrite /safety.finite_on_x /safety.possible_image /=.
    rewrite /DMS.DryConc.new_step /DMS.DryConc.new_valid /=.
    rewrite /DMS.DryConc.valid /DMS.DryConc.correct_schedule.
    rewrite /DMS.DryConc.unique_Krun /DMS.DryMachine.ThreadPool.containsThread.
    rewrite /DMS.DryConc.mk_ostate.
    (*First check if it's mem_compatible. If not, it can't step! *)
    pose (mem_compat_dec:=
              DMS.DryMachine.mem_compatible dm m).
    destruct (Classical_Prop.classic mem_compat_dec) as [Hcmpt|NHcmpt].
    Focus 2. (*it can't step! *)
    { 
    exists 1%nat, (fun _ => (tr, dm, m)).
    move => x y [] val [] y' stp.
    inversion stp; subst.
    - exists O; split.
      + compute; reflexivity.
      + destruct x as [[ ? ?] ?]; reflexivity.
    - inversion H; destruct x as [[a b] c]; simpl in *; subst;
      try solve [exfalso; apply NHcmpt; exact Hcmpt].
      (*only the schedule fail is left*)
       exists O; split.
      + compute; reflexivity.
      + reflexivity.
    } Unfocus.

    
      (*Introduce a bound to do induction*)
      cut ( forall M:nat,
            exists (n : nat) (f : nat -> DMS.DryConc.new_state),
    forall (x : DMS.DryConc.new_state) (y : SCH.schedule),
    match SCH.schedPeek y with
    | Some i =>
      (i < M) /\
        forall (j : DMS.DryMachine.ThreadPool.TID.tid)
          (cnti : (j < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N)
          (q : DMS.DryMachine.ThreadPool.SEM.C),
        DMS.DryMachine.ThreadPool.getThreadC cnti = Krun q ->
        ~ DMS.DryMachine.threadHalted cnti -> SCH.TID.eq_tid_dec i j
    | None => True
    end /\
    (exists y' : SCH.schedule,
       DMS.DryConc.sem_with_halt prog (y, tr, dm) m (y', x.1.1, x.1.2) x.2) ->
    exists i : nat, (i < n)%N /\ f i = x ).
      { simpl. move => /(_ (pos.n (DMS.DryMachine.ThreadPool.num_threads dm))) [] n [] f CUT.
        exists (n+1)%nat, (fun n => match n with
                          | O => (tr,dm, m)
                          | S n' => f n'
                          end).
        move=> x y.
        specialize (CUT x y).
        destruct (SCH.schedPeek y ) eqn:PEEK.
        Focus 2. { (*Machine is halted: end of schedule*)
          move => [] _ [] y' steps.
          inversion steps; simpl in*; subst.
          - exists 0%nat; split.
            + ssromega.
            + destruct x as [[a b ] c]; reflexivity.
          - inversion H; simpl in*; subst;
            try match goal with
                | [ H: SCH.schedPeek ?Y = Some _ ,
                       H': SCH.schedPeek ?Y = None  |- _ ] =>
                  rewrite H in H'; inversion H'
                end.
        } Unfocus.

        destruct (t <  pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N eqn: within_bound.
        - move => [] A B.
          move: (CUT ltac:(repeat split; eauto)) => [] i [] ineq f_ok.
          exists (S i); split; auto.
          ssromega.
        - clear - PEEK within_bound .
          move => [] A [] y' B.
          inversion B; subst.
          + move: H5.
            rewrite /DMS.DryConc.halted /= PEEK => H5; inversion H5.
          + inversion H; simpl in *; subst;
            try match goal with
                | [ H: SCH.schedPeek ?Y = Some _ ,
                       H': SCH.schedPeek ?Y = Some _  |- _ ] =>
                  rewrite H in H'; inversion H'; subst
                end;
            try solve [exfalso;
            unfold DMS.DryMachine.ThreadPool.containsThread in Htid;
            assert (Htid':=Htid);
            rewrite within_bound in Htid'; auto].
        (*schedule fail case*)
            exists 0%nat; split; auto.
            -- ssromega.
            -- destruct x as [[? ?] ?]; simpl in *; subst; auto.
      }

      { (*Proving th cut: a bounded version of finite_branching (bounded threads)*)
        induction M.
        - (*base case must be halted.*)
          exists 1%nat, (fun _ => (tr,dm, m)).
          move => x y.
          destruct (SCH.schedPeek y) eqn:PEEK.
          + move => []  [] WRONG.
            inversion WRONG.
          + move => []  [] [] y' STEP.
            inversion STEP; simpl in *; subst.
            * (*If halted is itself*)
              exists 0%nat; split; auto.
              destruct x as [[a b ] c]; reflexivity.
            * inversion H; simpl in*; subst;
            try match goal with
                | [ H: SCH.schedPeek ?Y = Some _ ,
                       H': SCH.schedPeek ?Y = None  |- _ ] =>
                  rewrite H in H'; inversion H'
                end.
        - (*Now lets do the inductive step M ->  M+1*)
          (*Step 1: get all the branches from thread M*)
          move: (finite_branching_fixed_thread (tr, dm, m) prog M) => [] NM [] fM threadM.
          
          (*Step2: get all the branches for threads <M, eith the Ind. Hyp.*)
          move: IHM => [] N [] f other_threads.

          (*Use both bounds to construct the new bound*)
          exists (NM + N)%nat.
          exists (fun n => if n < N then (f n) else (fM (n - N)%nat)).
          move => st' U.

          (*Check schedule*)
           destruct (SCH.schedPeek U ) eqn:PEEK.
           Focus 2. {
             move=> HH (*[] _ [] y' STEP *).
             move : (other_threads st' U).
             rewrite /safety.possible_image /=.
             rewrite PEEK => /(_ HH) [] i [] ineq f_eq.
             exists i; split.
             - ssromega.
             - rewrite ineq; simpl; auto.
           } Unfocus.

           (*Check if t (active thread) is ==M*)
           destruct (NatTID.eq_tid_dec t M).
          + (*t = M*)
            subst.
            move=> [] [] ineq VAL [] y' STEP .
            move : (threadM st' U).
            rewrite /safety.possible_image
                    /DMS.DryConc.new_valid /DMS.DryConc.valid /DMS.DryConc.correct_schedule /=.
            rewrite PEEK => /(_ ltac:(eauto)) [] i [] ineq' f_eq.
            exists (N + i)%nat; split.
            * ssromega.
            * assert ( is_false: (N + i < N)%N = false).
              { clear. apply /negb_true_iff /eq_true_not_negb.
                intros HH. ssromega. }
              rewrite is_false.
              replace (N + i - N)%nat with i; auto.
              ssromega.
          + (* t < M*)
            move=> [] [] ineq VAL [] y' STEP .
            assert (ineq': (t< M)%nat).
            { clear - n ineq. apply /ltP.
              move: ineq => /ltP ineq.
              unfold lt in *.
              eapply le_lt_eq_dec in ineq.
              destruct ineq; auto.
              unfold lt in l.
              apply le_S_n; auto.
              exfalso; apply n.
              inversion e; auto. }
            move : (other_threads st' U).
            rewrite /safety.possible_image
                    /DMS.DryConc.new_valid /DMS.DryConc.valid /DMS.DryConc.correct_schedule /=.
            rewrite PEEK => /(_ ltac:(eauto)) [] i [] ineq'' f_eq.
            exists i%nat; split.
            * ssromega.
            * rewrite ineq''; auto.
      }
  Qed.




          
    
    
    (*Second check if any thread is running*)
    pose (running_dec:=
              exists i q cnti,
                @DMS.DryMachine.ThreadPool.getThreadC i dm cnti = Krun q /\
          ~ DMS.DryMachine.threadHalted cnti ).
    destruct (Classical_Prop.classic running_dec) as [H|H]; move: H.
    { (*First case were something is running*)
      move => [] i [] q [] cnti [] is_running not_halted.
      (*If the schedule is empty, it's halted so the same state *)
      pose (st0 := (tr,dm,m)).
      (* Otherwise, make a fake schedule, standing in for the real one *)
      pose (sch0:= i::nil).
      (*Step suspending would go to: *)
      pose (st1 := (tr,DMS.DryMachine.ThreadPool.updThreadC cnti (Kblocked q),m)).
      (*Otherwise it will take a step*)
      pose (m1:= restrPermMap (DMS.DryMachine.compat_th Hcmpt cnti).1).
      pose (step_dec:=
              exists c' m',
                veric.Clight_new.cl_step prog q m1 c' m').
      destruct (Classical_Prop.classic step_dec) as [steps | steps]; move: steps.
      - move=> [] c' [] m' steps.
        pose (st2 := (tr,
                      DMS.DryMachine.ThreadPool.updThread
                        cnti
                        (Krun c')
                        (getCurPerm m',
                         (DMS.DryMachine.ThreadPool.getThreadR cnti).2)
                      ,m')).
        exists 4%nat.
        exists (fun i => match i with
                 | O => st0
                 | 1%nat => st1
                 | _ => st2
                         end).
        move => x y [] VAL [] y' steps2.
        inversion steps2; subst.
        + (* if halted *)
          exists O; split.
          * compute; reflexivity.
          * destruct x as [[? ?] ?]; reflexivity.
        + (*its a machine step*)
          simpl in VAL.
          destruct (SCH.schedPeek y ) eqn:PEEK.
          Focus 2. (*Halted*)
          { simpl in H.
            inversion H; simpl in *; try subst y;
            try congruence. (*All other steps will contradict hyp. PEEK*)
          } Unfocus.
          (*If not halted, the running thread is i*)
          specialize (VAL _ _ _ is_running not_halted);
            destruct (SCH.TID.eq_tid_dec); inversion VAL; subst t.
          inversion H; (*Lets go through all possible steps*)
            simpl in *; subst;
          match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end) .
          * (*Thread step*)
            subst.
            apply ev_step_ax1 in Hcorestep.
            move: Hcorestep.
            rewrite /DMS.DryMachine.ThreadPool.SEM.Sem SEM.CLN_msem /= => steps'.
            (*We use that CLight is deterministic: *)
            Lemma CLight_Deterministic: forall ge c m c1 m1 c2 m2,
                veric.Clight_new.cl_step ge c m c2 m2 ->
                veric.Clight_new.cl_step ge c m c1 m1 ->
                c1 = c2 /\ m1 = m2.
                    
            Admitted.
            move: steps'.
            replace Hcmpt0 with Hcmpt by apply proof_irrelevance;
              replace Htid with cnti by apply proof_irrelevance .
            move => steps'.
            destruct (CLight_Deterministic _ _ _ _ _ _ _ steps steps').
            exists 2%nat; split.
            -- compute; reflexivity.
            -- destruct x as [[? ?]?]; simpl in *; subst.
               unfold st2; simpl.
               replace Htid with cnti by apply proof_irrelevance.
               reflexivity.
          * (*suspend_step *)
            exists 1%nat.
            split.
            -- compute; reflexivity.
            -- destruct x as [[? ?]?]; simpl in *; subst.
               unfold st1; simpl.
               replace Htid with cnti by apply proof_irrelevance.
               reflexivity.
          * (*Halted*)
            exfalso.
            apply not_halted.
            replace cnti with Htid by apply proof_irrelevance.
            assumption.
          * (*Schedule fail*)
            exfalso.
            apply Htid.
            assumption.
      - (*Other cases when can't step*)
        exists 3%nat.
        exists (fun i => match i with
                 | O => st0
                 | _ => st1
                 end) => x y /=.
        move => [] VAL [] y' steps2.
        inversion steps2; subst.
        + (* if halted *)
          exists O; split.
          * compute; reflexivity.
          * destruct x as [[? ?] ?]; reflexivity.
        + (*its a machine step*)
          simpl in VAL.
          destruct (SCH.schedPeek y) eqn:PEEK.
          Focus 2. (*Halted*)
          { simpl in H.
            inversion H;
            simpl in *; subst y;
            simpl in *; try subst U;
            try congruence. (*All other steps will contradict hyp. PEEK*)
          } Unfocus.
          (*If not halted, the running thread is i*)
          specialize (VAL _ _ _ is_running not_halted);
            destruct (SCH.TID.eq_tid_dec); inversion VAL; subst t.
          subst.
          inversion H; (*Lets go through all possible steps*)
            simpl in *; try subst;
          try match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end; try subst;
          try ( inversion Htstep;
                match goal with
                | [ H: DMS.DryMachine.ThreadPool.getThreadC ?cnt1 = _ ,
                       H': DMS.DryMachine.ThreadPool.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end) ;
          try subst.
          * (*Thread step*)
            subst.
            apply ev_step_ax1 in Hcorestep.
            exfalso; apply steps.
            rewrite /step_dec.
            exists c', x.2.
            unfold m1.
            replace Hcmpt with Hcmpt0 by apply proof_irrelevance.
            replace cnti with Htid by apply proof_irrelevance.
            unfold DMS.DryMachine.ThreadPool.SEM.Sem in Hcorestep.
            rewrite ClightSEM.CLN_msem in Hcorestep.
            simpl in Hcorestep.
            assumption.
          * (*suspend step*)
            simpl in *;
            subst.
            exists 1%nat; split.
            -- compute; reflexivity.
            -- destruct x as [[xa xb] xc]; simpl in *.
               simpl.
               replace ctn with cnti in Hms' by apply proof_irrelevance.
               unfold st1.
               rewrite Hms'.
               subst.
               reflexivity.
          * exfalso; apply not_halted.
            replace cnti with Htid by apply proof_irrelevance.
            assumption.
          * exfalso; apply Htid.
            assumption.
    }
    { (*Second case when all threads are blocked, suspended or halted. *)
      (*Preliminaries*)
      rewrite /running_dec => HH.
      assert (not_running: forall i cnti q,
                 @DMS.DryMachine.ThreadPool.getThreadC i dm cnti = Krun q ->
                 ~ DMS.DryMachine.threadHalted cnti -> False).
      { move=> i cnti q is_running not_halted.
        apply: HH. exists i, q, cnti; auto. }
      clear HH.
      simpl.

      (*Introduce a bound to do induction*)
      cut ( forall M:nat,
            exists (n : nat) (f : nat -> DMS.DryConc.new_state),
    forall (x : DMS.DryConc.new_state) (y : SCH.schedule),
    match SCH.schedPeek y with
    | Some i =>
      (i < M) /\
        forall (j : DMS.DryMachine.ThreadPool.TID.tid)
          (cnti : (j < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N)
          (q : DMS.DryMachine.ThreadPool.SEM.C),
        DMS.DryMachine.ThreadPool.getThreadC cnti = Krun q ->
        ~ DMS.DryMachine.threadHalted cnti -> SCH.TID.eq_tid_dec i j
    | None => True
    end /\
    (exists y' : SCH.schedule,
       DMS.DryConc.sem_with_halt prog (y, tr, dm) m (y', x.1.1, x.1.2) x.2) ->
    exists i : nat, (i < n)%N /\ f i = x ).
      { simpl. move => /(_ (pos.n (DMS.DryMachine.ThreadPool.num_threads dm))) [] n [] f CUT.
        exists (n+1)%nat, (fun n => match n with
                          | O => (tr,dm, m)
                          | S n' => f n'
                          end).
        move=> x y.
        specialize (CUT x y).
        destruct (SCH.schedPeek y ) eqn:PEEK.
        Focus 2. { (*Machine is halted: end of schedule*)
          move => [] _ [] y' steps.
          inversion steps; simpl in*; subst.
          - exists 0%nat; split.
            + ssromega.
            + destruct x as [[a b ] c]; reflexivity.
          - inversion H; simpl in*; subst;
            try match goal with
                | [ H: SCH.schedPeek ?Y = Some _ ,
                       H': SCH.schedPeek ?Y = None  |- _ ] =>
                  rewrite H in H'; inversion H'
                end.
        } Unfocus.

        destruct (t <  pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N eqn: within_bound.
        - move => [] A B.
          move: (CUT ltac:(repeat split; eauto)) => [] i [] ineq f_ok.
          exists (S i); split; auto.
          ssromega.
        - clear - PEEK within_bound .
          move => [] A [] y' B.
          inversion B; subst.
          + move: H5.
            rewrite /DMS.DryConc.halted /= PEEK => H5; inversion H5.
          + inversion H; simpl in *; subst;
            try match goal with
                | [ H: SCH.schedPeek ?Y = Some _ ,
                       H': SCH.schedPeek ?Y = Some _  |- _ ] =>
                  rewrite H in H'; inversion H'; subst
                end;
            try solve [exfalso;
            unfold DMS.DryMachine.ThreadPool.containsThread in Htid;
            assert (Htid':=Htid);
            rewrite within_bound in Htid'; auto].
        (*schedule fail case*)
            exists 0%nat; split; auto.
            -- ssromega.
            -- destruct x as [[? ?] ?]; simpl in *; subst; auto.
      }
      { (*Proving th cut: a bounded version of finite_branching (bounded threads)*)
        induction M.
        - (*base case must be halted.*)
          exists 1%nat, (fun _ => (tr,dm, m)).
          move => x y.
          destruct (SCH.schedPeek y) eqn:PEEK.
          + move => []  [] WRONG.
            inversion WRONG.
          + move => []  [] [] y' STEP.
            inversion STEP; simpl in *; subst.
            * (*If halted is itself*)
              exists 0%nat; split; auto.
              destruct x as [[a b ] c]; reflexivity.
            * inversion H; simpl in*; subst;
            try match goal with
                | [ H: SCH.schedPeek ?Y = Some _ ,
                       H': SCH.schedPeek ?Y = None  |- _ ] =>
                  rewrite H in H'; inversion H'
                end.
        - (*Now lets do the inductive step M ->  M+1*)
          
          
    admit.
    }
    
  Admitted.
  
  End FiniteBranching.
  
End THE_DRY_MACHINE_SOURCE.

