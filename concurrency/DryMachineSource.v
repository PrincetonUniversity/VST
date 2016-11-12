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
    admit.
    }
    
  Admitted.
  
  End FiniteBranching.
  
End THE_DRY_MACHINE_SOURCE.

