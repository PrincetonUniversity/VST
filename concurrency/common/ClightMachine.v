Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.common.scheduler.

Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
(*Require Import VST.concurrency.common.juicy_machine. Import Concur.*)
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.

Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.erased_machine.

(*Semantics*)
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.sepcomp.event_semantics.
(*Require Import VST.veric.Clight_sim.*)
Require Import VST.concurrency.common.ClightSemanticsForMachines.
Require Import VST.concurrency.common.Clight_bounds.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.common.ssromega. (*omega in ssrnat *)
Set Bullet Behavior "Strict Subproofs".

Import threadPool.

Module Clight_newMachine.

  Import HybridMachineSig.

  Module DMS.
  Section DMS.

  Context {ge : genv}.
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Instance DSem : Semantics := Clight_newSem ge.


  (* First construct the Clight machine and the two projections:
     - ClightMachineSem (i.e.  MachineSemantics) 
     - ClightConcurSem (i.e. ConcurMachineSemantics)
  *)
  
  Definition ClightMachine :=(HybridCoarseMachine.HybridCoarseMachine
                                 (machineSig := DryHybridMachine.DryHybridMachineSig)).
  Definition ClightMachineSem := (MachineSemantics(HybridMachine := ClightMachine)).
  Definition ClightConcurSem := (ConcurMachineSemantics(HybridMachine := ClightMachine)).   
  End DMS.
  End DMS.
End Clight_newMachine.


Module ClightMachine.

  Import HybridMachineSig.

  Module DMS.
  Section DMS.

  Context {ge : genv}.
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Instance DSem : Semantics := ClightSem ge.


  (* First construct the Clight machine and the two projections:
     - ClightMachineSem (i.e.  MachineSemantics) 
     - ClightConcurSem (i.e. ConcurMachineSemantics)
  *)
  
  Definition ClightMachine :=(HybridCoarseMachine.HybridCoarseMachine
                                 (machineSig := DryHybridMachine.DryHybridMachineSig)).
  Definition ClightMachineSem := (MachineSemantics(HybridMachine := ClightMachine)).
  Definition ClightConcurSem := (ConcurMachineSemantics(HybridMachine := ClightMachine)).   
  End DMS.
  End DMS.
End ClightMachine.



Module FiniteBranching.

  (** *Finite Branching*)
(* Probably need to assume something about memory.
     Such as:
     1. Next block increases at most by one
     2. semantics is deterministic, so we know all possible changes to memory.
     3. it's finitely branching *)
(*    Lemma schedule_not_halted: forall y i,
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
      Qed.*)

(*    Lemma finite_branching_sync: forall ds ge i cnti c,
      getThreadC i ds.1.2 cnti = Kblocked c ->
          safety.finite_on_x
            (@safety.possible_image
               DMS.DryConc.new_state
               DMS.DryConc.Sch
               (fun x y x' => exists y', (DMS.DryConc.new_step ge x y x' y'))
               (fun st y => schedPeek y = Some i /\ DMS.DryConc.new_valid_bound st y)
               ds).
    Proof.
      move=> [] [] tr dm m ge i cnti c KRES.
      rewrite /safety.finite_on_x /safety.possible_image /=.
      rewrite /DMS.DryConc.new_step /DMS.DryConc.new_valid_bound /=.
      rewrite /DMS.DryConc.valid /DMS.DryConc.correct_schedule.
      rewrite /DMS.DryConc.unique_Krun /DMS.DryMachine.ThreadPool.containsThread.

      pose (bounded_mem_dec:= DMS.DryConc.bounded_mem m).
      destruct (Classical_Prop.classic bounded_mem_dec) as [Hbound|NHbound].
      2:{
        exists 1%nat, (fun _ => (tr, dm, m)).
        move => x y [] [] val [] sch_ok bounde [] y' stp.
        exfalso; apply NHbound; auto.
      }

      pose (mem_compat_dec:=
              DMS.DryMachine.mem_compatible dm m).
      destruct (Classical_Prop.classic mem_compat_dec) as [Hcmpt|NHcmpt].
      2:{ (*it can't step! *)
        exists 1%nat, (fun _ => (tr, dm, m)).
        move => x y [] val [] y' stp.
        inversion stp; subst.
        - exists O; split.
          + compute; reflexivity.
          + destruct x as [[ ? ?] ?]; reflexivity.
        - inversion H; destruct x as [[? ?] ?]; simpl in *; subst;
          try solve [exfalso; apply NHcmpt; exact Hcmpt].
          (*only the schedule fail is left*)
          exists O; split.
          + compute; reflexivity.
          + reflexivity.
      }


      Lemma is_syncStep:
        forall ge tr dm m i cnti c
        (Hcmpt: DMS.DryMachine.mem_compatible dm m),
          @DMS.DTP.getThreadC i dm cnti = Kblocked c ->
          forall y,
                  SCH.schedPeek y = Some i -> DMS.DryConc.new_valid_bound (tr, dm, m) y ->
                forall y' tr' dm' m',
                  DMS.DryConc.MachStep ge (y, tr, dm) m (y', tr', dm') m' ->
                  tr' = nil /\
                  SCH.schedPeek y = Some i /\
                  SCH.schedSkip y = y' /\
                  exists ev,
                    DMS.DryMachine.syncStep true ge cnti Hcmpt dm' m' ev.
      Proof.
        move=> ? ? ? ? ? cnti ? Hcmpt KBLOCK ? PEEK.
        rewrite PEEK => VAL y' tr' dm' m' STEP; split ; [|split].
        - inversion STEP; simpl in *; subst; try reflexivity.
        - reflexivity.
        - inversion STEP; simpl in *; try subst; (*Lets go through all possible steps*)
         match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
         end; simpl in *; try subst;
         try solve [inversion Htstep;
                match goal with
                | [ H: DMS.DTP.getThreadC ?cnt1 = _ ,
                       H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end].
          + split; auto; exists ev; auto.
            clear - Htstep.
            replace cnti with Htid by apply proof_irrelevance.
            replace Hcmpt with Hcmpt0 by apply proof_irrelevance.
            auto.
          + exfalso; eapply no_thread_halted; eassumption.
          + exfalso; apply Htid; assumption.
      Qed.

      pose (is_syncStep:= is_syncStep ge tr dm m i cnti c Hcmpt KRES).

      (*It most be at_external *)
      destruct (at_external DMS.DryMachine.ThreadPool.SEM.Sem ge c m) eqn:AtExt.
      2:{
        exists 0%nat, (fun _ => (tr, dm, m)).
        move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
        move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
        inversion Htstep;
          match goal with
          | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                 H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
            rewrite H in H'; inversion H'; subst c
          end; congruence.
       }

      (*the arguments can't be empty*)
      destruct p as [FUN ARGS].
      pose (the_args_dec:= exists b ofs ARGS', ARGS = Vptr b ofs :: ARGS').
      destruct (Classical_Prop.classic the_args_dec) as [Hargs|NHargs].
      2:{
        exists 0%nat, (fun _ => (tr, dm, m)).
        move=> x y [] [] PEEK.
        rewrite PEEK => VAL [] y' /(schedule_not_halted y i PEEK) STEP.
        inversion STEP; simpl in *; try subst; (*Lets go through all possible steps*)
         match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
         end; simpl in *; try subst;
         try (inversion Htstep;
                match goal with
                | [ H: DMS.DTP.getThreadC ?cnt1 = _ ,
                       H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end; subst);
        try (match goal with
        | [ H: at_external ?SEM _ ?c _ = Some (FUN, ARGS),
               H' : at_external ?SEM _ ?c _ = Some (_, ((Vptr ?b ?ofs):: ?ARGS')) |- _ ] =>
          exfalso; apply NHargs; exists b, ofs, ARGS';
          rewrite H in H'; inversion H'; auto; pose (2)
        | [ H: at_external ?SEM _ ?c _ = _ ,
               H' : at_external ?SEM _ ?c' _ =  _  |- _ ] =>
          pose (NNNN:= c); pose (NNNNN:= c'); pose (3)
             end).
        - exfalso; eapply no_thread_halted; eassumption.
        - exfalso; apply Htid; assumption.
      }
      move: Hargs => [] b [] ofs [] ARGS' HH.
      subst ARGS. clear the_args_dec.

      (** *MKLOCK case*)
      destruct (extfunct_eqdec FUN (EF_external "makelock" UNLOCK_SIG)) as [? | notMKLOCK].
      {
        subst.

        (*must be able to store*)
        pose (m1:= restrPermMap (DMS.DryMachine.compat_th Hcmpt cnti).1).
        destruct (Mem.store Mint32 m1 b (Ptrofs.intval ofs) (Vint Int.zero)) as [m'|] eqn:Hstore'.
        2:{
        exists 0%nat, (fun _ => (tr, dm, m)).
        move=> x y [] [] PEEK.
        rewrite PEEK => VAL [] y' /(schedule_not_halted y i PEEK) STEP.




        
        inversion STEP; simpl in *; try subst; (*Lets go through all possible steps*)
         match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
         end; simpl in *; try subst;
         try (inversion Htstep;
                match goal with
                | [ H: DMS.DTP.getThreadC ?cnt1 = _ ,
                       H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end; subst);
        try (match goal with
        | [ H: at_external ?SEM _ ?c _ = Some (_, _),
               H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
          try solve[ rewrite H in H'; inversion H']
        | [ H: at_external ?SEM _ ?c _ = Some (?FUN, _),
               H' : at_external ?SEM _ ?c _ = Some (?FUN', _ ) |- _ ] =>
          pose (NNNN:= FUN); pose (NNNNN:= FUN'); pose (3)
             end);
        try solve[ exfalso; eapply no_thread_halted; eassumption];
        try solve[ exfalso; apply Htid; assumption].

        
         
        rewrite AtExt in Hat_external; inversion Hat_external; subst.
        unfold m1 in Hstore'.
        replace Hcmpt0 with Hcmpt in Hstore by apply proof_irrelevance.
        replace Htid with cnti in Hstore by apply proof_irrelevance.
        clear - Hstore Hstore'.
        rewrite Hstore' in Hstore; inversion Hstore.
        }

        pose (pmap_tid'0:= (setPermBlock (Some Nonempty) b
                    (Ptrofs.intval ofs)
                    (DMS.DryMachine.ThreadPool.getThreadR cnti).1
                    LKSIZE_nat,
                    setPermBlock (Some Writable) b
                    (Ptrofs.intval ofs)
                    (DMS.DryMachine.ThreadPool.getThreadR cnti).2
                    LKSIZE_nat)).
        pose (tp'0:= DMS.DryMachine.ThreadPool.updThread cnti
                    (Kresume c Vundef) pmap_tid'0).
        pose (tp''0 :=
                  DMS.DryMachine.ThreadPool.updLockSet tp'0
                    (b, Ptrofs.intval ofs) (empty_map, empty_map)).
        exists 1%nat, (fun _ => ([::], tp''0, m')).
        move=> x y [] [] PEEK.
        rewrite PEEK => VAL [] y' /(schedule_not_halted y i PEEK) STEP.
        inversion STEP; simpl in *; try subst; (*Lets go through all possible steps*)
         match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
         end; simpl in *; try subst;
         try (inversion Htstep;
                match goal with
                | [ H: DMS.DTP.getThreadC ?cnt1 = _ ,
                       H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end; subst);
        try (match goal with
        | [ H: at_external ?SEM _ ?c _ = Some (_, _),
               H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
          rewrite H in H'; inversion H'
        | [ H: at_external ?SEM _ ?c _ = Some (?FUN, _),
               H' : at_external ?SEM _ ?c _ = Some (?FUN', _ ) |- _ ] =>
          pose (NNNN:= FUN); pose (NNNNN:= FUN'); pose (3)
             end);
        try solve[ exfalso; eapply no_thread_halted; eassumption];
        try solve[ exfalso; apply Htid; assumption].

        exists 0%nat; split; auto.
        destruct x as [[? ?] ?]; simpl in *; subst.
        repeat f_equal.
        - rewrite /tp''0 /tp'0; repeat f_equal;
          try apply proof_irrelevance.
          destruct pmap_tid'; simpl in *; subst.
          rewrite /pmap_tid'0.
          repeat f_equal; apply proof_irrelevance.
        - simpl in *; subst.
          unfold m1 in Hstore'.
          replace Hcmpt0 with Hcmpt in Hstore by apply proof_irrelevance.
          replace Htid with cnti in Hstore by apply proof_irrelevance.
          clear - Hstore Hstore'.
          rewrite Hstore' in Hstore; inversion Hstore.
          auto.
      }

      (*Compute the bounds*)
      assert (Hbound':=Hbound).
      eapply bounded_maps.finite_sub_maps
        in Hbound as bounded_delta_map.
      eapply bounded_maps.finite_sub_maps_simpl
        in Hbound' as bounded_access_map.

      pose (virtue_bound:= konig.finite_product bounded_delta_map bounded_delta_map).
      pose (otherLP_bound:= konig.finite_product bounded_access_map bounded_access_map).


      (** *ACQUIRE and ACQFAIL cases*)
      destruct (extfunct_eqdec FUN LOCK).
      { (* **acquire AND acquire fail case*)
        subst.
        pose (m1:= restrPermMap (DMS.DryMachine.compat_th Hcmpt cnti).2).

        (*Check if can acquire*)
        pose (load_one_dec:=
                Mem.load Mint32 m1 b (Ptrofs.intval ofs) = Some (Vint Int.one)).
        destruct (Classical_Prop.classic load_one_dec) as [Hone_zero| Nload].

        (*ACQFAIL*)
        2:{
        exists 1%nat, (fun _ => (tr, dm, m)).
        move=> x y [] [] PEEK.
        rewrite PEEK => VAL [] y' /(schedule_not_halted y i PEEK) STEP.
        inversion STEP; simpl in *; try subst; (*Lets go through all possible steps*)
         match goal with
          | [ H: SCH.schedPeek ?Y = Some _ ,
                 H': SCH.schedPeek ?Y = Some _  |- _ ] =>
            rewrite H in H'; inversion H'; subst
         end; simpl in *; try subst;
         try (inversion Htstep;
                match goal with
                | [ H: DMS.DTP.getThreadC ?cnt1 = _ ,
                       H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
                  replace cnt2 with cnt1 in H' by apply proof_irrelevance;
                    rewrite H in H'; inversion H'
                end; subst);
        try (match goal with
        | [ H: at_external ?SEM _ ?c _ = Some (_, _),
               H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
          rewrite H in H'; inversion H'
        | [ H: at_external ?SEM _ ?c _ = Some (?FUN, _),
               H' : at_external ?SEM _ ?c _ = Some (?FUN', _ ) |- _ ] =>
          pose (NNNN:= FUN); pose (NNNNN:= FUN'); pose (3)
             end);
        try solve[ exfalso; eapply no_thread_halted; eassumption];
        try solve[ exfalso; apply Htid; assumption].
        - subst. exfalso; apply Nload.
          rewrite /load_one_dec /m1.
          replace Hcmpt with Hcmpt0 by apply proof_irrelevance.
          replace cnti with Htid by apply proof_irrelevance.
          auto.
        - exists 0%nat; split; auto.
          destruct x as [[? ?] ?]; simpl in *; subst; auto.
        }

        pose (pmap_tid'0:=
                setPermBlock (Some Writable) b
                             (Ptrofs.intval ofs)
                             (DMS.DryMachine.ThreadPool.getThreadR cnti).2 LKSIZE_nat).

        pose (Hlt_dec:= permMapLt pmap_tid'0 (getMaxPerm m)).
        destruct (Classical_Prop.classic Hlt_dec) as [Hlt| NHlt].
        2:{
          exists 0%nat, (fun _ => (tr, dm, m)).
          move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
          move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
          inversion Htstep;
            match goal with
            | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                   H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
              rewrite H in H';  inversion H'; subst c
            end;
            try (match goal with
                 | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                        H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                   rewrite H in H'; pose (NN:= H'); inversion H'
                 end; simpl in *; try subst).
          - exfalso; apply NHlt; auto.
          - exfalso. subst. clear - AtExt  Hat_external. congruence.
          - rewrite Hone_zero in Hload; inversion Hload.
        }

        (*must be able to store*)
        pose (m2:= restrPermMap Hlt).
        destruct (Mem.store Mint32 m2 b (Ptrofs.intval ofs) (Vint Int.zero)) as [m'|] eqn:Hstore'.
        2:{
          exists 0%nat, (fun _ => (tr, dm, m)).
          move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
          move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
          inversion Htstep;
            match goal with
            | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                   H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
              rewrite H in H'; inversion H'; subst c
            end; try congruence; simpl in *; subst;
            try (match goal with
                 | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                        H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                   rewrite H in H'; inversion H'
                 end; simpl in *; try subst);
            try solve[rewrite Hone_zero in Hload; inversion Hload].
          - clear - Hstore Hstore'.
            replace Hlt' with Hlt in Hstore by apply proof_irrelevance.
            rewrite Hstore' in Hstore; inversion Hstore.
        }

        destruct virtue_bound as [N [virtue_generator virtue_gen_spec] ].
        pose (newThreadPerm v :=
                     (computeMap
                        (DMS.DryMachine.ThreadPool.getThreadR cnti).1
                        v.1,
                     computeMap (DMS.DryMachine.ThreadPool.getThreadR cnti).2
                       v.2)).
        (*pose (newThreadPerm
                (v:PTree.t (Z -> option permission)*PTree.t (Z -> option permission)) :=
                (((DMS.DTP.getThreadR cnti).1.1, v.1),
                 ((DMS.DTP.getThreadR cnti).2.1, v.2))). *)
        pose( tp'0 v:=
                   DMS.DryMachine.ThreadPool.updThread cnti
                     (Kresume c Vundef) (newThreadPerm v)).
        pose (tp''0 v:=
                DMS.DryMachine.ThreadPool.updLockSet (tp'0 v)
                     (b, Ptrofs.intval ofs) (empty_map, empty_map)).

        exists N.
        exists (fun n => (nil,
                  tp''0 (virtue_generator n),
                  m')).
        move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
        move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
        inversion Htstep;
          match goal with
          | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                 H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
            rewrite H in H'; inversion H'; subst c
          end; try congruence;
          try (match goal with
               | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                      H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                 rewrite H in H'; inversion H'
               end; simpl in *; try subst);
          try solve[rewrite Hone_zero in Hload; inversion Hload].
        unfold tp''0, tp'0.
        assert (H: bounded_maps.sub_map virtueThread.1 (getMaxPerm m).2 /\
                    bounded_maps.sub_map virtueThread.2 (getMaxPerm m).2).
        { auto. }
        move: H => /virtue_gen_spec [] j [] /ltP ineq vg_spec.
        exists j; split; auto.
        rewrite vg_spec.
        destruct x as [[ ? ?] ?]; simpl in *; subst.
        repeat f_equal.
        clear -Hstore Hstore'.
        replace Hlt' with Hlt in Hstore by apply proof_irrelevance.
        rewrite Hstore' in Hstore; inversion Hstore.
        auto.

      }




      (** *RELEASE cases*)
      destruct (extfunct_eqdec FUN UNLOCK).
      { (* **Release case*)



        subst.
        pose (m0:= restrPermMap (DMS.DryMachine.compat_th Hcmpt cnti).2).

        (*Most be acquired*)
        pose (load_one_dec:=
                Mem.load Mint32 m0 b (Ptrofs.intval ofs) = Some (Vint Int.zero)).
        destruct (Classical_Prop.classic load_one_dec) as [Hone_zero| Nload].
        2:{
        exists 0%nat, (fun _ => (tr, dm, m)).
          move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
          move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
          inversion Htstep;
            match goal with
            | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                   H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
              rewrite H in H';  inversion H'; subst c
            end; try congruence;
            try (match goal with
                 | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                        H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                   rewrite H in H'; pose (NN:= H'); inversion H'
                 end; simpl in *; try subst).
        - exfalso; apply Nload.
          apply Hload.
        }

        pose (pmap_tid'0:=
                setPermBlock (Some Writable) b
                             (Ptrofs.intval ofs)
                             (DMS.DryMachine.ThreadPool.getThreadR cnti).2 LKSIZE_nat).
        pose (Hlt_dec:= permMapLt pmap_tid'0 (getMaxPerm m)).
        destruct (Classical_Prop.classic Hlt_dec) as [Hlt| NHlt].
        2:{
          exists 0%nat, (fun _ => (tr, dm, m)).
          move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
          move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
          inversion Htstep;
            match goal with
            | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                   H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
              rewrite H in H';  inversion H'; subst c
            end; try congruence;
            try (match goal with
                 | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                        H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                   rewrite H in H'; pose (NN:= H'); inversion H'
                 end; simpl in *; try subst).
          - exfalso; apply NHlt. auto.
        }

        (*must be able to store*)
        pose (m1:= restrPermMap Hlt).
        destruct (Mem.store Mint32 m1 b (Ptrofs.intval ofs) (Vint Int.one)) as [m'|] eqn:Hstore'.
        2:{
          exists 0%nat, (fun _ => (tr, dm, m)).
          move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
          move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
          inversion Htstep;
            match goal with
            | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                   H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
              rewrite H in H'; inversion H'; subst c
            end; try congruence;
            try (match goal with
                 | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                        H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                   rewrite H in H'; inversion H'
                 end; simpl in *; try subst).
          - clear - Hstore Hstore'.
            replace Hlt' with Hlt in Hstore by apply proof_irrelevance.
            rewrite Hstore' in Hstore; inversion Hstore.
        }

        pose (virtueXother_bound:= konig.finite_product virtue_bound otherLP_bound).

        destruct virtueXother_bound as [N [virtue_generator virtue_gen_spec] ].
        pose (newThreadPerm v :=
                     (computeMap
                        (DMS.DryMachine.ThreadPool.getThreadR cnti).1
                        v.1,
                     computeMap (DMS.DryMachine.ThreadPool.getThreadR cnti).2
                                v.2)).
        pose (virtueLP (ov: PTree.t (Z -> option permission) *
                                 PTree.t (Z -> option permission)) :=
                ((fun _ :Z => @None permission, ov.1),(fun _ :Z => @None permission, ov.2))).
        pose( tp'0 v:=
                   DMS.DryMachine.ThreadPool.updThread cnti
                     (Kresume c Vundef) (newThreadPerm v)).
        pose (tp''0 v:=
                DMS.DryMachine.ThreadPool.updLockSet (tp'0 v.1)
                     (b, Ptrofs.intval ofs) (virtueLP v.2)).
        exists N.
        exists (fun n => (nil,
                  tp''0 (virtue_generator n),
                  m')).
        move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
        move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
        inversion Htstep;
          match goal with
          | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                 H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
            rewrite H in H'; inversion H'; subst c
          end; try congruence;
          try (match goal with
               | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                      H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                 rewrite H in H'; inversion H'
               end; simpl in *; try subst);
          try solve[rewrite Hone_zero in Hload; inversion Hload].
        unfold tp''0, tp'0.
        assert (H: bounded_maps.sub_map virtueThread.1 (getMaxPerm m).2 /\
                    bounded_maps.sub_map virtueThread.2 (getMaxPerm m).2).
        { auto. }
        assert (H': bounded_maps.sub_map virtueLP0.1.2 (getMaxPerm m).2 /\
                    bounded_maps.sub_map virtueLP0.2.2 (getMaxPerm m).2).
        { move: HboundedLP => [] A [] B //. }
        assert (HH: (bounded_maps.sub_map (virtueThread,(virtueLP0.1.2, virtueLP0.2.2)).1.1 (getMaxPerm m).2 /\
                    bounded_maps.sub_map (virtueThread,(virtueLP0.1.2, virtueLP0.2.2)).1.2 (getMaxPerm m).2) /\
                    (bounded_maps.sub_map (virtueThread,(virtueLP0.1.2, virtueLP0.2.2)).2.1 (getMaxPerm m).2 /\
                     bounded_maps.sub_map (virtueThread,(virtueLP0.1.2, virtueLP0.2.2)).2.2 (getMaxPerm m).2)).
        { split; auto. }
        move virtue_gen_spec at bottom.
        move: HH => /virtue_gen_spec [] j [] /ltP ineq vg_spec.
        exists j; split; auto.
        rewrite vg_spec.
        destruct x as [[ ? ?] ?]; simpl in *; subst.
        repeat f_equal.
        - rewrite /virtueLP.
          destruct virtueLP0 as [[LP11 LP12][LP21 LP22]]; simpl.
          f_equal.
          move: HboundedLP.
          rewrite /bounded_maps.map_empty_def => /= [] [] -> [] -> _.
          reflexivity.
        - clear -Hstore Hstore'.
          replace Hlt' with Hlt in Hstore by apply proof_irrelevance.
          rewrite Hstore' in Hstore; inversion Hstore.
          auto.
      }

      (** *CREATE cases*)
      destruct (extfunct_eqdec FUN CREATE).
      { (* **CREATE/SPAWN  case*)

        subst.

        (*get a pair of virtues*)
        pose (virtueXvirtue_bound:= konig.finite_product virtue_bound virtue_bound).

        destruct virtueXvirtue_bound as [N [virtue_generator virtue_gen_spec] ].
        pose (threadPerm' virtue1 := (computeMap
                       (DMS.DryMachine.ThreadPool.getThreadR cnti).1
                       virtue1.1,
                    computeMap
                      (DMS.DryMachine.ThreadPool.getThreadR cnti).2
                      virtue1.2)).
        pose (newThreadPerm virtue2 :=
                     (computeMap empty_map virtue2.1,
                      computeMap empty_map virtue2.2)).
        pose (tp_upd0 v:=
                  DMS.DryMachine.ThreadPool.updThread cnti
                                                      (Kresume c Vundef) (threadPerm' v)).
        pose (arg:= match ARGS' with
                    | arg::_ => arg
                    | _ => Vundef
             end ).
        pose (tp'0 v :=
                  DMS.DryMachine.ThreadPool.addThread (tp_upd0 v.1)
                    (Vptr b ofs) arg (newThreadPerm v.2)).
        exists N.
        exists (fun n => (nil,
                  tp'0 (virtue_generator n),
                  m)).
        move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
        move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
        inversion Htstep;
          match goal with
          | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                 H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
            rewrite H in H'; inversion H'; subst c
          end; try congruence;
(*          try (match goal with
               | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                      H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                 rewrite H in H'; inversion H'
               end; simpl in *; try subst);
 *)
          try solve[rewrite Hone_zero in Hload; inversion Hload].
        unfold tp'0, tp_upd0. subst.
        rewrite AtExt in Hat_external. inv Hat_external.
        assert (H: bounded_maps.sub_map virtue1.1 (getMaxPerm x.2).2 /\
                    bounded_maps.sub_map virtue1.2 (getMaxPerm x.2).2).
        { auto. }
        assert (H': bounded_maps.sub_map virtue2.1 (getMaxPerm x.2).2 /\
                    bounded_maps.sub_map virtue2.2 (getMaxPerm x.2).2).
        { auto.  }
        assert (HH: (bounded_maps.sub_map (virtue1,virtue2).1.1 (getMaxPerm x.2).2 /\
                    bounded_maps.sub_map (virtue1,virtue2).1.2 (getMaxPerm x.2).2) /\
                    (bounded_maps.sub_map (virtue1,virtue2).2.1 (getMaxPerm x.2).2 /\
                     bounded_maps.sub_map (virtue1,virtue2).2.2 (getMaxPerm x.2).2)).
        { split; auto. } clear H H'.
        move virtue_gen_spec at bottom.
        move: HH => /virtue_gen_spec [] j [] /ltP ineq vg_spec.
        exists j; split; auto.
        rewrite vg_spec.
        destruct x as [[ ? ?] ?]; simpl in *; subst.
        repeat f_equal.

      }

       (** *CREATE cases*)
      destruct (extfunct_eqdec FUN CREATE).
      { (* **CREATE/SPAWN  case*)

        subst.

        (*get a pair of virtues*)
        pose (virtueXvirtue_bound:= konig.finite_product virtue_bound virtue_bound).

        destruct virtueXvirtue_bound as [N [virtue_generator virtue_gen_spec] ].
        pose (threadPerm' virtue1 := (computeMap
                       (DMS.DryMachine.ThreadPool.getThreadR cnti).1
                       virtue1.1,
                    computeMap
                      (DMS.DryMachine.ThreadPool.getThreadR cnti).2
                      virtue1.2)).
        pose (newThreadPerm virtue2 :=
                     (computeMap empty_map virtue2.1,
                      computeMap empty_map virtue2.2)).
        pose (tp_upd0 v:=
                  DMS.DryMachine.ThreadPool.updThread cnti
                                                      (Kresume c Vundef) (threadPerm' v)).
        pose (arg:= match ARGS' with
                    | arg::_ => arg
                    | _ => Vundef
             end ).
        pose (tp'0 v :=
                  DMS.DryMachine.ThreadPool.addThread (tp_upd0 v.1)
                    (Vptr b ofs) arg (newThreadPerm v.2)).
        exists N.
        exists (fun n => (nil,
                  tp'0 (virtue_generator n),
                  m)).
        move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
        move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
        inversion Htstep;
          match goal with
          | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                 H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
            rewrite H in H'; inversion H'; subst c
          end; subst;
          try (match goal with
               | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                      H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                 rewrite H in H'; inversion H'
               end; simpl in *; try subst);
          try solve[rewrite Hone_zero in Hload; inversion Hload].
        unfold tp'0, tp_upd0.
        assert (H: bounded_maps.sub_map virtue1.1 (getMaxPerm x.2).2 /\
                    bounded_maps.sub_map virtue1.2 (getMaxPerm x.2).2).
        { auto. }
        assert (H': bounded_maps.sub_map virtue2.1 (getMaxPerm x.2).2 /\
                    bounded_maps.sub_map virtue2.2 (getMaxPerm x.2).2).
        { auto.  }
        assert (HH: (bounded_maps.sub_map (virtue1,virtue2).1.1 (getMaxPerm x.2).2 /\
                    bounded_maps.sub_map (virtue1,virtue2).1.2 (getMaxPerm x.2).2) /\
                    (bounded_maps.sub_map (virtue1,virtue2).2.1 (getMaxPerm x.2).2 /\
                     bounded_maps.sub_map (virtue1,virtue2).2.2 (getMaxPerm x.2).2)).
        { split; auto. } clear H H'.
        move virtue_gen_spec at bottom.
        move: HH => /virtue_gen_spec [] j [] /ltP ineq vg_spec.
        exists j; split; auto.
        rewrite vg_spec.
        destruct x as [[ ? ?] ?]; simpl in *; subst.
        repeat f_equal.

      }


       (** *FREELOCK cases*)
      destruct (extfunct_eqdec FUN FREE_LOCK).
      { (* **FREE LOCK  case*)

        subst.

        destruct (bounded_maps.finite_bounded_nat_func_simpl LKSIZE_nat )
          as [N [virtue_generator virtue_gen_spec] ].

        (*get a pair of virtues*)
        pose (pmap_tid'0 pd:=
                (setPermBlock_var pd b (Ptrofs.intval ofs)
                      (DMS.DryMachine.ThreadPool.getThreadR cnti).1
                      LKSIZE_nat,
                    setPermBlock None b (Ptrofs.intval ofs)
                      (DMS.DryMachine.ThreadPool.getThreadR cnti).2
                      LKSIZE_nat)).
        pose (tp'0 pd:=
                DMS.DryMachine.ThreadPool.updThread cnti
                                                    (Kresume c Vundef) (pmap_tid'0 pd)).
        pose (tp''0 pd:=
                    DMS.DryMachine.ThreadPool.remLockSet (tp'0 pd)
                      (b, Ptrofs.intval ofs)).
        exists N.
        exists (fun n => (nil,
                  tp''0 (virtue_generator n),
                  m)).
        move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
        move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
        inversion Htstep;
          match goal with
          | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                 H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
            rewrite H in H'; inversion H'; subst c
          end; try congruence;
          try (match goal with
               | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                      H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
                 rewrite H in H'; inversion H'
               end; simpl in *; try subst);
          try solve[rewrite Hone_zero in Hload; inversion Hload].
        unfold tp''0, tp'0.
        assert (H: bounded_maps.bounded_nat_func' pdata LKSIZE_nat).
        { auto. }

        move virtue_gen_spec at bottom.
        move: H => /virtue_gen_spec [] j [] /ltP ineq vg_spec.
        exists j; split; auto.
        rewrite vg_spec; clear vg_spec.
        destruct x as [[ ? ?] ?]; simpl in *; subst.
        repeat f_equal.
        unfold pmap_tid'0; destruct pmap_tid'; simpl in *; subst.
        auto.

      }

      (*That's it folks it can't be anything else*)
      exists 0%nat, (fun _ => (tr, dm, m)).
      move=> x y [] [] PEEK VAL [] y' /(schedule_not_halted y i PEEK).
      move => /(is_syncStep y PEEK VAL) [] TR [] _ [] SKIP [] ev Htstep.
      inversion Htstep;
        match goal with
            | [ H: DMS.DTP.getThreadC ?cnt1 = Kblocked c ,
                   H': DMS.DTP.getThreadC ?cnt2 = _  |- _ ] =>
              rewrite H in H'; inversion H'; subst c
        end; subst;
        try (match goal with
             | [ H: at_external ?SEM _ ?c _ = Some (_, _),
                    H' : at_external ?SEM _ ?c _ = Some (_, _ ) |- _ ] =>
               rewrite H in H'; inversion H'
             end; simpl in *; try subst);
      try (match goal with
      | [ H: ?FUN_NAME <> ?FUN_NAME |- _ ] =>
        exfalso; apply H; reflexivity
      end).


    Qed.

    Lemma finite_branching_fixed_thread: forall ds ge i,
          safety.finite_on_x
            (@safety.possible_image
               DMS.DryConc.new_state
               DMS.DryConc.Sch
               (fun x y x' => exists y', (DMS.DryConc.new_step ge x y x' y'))
               (fun st y => SCH.schedPeek y = Some i /\ DMS.DryConc.new_valid_bound st y)
               ds).
    Proof.
      move=> [] [] tr dm m  prog i.
      rewrite /safety.finite_on_x /safety.possible_image /=.
      rewrite /DMS.DryConc.new_step /DMS.DryConc.new_valid_bound /=.
      rewrite /DMS.DryConc.valid /DMS.DryConc.correct_schedule.
      rewrite /DMS.DryConc.unique_Krun /DMS.DryMachine.ThreadPool.containsThread.
      rewrite /DMS.DryConc.mk_ostate /=.

      (*Preliminary lemmas*)
      (*No lemmas here enymore*)

      (*First check if it's mem_compatible. If not, it can't step! *)
      pose (mem_compat_dec:=
              DMS.DryMachine.mem_compatible dm m).
      destruct (Classical_Prop.classic mem_compat_dec) as [Hcmpt|NHcmpt].
      2: (*it can't step! *)
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
      }

      (*Second, check the thread is contained *)
      destruct (i < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N eqn:cnti'.
      2:{
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
      }

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
            move: steps'.
            replace Hcmpt0 with Hcmpt by apply proof_irrelevance;
              replace Htid with cnti by apply proof_irrelevance .
            move => steps'.
            destruct (Clight_bounds.CLight_Deterministic steps steps').
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
        move: (finite_branching_sync (tr, dm, m) prog i cnti c Hblocked) => [] n [] f /= HH.
        exists n , f.
        move=> x y [] [] PEEK [] sch_ok bounded_mem ESTEP.
        eapply HH; repeat split; eauto.
      }

      { (*Kresume*)
        (*then it must be after external*)
        destruct (after_external DMS.DryMachine.ThreadPool.SEM.Sem prog None c) eqn:AftEx.
        2:{
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
        }


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
        destruct (initial_core DMS.DryMachine.ThreadPool.SEM.Sem (SCH.TID.tid2nat i) prog m v [:: v0]) as [[? ?]|] eqn:Hinit.
        2:{
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
        }

        exists 1%nat.
        exists (fun _ => (tr,
                  @DMS.DryMachine.ThreadPool.updThreadC i dm cnti (Krun c),
                  machine_semantics.option_proj m o)).
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
    Qed.




  Lemma finite_branching: forall ds ge,
          safety.finite_on_x
            (@safety.possible_image
               DMS.DryConc.new_state
               DMS.DryConc.Sch
               (fun x y x' => exists y', (DMS.DryConc.new_step ge x y x' y'))
               DMS.DryConc.new_valid_bound ds).
  Proof.
    move=> [] [] tr dm m  prog.
    rewrite /safety.finite_on_x /safety.possible_image /=.
    rewrite /DMS.DryConc.new_step /DMS.DryConc.new_valid_bound /=.
    rewrite /DMS.DryConc.valid /DMS.DryConc.correct_schedule.
    rewrite /DMS.DryConc.unique_Krun /DMS.DryMachine.ThreadPool.containsThread.
    rewrite /DMS.DryConc.mk_ostate.
    (*First check if it's mem_compatible. If not, it can't step! *)
    pose (mem_compat_dec:=
              DMS.DryMachine.mem_compatible dm m).
    destruct (Classical_Prop.classic mem_compat_dec) as [Hcmpt|NHcmpt].
    2: (*it can't step! *)
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
    }


      (*Introduce a bound to do induction*)
      cut ( forall M:nat,
            exists (n : nat) (f : nat -> DMS.DryConc.new_state),
    forall (x : DMS.DryConc.new_state) (y : SCH.schedule),
    (match SCH.schedPeek y with
    | Some i =>
      (i < M) /\
        forall (j : DMS.DryMachine.ThreadPool.TID.tid)
          (cnti : (j < pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N)
          (q : DMS.DryMachine.ThreadPool.SEM.C),
        DMS.DryMachine.ThreadPool.getThreadC cnti = Krun q ->
        ~ DMS.DryMachine.threadHalted cnti -> SCH.TID.eq_tid_dec i j
    | None => True
    end /\ DMS.DryConc.bounded_mem m) /\
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
        2:{ (*Machine is halted: end of schedule*)
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
        }

        destruct (t <  pos.n (DMS.DryMachine.ThreadPool.num_threads dm))%N eqn: within_bound.
        - move => [] [] A A' B.
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
          + move => []  [] [] WRONG sch_ok bound_mem.
            inversion WRONG.
          + move => []  [] _ bounded_mem [] y' STEP.
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
           2:{
             move=> HH (*[] _ [] y' STEP *).
             move : (other_threads st' U).
             rewrite /safety.possible_image /=.
             rewrite PEEK => /(_ HH) [] i [] ineq f_eq.
             exists i; split.
             - ssromega.
             - rewrite ineq; simpl; auto.
           }

           (*Check if t (active thread) is ==M*)
           destruct (NatTID.eq_tid_dec t M).
          + (*t = M*)
            subst.
            move=> [] [] [] ineq VAL bounded_mem [] y' STEP .
            move : (threadM st' U).
            rewrite /safety.possible_image
                    /DMS.DryConc.new_valid_bound /DMS.DryConc.valid /DMS.DryConc.correct_schedule /=.
            rewrite PEEK => /(_ ltac:(split; eauto)) [] i [] ineq' f_eq.
            exists (N + i)%nat; split.
            * ssromega.
            * assert ( is_false: (N + i < N)%N = false).
              { clear. apply /negb_true_iff /eq_true_not_negb.
                intros HH. ssromega. }
              rewrite is_false.
              replace (N + i - N)%nat with i; auto.
              ssromega.
          + (* t < M*)
            move=> [] [] [] ineq VAL bounded_mem [] y' STEP .
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
                    /DMS.DryConc.new_valid_bound /DMS.DryConc.valid /DMS.DryConc.correct_schedule /=.
            rewrite PEEK => /(_ ltac:(eauto)) [] i [] ineq'' f_eq.
            exists i%nat; split.
            * ssromega.
            * rewrite ineq''; auto.
      }
  Qed.
 *)


  End FiniteBranching.

