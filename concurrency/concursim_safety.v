From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.

Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

(* The concurrent machinery*)
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.HybridMachine. Import Concur.
Require Import VST.concurrency.scheduler.

(* Require Import VST.concurrency.lifting. *)

Require Import VST.sepcomp.event_semantics.

(** The X86 DryConc Machine*)
Require Import VST.concurrency.dry_context.
Require Import VST.concurrency.x86_context.


(** The Clight DryConc Machine*)
Require Import VST.concurrency.DryMachineSourceCore.

Require Import VST.concurrency.machine_simulation. Import machine_simulation.


(*Require Import VST.concurrency.HybridMachine_simulation_proof.*)

Set Bullet Behavior "Strict Subproofs".

Module concure_simulation_safety (SMachine TMachine: MachinesSig).
  Module SDryConc:= SMachine.DryConc.
  Module TDryConc:= TMachine.DryConc.

  Section Simulation2Safety.
  Variable Gs Gt: Type.
  Variable ges: SMachine.DryMachine.ThreadPool.SEM.G.
  Variable get: TMachine.DryMachine.ThreadPool.SEM.G.
  Variable sch: DMS.SC.Sch.
  Variable psrc: option SMachine.DryMachine.ThreadPool.RES.res.
  Variable ptgt: option TMachine.DryMachine.ThreadPool.RES.res.
  Variable start_block : Values.val.
  Hypothesis the_simulation:
    Machine_sim
      (SDryConc.new_MachineSemantics sch psrc)
      (TDryConc.new_MachineSemantics sch ptgt)
      ges get start_block.

  Lemma safety_preservation'':
        forall  tr Sds Sm Tds Tm cd
          (MATCH: exists j, (MSmatch_states start_block the_simulation) cd j Sds Sm Tds Tm),
          (forall sch, SMachine.DryConc.new_valid (tr, Sds, Sm) sch ->
                  SMachine.DryConc.explicit_safety ges sch Sds Sm) ->
          (forall sch, TMachine.DryConc.valid (sch, tr, Tds) ->
                  TMachine.DryConc.stutter_stepN_safety
                    (core_ord:=MSorder start_block the_simulation) get cd sch Tds Tm).
  Proof.
    cofix CIH.
    intros.
    assert (H':=H).
    specialize (H sch0).
    move: MATCH => [] j MATCH.
    assert (equivalid:
               forall cd j Sm Tm tr Sds Tds,
                 (MSmatch_states start_block the_simulation) cd j Sds Sm Tds Tm ->
                 forall sch,
                   SMachine.DryConc.valid (sch, tr, Sds)  <->
                   TMachine.DryConc.valid (sch, tr, Tds) ).
    { unfold  SMachine.DryConc.valid,
              SMachine.DryConc.correct_schedule,
              SMachine.DryConc.unique_Krun,
              mySchedule.schedPeek,
              TMachine.DryConc.valid,
              TMachine.DryConc.correct_schedule,
              TMachine.DryConc.unique_Krun,
              mySchedule.schedPeek; simpl; eauto.

      intros ? ? ? ? tr0 Sds' Tds' MATCH' sch'.
      destruct (List.hd_error sch'); try solve[split; auto].
      split.
      - intros H1 j0' cntj0' q KRUN not_halted.
        eapply the_simulation in KRUN; eauto.
        
      - move => H1  j0' cntj0' q KRUN not_halted.
        eapply the_simulation in KRUN; eauto.
    }

    move: (MATCH) => /equivalid /= AA.
    move: (AA tr sch0) => [A B].
    assert (HH:SMachine.DryConc.new_valid (tr, Sds, Sm) sch0).
    { apply B; auto.
    }
    apply H in HH.
    move: MATCH.
    inversion HH; clear HH.
    (*Halted case*)
    - {
        simpl in *; subst.
        econstructor.
        simpl.
        unfold SMachine.DryConc.halted in H1;
          unfold TMachine.DryConc.halted; simpl in *.
        destruct (SCH.schedPeek sch0); eauto.
      Guarded.
      }

    - (*Internal StepN case*)
      { simpl in H2. simpl in *; subst.
        assert (my_core_diagram:= MSthread_diagram start_block the_simulation).
        simpl in my_core_diagram.
        intros MATCH.
        destruct y'.
        eapply my_core_diagram in MATCH; eauto.
        clear my_core_diagram.
        move: MATCH => [] st2' [] m2' [] cd' [] mu' [] MATCH' [step_plus | [] [] n stepN data_step ].
        (*Internal step Plus*)
        - unfold machine_semantics_lemmas.thread_step_plus in step_plus.
          destruct step_plus as [n step_plus].
          apply (coinductive_safety.internal_safetyN_stut) with (cd':= cd')(y':=(st2',m2'))(n:=n).
          +
            Lemma thread_stepN_stepN:
              forall Tg n sch Tds Tm st2' m2' U p,
               machine_semantics_lemmas.thread_stepN
                (TMachine.DryConc.new_MachineSemantics U p) Tg n sch Tds
                Tm st2' m2' ->
                coinductive_safety.stepN
                  DMS.SC.Sch (TMachine.DryMachine.ThreadPool.t * mem)
                  (fun U0 (stm stm' : TMachine.DryMachine.ThreadPool.t * mem)
                   =>
                     @TMachine.DryConc.internal_step Tg U0 (fst stm) (snd stm)
                                                   (fst stm') (snd stm'))
                  sch (Tds, Tm) (st2', m2') n.
            Proof.
              move=> Tg n.
              induction n; simpl.
              - move=>  sch' Tds Tm st2' m2' U p HH; inversion HH; subst.
                constructor 1; auto.
              - move=>  sch' Tds Tm st2' m2' U p [] c2 [] m2 [] step PAST.
                econstructor 2; eauto.
                simpl. auto.
            Qed.
            eapply thread_stepN_stepN; eauto.
          + simpl. intros.
            eapply CIH with (Sds:=t) (Sm:=m); eauto.
            Guarded.
            (*
(*            * a dmit. (* By steping! *) *)
(*            * destruct H3; auto. (* By steping! *)*)
            * 

              intros. destruct y' as [a b]; eapply H2.
              auto.
(*            * simpl in *.
              destruct H3; eauto. *)*)

        -  (*Maybe stutter.... depends on n*)
          destruct n.
          + (*Stutter case*)
            inversion stepN; subst.
            apply coinductive_safety.stutter with (cd':=cd'); auto.
            apply CIH with (tr:=tr)(Sds:= t )(Sm:=m); eauto.
            (*
(*            * a dmit. (*by stepping*) *)
(*            * auto. *)
            * exists mu'; eassumption.
            * destruct y' as [a b]; apply H2; auto.
            * assumption. *)
          + (*Fake stutter case*)
            apply (coinductive_safety.internal_safetyN_stut) with (cd':= cd')(y':=(st2',m2'))(n:=n).
            * eapply thread_stepN_stepN; eauto.
            *  {simpl. intros.
                eapply CIH with (Sds:=t) (Sm:=m). Guarded.
                - exists mu'; assumption.
                - eapply H2.
               - assumption.
 }
      }
    - 
      assert (my_machine_diagram:= MSmachine_diagram start_block the_simulation).
      simpl in my_machine_diagram.
        intros MATCH.
        eapply my_machine_diagram with (st1':= fst y')(m1':=snd y') in MATCH; eauto.
        + clear my_machine_diagram.
          move: MATCH => [] st2' [] m2' [] cd' [] mu' [] MATCH' step.
          apply coinductive_safety.external_safetyN_stut with (cd':=cd')(x':=x')(y':= (st2', m2')).
          * apply step.
          * intros; eapply CIH with (tr:=tr)(Sds:= (fst y') )(Sm:=(snd y')).
            -- exists mu'; exact MATCH'.
            -- destruct y' as [a b]; eapply H2.
            -- assumption.
               Guarded.

  Qed.

    Lemma safety_preservation':
      forall tr Sds Sm Tds Tm cd
        (MATCH: exists j, (MSmatch_states start_block the_simulation) cd j Sds Sm Tds Tm),
      (forall sch, SMachine.DryConc.valid (sch, tr, Sds) ->
              SMachine.DryConc.explicit_safety ges sch Sds Sm) ->
      (forall sch, TMachine.DryConc.valid (sch, tr, Tds) ->
              TMachine.DryConc.explicit_safety get sch Tds Tm).
  Proof.
    move=> tr Sds Sm Tds Tm  cd [] j MATCH HH sch' VAL.
    apply @coinductive_safety.safety_stutter_stepN_equiv
    with (core_ord:=MSorder start_block the_simulation); auto.
    + eapply MSord_wf; eauto.
    + exists cd.
      apply safety_preservation'' with (tr:=tr)(Sds:=Sds)(Sm:=Sm); try exists j; assumption.
      
  Qed.

  Lemma safety_preservation:
    forall Sds Sm Tds Tm cd j
      (MATCH: (MSmatch_states start_block the_simulation) cd j Sds Sm Tds Tm),
      (forall sch, SMachine.DryConc.valid (sch, nil, Sds) ->
              SMachine.DryConc.safe_new_step ges (sch, nil, Sds) Sm) ->
      (forall sch, TMachine.DryConc.valid (sch, nil, Tds) ->
              TMachine.DryConc.safe_new_step get (sch, nil, Tds) Tm).
  Proof.
    intros.
    eapply TMachine.DryConc.safety_equivalence2; auto.
    intros.
    eapply safety_preservation' with (tr:=nil); eauto.
    intros.
    eapply SMachine.DryConc.safety_equivalence2; auto.
  Qed.

  Definition The_init:= (core_initial
                           _ _ _ _ _
                           the_simulation).

  Lemma initial_safety_preservation:
     forall (c1 : SMachine.DryMachine.ThreadPool.t) (vals1 : seq Values.val) 
         (m1 : mem) (vals2 : seq Values.val) (m2 : mem) (j : Values.Val.meminj),
       machine_semantics.initial_machine (SDryConc.new_MachineSemantics sch psrc) ges
         m1 start_block vals1 = Some (c1, None) ->
       Mem.inject j m1 m2 ->
       List.Forall2 (val_inject j) vals1 vals2 ->
       smthng_about_globals ges j ->
       (forall sch, SMachine.DryConc.valid (sch, nil, c1) ->
               SMachine.DryConc.safe_new_step ges (sch, nil, c1) m1) ->
       exists (c2 : TMachine.DryMachine.ThreadPool.t),
         machine_semantics.initial_machine (TDryConc.new_MachineSemantics sch ptgt) get
                                           m2 start_block vals2 = Some (c2, None) /\
         (forall sch, TMachine.DryConc.valid (sch, nil, c2) ->
              TMachine.DryConc.safe_new_step get (sch, nil, c2) m2).
  Proof.
    intros.
    eapply The_init in H; eauto.
    destruct H as (cd & c2 & INIT_ok & MATCH).
    eexists; split; eauto.
    eapply safety_preservation; eauto.
  Qed.
  End Simulation2Safety.
    
End concure_simulation_safety.
