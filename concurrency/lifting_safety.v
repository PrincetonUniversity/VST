From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.

Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

(* The concurrent machinery*)
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_machine. Import Concur.
Require Import concurrency.scheduler.

Require Import concurrency.lifting.

Require Import sepcomp.event_semantics.

(** The X86 DryConc Machine*)
Require Import concurrency.dry_context.
Require Import concurrency.x86_context.


(** The Clight DryConc Machine*)
Require Import concurrency.DryMachineSourceCore.

Require Import concurrency.machine_simulation. Import machine_simulation.


Require Import concurrency.HybridMachine_simulation_proof.


Module lifting_safety.
  Import DMS.
  Import X86Machines.

  Notation semS := (DMS.SEM.Sem).
  Notation semT := (SEM.Sem).

  (*These are variables spilling from lifting.v*)
  Notation GS := (DMS.SEM.G).
  Notation GT := (SEM.G).
  Context (gT : GT)( gS : GS)
          (p : Clight.program) (tp : Asm.program).
  Hypothesis compiled : Compiler.simpl_transf_clight_program p = Errors.OK tp.

  (*This is the real context*)
  Context (psrc : option DMS.DryMachine.ThreadPool.RES.res)
         (ptgt : option DryMachine.ThreadPool.RES.res) (sch : SC.Sch).
  Definition the_simulation:=
    lifting.concur_sim p tp compiled
                       Values.Vundef psrc ptgt sch.
  
  
  Lemma safety_preservation'':
        forall Sg Tg tr Sds Sm Tds Tm cd
          (MATCH: exists j, (MSmatch_states Values.Vundef the_simulation) cd j Sds Sm Tds Tm),
          (forall sch, DMS.DryConc.new_valid (tr, Sds, Sm) sch ->
                  DMS.DryConc.explicit_safety Sg sch Sds Sm) ->
          (forall sch, DryConc.valid (sch, tr, Tds) ->
                  DryConc.stutter_stepN_safety
                    (core_ord:=MSorder Values.Vundef the_simulation) Tg cd sch Tds Tm).
  Proof.
    move => main psrc ptgt U Sg Tg.
    cofix CIH.
    intros.
    assert (H':=H).
    specialize (H sch).
    move: MATCH => [] j MATCH.
    assert (equivalid:
               forall cd j Sm Tm tr Sds Tds,
                 (MSmatch_states Values.Vundef the_simulation) cd j Sds Sm Tds Tm ->
                 forall sch,
                   DMS.DryConc.valid (sch, tr, Sds)  <->
                   DryConc.valid (sch, tr, Tds) ).
    { rewrite /DMS.DryConc.valid
              /DMS.DryConc.correct_schedule
              /DMS.DryConc.unique_Krun
              /mySchedule.schedPeek
              /DryConc.valid
              /DryConc.correct_schedule
              /DryConc.unique_Krun
              /mySchedule.schedPeek /=.

      move => ? ? ? ? ? Sds' Tds' MATCH' sch.
      destruct (List.hd_error sch); try solve[split; auto].
      split.
      - move => H1  j0 cntj0 q KRUN not_halted.
        (*eapply H1.*)
        (*pose (same_running Tg Sg main p U cd j Sds' Sm Tds' Tm).*)
        pose ( machine_semantics.runing_thread (new_DMachineSem sch None)).
        unfold new_DMachineSem  in P; simpl in P.
        unfold DMS.DryConc.unique_Krun in P.
        eapply P.
        
        
        eapply (same_running) in KRUN; eauto.
      - move => H1  j0 cntj0 q KRUN not_halted.

        (*eapply H1.*)
        (*pose (same_running Tg Sg main p U cd j Sds' Sm Tds' Tm).*)
        pose ( machine_semantics.runing_thread (new_DMachineSem sch psrc)).
        unfold new_DMachineSem  in P; simpl in P.
        unfold DryConc.unique_Krun in P.
        eapply (same_running) in KRUN; eauto.
    }

    move: (MATCH) => /equivalid /= AA.
    move: (AA tr sch) => [A B].
    assert (HH:DryConc.new_valid (tr, Sds, Sm) sch).
    { (* split.
      - apply: B. auto.
      - simpl; assumption. *)
      apply: B; auto.
    }
    apply H in HH.
    move: MATCH.
    inversion HH; clear HH.
    (*Halted case*)
    - {
      simpl in *; subst.
      econstructor.
      move: MATCH H1 => /halt_axiom /= HHH /(halted_trace _ nil nil Sds) AAA.
      destruct (DryConc.halted (sch, nil ,Sds)) eqn:BBB; try solve [inversion AAA].
      move: BBB=> /HHH [] j' [] v2 [] inv Halt.
      rewrite Halt=> //.
      Guarded.
      }

    - (*Internal StepN case*)
      { simpl in H2. pose (note2:=5). simpl in *; subst.
        assert (my_core_diagram:= Machine_sim.thread_diagram
                           _ _ _ _ _ _ _ _
                           (concur_sim Tg Sg main psrc ptgt U)).
        simpl in my_core_diagram.
        intros MATCH.
        eapply my_core_diagram (*with (st1':= (Tds))(m1':=Tm)*) in MATCH; eauto.
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
                (Machine.DryConc.new_MachineSemantics U p) Tg n sch Tds
                Tm st2' m2' ->
                coinductive_safety.stepN
                  SC.Sch (Machine.DryMachine.ThreadPool.t * mem)
                  (fun (U0 : SC.Sch) (stm stm' : Machine.DryMachine.ThreadPool.t * mem)
                   =>
                     @Machine.DryConc.internal_step Tg U0 (fst stm) (snd stm)
                                                   (fst stm') (snd stm'))
                  sch (Tds, Tm) (st2', m2') n.
            Proof.
              move=> Tg n.
              induction n; simpl.
              - move=>  sch Tds Tm st2' m2' U p HH; inversion HH; subst.
                constructor 1; auto.
              - move=>  sch Tds Tm st2' m2' U p [] c2 [] m2 [] step PAST.
                econstructor 2; eauto.
                simpl. auto.
            Qed.

            eapply thread_stepN_stepN; eauto.
          + simpl. intros.
            eapply CIH with (Sds:=fst y') (Sm:=snd y'); eauto.
(*            * a dmit. (* By steping! *) *)
(*            * destruct H3; auto. (* By steping! *)*)
            * intros. destruct y' as [a b]; eapply H2.
              auto.
(*            * simpl in *.
              destruct H3; eauto. *)

        -  (*Maybe stutter.... depends on n*)
          destruct n.
          + (*Stutter case*)
            inversion stepN; subst.
            apply coinductive_safety.stutter with (cd':=cd'); auto.
            apply CIH with (tr:=tr)(Sds:= (fst y') )(Sm:=(snd y')).
(*            * a dmit. (*by stepping*) *)
(*            * auto. *)
            * exists mu'; eassumption.
            * destruct y' as [a b]; apply H2; auto.
            * assumption.
          + (*Fake stutter case*)
            apply (coinductive_safety.internal_safetyN_stut) with (cd':= cd')(y':=(st2',m2'))(n:=n).
            * eapply thread_stepN_stepN; eauto.
            *  {simpl. intros.
                eapply CIH with (Sds:=fst y') (Sm:=snd y'). Guarded.
                - exists mu'; assumption.
                - destruct y' as [a b]; eapply H2.
               - assumption.
 }
      }
    - (*External step case *)
      assert (my_machine_diagram:= Machine_sim.machine_diagram
                           _ _ _ _ _ _ _ _
                           (concur_sim Tg Sg main psrc ptgt U)).
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

               Unshelve.
               auto.
  Qed.

  Lemma safety_preservation': forall main psrc ptgt U Sg Tg tr Sds Sm Tds Tm
                                (MATCH: exists cd j, (match_st Tg Sg main psrc ptgt U) cd j Sds Sm Tds Tm),
      (forall sch, DryConc.valid (sch, tr, Sds) ->
              DryConc.explicit_safety Sg sch Sds Sm) ->
      (forall sch, Machine.DryConc.valid (sch, tr, Tds) ->
              Machine.DryConc.explicit_safety Tg sch Tds Tm).
  Proof.
    move=> main psrc ptgt U Sg Tg tr Sds Sm Tds Tm  [] cd  [] mu MATCH HH sch VAL.
    apply @coinductive_safety.safety_stutter_stepN_equiv
    with (core_ord:=core_ord Tg Sg main psrc ptgt U); auto.
    + apply (core_ord_wf Tg Sg main psrc ptgt U).
    (* + split; auto; simpl. *)
    + exists cd.
      apply safety_preservation'' with (tr:=tr)(Sds:=Sds)(Sm:=Sm); try exists mu; assumption.
  Qed.

  Lemma safety_preservation: forall main psrc ptgt U Sg Tg Sds Sm Tds Tm
                               (MATCH: exists cd j, (match_st Tg Sg main psrc ptgt U) cd j Sds Sm Tds Tm),
      (forall sch, DryConc.valid (sch, nil, Sds) ->
              DryConc.safe_new_step Sg (sch, nil, Sds) Sm) ->
      (forall sch, Machine.DryConc.valid (sch, nil, Tds) ->
              Machine.DryConc.safe_new_step Tg (sch, nil, Tds) Tm).
  Proof.
    intros.
    eapply Machine.DryConc.safety_equivalence2; auto.
    intros.
    eapply safety_preservation' with (tr:=nil); eauto.
    intros.
    eapply DryConc.safety_equivalence2; auto.
  Qed.

End lifting_safety.
