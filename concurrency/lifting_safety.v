From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.

Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

(* The concurrent machinery*)
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_machine. Import Concur.
Require Import concurrency.scheduler.

Require Import concurrency.lifting.

(* We lift to a whole-program simulation on the dry concurrency machine *)
Require Import sepcomp.wholeprog_simulations. Import Wholeprog_sim.

Require Import sepcomp.event_semantics.

(** The X86 DryConc Machine*)
Require Import concurrency.dry_context.

(** The Clight DryConc Machine*)
Require Import concurrency.DryMachineSource.

Require Import concurrency.machine_simulation. Import machine_simulation.


Module lifting_safety (SEMT: Semantics) (Machine: MachinesSig with Module SEM := SEMT).
  Module lftng:= lifting SEMT Machine. Import lftng.
  Module foo:= Machine.

  Definition match_st gT gS main p sch:=
    Machine_sim.match_state
      _ _ _ _ _ _ _ _
      (concur_sim gT gS main p sch).

  Definition running_thread gT gS main p sch:=
    Machine_sim.thread_running
      _ _ _ _ _ _ _ _
      (concur_sim gT gS main p sch).

  Definition halt_axiom gT gS main p sch:=
    Machine_sim.thread_halted
      _ _ _ _ _ _ _ _
      (concur_sim gT gS main p sch).
  Definition core_ord gT gS main p sch:=
    Machine_sim.core_ord
      _ _ _ _ _ _ _ _
      (concur_sim gT gS main p sch).
  Definition core_ord_wf gT gS main p sch:=
    Machine_sim.core_ord_wf
      _ _ _ _ _ _ _ _
      (concur_sim gT gS main p sch).

(*  THE_DRY_MACHINE_SOURCE.dmachine_state
    Machine.DryConc.MachState
 *)
  (* This axiom comes from the new simulation*)
  (*Axiom blah: forall  Tg Sg main p U,
    forall cd j Sm Tm Sds Tds,
      (match_st Tg Sg main p U) cd j Sds Sm Tds Tm ->
      forall sch,
        THE_DRY_MACHINE_SOURCE.DryMachine.valid  (sch, snd (fst Sds), snd Sds) <->
        Machine.DryConc.valid (sch, snd (fst Tds), snd Tds). *)

      Axiom halted_trace: forall U tr tr' st,
          THE_DRY_MACHINE_SOURCE.DryMachine.halted (U, tr, st) ->
          THE_DRY_MACHINE_SOURCE.DryMachine.halted (U, tr', st).
      Axiom halted_trace': forall U tr tr' st,
          Machine.DryConc.halted (U, tr, st) ->
          Machine.DryConc.halted (U, tr', st).

      Axiom determinismN:
        forall U p,
        forall ge sch st2 m2 st2' m2',
        forall n0 : nat,
          machine_semantics_lemmas.thread_stepN
            (Machine.DryConc.new_MachineSemantics U p) ge n0 sch st2 m2 st2' m2' ->
          forall U'0 : mySchedule.schedule,
            Machine.DryConc.valid (U'0, [::], st2) ->
            machine_semantics_lemmas.thread_stepN
              (Machine.DryConc.new_MachineSemantics U p) ge n0 U'0 st2 m2 st2' m2'.

      (*Lemma stepN_safety:
        forall U p ge st2' m2' n,
        forall (condition : forall sch : mySchedule.schedule,
              Machine.DryConc.valid (sch, [::], st2') ->
              Machine.DryConc.explicit_safety ge sch st2' m2'),
        forall (st2 : Machine.DryMachine.ThreadPool.t) 
          (m2 : mem) (sch : mySchedule.schedule),
          machine_semantics_lemmas.thread_stepN
            (Machine.DryConc.new_MachineSemantics U p) ge n sch st2 m2 st2' m2' ->
          forall U' : mySchedule.schedule,
            Machine.DryConc.valid (U', [::], st2) ->
            Machine.DryConc.explicit_safety ge U' st2 m2 .
      Proof.
        (*Make this a separated lemma*)
        induction n.
        - intros ? ? ? ? stepN U' val.
          inversion stepN; subst.
          apply: (condition _ val).
        - intros ? ? ? ? stepN U' val.
          assert (DeterminismN: forall n,
                     machine_semantics_lemmas.thread_stepN
                       (Machine.DryConc.new_MachineSemantics U p) ge n sch st2
                       m2 st2' m2' ->
                     forall U', Machine.DryConc.valid (U', [::], st2) ->
                           machine_semantics_lemmas.thread_stepN
                             (Machine.DryConc.new_MachineSemantics U p) ge n U' st2
                             m2 st2' m2'
                 ).
          apply: determinismN. (*This is true by determinism. *)
          eapply DeterminismN in stepN; eauto.
          inversion stepN. 
          move: H => /= [] m_ [] istep stepN'.
          eapply Machine.DryConc.internal_safety; eauto.
      Qed.
      
      Lemma stepN_safety':
        forall U p ge st2' m2' n,
        forall (st2 : Machine.DryMachine.ThreadPool.t) 
          (m2 : mem) (sch : mySchedule.schedule),
          machine_semantics_lemmas.thread_stepN
            (Machine.DryConc.new_MachineSemantics U p) ge n sch st2 m2 st2' m2' ->
        forall (condition : forall sch : mySchedule.schedule,
              Machine.DryConc.valid (sch, [::], st2') ->
              Machine.DryConc.explicit_safety ge sch st2' m2'),
          forall U' : mySchedule.schedule,
            Machine.DryConc.valid (U', [::], st2) ->
            Machine.DryConc.explicit_safety ge U' st2 m2 .
      Proof. intros. apply: stepN_safety; eauto. Qed.
      *)

      
      (*Lemma safety_equivalence_stutter' {core_data: Type} {core_ord}:
       @well_founded core_data  core_ord ->
       core_data ->
       forall (ge : Machine.DryMachine.ThreadPool.SEM.G)
         (U : mySchedule.schedule) (st : Machine.DryMachine.ThreadPool.t)
         (m : mem),
       (exists cd : core_data,
           @Machine.DryConc.explicit_safety_stutter core_data core_ord ge cd U st m) ->
       Machine.DryConc.explicit_safety ge U st m.
      Proof. Admitted.*)
        
      
  Lemma safety_preservation'': forall main p U Sg Tg tr Sds Sm Tds Tm cd 
      (MATCH: exists j, (match_st Tg Sg main p U) cd j Sds Sm Tds Tm),
      (forall sch, THE_DRY_MACHINE_SOURCE.DryMachine.valid (sch, tr, Sds) ->
              THE_DRY_MACHINE_SOURCE.DryMachine.explicit_safety Sg sch Sds Sm) ->
      (forall sch, Machine.DryConc.valid (sch, tr, Tds) ->
              Machine.DryConc.stutter_stepN_safety ( core_ord:=core_ord  Tg Sg main p U) Tg cd sch Tds Tm).
  Proof.
    move => main p U Sg Tg.
    cofix CIH.
    intros.
    assert (H':=H).
    specialize (H sch).
    move: MATCH => [] j MATCH.
    assert (equivalid: forall  Tg Sg main p U,
               forall cd j Sm Tm tr Sds Tds,
                 (match_st Tg Sg main p U) cd j Sds Sm Tds Tm ->
                 forall sch,
                   THE_DRY_MACHINE_SOURCE.DryMachine.valid (sch, tr, Sds)  <->
                   Machine.DryConc.valid (sch, tr, Tds) ).
    { 
      rewrite /THE_DRY_MACHINE_SOURCE.DryMachine.valid
              /THE_DRY_MACHINE_SOURCE.SCH.schedPeek
              /Machine.DryConc.valid
              /mySchedule.schedPeek /=.
      move => ? ? ? ? ? ? ? ? ? ? ? Tds' /(running_thread) /= -> U''.
            destruct (Machine.DryConc.running_thread (Tds')); intuition.
    }

    move: (MATCH) => /equivalid /= AA.
    move: (AA tr sch) => [A B].
    assert (HH:THE_DRY_MACHINE_SOURCE.DryMachine.valid (sch, tr, Sds)).
    { apply: B.
      apply: H0. }
    apply H in HH.
    move: MATCH.
    inversion HH; clear HH.
    (*Halted case*)
    - {
      simpl in *; subst.
      econstructor.
      move: MATCH H1 => /halt_axiom /= HHH /(halted_trace _ nil nil Sds) AAA.
      destruct (THE_DRY_MACHINE_SOURCE.DryMachine.halted (sch, nil ,Sds)) eqn:BBB; try solve [inversion AAA].
      move: BBB=> /HHH [] j' [] v2 [] inv Halt.
      rewrite Halt=> //.
      rewrite BBB in AAA; inversion AAA.
      Guarded.
      }
      
    - (*Internal StepN case*)
      { simpl in H2. pose (note2:=5). simpl in *; subst.
        assert (my_core_diagram:= Machine_sim.thread_diagram
                           _ _ _ _ _ _ _ _
                           (concur_sim Tg Sg main p U)).
        simpl in my_core_diagram.
        intros MATCH.
        eapply my_core_diagram (*with (st1':= (Tds))(m1':=Tm)*) in MATCH; eauto.
        clear my_core_diagram.
        move: MATCH => [] st2' [] m2' [] cd' [] mu' [] MATCH' [step_plus | [] [] n stepN data_step ].
        (*Internal step Plus*)
        - unfold machine_semantics_lemmas.thread_step_plus in step_plus.
          destruct step_plus as [n step_plus].
          apply (coinductive_safety.internal_safetyN_stut) with (cd':= cd')(y':=(st2',m2'))(n:=n).
          + admit. (* Equate the two different stepN... or redefine one... *)
          + simpl. apply CIH with (Sds:=fst y') (Sm:=snd y').
            * exists mu'; assumption.
            * destruct y' as [a b]; eapply H2.              
        -  (*Maybe stutter.... depends on n*)
          destruct n.
          + (*Stutter case*)
            inversion stepN; subst.
            apply coinductive_safety.stutter with (cd':=cd'); auto.
            apply CIH with (tr:=tr)(Sds:= (fst y') )(Sm:=(snd y')).
            * exists mu'; eassumption.
            * destruct y' as [a b]; apply H2; auto.
            * assumption.
          + (*Fake stutter case*)
            apply (coinductive_safety.internal_safetyN_stut) with (cd':= cd')(y':=(st2',m2'))(n:=n).
            * admit. (* Equate the two different stepN... or redefine one... *)
            *  {simpl. apply CIH with (Sds:=fst y') (Sm:=snd y'). Guarded.
                - exists mu'; assumption.
                - destruct y' as [a b]; eapply H2.  }
      }
    - (*External step case *)
      assert (my_machine_diagram:= Machine_sim.machine_diagram
                           _ _ _ _ _ _ _ _
                           (concur_sim Tg Sg main p U)).
        simpl in my_machine_diagram.
        intros MATCH.
        eapply my_machine_diagram with (st1':= fst y')(m1':=snd y') in MATCH; eauto.
        + clear my_machine_diagram.
          move: MATCH => [] st2' [] m2' [] cd' [] mu' [] MATCH' step.
          apply coinductive_safety.external_safetyN_stut with (cd':=cd')(x':=x')(y':= (st2', m2')).
          * apply step.
          * apply CIH with (tr:=tr)(Sds:= (fst y') )(Sm:=(snd y')). 
            exists mu'; exact MATCH'.
        + destruct y' as [a b]; eapply H2.
  Guarded.
  Admitted.
            
      Grab Existential Variables.
      - eauto.


      intros.
      apply coinductive_safety.external_safetyN_stut with (cd':=cd)(x':=sch)(y':= (Tds,Tm)).
      apply H1.
      
                  
             
            
            
            
          inversion step_plus.

          move: H3=> [] st2'' [] m2'' [] t_step t_stepN.
          assert (exists j, match_st Tg Sg main p U cd' j (st') m' st2' m2') by (exists mu' => //) .
          Guarded.
          apply (Machine.DryConc.exp_safety _ _ _ _ _
                      (Machine.DryConc.internal_safety _ _ _ _ _ _ t_step
                                                  (stepN_safety' U p Tg st2' m2' x _ _ _ t_stepN
                                                                 ( fun sch' val => safety_equivalence_stutter'
                                     (core_ord_wf _ _ _ _ _)
               cd
               _ _ _ _
               (ex_intro _ cd' (*exists cd' *)
                         (safety_preservation'' tr _ _ st2' m2' cd' H3 H2 _ val)))
                                                  )
                 )                      
                ).
          Guarded.
          apply: (Machine.DryConc.internal_safety _ _ _ _ _ _ t_step
                                                  (stepN_safety' U p Tg st2' m2' x _ _ _ t_stepN
                                                                 ( fun sch' val => safety_equivalence_stutter'
                                     (core_ord_wf _ _ _ _ _)
               cd
               _ _ _ _
               (ex_intro _ cd' (*exists cd' *)
                         (safety_preservation'' tr _ _ st2' m2' cd' H3 H2 _ val)))
                                                  )
                 )
          .
          apply: t_step.
          apply: (stepN_safety' U p Tg st2' m2' x _ _ _ t_stepN
                    ( fun sch' val => safety_equivalence_stutter'
               (core_ord_wf _ _ _ _ _)
               cd
               _ _ _ _
               (ex_intro _ cd' (*exists cd' *)
                         (safety_preservation'' tr _ _ st2' m2' cd' H3 H2 _ val)))
                 )
          .
          (* move => sch' val.
          *)
          eapply
            ( fun sch' val => safety_equivalence_stutter'
               (core_ord_wf _ _ _ _ _)
               cd
               _ _ _ _
               (ex_intro _ cd' (*exists cd' *)
              (safety_preservation'' tr _ _ st2' m2' cd' H3 H2 _ val))
               
            ). 
          apply (
              ex_intro _ cd' (*exists cd' *)
              (safety_preservation'' tr _ _ st2' m2' cd' H3 H2 _ val)).
          Guarded.
             ;
            [apply: | |  exists cd' ]. eauto.
          
          apply: core_ord_wf.
          
          
          apply: my_safeN; intros.
          
          econstructor.
          

          eapply (Machine.DryConc.internal_safety Tg sch (Tds) Tm).
          + apply: t_step.
            
            
          +
            {
              (*move /(safety_preservation'' nil (st') m' st2' m2') => condition.
              move: H2 => /condition. *)
              rewrite / Machine.DryConc.new_valid /Machine.DryConc.mk_ostate /=.
              clear - t_stepN safety_preservation''.
              rename Tg into ge.
              rename st2'' into st2.
              rename m2'' into m2.
              rename x into n.
              move=> condition.
              move: st2 m2 sch t_stepN.
              clear - condition safety_preservation''.
              apply: stepN_safety => U'' val.
              eapply Machine.DryConc.safety_equivalence_stutter; 
                [apply: core_ord_wf| |  exists cd' ]; eauto.
              eapply (safety_preservation'' nil (st') m' st2' m2').
              
          }
          { exists mu'=> //. }
        (*Step star with the data step*)
        - pose (note1:=5). destruct n.
         (* the zero case *)
          + pose (note4:=5). inversion stepN; subst.
            {
              simpl in MATCH'.
              apply: (Machine.DryConc.stutter _ _ _ _ _ cd').
              eapply safety_preservation''; eauto.
              exact data_step.
            }
            
          (*Same as the step_N case: *)
          + { pose (note5:=5). inversion stepN.
              move: H3=>  [] m2'' [] t_step t_stepN'.
              econstructor.
              eapply (Machine.DryConc.internal_safety Tg sch (Tds) Tm).
              + apply: t_step.
              + specialize (safety_preservation'' nil (st') m' st2' m2').
                cut ( exists j, match_st Tg Sg main p U cd' j (st') m' st2' m2').
                { move /safety_preservation'' => condition.
                  move: H2 => /condition.
                  rewrite / Machine.DryConc.new_valid /Machine.DryConc.mk_ostate /=.
                  clear -t_stepN'.
                  rename Tg into ge.
                  rename x into st2.
                  rename m2'' into m2.
              
              move=> condition.
              move: st2 m2 sch t_stepN'.
              clear - condition.
              apply: stepN_safety => U'' val.
              eapply Machine.DryConc.safety_equivalence_stutter; 
                  [apply: core_ord_wf| |  exists cd' ]; eauto.
          }
                { exists mu'=> //. }
                
            }
      }
    (*External Step case*)
    - { pose (note6:=5).
        rename equivalid into bobo.
        assert (my_machine_diagram:= Machine_sim.machine_diagram
                           _ _ _ _ _ _ _ _
                           (concur_sim Tg Sg main p U)).
        simpl in my_machine_diagram.
        intros MATCH.
        eapply my_machine_diagram with (st1':= (st'))(m1':=m') in MATCH; eauto.
        clear my_machine_diagram.
        move: MATCH => [] st2' [] m2' [] cd' [] mu' [] MATCH' step.
        econstructor.
        eapply (Machine.DryConc.external_safety); eauto.
        intros.
        eapply Machine.DryConc.safety_equivalence_stutter;
        [ apply: core_ord_wf |
          exact cd' |
          pose (note7:=1);
         exists cd'; eapply safety_preservation''; eauto ]; eauto.
      }
      Grab Existential Variables.
      - eauto.
  Qed.
      
        
        
        
        Lemma safety_preservation': forall main p U Sg Tg tr Sds Sm Tds Tm
      (MATCH: exists cd j, (match_st Tg Sg main p U) cd j Sds Sm Tds Tm),
      (forall sch, THE_DRY_MACHINE_SOURCE.DryMachine.valid (sch, tr, Sds) ->
              THE_DRY_MACHINE_SOURCE.DryMachine.explicit_safety Sg sch Sds Sm) ->
      (forall sch, Machine.DryConc.valid (sch, tr, Tds) ->
              Machine.DryConc.explicit_safety Tg sch Tds Tm).
            
            
            
            
            
         
         
            
              

              inversion t_stepN. clear t_stepN.
              move: H0 => [] m_ [] t_step t_stepN'.
              apply: Machine.DryConc.internal_safety => //.
              move: (t_step) => /=.
              cut ( (fst st2 = nil) /\ (fst x = nil));
                [ clear t_step; move=> [] -> -> t_step | (inversion t_step; split; reflexivity)].
              
              
              
            eapply t_step.
              
              
              eapply IHn in t_stepN'.
              
            eapply condition in H2.
          eapply safety_preservation' in MATCH'.
          clear - t_stepN safety_preservation'.
           

        
        
        move: H3 => [] st2' [] m2' [] cd' [] mu' [] MATCH' [ [] n steps' | [] steps' cordr  ].
        {
          
          assert (SFT: forall sch,
                     Machine.DryConc.valid (sch, snd (fst st2'), snd st2') -> 
                     Machine.DryConc.safe_new_step Tg (sch, snd (fst st2'), snd st2')  m2').
          { eapply safety_preservation.
            * exists cd', mu' => //.
                unfold match_st.
                eapply MATCH'.
              * intros. rewrite /THE_DRY_MACHINE_SOURCE.DryMachine.mk_ostate
                                /THE_DRY_MACHINE_SOURCE.DryMachine.safe_new_step
                                /THE_DRY_MACHINE_SOURCE.DryMachine.mk_nstate /=.
                destruct st' as [[x y] z]=> /=.
                eapply H2 => //. }
          assert (VAL:Machine.DryConc.valid (sch, snd (fst Tds), snd Tds)).



          
  
  Lemma safety_preservation: forall main p U Sg Tg Sds Sm Tds Tm
      (MATCH: exists cd j, (match_st Tg Sg main p U) cd j Sds Sm Tds Tm),
      (forall sch, THE_DRY_MACHINE_SOURCE.DryMachine.valid (sch, fst Sds, snd Sds) ->
              THE_DRY_MACHINE_SOURCE.DryMachine.safe_new_step Sg (sch, fst Sds, snd Sds) Sm) ->
      (forall sch, Machine.DryConc.valid (sch, fst Tds, snd Tds) ->
  Machine.DryConc.safe_new_step Tg (sch, fst Tds, snd Tds) Tm).
  Proof.
    move => main p U Sg Tg.
    assert (ax:= blah Tg Sg main p U).
    cofix.
    intros.
    assert (H':=H).
    specialize (H sch).
    move: MATCH => [] cd [] j MATCH.
    move: (MATCH) => /blah /= AA.
    move: (AA sch) => [A B].
    assert (HH:THE_DRY_MACHINE_SOURCE.DryMachine.new_valid
             (THE_DRY_MACHINE_SOURCE.DryMachine.mk_nstate Sds Sm) sch).
    { rewrite /THE_DRY_MACHINE_SOURCE.DryMachine.new_valid
              /THE_DRY_MACHINE_SOURCE.DryMachine.mk_ostate
              /THE_DRY_MACHINE_SOURCE.DryMachine.mk_nstate /=.
      destruct Sds as [[a b] c] => /=; simpl in B.
      apply: B.
      apply: H0. }
    apply H in HH.
    inversion HH.
    inversion H1.
    (*Halted case*)
    - {
      destruct Sds as [[a b] c]; simpl in *; subst.
      econstructor.
      + (*Notice I Don't use core_halted! might remove it from simulation!!*)
        econstructor.
        move: H9;
          rewrite /THE_DRY_MACHINE_SOURCE.DryMachine.halted
                  /Machine.DryConc.halted /= //.
      + rewrite /Machine.DryConc.mk_nstate => U''/= VAL.
        unfold Machine.DryConc.safe_new_step,
        Machine.DryConc.mk_nstate in safety_preservation.
        simpl in safety_preservation.
        apply: safety_preservation => //.
        * exists cd, j; apply: MATCH.
        * move =>  sch.
          move: H2. rewrite /THE_DRY_MACHINE_SOURCE.DryMachine.safe_new_step
                            /THE_DRY_MACHINE_SOURCE.DryMachine.mk_nstate /=.
          destruct st' as [[a' b' ] c']=> /= HH2.
          apply: HH2.
      }
      (*Step case*)
    - { assert (my_core_diagram:= core_diagram
                           _ _ _ _ _ _ _ _
                           (concur_sim Tg Sg main p U)).
        eapply my_core_diagram with (cd:=cd)(mu:=j)(st2:=(sch, snd (fst Tds), snd Tds))(m2:=Tm) in H3 . clear my_core_diagram.
        move: H3 => [] st2' [] m2' [] cd' [] mu' [] MATCH' [ [] n steps' | [] steps' cordr  ].
        {
          
          assert (SFT: forall sch,
                     Machine.DryConc.valid (sch, snd (fst st2'), snd st2') -> 
                     Machine.DryConc.safe_new_step Tg (sch, snd (fst st2'), snd st2')  m2').
          { eapply safety_preservation.
            * exists cd', mu' => //.
                unfold match_st.
                eapply MATCH'.
              * intros. rewrite /THE_DRY_MACHINE_SOURCE.DryMachine.mk_ostate
                                /THE_DRY_MACHINE_SOURCE.DryMachine.safe_new_step
                                /THE_DRY_MACHINE_SOURCE.DryMachine.mk_nstate /=.
                destruct st' as [[x y] z]=> /=.
                eapply H2 => //. }
          assert (VAL:Machine.DryConc.valid (sch, snd (fst Tds), snd Tds)).
          
          
          { eapply A=>//. 
          clear H0 MATCH A B AA. (*Tds*)
          clear H HH H1 H4 H5. (*sch*)
          clear MATCH'. (*st2'*)
          move: m2' st2' SFT sch Tm Tds steps'.
          
          induction n.
          - move => m2' st2' SFT sch Tm Tds steps'.
            inversion steps'. move: H =>[] m2'' [] STEP' nothing. 
            inversion nothing; subst.
            econstructor.
            + instantiate(2:=Machine.DryConc.mk_nstate st2' m2'); instantiate (1:=fst (fst st2')).
              econstructor 2.
              move: STEP'.
              destruct Tds as [[x y ] z];
                destruct st2' as [[x' y'] z']=> //.
            + by rewrite /Machine.DryConc.new_valid /Machine.DryConc.mk_nstate.
              
          - move => m2' st2' SFT sch Tm Tds steps'.
            inversion steps'. move: H => [] m2 [] STEP steps''. 
            simpl in STEP.
            econstructor.
            + instantiate (2:= Machine.DryConc.mk_nstate x m2); instantiate (1:= fst (fst x)).
              econstructor 2.
              move: STEP; rewrite /Machine.DryConc.mk_nstate /Machine.DryConc.mk_ostate /Machine.DryConc.MachStep /= => STEP.
              eapply STEP.
            + move=> U'' VAL.
              move: (IHn m2 x); clear IHn.
              destruct x as [[a b ] c].
              rewrite /Machine.DryConc.safe_new_step
                      /Machine.DryConc.mk_nstate
                      /Machine.DryConc.mk_ostate => /= IHn /=.
              simpl in VAL.
              specialize (STEPS a m2 (a, b ,c)).
              simpl in STEPS. simpl in steps''. eapply STEPS in steps''.
              simpl.
              
          

          => STEP'.
          eapply STEP'.
        
        
        rewrite /Machine.DryConc.safe_new_step
                /Machine.DryConc.mk_nstate /=.
        eapply (safety.csft_step _ _) .
        econstructor 2.
face        
        move: my_core_diagram.
        

        rewrite /corestep /THE_DRY_MACHINE_SOURCE.DryMachine.MachineSemantics.
        simpl.