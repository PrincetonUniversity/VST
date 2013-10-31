Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.StructuredInjections.

Require Import effect_simulations.

Section Eff_INJ_SIMU_DIAGRAMS.
  Context {F1 V1 C1 F2 V2 C2:Type}
          {Sem1 : @EffectSem (Genv.t F1 V1) C1} 
          {Sem2 : @EffectSem (Genv.t F2 V2) C2}

          {ge1: Genv.t F1 V1} 
          {ge2: Genv.t F2 V2} 
          {entry_points : list (val * val * signature)}. 

  Let core_data := C1.

  Variable match_states: core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop.
   
   Hypothesis genvs_dom_eq: genvs_domain_eq ge1 ge2.

   Hypothesis match_sm_wd: forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 ->
          SM_wd mu.

   Hypothesis match_norm: forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 ->
          forall mu23, (SM_wd mu23 /\ DomTgt mu = DomSrc mu23 /\
                        locBlocksTgt mu = locBlocksSrc mu23 /\
                       (forall b, pubBlocksTgt mu b = true -> pubBlocksSrc mu23 b = true) /\
                       (forall b, frgnBlocksTgt mu b = true -> frgnBlocksSrc mu23 b = true)) ->
          match_states d (sm_extern_normalize mu mu23) c1 m1 c2 m2.

   Hypothesis match_validblocks: forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 ->
          sm_valid mu m1 m2.

(*
    Hypothesis match_genv: forall d mu c1 m1 c2 m2,  match_state d mu c1 m1 c2 m2 -> 
          meminj_preserves_globals ge1 (foreign_of mu); *)
    Hypothesis match_genv: forall d mu c1 m1 c2 m2 (MC:match_states d mu c1 m1 c2 m2),
          meminj_preserves_globals ge1 (extern_of mu) /\
          (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true).
  
   Hypothesis inj_initial_cores: forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2 DomS DomT,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          Forall2 (val_inject j) vals1 vals2 ->
          meminj_preserves_globals ge1 j ->

         (forall b1 b2 d, j b1 = Some (b2, d) -> 
                          DomS b1 = true /\ DomT b2 = true) ->
         (forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> DomT b = true) ->
       exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_states c1 (initial_SM DomS
                                       DomT 
                                       (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
                                       (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
                           c1 m1 c2 m2.

  Hypothesis inj_halted : forall cd mu c1 m1 c2 m2 v1,
      match_states cd mu c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->

      exists v2, 
             Mem.inject (as_inj mu) m1 m2 /\
             val_inject (as_inj mu) v1 v2 /\
             halted Sem2 c2 = Some v2.

  Hypothesis inj_at_external : 
      forall cd mu c1 m1 c2 m2 e vals1 ef_sig,
        match_states cd mu c1 m1 c2 m2 ->
        at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
        ( Mem.inject (as_inj mu) m1 m2 /\ 
          exists vals2, 
            Forall2 (val_inject (as_inj mu)) vals1 vals2 /\ 
            at_external Sem2 c2 = Some (e,ef_sig,vals2)).


  Hypothesis inj_after_external:
      forall cd mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
        (MemInjMu: Mem.inject (as_inj mu) m1 m2)
        (MatchMu: match_states cd mu st1 m1 st2 m2)
        (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals1))

        (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals2)) 

        (ValInjMu: Forall2 (val_inject (as_inj mu)) vals1 vals2)  

        pubSrc' (pubSrcHyp: pubSrc' = fun b => andb (locBlocksSrc mu b)
                                                    (REACH m1 (exportedSrc mu vals1) b))

        pubTgt' (pubTgtHyp: pubTgt' = fun b => andb (locBlocksTgt mu b)
                                                    (REACH m2 (exportedTgt mu vals2) b))

        nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),

      forall nu' ret1 m1' ret2 m2'
        (INC: extern_incr nu nu')  
        (SEP: sm_inject_separated nu nu' m1 m2)

        (WDnu': SM_wd nu') (SMvalNu': sm_valid nu' m1' m2')

        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')

        frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (locBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

        frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (locBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
 
        (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
                                                      pubBlocksSrc nu b = false) m1 m1') 

        (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),

       exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' mu' st1' m1' st2' m2'.

Section EFF_INJ_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

  Hypothesis inj_core_diagram : 
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall st2 mu m2,
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
          match_states st1' mu' st1' m1' st2' m2' /\

          SM_wd mu' /\ sm_valid mu' m1' m2' /\

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            order st1' st1).

    Hypothesis inj_effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2,
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\
          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
              (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
               order st1' st1)) /\ 

             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true))).

  Hypothesis inj_effect_diagram_strong : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b z, U1 b z = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\

          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
              (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
               order st1' st1)) /\

             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true))).

  Hypothesis inj_effect_diagram_strong_perm : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b z, U1 b z = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\

          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
              (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
               order st1' st1)) /\

             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty))).

Lemma  inj_simulation_star_wf: 
  SM_simulation.SM_simulation_inject Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply SM_simulation.Build_SM_simulation_inject with
    (core_ord := order)
    (match_state := fun d j c1 m1 c2 m2 => d = c1 /\ match_states d j c1 m1 c2 m2).
  apply order_wf.
clear - match_sm_wd. intros. destruct H; subst. eauto.
assumption.
clear - match_genv. intros. destruct MC; subst. eauto.
clear - match_norm. intros. destruct H; subst. split; eauto.
clear - match_validblocks. intros. destruct H; subst. eauto.
clear - inj_initial_cores. intros.
    destruct (inj_initial_cores _ _ _ H
         _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4 H5)
    as [c2 [INI MS]].
  exists c1, c2. intuition. 
clear - inj_core_diagram.
  intros. destruct H0; subst.
  destruct (inj_core_diagram _ _ _ _ H _ _ _ H1) as 
    [c2' [m2' [mu' [INC [SEP [LAC [MC' [WD [Valid' Step]]]]]]]]].
  exists c2'. exists m2'. exists st1'. exists mu'. intuition.
clear - inj_effcore_diagram.
  intros. destruct H0; subst.
  destruct (inj_effcore_diagram _ _ _ _ _ H _ _ _ H1) as 
    [c2' [m2' [mu' [INC [SEP [LAC [MC' XX]]]]]]]. 
  exists c2'. exists m2'. exists st1'. exists mu'. intuition.
clear - inj_effect_diagram_strong. 
  intros. destruct H0; subst.
  destruct (inj_effect_diagram_strong _ _ _ _ _ H _ _ _ UHyp H1) as 
    [c2' [m2' [mu' [INC [SEP [LAC [MC' XX]]]]]]]. 
  exists c2'. exists m2'. exists st1'. exists mu'. intuition.
clear - inj_effect_diagram_strong_perm. 
  intros. destruct H0; subst.
  destruct (inj_effect_diagram_strong_perm _ _ _ _ _ H _ _ _ UHyp H1) as 
    [c2' [m2' [mu' [INC [SEP [LAC [MC' XX]]]]]]]. 
  exists c2'. exists m2'. exists st1'. exists mu'. intuition.
clear - inj_halted. intros. destruct H; subst.
  destruct (inj_halted _ _ _ _ _ _ _ H1 H0) as [v2 [INJ [VAL HH]]].
  exists v2; intuition.
clear - inj_at_external. intros. destruct H; subst.
  destruct (inj_at_external _ _ _ _ _ _ _ _ _ H1 H0)
    as [INJ [vals2 [VALS AtExt2]]].
  split. trivial. exists vals2. intuition.
clear - inj_after_external. intros. 
  destruct MatchMu as [ZZ matchMu]. subst cd.
  destruct (inj_after_external _ _ _ _ _ _ _ _ _ _ _ _
      MemInjMu matchMu AtExtSrc AtExtTgt ValInjMu _
      pubSrcHyp _ pubTgtHyp _ NuHyp _ _ _ _ _ INC SEP
      WDnu' SMvalNu' MemInjNu' RValInjNu' FwdSrc FwdTgt 
      _ frgnSrcHyp _ frgnTgtHyp _ Mu'Hyp UnchPrivSrc UnchLOOR)
    as [st1' [st2' [AftExt1 [AftExt2 MS']]]].
  exists st1', st1', st2'. intuition.
Qed.

End EFF_INJ_SIMULATION_STAR_WF.

Section EFF_INJ_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis inj_core_diagram : 
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall st2 mu m2,
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
          match_states st1' mu' st1' m1' st2' m2' /\

          SM_wd mu' /\ sm_valid mu' m1' m2' /\

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            ((measure st1' < measure st1)%nat /\ corestep_star Sem2 ge2 st2 m2 st2' m2')).

    Hypothesis inj_effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2,
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\
          exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
           /\ 
             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true)).

  Hypothesis inj_simulation_strong : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\

          exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
            /\
             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true)).

  Hypothesis inj_simulation_strong_perm : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\

          exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
            /\
             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty)).


Lemma inj_simulation_star: 
  SM_simulation.SM_simulation_inject Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply inj_simulation_star_wf.
  apply  (well_founded_ltof _ measure).
clear - inj_core_diagram. intros.
  destruct (inj_core_diagram _ _ _ _ H _ _ _ H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [WD' [VAL' STEP]]]]]]]]]. 
  exists c2'. exists m2'. exists mu'.
  intuition.
clear - inj_effcore_diagram. intros.
  destruct (inj_effcore_diagram _ _ _ _ _ H _ _ _ H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
clear - inj_simulation_strong. intros.
  destruct (inj_simulation_strong _ _ _ _ _ H _ _ _ UHyp H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
clear - inj_simulation_strong_perm. intros.
  destruct (inj_simulation_strong_perm _ _ _ _ _ H _ _ _ UHyp H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
Qed.

End EFF_INJ_SIMULATION_STAR.

Section EFF_INJ_SIMULATION_PLUS.
  Variable measure: C1 -> nat. 
  Hypothesis inj_core_diagram : 
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall st2 mu m2,
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
          match_states st1' mu' st1' m1' st2' m2' /\

          SM_wd mu' /\ sm_valid mu' m1' m2' /\

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            ((measure st1' < measure st1)%nat /\ corestep_star Sem2 ge2 st2 m2 st2' m2')).

    Hypothesis inj_effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2,
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\
          exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
           /\ 
             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true)).

  Hypothesis inj_simulation_strong : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\

          exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
            /\
             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true)).

  Hypothesis inj_simulation_strong_perm : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_states st1 mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_states st1' mu' st1' m1' st2' m2' /\

          exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
            /\
             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty)).
  
Lemma inj_simulation_plus: 
  SM_simulation.SM_simulation_inject Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply inj_simulation_star with (measure:=measure).
clear - inj_core_diagram. intros.
  destruct (inj_core_diagram _ _ _ _ H _ _ _ H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [WD' [VAL' STEP]]]]]]]]]. 
  exists c2'. exists m2'. exists mu'.
  intuition.
clear - inj_effcore_diagram. intros.
  destruct (inj_effcore_diagram _ _ _ _ _ H _ _ _ H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
clear - inj_simulation_strong. intros.
  destruct (inj_simulation_strong _ _ _ _ _ H _ _ _ UHyp H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
clear - inj_simulation_strong_perm. intros.
  destruct (inj_simulation_strong_perm _ _ _ _ _ H _ _ _ UHyp H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
Qed.

End EFF_INJ_SIMULATION_PLUS.

End Eff_INJ_SIMU_DIAGRAMS.

Definition compose_sm (mu1 mu2 : SM_Injection) : SM_Injection :=
 Build_SM_Injection 
   (DomSrc mu1) (DomTgt mu2)
   (locBlocksSrc mu1) (locBlocksTgt mu2)
   (pubBlocksSrc mu1) (pubBlocksTgt mu2)
   (frgnBlocksSrc mu1) (frgnBlocksTgt mu2) 
   (compose_meminj (extern_of mu1) (extern_of mu2))
   (compose_meminj (local_of mu1) (local_of mu2)).
(*
Definition compose_sm (mu1 mu2 : SM_Injection) : SM_Injection :=
 Build_SM_Injection 
   (DomSrc mu1) (DomTgt mu2)
   (locBlocksSrc mu1) (locBlocksTgt mu2)
   (fun b1 => exists b3 z, 
      compose_meminj (pubInj mu1) (pubInj mu2) b1 = Some(b3,z))
   (fun b3 => exists b1 z, 
      compose_meminj (local_of mu1) (local_of mu2) b1 = Some(b3,z) /\
      locBlocksTgt mu2 b3)
   (compose_meminj (unknown_of mu1) (extern_of mu2))
   (compose_meminj (foreign_of mu1) (foreign_of mu2))
   (compose_meminj (pub_of mu1) (pub_of mu2))
   (compose_meminj (priv_of mu1) (local_of mu2)).
*)
Lemma compose_sm_valid: forall mu1 mu2 m1 m2 m2' m3
          (SMV1: sm_valid mu1 m1 m2) (SMV2: sm_valid mu2 m2' m3),
       sm_valid (compose_sm mu1 mu2) m1 m3.
Proof.  split. apply SMV1. apply SMV2. Qed.

Lemma compose_sm_pub: forall mu12 mu23 
         (HypPub: forall b, pubBlocksTgt mu12 b = true ->
                            pubBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12),
      pub_of (compose_sm mu12 mu23) =
      compose_meminj (pub_of mu12) (pub_of mu23).
Proof. intros. unfold compose_sm, pub_of. 
  extensionality b. 
  destruct mu12 as [DomS1 DomT1 BSrc1 BTgt1 pSrc1 pTgt1 fSrc1 fTgt1 extern1 local1]; simpl.
  destruct mu23 as [DomS2 DomT2 BSrc2 BTgt2 pSrc2 pTgt2 fSrc2 fTgt2 extern2 local2]; simpl.
  remember (pSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    destruct (pubSrc _ WD1 _ Heqd) as [b2 [d1 [LOC1 Tgt1]]]; simpl in *.
    rewrite Heqd in LOC1. apply HypPub in Tgt1. 
    unfold compose_meminj. rewrite Heqd. rewrite LOC1. rewrite Tgt1.
    trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_foreign: forall mu12 mu23
         (HypFrg: forall b, frgnBlocksTgt mu12 b = true ->
                            frgnBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12),
      foreign_of (compose_sm mu12 mu23) = 
      compose_meminj (foreign_of mu12) (foreign_of mu23).
Proof. intros. unfold compose_sm, foreign_of. 
  extensionality b. 
  destruct mu12 as [DomS1 DomT1 BSrc1 BTgt1 pSrc1 pTgt1 fSrc1 fTgt1 extern1 local1]; simpl.
  destruct mu23 as [DomS2 DomT2 BSrc2 BTgt2 pSrc2 pTgt2 fSrc2 fTgt2 extern2 local2]; simpl.
  remember (fSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    destruct (frgnSrc _ WD1 _ Heqd) as [b2 [d1 [EXT1 Tgt1]]]; simpl in *.
    rewrite Heqd in EXT1. apply HypFrg in Tgt1. 
    unfold compose_meminj. rewrite Heqd. rewrite EXT1. rewrite Tgt1.
    trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_priv: forall mu12 mu23,
   priv_of (compose_sm mu12 mu23) =
   compose_meminj (priv_of mu12) (local_of mu23).
Proof. intros. unfold priv_of, compose_sm.
  extensionality b.
  destruct mu12 as [DomS1 DomT1 BSrc1 BTgt1 pSrc1 pTgt1 fSrc1 fTgt1 extern1 local1]; simpl.
  destruct mu23 as [DomS2 DomT2 BSrc2 BTgt2 pSrc2 pTgt2 fSrc2 fTgt2 extern2 local2]; simpl.
  remember (pSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    unfold compose_meminj. rewrite Heqd. trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_unknown: forall mu12 mu23,
   unknown_of (compose_sm mu12 mu23) = 
   compose_meminj (unknown_of mu12) (extern_of mu23).
Proof. intros. unfold unknown_of, compose_sm.
  extensionality b.
  destruct mu12 as [DomS1 DomT1 BSrc1 BTgt1 pSrc1 pTgt1 fSrc1 fTgt1 extern1 local1]; simpl.
  destruct mu23 as [DomS2 DomT2 BSrc2 BTgt2 pSrc2 pTgt2 fSrc2 fTgt2 extern2 local2]; simpl.
  remember (BSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    unfold compose_meminj. rewrite Heqd. trivial.
  remember (fSrc1 b) as q; destruct q; apply eq_sym in Heqq.
    unfold compose_meminj. rewrite Heqd. rewrite Heqq. trivial.
  unfold compose_meminj.
    rewrite Heqd. rewrite Heqq. trivial.
Qed.

Lemma compose_sm_local: forall mu12 mu23,
   local_of (compose_sm mu12 mu23) =
   compose_meminj (local_of mu12) (local_of mu23).
Proof. intros. reflexivity. Qed. 

Lemma compose_sm_extern: forall mu12 mu23,
   extern_of (compose_sm mu12 mu23) =
   compose_meminj (extern_of mu12) (extern_of mu23).
Proof. intros. reflexivity. Qed. 

Lemma compose_sm_shared: forall mu12 mu23 
         (HypPub: forall b, pubBlocksTgt mu12 b = true ->
                            pubBlocksSrc mu23 b = true)
         (HypFrg: forall b, frgnBlocksTgt mu12 b = true ->
                            frgnBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12) (WD2:SM_wd mu23),
      shared_of (compose_sm mu12 mu23) =
      compose_meminj (shared_of mu12) (shared_of mu23).
Proof. intros. unfold shared_of. 
  rewrite compose_sm_pub; trivial.
  rewrite compose_sm_foreign; trivial.
  unfold join, compose_meminj. extensionality b.
  remember (foreign_of mu12 b) as f; destruct f; apply eq_sym in Heqf.
    destruct p as [b2 d1].
    destruct (foreign_DomRng _ WD1 _ _ _ Heqf) as [A [B [C [D [E [F [G H]]]]]]].
    apply HypFrg in F.
    destruct (frgnSrc _ WD2 _ F) as [b3 [d2 [FRG2 TGT2]]].
    rewrite FRG2. trivial.
  remember (pub_of mu12 b) as d; destruct d; apply eq_sym in Heqd; trivial.
    destruct p as [b2 d1].
    destruct (pub_locBlocks _ WD1 _ _ _ Heqd) as [A [B [C [D [E [F [G H]]]]]]].
    apply HypPub in B.
    destruct (pubSrc _ WD2 _ B) as [b3 [d2 [PUB2 TGT2]]].
    rewrite PUB2.
    apply (pubBlocksLocalSrc _ WD2) in B.
    apply (locBlocksSrc_frgnBlocksSrc _ WD2) in B.
    unfold foreign_of. destruct mu23. simpl in *. rewrite B. trivial.
Qed.

Lemma compose_sm_wd: forall mu1 mu2 (WD1: SM_wd mu1) (WD2:SM_wd mu2)
         (HypPub: forall b, pubBlocksTgt mu1 b = true ->
                            pubBlocksSrc mu2 b = true)
         (HypFrg: forall b, frgnBlocksTgt mu1 b = true ->
                            frgnBlocksSrc mu2 b = true),
      SM_wd (compose_sm mu1 mu2).
Proof. intros.
destruct mu1 as [DomS1 DomT1 BSrc1 BTgt1 pSrc1 pTgt1 fSrc1 fTgt1 extern1 local1]; simpl.
destruct mu2 as [DomS2 DomT2 BSrc2 BTgt2 pSrc2 pTgt2 fSrc2 fTgt2 extern2 local2]; simpl.
split; simpl.
(*local_DomRng*)
  intros b1 b3 d H. 
  destruct (compose_meminjD_Some _ _ _ _ _ H) 
    as [b2 [d1 [d2 [PUB1 [PUB2 X]]]]]; subst; clear H.
  split. eapply WD1. apply PUB1. 
         eapply WD2. apply PUB2. 
(*extern_DomRng*)
  intros b1 b3 d H. 
  destruct (compose_meminjD_Some _ _ _ _ _ H) 
    as [b2 [d1 [d2 [EXT1 [EXT2 X]]]]]; subst; clear H.
  split. eapply WD1. apply EXT1. 
  split. eapply WD2. apply EXT2. 
  split. eapply WD1. apply EXT1. 
         eapply WD2. apply EXT2. 
(*pubSrc*)
  intros. rewrite H. 
  destruct (pubSrc _ WD1 _ H) as [b2 [d1 [Loc1 Tgt1]]]. simpl in *.
  apply HypPub in Tgt1. 
  destruct (pubSrc _ WD2 _ Tgt1) as [b3 [d2 [Loc2 Tgt2]]]. simpl in *.
  unfold compose_meminj. exists b3, (d1+d2).
  rewrite H in *. rewrite Tgt1 in *. rewrite Loc1. rewrite Loc2. auto.
(*frgnSrc*)
  intros. rewrite H. 
  destruct (frgnSrc _ WD1 _ H) as [b2 [d1 [Ext1 Tgt1]]]. simpl in *.
  apply HypFrg in Tgt1. 
  destruct (frgnSrc _ WD2 _ Tgt1) as [b3 [d2 [Ext2 Tgt2]]]. simpl in *.
  unfold compose_meminj. exists b3, (d1+d2).
  rewrite H in *. rewrite Tgt1 in *. rewrite Ext1. rewrite Ext2. auto.
(*locBlocksDomSrc*)
  apply WD1.
(*locBlocksDomTgt*)
  apply WD2.
(*pubBlocksLocalTgt*)
  apply WD2.
(*frgnBlocksDomTgt*)
  apply WD2.
Qed.
 (*   
Lemma compose_sm_initial: forall m j,
  initial_SM (compose_meminj (Mem.flat_inj (Mem.nextblock m)) j) =
  compose_sm (initial_SM (Mem.flat_inj (Mem.nextblock m))) (initial_SM j).
Proof. intros.
(*remember (initial_SM (compose_meminj (Mem.flat_inj (Mem.nextblock m)) j)) as R1.
remember (compose_sm (initial_SM (Mem.flat_inj (Mem.nextblock m))) (initial_SM j)) as R2.
*)
unfold compose_sm, initial_SM. simpl.
f_equal.
extensionality b.
  apply prop_ext.
  split; intros; intuition.
  destruct H as [b3 [z H]].
  destruct (compose_meminjD_Some _ _ _ _ _ H)
   as [b2 [z1 [z2 [J1 [J2 X]]]]]; subst.
  inv J1.
extensionality b.
  apply prop_ext.
  split; intros; intuition.
  destruct H as [b3 [z H]].
  destruct (compose_meminjD_Some _ _ _ _ _ H)
   as [b2 [z1 [z2 [J1 [J2 X]]]]]; subst.
  inv J1.
(*
assert (locBlocksSrc R1  = locBlocksSrc R2).
  subst. unfold compose_sm, initial_SM. simpl. trivial.
assert (locBlocksTgt R1  = locBlocksTgt R2).
  subst. unfold compose_sm, initial_SM. simpl. trivial.
assert (frgnInj R1  = frgnInj R2).
  subst. unfold compose_sm, initial_SM. simpl. trivial.
assert (pubInj R1  = pubInj R2).
  subst. unfold compose_sm, initial_SM. simpl.
  extensionality b1.
  unfold compose_meminj. trivial.
assert (privInj R1  = privInj R2).
  subst. unfold compose_sm, initial_SM. simpl.
  extensionality b1.
  unfold compose_meminj. trivial.
apply f_equal. congruence.
(*Rest of this proof is proof irrelevance...*)*)
Qed.
*)

Lemma compose_sm_as_inj: forall mu12 mu23 (WD1: SM_wd mu12) (WD2: SM_wd mu23)
   (SrcTgt: locBlocksTgt mu12 = locBlocksSrc mu23),
   as_inj (compose_sm mu12 mu23) = 
   compose_meminj (as_inj mu12) (as_inj mu23).
Proof. intros.
  unfold as_inj.
  rewrite compose_sm_extern.
  rewrite compose_sm_local.
  unfold join, compose_meminj. extensionality b.
  remember (extern_of mu12 b) as f; destruct f; apply eq_sym in Heqf.
    destruct p as [b2 d1].
    remember (extern_of mu23 b2) as d; destruct d; apply eq_sym in Heqd.
      destruct p as [b3 d2]. trivial.
    destruct (disjoint_extern_local _ WD1 b).
       rewrite H in Heqf. discriminate.
    rewrite H. 
    destruct (extern_DomRng _ WD1 _ _ _ Heqf) as [A [B [C D]]]. 
    rewrite SrcTgt in B.
    remember (local_of mu23 b2) as q; destruct q; trivial; apply eq_sym in Heqq.
    destruct p as [b3 d2].
    destruct (local_DomRng _ WD2 _ _ _ Heqq) as [AA BB].
    rewrite AA in *; discriminate.
  remember (local_of mu12 b) as q; destruct q; trivial; apply eq_sym in Heqq.
    destruct p as [b2 d1].
    destruct (local_DomRng _ WD1 _ _ _ Heqq) as [AA BB].
    remember (extern_of mu23 b2) as d; destruct d; trivial; apply eq_sym in Heqd.
      destruct p as [b3 d2].
      destruct (extern_DomRng _ WD2 _ _ _ Heqd) as [A [B [C D]]]. 
      rewrite SrcTgt in BB. rewrite BB in A. discriminate.
Qed.

Lemma sm_extern_normalize_compose_sm: forall mu12 mu23,
  compose_sm mu12 mu23 = compose_sm (sm_extern_normalize mu12 mu23) mu23.
Proof. intros.
  unfold compose_sm. 
  rewrite sm_extern_normalize_DomSrc, sm_extern_normalize_locBlocksSrc,
          sm_extern_normalize_pubBlocksSrc, sm_extern_normalize_frgnBlocksSrc,
          sm_extern_normalize_local, sm_extern_normalize_extern.
    rewrite normalize_compose. apply f_equal. trivial.
Qed.

Lemma compose_sm_intern_incr:
      forall mu12 mu12' mu23 mu23'
            (inc12: intern_incr mu12 mu12') 
            (inc23: intern_incr mu23 mu23'),
      intern_incr (compose_sm mu12 mu23) (compose_sm mu12' mu23').
Proof. intros.
split; simpl in *.
    eapply compose_meminj_inject_incr.
        apply inc12.
        apply intern_incr_local; eassumption.
split. rewrite (intern_incr_extern _ _ inc12).
       rewrite (intern_incr_extern _ _ inc23).
       trivial.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
apply inc23.
Qed.

Lemma compose_sm_extern_incr:
      forall mu12 mu12' mu23 mu23'
            (inc12: extern_incr mu12 mu12') 
            (inc23: extern_incr mu23 mu23')
  (FRG': forall b1 b2 d1, foreign_of mu12' b1 = Some(b2,d1) ->
         exists b3 d2, foreign_of mu23' b2 = Some(b3,d2))
  (WD12': SM_wd mu12') (WD23': SM_wd mu23'),
  extern_incr (compose_sm mu12 mu23) (compose_sm mu12' mu23').
Proof. intros.
split; intros.
  rewrite compose_sm_extern.
  rewrite compose_sm_extern.
  eapply compose_meminj_inject_incr.
    apply inc12.
    apply extern_incr_extern; eassumption.
split; simpl.
  rewrite (extern_incr_local _ _ inc12). 
  rewrite (extern_incr_local _ _ inc23).
  trivial.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
apply inc23.
Qed.

Lemma extern_incr_inject_incr: 
      forall nu12 nu23 nu' (WDnu' : SM_wd nu')
          (EXT: extern_incr (compose_sm nu12 nu23) nu')
          (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                      DomTgt nu12 = DomSrc nu23 /\ 
                      locBlocksTgt nu12 = locBlocksSrc nu23 /\
                      (forall b, pubBlocksTgt nu12 b = true -> 
                                 pubBlocksSrc nu23 b = true) /\
                      (forall b, frgnBlocksTgt nu12 b = true -> 
                                 frgnBlocksSrc nu23 b = true)),
      inject_incr (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu').
Proof. intros.
  intros b; intros.
  destruct (compose_meminjD_Some _ _ _ _ _ H)
    as [b2 [d1 [d2 [Nu12 [Nu23 D]]]]]; subst; clear H.
  unfold extern_incr in EXT. simpl in EXT.
  destruct EXT as [EXT [LOC [Dom12 [Tgt23 [mySrc12 [myTgt23 [pubSrc12 [pubTgt23 [frgnSrc12 frgnTgt23]]]]]]]]].
  destruct (joinD_Some _ _ _ _ _ Nu12); clear Nu12.
  (*extern12*)
     destruct (joinD_Some _ _ _ _ _ Nu23); clear Nu23.
     (*extern12*)
        apply join_incr_left. apply EXT.
        unfold compose_meminj. rewrite H. rewrite H0. trivial.
     (*local*)
        destruct H0.
        destruct GlueInvNu as [GLa [GLb [GLc [GLd [GLe GLf]]]]].
        destruct (extern_DomRng' _ GLa _ _ _ H) as [? [? [? [? [? ?]]]]].
        destruct (local_locBlocks _ GLb _ _ _ H1) as [? [? [? [? [? ?]]]]].
        rewrite GLd in *. rewrite H8 in H5. inv H5. 
  (*local*) 
     destruct H.
     destruct (joinD_Some _ _ _ _ _ Nu23); clear Nu23.
     (*extern12*)
        destruct GlueInvNu as [GLa [GLb [GLc [GLd [GLe GLf]]]]].
        destruct (extern_DomRng' _ GLb _ _ _ H1) as [? [? [? [? [? ?]]]]].
        destruct (local_locBlocks _ GLa _ _ _ H0) as [? [? [? [? [? ?]]]]].
        rewrite GLd in *. rewrite H9 in H4. inv H4.
     (*local*)
        destruct H1. 
        apply join_incr_right. eapply disjoint_extern_local. apply WDnu'.
        rewrite <- LOC. unfold compose_meminj. rewrite H0. rewrite H2. trivial.
Qed.

Lemma compose_sm_as_injD: forall mu1 mu2 b1 b3 d
      (I: as_inj (compose_sm mu1 mu2) b1 = Some (b3, d))
      (WD1: SM_wd mu1) (WD2: SM_wd mu2),
      exists b2 d1 d2, as_inj mu1 b1 = Some(b2,d1) /\
                       as_inj mu2 b2 = Some(b3,d2) /\
                       d=d1+d2.
Proof. intros.
destruct (joinD_Some _ _ _ _ _ I); clear I.
(*extern*)
  rewrite compose_sm_extern in H.
  destruct (compose_meminjD_Some _ _ _ _ _ H)
      as [b2 [d1 [d2 [EXT1 [EXT2 D]]]]]; clear H.
  exists b2, d1, d2.
  split. apply join_incr_left. assumption.
  split. apply join_incr_left. assumption.
         assumption. 
(*local*)
  destruct H. 
  rewrite compose_sm_extern in H.
  rewrite compose_sm_local in H0.
  destruct (compose_meminjD_Some _ _ _ _ _ H0)
      as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; clear H0.
  exists b2, d1, d2.
  split. apply join_incr_right.
           apply disjoint_extern_local; assumption. 
           assumption.
  split. apply join_incr_right.
           apply disjoint_extern_local; assumption. 
           assumption.
         assumption.
Qed. 

Lemma compose_sm_intern_separated:
      forall mu12 mu12' mu23 mu23' m1 m2 m3 
        (inc12: intern_incr mu12 mu12') 
        (inc23: intern_incr mu23 mu23')
        (InjSep12 : sm_inject_separated mu12 mu12' m1 m2)
        (InjSep23 : sm_inject_separated mu23 mu23' m2 m3)
        (WD12: SM_wd mu12) (WD12': SM_wd mu12') (WD23: SM_wd mu23) (WD23': SM_wd mu23')
        (MYB: locBlocksTgt mu12 = locBlocksSrc mu23)
        (DOM2: DomTgt mu12 = DomSrc mu23),
      sm_inject_separated (compose_sm mu12 mu23)
                          (compose_sm mu12' mu23') m1 m3.
Proof. intros.
destruct InjSep12 as [AsInj12 [DomTgt12 Sep12]].
destruct InjSep23 as [AsInj23 [DomTgt23 Sep23]].
split.
  intros b1 b3 d; intros.
  simpl.
  destruct (compose_sm_as_injD _ _ _ _ _ H0)
     as [b2 [d1 [d2 [AI12' [AI23' X]]]]]; subst; trivial; clear H0.
  assert (DomSrc (compose_sm mu12' mu23') b1 = true /\
          DomTgt (compose_sm mu12' mu23') b3 = true).
    simpl.
    split. eapply as_inj_DomRng; eassumption.
    eapply as_inj_DomRng; eassumption. 
  destruct H0 as [DOM1 TGT3]; simpl in *.
  assert (TGT2: DomTgt mu12' b2 = true).
    eapply as_inj_DomRng. eassumption. eapply WD12'.
  assert (DOMB2: DomSrc mu23' b2 = true).
    eapply as_inj_DomRng. eassumption. eapply WD23'.
  remember (as_inj mu12 b1) as q.
  destruct q; apply eq_sym in Heqq.
    destruct p.
    specialize (intern_incr_as_inj _ _ inc12 WD12' _ _ _ Heqq); intros.
    rewrite AI12' in H0. apply eq_sym in H0. inv H0.
    destruct (joinD_Some _ _ _ _ _ Heqq); clear Heqq.
    (*extern12Some*)
       assert (extern_of mu12' b1 = Some (b2, d1)).
          rewrite <- (intern_incr_extern _ _ inc12). assumption.
       destruct (joinD_None _ _ _ H); clear H.
       clear AI12'.
       destruct (joinD_Some _ _ _ _ _ AI23'); clear AI23'.
       (*extern23'Some*)
         assert (extern_of mu23 b2 = Some (b3, d2)).
           rewrite (intern_incr_extern _ _ inc23). assumption.
         rewrite compose_sm_extern in H2.
         unfold compose_meminj in H2. 
         rewrite H0 in H2. rewrite H4 in H2. inv H2.
       (*extern23'None*)
         destruct H.
         rewrite compose_sm_extern in H2.
         destruct (compose_meminjD_None _ _ _ H2); clear H2.
            rewrite H5 in H0. discriminate.
         destruct H5 as [bb2 [dd1 [EXT12 EXT23]]].
         rewrite EXT12 in H0. inv H0.
         rewrite compose_sm_local in H3.
         remember (local_of mu23 b2) as qq.
         destruct qq; apply eq_sym in Heqqq.
            destruct p.
            specialize (intern_incr_local _ _ inc23); intros.
            specialize (H0 _ _ _ Heqqq). rewrite H0 in H4. inv H4.
            destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [A [B [C D]]].
            destruct (local_DomRng _ WD23 _ _ _ Heqqq) as [AA BB].
            rewrite MYB in B. rewrite B in AA. inv AA.
         destruct (AsInj23 b2 b3 d2).
            apply joinI_None. assumption. assumption.
            apply join_incr_right.
              apply disjoint_extern_local. assumption.
              assumption.
         destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [_ [_ [_ XX]]].
         rewrite DOM2 in XX. rewrite XX in H0. discriminate. 
    (*extern12None*)
       destruct H0.
       assert (extern_of mu12' b1 = None).
          rewrite <- (intern_incr_extern _ _ inc12). assumption.
       assert (local_of mu12' b1 = Some (b2, d1)).
          eapply (intern_incr_local _ _ inc12). assumption.
       destruct (joinD_None _ _ _ H); clear H.
       clear AI12'.
       destruct (joinD_Some _ _ _ _ _ AI23'); clear AI23'.
       (*extern23'Some*)
         destruct (local_DomRng _ WD12' _ _ _ H3) as [AA BB].
         destruct (extern_DomRng _ WD23' _ _ _ H) as [A [B [C D]]].
         destruct (local_DomRng _ WD12 _ _ _ H1) as [AAA BBB].
         rewrite MYB in BBB. 
         assert (locBlocksSrc mu23' b2 = true). apply inc23. assumption.
         rewrite H6 in A. discriminate.
       (*extern23'None*)
         destruct H.
         assert (extern_of mu23 b2 = None).
           rewrite (intern_incr_extern _ _ inc23). assumption.
         rewrite compose_sm_local in H5.
         unfold compose_meminj in H5. rewrite H1 in H5.
         remember (local_of mu23 b2).
         destruct o. destruct p. inv H5. clear H5. apply eq_sym in Heqo.
         clear H4.
         destruct (local_DomRng _ WD12 _ _ _ H1) as [AA BB].
         assert (DomSrc mu23 b2 = false /\ DomTgt mu23 b3 = false).
            eapply AsInj23.
              apply joinI_None; assumption.
              apply join_incr_right; try eassumption.
                apply disjoint_extern_local; eassumption.
         destruct H4.  
         destruct (local_locBlocks _ WD12 _ _ _ H1) 
           as [AAA [BBB [CCC [DDD [EEE FFF]]]]].
         rewrite DOM2 in FFF. rewrite FFF in H4. discriminate.
   (*as_inj mu12 b1 = None*)
     destruct (AsInj12 _ _ _ Heqq AI12'). split; trivial. clear H.
     remember (as_inj mu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p.
       specialize (intern_incr_as_inj _ _ inc23 WD23' _ _ _ Heqd).
       intros ZZ; rewrite AI23' in ZZ. apply eq_sym in ZZ; inv ZZ.
       destruct (as_inj_DomRng _ _ _ _ Heqd WD23).
       rewrite DOM2 in H1. rewrite H1 in H. discriminate.
     eapply AsInj23. eassumption. eassumption.
simpl.
  split. apply DomTgt12. apply Sep23.
Qed.

(*         

Lemma sm_inject_incr_pub: forall mu j (WD: SM_wd mu)
         (Incr : inject_incr (shared_of mu) j) b1 b2 z
         (P: pubInj mu b1 = Some(b2,z)), 
          j b1 = Some(b2,z).
Proof. intros.
  destruct mu as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
  destruct WD as [dist [locDom [frgnDom [SrcDec TgtDec]]]].
  simpl in *.
  apply Incr.
  unfold join. rewrite P.
  remember (frgn1 b1) as u.
  destruct u; apply eq_sym in Hequ; trivial.
      destruct p. destruct (frgnDom _ _ _ Hequ).
      exfalso. apply H. apply (locDom b1 b2 z).
      unfold join. rewrite P. trivial.
Qed.

Lemma compose_sm_extend_foreign: forall mu1 mu2 j1 j2 m1 m2 m3
          (Incr12 : inject_incr (shared_of mu1) j1)
          (Incr23 : inject_incr (shared_of mu2) j2)
          (Sep12 : inject_separated (shared_of mu1) j1 m1 m2)
          (Sep23 : inject_separated (shared_of mu2) j2 m2 m3)
          (SMV1: sm_valid mu1 m1 m2) (SMV2: sm_valid mu2 m2 m3) 
          (WD1: SM_wd mu1) (WD2: SM_wd mu2)
          (BB: locBlocksTgt mu1 = locBlocksSrc mu2),
      extend_foreign (compose_sm mu1 mu2) (compose_meminj j1 j2) m1 m3 =
      compose_sm (extend_foreign mu1 j1 m1 m2) (extend_foreign mu2 j2 m2 m3).
Proof. intros.
  destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
  destruct mu2 as [BSrc2 BTgt2 pSrc2 pTgt2 frgn2 pub2 priv2].
  unfold compose_sm, extend_foreign in *; simpl in *. subst.
  f_equal.
  extensionality b1.
  unfold compose_meminj.
  remember (pub1 b1) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p as [b2 z1].
    assert (J1: j1 b1 = Some (b2,z1)).
      apply (sm_inject_incr_pub _ _ WD1 Incr12); eauto.
    rewrite J1.
    remember (pub2 b2) as q.
    destruct q; apply eq_sym in Heqq.
      destruct p as [b3 z2]. trivial.
    remember (frgn2 b2) as f.
    destruct f; apply eq_sym in Heqf.
      destruct p.
      destruct WD2 as [_ [_ [F2 _]]]. simpl in *.
      destruct (F2 _ _ _ Heqf).
      exfalso. apply H; clear F2 H H0. 
      destruct WD1 as [_ [PUB1 _]]. simpl in *.
      eapply (PUB1 b1). unfold join. rewrite Heqd. reflexivity.
    assert (Shared2: join frgn2 pub2 b2 = None).
      unfold join. rewrite Heqq, Heqf. trivial.
    remember (j2 b2) as a.
    destruct a; apply eq_sym in Heqa; trivial.
      destruct p as [b3 z3].
      destruct (Sep23 _ _ _ Shared2 Heqa).
      exfalso. apply H; clear H H0.
      eapply SMV1. simpl. left.
      destruct WD1 as [_ [PUB1 _]]. simpl in *.
      eapply (PUB1 b1). unfold join. rewrite Heqd. reflexivity.
  remember (j1 b1) as q.
  destruct q; apply eq_sym in Heqq; trivial.
    destruct p as [b2 z1].
    remember (frgn1 b1) as w.
    destruct w; apply eq_sym in Heqw.
      destruct p as [bb2 zz1].
      assert (j1 b1 =  Some (bb2, zz1)).
         apply Incr12. unfold join. rewrite Heqw. trivial.
      rewrite H in Heqq. inv Heqq.
      destruct WD1 as [_ [_ [F1 _]]]. simpl in *.
      destruct (F1 _ _ _ Heqw).
      remember (pub2 b2) as a.
      destruct a; apply eq_sym in Heqa.
        destruct p as [b3 z2].
        exfalso. apply H1; clear H0 H1.
        destruct WD2 as [_ [PUB2 _]]. simpl in *.
        eapply PUB2. unfold join. rewrite Heqa. reflexivity.
      reflexivity.
   assert (Shared1: join frgn1 pub1 b1 = None).
     unfold join. rewrite Heqd, Heqw. trivial.
   destruct (Sep12 _ _ _ Shared1 Heqq).
   remember (pub2 b2) as a.
   destruct a; apply eq_sym in Heqa.
     destruct p as [b3 z2].
     exfalso. apply H0; clear H H0.
     eapply SMV2. simpl. left.
      destruct WD2 as [_ [PUB2 _]]. simpl in *.
      eapply PUB2. unfold join. rewrite Heqa. trivial. 
   reflexivity.
Qed.

Lemma compose_sm_foreign_extend_foreign: forall mu1 mu2 j1 j2 m1 m2 m3
          (Incr12 : inject_incr (foreign_of mu1) j1)
          (Incr23 : inject_incr (foreign_of mu2) j2)
          (Sep12 : inject_separated (foreign_of mu1) j1 m1 m2)
          (Sep23 : inject_separated (foreign_of mu2) j2 m2 m3)
          (SMV1: sm_valid mu1 m1 m2) (SMV2: sm_valid mu2 m2 m3) 
          (WD1: SM_wd mu1) (WD2: SM_wd mu2)
          (BB: locBlocksTgt mu1 = locBlocksSrc mu2),
      extend_foreign (compose_sm mu1 mu2) (compose_meminj j1 j2) m1 m3 =
      compose_sm (extend_foreign mu1 j1 m1 m2) (extend_foreign mu2 j2 m2 m3).
Proof. intros.
  destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
  destruct mu2 as [BSrc2 BTgt2 pSrc2 pTgt2 frgn2 pub2 priv2].
  unfold compose_sm, extend_foreign in *; simpl in *. subst.
  f_equal.
  extensionality b1.
  unfold compose_meminj.
  specialize (sm_wd_disjoint_foreign_pub _ WD2); intros D2.
  specialize (sm_wd_disjoint_foreign_pub _ WD1); intros D1.
  simpl in *.
  remember (frgn1 b1) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p as [b2 z1].
    destruct (D1 b1); rewrite H in *.
      discriminate.
   specialize (Incr12 _ _ _ Heqd).
   rewrite Incr12.
   remember (pub2 b2) as q.
   destruct q; apply eq_sym in Heqq.
     destruct p.
     exfalso. 
     destruct WD1 as [? [? [? _]]]. simpl in *.
     destruct (H2 _ _ _ Heqd).
     apply H4; clear H3 H4. subst.
     eapply WD2. unfold join; simpl.
     rewrite Heqq; reflexivity.
  trivial.
remember (pub1 b1) as e.
  destruct e; apply eq_sym in Heqe.
    destruct p as [b2 z1].
    remember (j1 b1) as q. 
    destruct q; apply eq_sym in Heqq. 
      destruct p. 
      destruct (Sep12 _ _ _ Heqd Heqq).
      exfalso. apply H; clear H H0.
      eapply SMV1. left. eapply WD1. 
      unfold join; simpl. rewrite Heqe. reflexivity.
    remember (pub2 b2) as t.
    destruct t; apply eq_sym in Heqt.
      destruct p as [b3 z2]. trivial. trivial.
  remember (j1 b1) as q. 
    destruct q; apply eq_sym in Heqq; trivial. 
    destruct p.
    destruct (Sep12 _ _ _ Heqd Heqq). 
    remember (pub2 b) as f.
    destruct f; apply eq_sym in Heqf; trivial.
      destruct p. exfalso. apply H0; clear H H0.
      eapply SMV2. left. eapply WD2.
      unfold join; simpl. rewrite Heqf. reflexivity.
Qed.

Lemma extend_foreign_locBlocksTgt: forall mu j m1 m2,
  locBlocksTgt (extend_foreign mu j m1 m2) = locBlocksTgt mu.
Proof. intros.
  destruct mu as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
  reflexivity.
Qed.

Lemma extend_foreign_locBlocksSrc: forall mu j m1 m2,
  locBlocksSrc (extend_foreign mu j m1 m2) = locBlocksSrc mu.
Proof. intros.
  destruct mu as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
  reflexivity.
Qed.

Lemma compose_pub_join: forall j12' j23' mu1 mu2 m1 m2 m3
     (Incr12 : inject_incr (frgnInj mu1) j12')
     (Incr23 : inject_incr (frgnInj mu2) j23')
     (Sep12 : inject_separated (frgnInj mu1) j12' m1 m2)
     (Sep23 : inject_separated (frgnInj mu2) j23' m2 m3)
     (WD12: SM_wd mu1)  (WD23: SM_wd mu2)
     (SMV12: sm_valid mu1 m1 m2)
     (SMV23: sm_valid mu2 m2 m3)
     (B: locBlocksTgt mu1 = locBlocksSrc mu2),
   join (compose_meminj j12' j23')
           (compose_meminj (pub_of mu1) (pub_of mu2))
  = compose_meminj (join j12' (pub_of mu1)) (join j23' (pub_of mu2)).
Proof. intros.
  specialize (sm_wd_disjoint_foreign_pub _ WD12).
  specialize (sm_wd_disjoint_foreign_pub _ WD23).
  destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
  destruct mu2 as [BSrc2 BTgt2 pSrc2 pTgt2 frgn2 pub2 priv2].
  simpl in *.
  unfold join, compose_meminj. intros D23 D12.
  extensionality b.
  remember (j12' b) as d.
  destruct d.
    destruct p as [b1 delta1].
    remember (j23' b1) as q.
    destruct q.
      destruct p as [b2 delta2]. trivial.
    remember (frgn1 b) as w.
    destruct w; apply eq_sym in Heqw.
      destruct p as [bb dd].
      rewrite (Incr12 _ _ _ Heqw) in Heqd. inv Heqd.
      destruct (D12 b).
      rewrite H in Heqw. discriminate.
      rewrite H.
      remember (pub2 bb) as r.
      destruct r; apply eq_sym in Heqr.
        destruct p.
        destruct WD12 as [_ [? [? [? _]]]].
        destruct WD23 as [_ [? [? [? _]]]].
        simpl in *.
        destruct (H1 _ _ _ Heqw).
        exfalso. apply H7; clear H6 H7.
        eapply H3. unfold join. rewrite Heqr. reflexivity.
      trivial.
   apply eq_sym in Heqd.
     destruct (Sep12 _ _ _ Heqw Heqd).
     remember (pub1 b) as r.
     destruct r; apply eq_sym in Heqr.
       destruct p. exfalso.
       apply H; clear H H0.
       eapply SMV12. unfold DOM. left. 
        eapply WD12. simpl in *.
         unfold join.
         rewrite Heqr. reflexivity.
     remember (pub2 b1) as a.
     destruct a; trivial; apply eq_sym in Heqa.
     destruct p. exfalso. apply H0; clear H H0.
     eapply SMV23. unfold DOM; simpl. left.
        subst. eapply WD23. unfold join; simpl.
        rewrite Heqa. reflexivity.
  remember (pub1 b) as w.  
  destruct w; trivial; apply eq_sym in Heqw.
  destruct p as [b2 delta2].
  remember (j23' b2) as q.
  destruct q; trivial; apply eq_sym in Heqq.
  destruct p as [b3 delta3].
  remember (pub2 b2) as t.
  destruct t; apply eq_sym in Heqt.
    destruct p.
    exfalso.
    destruct (D23 b2).
      destruct (Sep23 _ _ _ H Heqq).
      apply H0; clear H0 H1.
      eapply SMV23. left. 
      eapply WD23. simpl. unfold join. 
        rewrite Heqt. reflexivity. 
    rewrite H in Heqt. discriminate.
  exfalso. 
  remember (frgn2 b2) as a.
  destruct a; apply eq_sym in Heqa.
    destruct p.
    destruct WD12 as [_ [? [? [? _]]]].
    destruct WD23 as [_ [? [? [? _]]]].
    simpl in *.
    destruct (H3 _ _ _ Heqa).
    apply H5; clear H5 H6.
    subst. eapply (H b). unfold join.
     rewrite Heqw. reflexivity.
  destruct (Sep23 _ _ _ Heqa Heqq).
    apply H; clear H0 H.
    eapply SMV12. simpl. left.
    destruct WD12 as [_ [? [? [? _]]]].
    eapply (H b). unfold join; simpl.
    rewrite Heqw. reflexivity.
Qed.

*)