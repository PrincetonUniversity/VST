Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import msl.Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.reach.

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

    Hypothesis match_visible: forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 -> 
          REACH_closed m1 (vis mu).

    Hypothesis match_restrict: forall d mu c1 m1 c2 m2 X, 
          match_states d mu c1 m1 c2 m2 -> 
          (forall b, vis mu b = true -> X b = true) ->
          REACH_closed m1 X ->
          match_states d (restrict_sm mu X) c1 m1 c2 m2.

   Hypothesis match_validblocks: forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 ->
          sm_valid mu m1 m2.

(*experimental
   Hypothesis match_divalblocks : forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 ->
          DomSrc mu = valid_block_dec m1 /\
          DomTgt mu = valid_block_dec m2.
   Hypothesis match_protected: forall d mu c1 m1 c2 m2, 
          match_states d mu c1 m1 c2 m2 ->
          forall b, REACH m1 (extBlocksSrc mu) b = true ->
                    locBlocksSrc mu b = true ->
                    REACH m1 (frgnBlocksSrc mu) b = true.
*)

(*
    Hypothesis match_genv: forall d mu c1 m1 c2 m2,  match_state d mu c1 m1 c2 m2 -> 
          meminj_preserves_globals ge1 (foreign_of mu); *)
    Hypothesis match_genv: forall d mu c1 m1 c2 m2 (MC:match_states d mu c1 m1 c2 m2),
          meminj_preserves_globals ge1 (extern_of mu) /\
          (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true).
  
(*Version if the environment provides structured injections:
   Hypothesis 
    core_initial_sm : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 mu vals2 m2,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject (as_inj mu) m1 m2 -> 
          Forall2 (val_inject (as_inj mu)) vals1 vals2 ->
          meminj_preserves_globals ge1 (as_inj mu) ->
          SM_wd mu -> sm_valid mu m1 m2 ->
          (forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> 
                     DomTgt mu b = true) ->
       exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_states c1 (mkinitial_SM mu (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))
                                            (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)))
                           c1 m1 c2 m2.
*)
   Hypothesis inj_initial_cores: forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2 DomS DomT,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          Forall2 (val_inject j) vals1 vals2 ->
          meminj_preserves_globals ge1 j ->

        (*the next two conditions are required to guarantee intialSM_wd*)
         (forall b1 b2 d, j b1 = Some (b2, d) -> 
                          DomS b1 = true /\ DomT b2 = true) ->
         (forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> DomT b = true) ->

        (*the next two conditions ensure the initialSM satisfies sm_valid*)
         (forall b, DomS b = true -> Mem.valid_block m1 b) ->
         (forall b, DomT b = true -> Mem.valid_block m2 b) ->

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
             val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
             halted Sem2 c2 = Some v2.

  Hypothesis inj_at_external : 
      forall mu c1 m1 c2 m2 e vals1 ef_sig,
        match_states c1 mu c1 m1 c2 m2 ->
        at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
        Mem.inject (as_inj mu) m1 m2 /\ 
          exists vals2, 
            Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\ 
            at_external Sem2 c2 = Some (e,ef_sig,vals2)
    /\ forall
       (pubSrc' pubTgt' : block -> bool)
       (pubSrcHyp : pubSrc' =
                  (fun b : block =>
                  locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgtHyp: pubTgt' =
                  (fun b : block =>
                  locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (Hnu: nu = (replace_locals mu pubSrc' pubTgt')),
       match_states c1 nu c1 m1 c2 m2 
       /\ Mem.inject (shared_of nu) m1 m2.


  Hypothesis inj_after_external:
      forall mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
        (MemInjMu: Mem.inject (as_inj mu) m1 m2)
        (MatchMu: match_states st1 mu st1 m1 st2 m2)
        (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals1))

        (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals2)) 

        (ValInjMu: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)  

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

(*          SM_wd mu' /\ sm_valid mu' m1' m2' /\*)

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            order st1' st1).

  Hypothesis inj_effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b z, U1 b z = true -> vis mu b = true),
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
                       (visTgt mu b = true /\ (*Mem.valid_block m2 b /\*)
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
clear - match_visible. intros. destruct H; subst. eauto.
clear - match_restrict. intros. destruct H; subst. eauto.
clear - match_validblocks. intros.
    destruct H; subst. eauto.
(*clear - match_divalblocks. intros.
    destruct H; subst. eauto.*)
(*clear - match_protected. intros.
    destruct H; subst. eauto. *)
(*version with structured injections
clear - core_initial_sm. intros.
    exploit (core_initial_sm _ _ _ H); try eassumption.
    intros [c2 [INI MS]].
  exists c1, c2. intuition. *)
clear - inj_initial_cores. intros.
    destruct (inj_initial_cores _ _ _ H
         _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4 H5 H6 H7)
    as [c2 [INI MS]].
  exists c1, c2. intuition. 
clear - inj_core_diagram.
  intros. destruct H0; subst.
  destruct (inj_core_diagram _ _ _ _ H _ _ _ H1) as 
    [c2' [m2' [mu' [INC [SEP [LAC [MC' (*[WD [Valid'*) Step(*]]*)]]]]]]].
  exists c2'. exists m2'. exists st1'. exists mu'. intuition.
clear - inj_effcore_diagram. 
  intros. destruct H0; subst.
  destruct (inj_effcore_diagram _ _ _ _ _ H _ _ _ UHyp H1) as 
    [c2' [m2' [mu' [INC [SEP [LAC [MC' XX]]]]]]]. 
  exists c2'. exists m2'. exists st1'. exists mu'. intuition.
clear - inj_halted. intros. destruct H; subst.
  destruct (inj_halted _ _ _ _ _ _ _ H1 H0) as [v2 [INJ [VAL HH]]].
  exists v2; intuition.
clear - inj_at_external. intros. destruct H; subst.
  destruct (inj_at_external _ _ _ _ _ _ _ _ H1 H0)
    as [INJ [vals2 [VALS [AtExt2 SH]]]].
  split. trivial. exists vals2. split; trivial. split; trivial. 
    intros. split. split. trivial. eapply SH; eassumption. eapply SH; eassumption.
clear - inj_after_external. intros. 
  destruct MatchMu as [ZZ matchMu]. subst cd.
  destruct (inj_after_external _ _ _ _ _ _ _ _ _ _ _
      MemInjMu matchMu AtExtSrc AtExtTgt ValInjMu _
      pubSrcHyp _ pubTgtHyp _ NuHyp _ _ _ _ _ INC SEP
      WDnu' SMvalNu' MemInjNu' RValInjNu' FwdSrc FwdTgt 
      _ frgnSrcHyp _ frgnTgtHyp _ Mu'Hyp 
      UnchPrivSrc UnchLOOR)
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

(*          SM_wd mu' /\ sm_valid mu' m1' m2' /\*)

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            ((measure st1' < measure st1)%nat /\ corestep_star Sem2 ge2 st2 m2 st2' m2')).

  Hypothesis inj_effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> vis mu b = true),
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
                       (visTgt mu b = true /\ (*Mem.valid_block m2 b /\*)
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
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' (*[WD' [VAL'*) STEP (*]]*)]]]]]]]. 
  exists c2'. exists m2'. exists mu'.
  intuition.
clear - inj_effcore_diagram. intros.
  destruct (inj_effcore_diagram _ _ _ _ _ H _ _ _ UHyp H0) 
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

(*          SM_wd mu' /\ sm_valid mu' m1' m2' /\*)

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            ((measure st1' < measure st1)%nat /\ corestep_star Sem2 ge2 st2 m2 st2' m2')).

  Hypothesis inj_effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> vis mu b = true),
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
                       (visTgt mu b = true /\ (*Mem.valid_block m2 b /\*)
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
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' (*[WD' [VAL'*) STEP(*]]*)]]]]]]]. 
  exists c2'. exists m2'. exists mu'.
  intuition.
clear - inj_effcore_diagram. intros.
  destruct (inj_effcore_diagram _ _ _ _ _ H _ _ _ UHyp H0) 
    as [c2' [m2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]]].
  exists c2'. exists m2'. exists mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
Qed.

End EFF_INJ_SIMULATION_PLUS.

End Eff_INJ_SIMU_DIAGRAMS.

Definition compose_sm (mu1 mu2 : SM_Injection) : SM_Injection :=
 Build_SM_Injection 
   (locBlocksSrc mu1) (locBlocksTgt mu2)
   (pubBlocksSrc mu1) (pubBlocksTgt mu2)
   (compose_meminj (local_of mu1) (local_of mu2))
   (extBlocksSrc mu1) (extBlocksTgt mu2)
   (frgnBlocksSrc mu1) (frgnBlocksTgt mu2) 
   (compose_meminj (extern_of mu1) (extern_of mu2)).

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
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
  remember (pSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    destruct (pubSrc _ WD1 _ Heqd) as [b2 [d1 [LOC1 Tgt1]]]; simpl in *.
    rewrite Heqd in LOC1. apply HypPub in Tgt1. 
    unfold compose_meminj. rewrite Heqd. rewrite LOC1. rewrite Tgt1.
    trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_DomSrc: forall mu12 mu23,
  DomSrc (compose_sm mu12 mu23) = DomSrc mu12.
Proof. intros. unfold compose_sm, DomSrc; simpl. trivial. Qed. 

Lemma compose_sm_DomTgt: forall mu12 mu23,
  DomTgt (compose_sm mu12 mu23) = DomTgt mu23.
Proof. intros. unfold compose_sm, DomTgt; simpl. trivial. Qed. 

Lemma compose_sm_foreign: forall mu12 mu23
         (HypFrg: forall b, frgnBlocksTgt mu12 b = true ->
                            frgnBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12),
      foreign_of (compose_sm mu12 mu23) = 
      compose_meminj (foreign_of mu12) (foreign_of mu23).
Proof. intros. unfold compose_sm, foreign_of. 
  extensionality b. 
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
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
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
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
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
  remember (locBSrc1 b) as d; destruct d; apply eq_sym in Heqd.
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
  destruct mu1 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu2 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
split; simpl in *.
apply WD1.
apply WD2.
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
         eapply WD2. apply EXT2. 
(*pubSrc*)
  intros. 
  destruct (pubSrc _ WD1 _ H) as [b2 [d1 [Loc1 Tgt1]]]. simpl in *.
  apply HypPub in Tgt1. 
  destruct (pubSrc _ WD2 _ Tgt1) as [b3 [d2 [Loc2 Tgt2]]]. simpl in *.
  unfold compose_meminj. exists b3, (d1+d2).
  rewrite H in *. rewrite Tgt1 in *. rewrite Loc1. rewrite Loc2. auto.
(*frgnSrc*)
  intros.
  destruct (frgnSrc _ WD1 _ H) as [b2 [d1 [Ext1 Tgt1]]]. simpl in *.
  apply HypFrg in Tgt1. 
  destruct (frgnSrc _ WD2 _ Tgt1) as [b3 [d2 [Ext2 Tgt2]]]. simpl in *.
  unfold compose_meminj. exists b3, (d1+d2).
  rewrite H in *. rewrite Tgt1 in *. rewrite Ext1. rewrite Ext2. auto.
(*locBlocksDomTgt*)
  apply WD2.
(*frgnBlocksDomTgt*)
  apply WD2.
Qed.

Lemma compose_sm_as_inj: forall mu12 mu23 (WD1: SM_wd mu12) (WD2: SM_wd mu23)
   (SrcTgtLoc: locBlocksTgt mu12 = locBlocksSrc mu23)
   (SrcTgtExt: extBlocksTgt mu12 = extBlocksSrc mu23),
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
    destruct (extern_DomRng _ WD1 _ _ _ Heqf) as [A B]. 
    rewrite SrcTgtExt in B.
    remember (local_of mu23 b2) as q; destruct q; trivial; apply eq_sym in Heqq.
    destruct p as [b3 d2].
    destruct (local_DomRng _ WD2 _ _ _ Heqq) as [AA BB].
    destruct (disjoint_extern_local_Src _ WD2 b2); congruence. 
  remember (local_of mu12 b) as q; destruct q; trivial; apply eq_sym in Heqq.
    destruct p as [b2 d1].
    destruct (local_DomRng _ WD1 _ _ _ Heqq) as [AA BB].
    remember (extern_of mu23 b2) as d; destruct d; trivial; apply eq_sym in Heqd.
      destruct p as [b3 d2].
      destruct (extern_DomRng _ WD2 _ _ _ Heqd) as [A B]. 
      rewrite SrcTgtLoc in BB.
      destruct (disjoint_extern_local_Src _ WD2 b2); congruence.  
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
                      locBlocksTgt nu12 = locBlocksSrc nu23 /\
                      extBlocksTgt nu12 = extBlocksSrc nu23 /\
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
  destruct EXT as [EXT [LOC [extBSrc12 [extBTgt23 [locBSrc12 [locBTgt23 [pubBSrc12 [pubBTgt23 [frgnBSrc12 frgnBTgt23]]]]]]]]].
  destruct (joinD_Some _ _ _ _ _ Nu12); clear Nu12.
  (*extern12*)
     destruct (joinD_Some _ _ _ _ _ Nu23); clear Nu23.
     (*extern12*)
        apply join_incr_left. apply EXT.
        unfold compose_meminj. rewrite H. rewrite H0. trivial.
     (*local*)
        destruct H0.
        destruct GlueInvNu as [GLa [GLb [GLc [GLd [GLe GLf]]]]].
        destruct (extern_DomRng' _ GLa _ _ _ H) as [? [? [? [? [? [? [? ?]]]]]]].
        destruct (local_locBlocks _ GLb _ _ _ H1) as [? [? [? [? [? [? [? ?]]]]]]].
        rewrite GLd in *. congruence.  
  (*local*) 
     destruct H.
     destruct (joinD_Some _ _ _ _ _ Nu23); clear Nu23.
     (*extern12*)
        destruct GlueInvNu as [GLa [GLb [GLc [GLd [GLe GLf]]]]].
        destruct (extern_DomRng' _ GLb _ _ _ H1) as [? [? [? [? [? ?]]]]].
        destruct (local_locBlocks _ GLa _ _ _ H0) as [? [? [? [? [? ?]]]]].
        rewrite GLd in *. congruence. 
     (*local*)
        destruct H1. 
        apply join_incr_right. eapply disjoint_extern_local. apply WDnu'.
        rewrite <- LOC. unfold compose_meminj.
        rewrite H0, H2. trivial.
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
        (BlocksLoc: locBlocksTgt mu12 = locBlocksSrc mu23)
        (BlocksExt: extBlocksTgt mu12 = extBlocksSrc mu23),
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
  rewrite compose_sm_DomSrc, compose_sm_DomTgt.
  assert (DomSrc (compose_sm mu12' mu23') b1 = true /\
          DomTgt (compose_sm mu12' mu23') b3 = true).
    rewrite compose_sm_DomSrc, compose_sm_DomTgt.
    split. eapply as_inj_DomRng; eassumption.
           eapply as_inj_DomRng; eassumption. 
  destruct H0 as [DOM1 TGT3]; simpl in *.
  assert (TGT2: DomTgt mu12' b2 = true).
    eapply as_inj_DomRng. eassumption. eapply WD12'.
  assert (DOMB2: DomSrc mu23' b2 = true).
    eapply as_inj_DomRng. eassumption. eapply WD23'.
  rewrite compose_sm_DomSrc, compose_sm_DomTgt in *.
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
            destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [A B].
            destruct (local_DomRng _ WD23 _ _ _ Heqqq) as [AA BB].
            rewrite BlocksExt in B. 
            destruct (disjoint_extern_local_Src _ WD23 b2); congruence.
         destruct (AsInj23 b2 b3 d2).
            apply joinI_None. assumption. assumption.
            apply join_incr_right.
              apply disjoint_extern_local. assumption.
              assumption.
         destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [XX YY].
           rewrite BlocksExt in YY. unfold DomSrc in H0.
           rewrite YY in H0. rewrite orb_comm in H0. discriminate.
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
         destruct (extern_DomRng _ WD23' _ _ _ H) as [A B].
         destruct (local_DomRng _ WD12 _ _ _ H1) as [AAA BBB].
         rewrite BlocksLoc in BBB. 
         assert (locBlocksSrc mu23' b2 = true). apply inc23. assumption.
         destruct (disjoint_extern_local_Src _ WD23' b2); congruence.
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
         rewrite BlocksLoc in BBB. unfold DomSrc in H4.
             rewrite BBB in H4. discriminate.
   (*as_inj mu12 b1 = None*)
     destruct (AsInj12 _ _ _ Heqq AI12'). split; trivial. clear H.
     remember (as_inj mu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p.
       specialize (intern_incr_as_inj _ _ inc23 WD23' _ _ _ Heqd).
       intros ZZ; rewrite AI23' in ZZ. apply eq_sym in ZZ; inv ZZ.
       destruct (as_inj_DomRng _ _ _ _ Heqd WD23).
       unfold DomSrc in H. unfold DomTgt in H1.
       rewrite BlocksLoc, BlocksExt in H1. rewrite H1 in H; discriminate.
     eapply AsInj23. eassumption. eassumption.
simpl.
  split. apply DomTgt12. apply Sep23.
Qed.

Lemma vis_compose_sm: forall mu nu, vis (compose_sm mu nu) = vis mu.
Proof. intros. unfold vis. destruct mu; simpl. reflexivity. Qed.

Lemma restrict_compose: forall j k X, 
  restrict (compose_meminj j k) X = compose_meminj (restrict j X) k.
Proof. intros.
  extensionality b.
  unfold compose_meminj, restrict.
  remember (X b) as d.
  destruct d; trivial.
Qed.
