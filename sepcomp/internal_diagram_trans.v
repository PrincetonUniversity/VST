Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import VST.msl.Axioms.

Require Import VST.sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.effect_semantics.

Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.
Require Import VST.sepcomp.simulations.
Require Import VST.sepcomp.simulations_lemmas.
Require Import VST.sepcomp.effect_properties.

Require Import Wellfounded.
Require Import Relations.

Require Import VST.sepcomp.full_composition.


(*
Definition entrypoints_compose
  (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
  forall v1 v3 sig, In (v1,v3,sig) ep13 =
    exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.

Section CoreDiagrams_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3)
        epts12 epts23 epts13
        (EPC : entrypoints_compose epts12 epts23 epts13).

Inductive sem_compose_ord_eq_eq {D12 D23:Type}
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop) (C2:Type):
  (D12 * option C2 * D23) ->  (D12 * option C2 * D23) ->  Prop :=
| sem_compose_ord1 :
  forall (d12 d12':D12) (c2:C2) (d23:D23),
    ord12 d12 d12' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2,d23)
| sem_compose_ord2 :
  forall (d12 d12':D12) (c2 c2':C2) (d23 d23':D23),
    ord23 d23 d23' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2',d23').

Lemma effcore_diagram_trans: forall
(core_data12 : Type)
(match_core12 : core_data12 -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(eff_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Injection)
                   (m2 : mem),
                 match_core12 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C2) (m2' : mem) (cd' : core_data12) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   (*sm_inject_separated mu mu' m1 m2 /\*)
                   globals_separate g2 mu mu' /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core12 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\
                        core_ord12 cd' cd))
                    /\ (forall
                         (UHyp: forall b ofs, U1 b ofs = true -> vis mu b = true)
                          b ofs (Ub: U2 b ofs = true),
                       visTgt mu b = true /\
                       (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty))))
(core_data23 : Type)
(match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(genvs_dom_eq23 : genvs_domain_eq g2 g3)
(match_genv23 :
    forall d mu c1 m1 c2 m2 (MC :  match_core23 d mu c1 m1 c2 m2),
    meminj_preserves_globals g2 (extern_of mu) /\
    (forall b, isGlobalBlock g2 b = true -> frgnBlocksSrc mu b = true))
(eff_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Injection)
                   (m2 : mem),
                 match_core23 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   (*sm_inject_separated mu mu' m1 m2 /\ *)
                   globals_separate g3 mu mu' /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core23 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\
                        core_ord23 cd' cd))
                    /\ (forall
                         (UHyp: forall b ofs, U1 b ofs = true -> vis mu b = true)
                          b ofs (Ub: U2 b ofs = true),
                         visTgt mu b = true /\
                           (locBlocksTgt mu b = false->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty))))
 (match_sm_wd12 : forall (d : core_data12) (mu : SM_Injection) (c1 : C1)
                  (m1 : mem) (c2 : C2) (m2 : mem),
                match_core12 d mu c1 m1 c2 m2 -> SM_wd mu)
 (match_validblock12 : forall (d : core_data12) (j : SM_Injection) (c1 : C1)
                       (m1 : mem) (c2 : C2) (m2 : mem),
                     match_core12 d j c1 m1 c2 m2 -> sm_valid j m1 m2)
 (match_sm_wd23 : forall (d : core_data23) (mu : SM_Injection) (c1 : C2)
                  (m1 : mem) (c2 : C3) (m2 : mem),
                match_core23 d mu c1 m1 c2 m2 -> SM_wd mu)
 (match_validblock23 : forall (d : core_data23) (j : SM_Injection) (c1 : C2)
                       (m1 : mem) (c2 : C3) (m2 : mem),
                     match_core23 d j c1 m1 c2 m2 -> sm_valid j m1 m2)
 (st1 : C1)
  (m1 : mem)
  (st1' : C1)
  (m1' : mem)
  U1
  (CS1 : effstep Sem1 g1 U1 st1 m1 st1' m1')
  (d12 : core_data12)
  (d23 : core_data23)

  (st3 : C3)
  (m3 : mem)
  (st2 : C2)
  (m2 : mem)
  (mu12 : SM_Injection)
  (mu23 : SM_Injection)
  (INV : locBlocksTgt mu12 = locBlocksSrc mu23 /\
         extBlocksTgt mu12 = extBlocksSrc mu23 /\
        (forall b : block,
         pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true) /\
        (forall b : block,
         frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true))
  (MC12 : match_core12 d12 mu12 st1 m1 st2 m2)
  (MC23 : match_core23 d23 mu23 st2 m2 st3 m3)
  (full : full_ext mu12 mu23),
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Injection),
  intern_incr (compose_sm mu12 mu23) mu' /\
  globals_separate g3 (compose_sm mu12 mu23) mu' /\
  (*sm_inject_separated (compose_sm mu12 mu23) mu' m1 m3 /\ *)
  sm_locally_allocated (compose_sm mu12 mu23) mu' m1 m3 m1' m2' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists
     (c0 : C2) (m0 : mem) (mu1 mu2 : SM_Injection),
     X = Some c0 /\
     mu' = compose_sm mu1 mu2 /\
     (locBlocksTgt mu1 = locBlocksSrc mu2/\
      extBlocksTgt mu1 = extBlocksSrc mu2/\
      (forall b : block,
       pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
      (forall b : block,
       frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\
     match_core12 d1 mu1 st1' m1' c0 m0 /\
     match_core23 d2 mu2 c0 m0 st2' m2' /\
      (*pure_comp_ext mu1 mu2 m1' m0 /\*)
      full_ext mu1 mu2) /\
  (exists U3 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U3 st3 m3 st2' m2' \/
      effstep_star Sem3 g3 U3 st3 m3 st2' m2' /\
      clos_trans
        (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
        (d12, Some st2, d23))
    /\ (forall
          (UHyp : forall b ofs, U1 b ofs = true -> vis (compose_sm mu12 mu23) b = true)
          b ofs (Ub: U3 b ofs = true),
        visTgt (compose_sm mu12 mu23) b = true /\
        (locBlocksTgt (compose_sm mu12 mu23) b = false ->
        exists (b1 : block) (delta1 : Z),
          foreign_of (compose_sm mu12 mu23) b1 = Some (b, delta1) /\
          U1 b1 (ofs - delta1) = true /\
          Mem.perm m1 b1 (ofs-delta1) Max Nonempty))).
Proof.
  intros.
  destruct (eff_diagram12 _ _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [mu12' [InjIncr12 [Gsep [LocAlloc12
       [MC12' [U2 [Y MOD21]]]]]]]]]]; clear eff_diagram12.
  assert (ZZ: effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. simpl in H. destruct H. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*)
  destruct CS2.
  clear CS1.
  cut (exists st3' : C3,  exists m3' : mem,
    exists d23':core_data23, exists mu23',
      (locBlocksTgt mu12' = locBlocksSrc mu23' /\
        extBlocksTgt mu12' = extBlocksSrc mu23' /\
      (forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true) /\
      (forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true)) /\
      intern_incr mu23 mu23' /\
      globals_separate g3 mu23 mu23' /\
    (*sm_inject_separated mu23 mu23' m2 m3 /\ *)
    sm_locally_allocated mu23 mu23' m2 m3 m2' m3' /\
    match_core23 d23' mu23' st2' m2' st3' m3' /\
    (exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some st2', d23')
        (d12, Some st2,d23)))
    /\ (forall (UHyp: forall b ofs, U2 b ofs = true -> vis mu23 b = true)
              b ofs (Ub: U3 b ofs = true),
        (visTgt mu23 b = true /\
           (locBlocksTgt mu23 b = false ->
           exists b2 delta2, foreign_of mu23 b2 = Some(b,delta2) /\
               U2 b2 (ofs-delta2) = true /\
               Mem.perm m2 b2 (ofs-delta2) Max Nonempty))))).
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [INV' [InjIncr23
          [GSEP [LocAlloc23 [MC23' [U3 [ZZ MOD32]]]]]]]]]]].
  exists st3'. exists m3'.
  exists (d12', Some st2', d23').
  exists (compose_sm mu12' mu23').
  split. solve [eapply compose_sm_intern_incr; eauto].
  destruct INV as [INVa [INVb [INVc INVd]]]; subst.
  (* split. solve [eapply compose_sm_intern_separated; eauto]. *)
  split.
  (*Lemma gsep_compose:
    forall {F V} (ge:  Genv.t F V) mu12 mu23 mu12' mu23',
      globals_separate ge mu12 mu12' ->
      globals_separate ge mu23 mu23' ->
      globals_separate ge (compose_sm mu12 mu23) (compose_sm mu12' mu23').
    ad_it.
    Qed. *)

(*The following deserves its own lemma*)
{
apply (gsep_domain_eq _ _ g2 g3); try assumption.

  assert (WD12: SM_wd mu12) by (eapply match_sm_wd12; eauto).
  assert (WD23: SM_wd mu23) by (eapply match_sm_wd23; eauto).
  assert (WD12': SM_wd mu12') by (eapply match_sm_wd12; eauto).
  assert (WD23': SM_wd mu23') by (eapply match_sm_wd23; eauto).
    assert (pglobals: meminj_preserves_globals g2 (extern_of mu23')).
    eapply match_genv23; eauto.
  assert (INCR: Values.inject_incr (as_inj mu12) (as_inj mu12')) by (eapply intern_incr_as_inj; eauto).
  assert (GLUE: (locBlocksTgt mu12 = locBlocksSrc mu23 /\
           extBlocksTgt mu12 = extBlocksSrc mu23))
    by (destruct INV' as [A [B ?]]; split; assumption).
    assert (gsep12: globals_separate g2 mu12 mu12') by assumption.
    assert (gsep23: globals_separate g2 mu23 mu23').
    { eapply gsep_domain_eq. eauto.
    apply genvs_domain_eq_sym; assumption. }
    intros  b1 b3 d3 map13 map13'.

  destruct (compose_sm_as_injD _ _ _ _ _ map13' WD12' WD23') as [b2 [d1 [d2 [map12 [map23 extra]]]]].
  destruct (compose_sm_as_injD_None _ _ _ WD12 WD23 GLUE map13) as [map12'| [b2' [d [map12' map23']]]].

  - assert (isGlobalBlock g2 b2 = false).
    eapply gsep12; eauto.
    destruct (isGlobalBlock g2 b3) eqn:isglob; [ | reflexivity].
    apply (meminj_preserves_globals_isGlobalBlock _ _ pglobals) in isglob.
    apply WD23' in isglob. destruct isglob as [extS extT].
    rewrite <- (as_inj_extBlocks _ _ _ _ WD23' map23) in extT.
    rewrite <- (intern_incr_extBlocksSrc _ _ InjIncr23) in extT.
    destruct GLUE as [GLUEloc GLUEext].
    rewrite <- GLUEext in extT.
    apply as_injD_None in map12'. destruct map12' as [extmap12 locmap12].
    rewrite (intern_incr_extern _ _ InjIncr12) in extmap12.
    rewrite (intern_incr_extBlocksTgt _ _ InjIncr12) in extT.
    unfold as_inj, join in map12. rewrite extmap12 in map12.
    apply WD12' in map12.
    destruct map12 as [locS locT].
    destruct WD12' as [disj_src disj_tgt _].
    destruct (disj_tgt b2) as [theFalse | theFalse];
    rewrite theFalse in * ; discriminate.
  - assert (HH:as_inj mu12' b1 = Some (b2', d))
      by (eapply INCR; auto).
    rewrite HH in map12; inversion map12; subst.
    eapply gsep23; eauto. }

split. unfold compose_sm; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.

         split; simpl. eapply LocAlloc12.
         split; simpl in *. eapply LocAlloc23.
         split; simpl. eapply LocAlloc12. eapply LocAlloc23.
  split. exists st2', m2', mu12', mu23'.
     split. reflexivity.
     split; trivial.
     split. clear ZZ.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; trivial.
         split; trivial.
         split; assumption.
     do 3 (try split; try assumption).
     (*{ (*clear - pure InjIncr12 InjIncr23.*)
       unfold pure_comp_ext, pure_composition, pure_composition_locat, pure_composition_block,
       replace_locals, DomSrc, exportedSrc, sharedSrc, shared_of,
       intern_incr in *;
         destruct mu12', mu23', mu12, mu23; simpl in *.
       destruct InjIncr12 as [injincr12 [exteq12 ?]].
       destruct InjIncr23 as [injincr23 [exteq23 ?]].
       clear - pure exteq12 exteq23.
       rewrite <- exteq23, <- exteq12.
       destruct pure.
       split.
       + ad_it.
       + apply H0.
     }*)
     (* Full HERE *)
     { apply intern_incr_extern in InjIncr12.
       apply intern_incr_extern in InjIncr23.
       unfold full_ext, full_comp.
       rewrite <- InjIncr12, <- InjIncr23.
       exact full.
     }
     exists U3.
  split; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *. apply ZZ.
    { (*proof of MOD31*)
         intros HypU1 b3 ofs HypU3. clear ZZ eff_diagram23.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *. rewrite vis_compose_sm in HypU1.
         specialize (MOD21 HypU1).
         assert (U2Hyp: forall b ofs, U2 b ofs = true -> vis mu23 b = true).
           intros. clear MOD32. destruct (MOD21 _ _ H0).
           clear - INVa INVd H1. unfold vis. unfold visTgt in H1.
           rewrite INVa in H1. destruct (locBlocksSrc mu23 b); simpl in *.
           trivial. intuition.
         destruct (MOD32 U2Hyp _ _ HypU3) as [vb3 Uhyp32]; clear MOD32.
         split; trivial.
         intros.
         destruct (Uhyp32 H0) as [b2 [d2 [Frg2 [HypU2 HypPerm2]]]]; clear Uhyp32.
         destruct (MOD21 _ _ HypU2) as [vb2 Uhyp21]; clear MOD21.
         rewrite INVa in Uhyp21; clear INVa.
         destruct Uhyp21 as [b1 [d1 [Frg1 Perm1]]].
            eapply frgnBlocksSrc_locBlocksSrc. eauto.
              eapply foreign_DomRng. eauto. apply Frg2.
         exists b1, (d1 + d2).
           assert (FrgB1 : frgnBlocksSrc mu12 b1 = true).
              eapply foreign_DomRng. eauto. apply Frg1.
           rewrite FrgB1.
           unfold compose_meminj.
           rewrite (foreign_in_extern _ _ _ _ Frg1).
           rewrite (foreign_in_extern _ _ _ _ Frg2).
           assert (Arith: ofs - (d1 + d2) = ofs - d2 - d1) by omega.
           rewrite Arith. eauto.
    }
  (*proof of the cut*)
  assert (locLocAlloc12': locBlocksTgt mu12' =
                         fun b => orb (locBlocksTgt mu12 b) (freshloc m2 m2' b)).
         destruct mu12; destruct mu12'; simpl in *. subst.
         eapply LocAlloc12.
  assert (extLocAlloc12': extBlocksTgt mu12' = extBlocksTgt mu12).
         destruct mu12; destruct mu12'; simpl in *. subst.
         eapply LocAlloc12.
  assert (pubAlloc12': pubBlocksTgt mu12 = pubBlocksTgt mu12').
         eapply InjIncr12.
  assert (frgnAlloc12': frgnBlocksTgt mu12 = frgnBlocksTgt mu12').
         eapply InjIncr12.
  rewrite locLocAlloc12', extLocAlloc12' in *. clear locLocAlloc12' extLocAlloc12'.
  destruct INV as [lBlocks2 [eBlocks2 [pBlocks2 fBlocks2]]].
  rewrite lBlocks2, eBlocks2 in *.
  subst.
  clear MC12 InjIncr12 MC12' match_sm_wd12 match_validblock12.
  clear LocAlloc12 full.
  clear st1 m1 st1' m1' (*UHyp*) MOD21.
  rewrite pubAlloc12' in *; clear pubAlloc12'.
  rewrite frgnAlloc12' in *; clear frgnAlloc12'.
  clear lBlocks2 eBlocks2 mu12 Gsep.
  remember (pubBlocksTgt mu12') as pubTgt12'.
  remember (frgnBlocksTgt mu12') as frgnTgt12'.
  clear HeqpubTgt12' HeqfrgnTgt12'.
  clear mu12'.
  clear C1 Sem1 match_core12 g1.
  rename pBlocks2 into HypPubTgt12'.
  rename fBlocks2 into HypFrgnTgt12'.
  revert U2 mu23 d23 st2 m2 st3 m3 H MC23 HypPubTgt12' HypFrgnTgt12' (*UHyp2*).
  induction x; intros.
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [U3 [U4 [? [? ?]]]]]].
    destruct H0. inv H0; simpl in *.
    destruct (eff_diagram23 _ _ _ _ _ H _ _ _ _ (*UHYP2*) MC23)
      as [st3' [m3' [d23' [mu23' [InjInc23
          [GSEP [LocAlloc23 [? [U5 [? MOD32]]]]]]]]]]; clear eff_diagram23.
    exists st3'. exists m3'. exists d23'. exists mu23'.
    split.
      assert (pubBlock23: pubBlocksSrc mu23 = pubBlocksSrc mu23') by apply InjInc23.
      assert (frgnBlock23: frgnBlocksSrc mu23 = frgnBlocksSrc mu23') by apply InjInc23.
      destruct mu23; destruct mu23'. simpl in *.
      destruct LocAlloc23 as [LA12a [LA12b [LA12c LA12d]]].
      subst; simpl in *.
      split; trivial.
      split; trivial.
      split; assumption.
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    exists U5.
    split. destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
    intros.
      assert (U3Hyp': forall b ofs, U3 b ofs = true -> vis mu23 b = true).
         intros. eapply (UHyp b0 ofs0).  rewrite H2; trivial.
      clear UHyp.
      destruct (MOD32 U3Hyp' _ _ Ub). split; trivial.
      intros. destruct (H3 H4) as [b1 [d D]].
      exists b1, d. rewrite orb_false_r. apply D.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [U4 [U3 [Step2 [StepN2 HU]]]]]]. subst x'.
    destruct (eff_diagram23 _ _ _ _ _ Step2 _ _ _ _ MC23)
      as [c3' [m3' [d23' [mu23' [InjInc23
             [GSEP [LocAlloc23 [MC23' [U5 [Steps3 MOD32]]]]]]]]]]; clear eff_diagram23.
    assert (pubSrc23: pubBlocksSrc mu23 = pubBlocksSrc mu23') by eapply InjInc23.
    assert (frgnSrc23: frgnBlocksSrc mu23 = frgnBlocksSrc mu23') by eapply InjInc23.
    assert (XX1: forall b : block, pubTgt12' b = true -> pubBlocksSrc mu23' b = true).
       rewrite pubSrc23 in *. assumption.
    assert (XX2: forall b : block, frgnTgt12' b = true -> frgnBlocksSrc mu23' b = true).
       rewrite frgnSrc23 in *. assumption.
    assert (FWD2: mem_forward m2 m2').
        eapply effstep_fwd; eassumption.
    assert (FWD2': mem_forward m2' m2'').
        eapply effstepN_fwd; eassumption.
    assert (FWD3: mem_forward m3 m3').
        destruct Steps3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
   destruct (IHx _ mu23' d23' _ _ c3' m3' StepN2 MC23' XX1 XX2)
        as [c3'' [m3'' [d23'' [mu23'' [ZZ [InjIncr'
             [GSEP' [LocAlloc23' [MC23'' [U3' [StepN3 MOD32']]]]]]]]]]]; clear IHx.
    assert (FWD3': mem_forward m3' m3'').
        destruct StepN3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    exists c3''. exists m3''. exists d23''. exists mu23''.
    split. clear StepN3 Steps3 MOD32' MOD32.
           rewrite pubSrc23 in *; clear pubSrc23.
           rewrite frgnSrc23 in *; clear frgnSrc23.
           destruct ZZ as [ZZa' [ZZb' [ZZc' ZZd']]].
           rewrite <- ZZa' in *.
           rewrite <- ZZb' in *. clear ZZa' ZZb'.
           destruct mu23; destruct mu23'.
           destruct LocAlloc23 as [LA23a [LA23b [LA23c LA23d]]].
           simpl in *. subst; simpl in *. destruct mu23''.
           destruct LocAlloc23' as [LA23'a [LA23'b [LA23'c LA23'd]]].
           simpl in *. subst; simpl in *. intuition.
           extensionality b.
                  rewrite <- orb_assoc.
                  rewrite freshloc_trans; trivial.
    split. solve [eapply intern_incr_trans; eassumption].
    (*split. eapply intern_separated_incr_fwd2; try eassumption.
           eauto.  *)
    split.
      (*Lemma gsep_trans:
    forall {F V} (ge:  Genv.t F V) mu12 mu12' mu12'',
      globals_separate ge mu12 mu12' ->
      globals_separate ge mu12' mu12'' ->
      globals_separate ge mu12 mu12''.
    ad_it.
      Qed.*)
    assert (INCR: inject_incr (as_inj mu23') (as_inj mu23'')).
    { apply intern_incr_as_inj; auto. eapply match_sm_wd23; eauto. }
    eapply (gsep_trans _ mu23 mu23' mu23''); eauto.
    split. eapply sm_locally_allocated_trans; eassumption.
    split. apply MC23''.
    exists (fun b z => U5 b z || (U3' b z && valid_block_dec m3 b)).
    split. clear MOD32 MOD32' ZZ.
           destruct Steps3; destruct StepN3.
           (*1/4*)
              left. eapply effstep_plus_trans; eassumption.
           (*2/4*)
              left. destruct H0 as [EFF3 CT].
              eapply effstep_plus_star_trans; eassumption.
           (*3/4*)
               left. destruct H as [EFF3 CORD].
               eapply effstep_star_plus_trans; eassumption.
           (*4/4*)
               right. destruct H as [EFF3 CORD].
                      destruct H0 as [EFF3' CT].
               split. eapply effstep_star_trans; eassumption.
               eapply t_trans.
                 apply CT. clear CT.
                 apply t_step.
                 constructor 2. apply CORD.
    (*MOD32-clause*) subst U2. intros U4Hyp b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
        assert (U4Hyp': forall b ofs,
            U4 b ofs = true -> vis mu23 b = true).
          clear - U4Hyp. intros. apply (U4Hyp b ofs). rewrite H; trivial.
        destruct (MOD32 U4Hyp' _ _ H). split; trivial.
        intros. destruct (H1 H2) as [b1 [d1 [Frg [HU4 Perm2]]]].
        exists b1, d1. rewrite HU4; simpl.
        split; trivial.
        split; trivial.
      apply andb_true_iff in H. destruct H.
         destruct (valid_block_dec m3 b3); try inv H0.
         assert (U3Hyp: forall b ofs,
            U3 b ofs = true -> vis mu23' b = true).
           clear H. intros.
           assert (U3valid:= effstepN_valid _ _ _ _ _ _ _ _ StepN2 _ _ H).
           clear Steps3 MOD32 MOD32' StepN3 ZZ. subst.
           assert (LB23': locBlocksSrc mu23' =
                (fun b => locBlocksSrc mu23 b || freshloc m2 m2' b)).
             apply sm_locally_allocatedChar in LocAlloc23. eapply LocAlloc23.
           specialize (U4Hyp b ofs0).
           destruct (valid_block_dec m2 b).
             eapply (intern_incr_vis _ _ InjInc23).
             apply U4Hyp. rewrite H; simpl. intuition.
           unfold vis. rewrite LB23'; clear LB23'.
             assert (FL: freshloc m2 m2' b = true).
               eapply freshloc_charT. split; trivial.
             rewrite FL.  intuition.
         destruct (MOD32' U3Hyp _ _ H) as [VIS23' UHyp32'];
             clear MOD32' StepN3.
         split. unfold visTgt. unfold visTgt in VIS23'.
                assert (FF: frgnBlocksTgt mu23 = frgnBlocksTgt mu23') by eapply InjInc23.
                rewrite FF. clear FF.
                assert (locBlocksTgt mu23' = (fun b => locBlocksTgt mu23 b || freshloc m3 m3' b)).
                   apply sm_locally_allocatedChar in LocAlloc23. eapply LocAlloc23.
                rewrite H0 in VIS23'; clear UHyp32' H0.
                unfold freshloc in VIS23'. destruct (valid_block_dec m3 b3); try contradiction.
                simpl in *. rewrite andb_false_r, orb_false_r in VIS23'. assumption.
         intros. remember (locBlocksTgt mu23' b3) as d.
                 destruct d; apply eq_sym in Heqd.
                   apply sm_locally_allocatedChar in LocAlloc23.
                   destruct LocAlloc23 as [AA [BB [CC [DD [EE FF]]]]].
                   rewrite DD, H0 in Heqd. simpl in Heqd.
                   apply freshloc_charT in Heqd. destruct Heqd; contradiction.
                 destruct (UHyp32' (eq_refl _)) as [b2 [d2 [F23' [UU Perm2']]]]; clear UHyp32'.
                   exists b2, d2.
                   rewrite <- (intern_incr_foreign _ _ InjInc23) in F23'.
                   split; trivial.
                   rewrite UU. simpl.
                   assert (Mem.valid_block m2 b2).
                     apply (match_validblock23 _ _ _ _ _ _ MC23).
                       eapply foreign_DomRng. eauto. apply F23'.
                   destruct (valid_block_dec m2 b2); simpl.
                   split. intuition.
                      apply FWD2; assumption.
                   contradiction.
  (*case 2*)
   inv CS2.
   apply sm_locally_allocatedChar in LocAlloc12.
   exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_sm mu12' mu23).
   destruct INV as [INVa [INVb [INVc INVd]]]. subst.
   split. eapply compose_sm_intern_incr; eauto.
           apply intern_incr_refl.
   (*split. eapply compose_sm_intern_separated; eauto.
            apply intern_incr_refl.
            apply sm_inject_separated_same_sminj.     *)
           split.

(*The following deserves its own lemma*)

{ apply (gsep_domain_eq _ _ g2 g3); try assumption.
  assert (WD12: SM_wd mu12) by (eapply match_sm_wd12; eauto).
  assert (WD23: SM_wd mu23) by (eapply match_sm_wd23; eauto).
  assert (WD12': SM_wd mu12') by (eapply match_sm_wd12; eauto).
    assert (pglobals: meminj_preserves_globals g2 (extern_of mu23)).
    eapply match_genv23; eauto.
  assert (INCR: Values.inject_incr (as_inj mu12) (as_inj mu12')) by (eapply intern_incr_as_inj; eauto).
  assert (GLUE: (locBlocksTgt mu12 = locBlocksSrc mu23 /\
           extBlocksTgt mu12 = extBlocksSrc mu23))
    by (split; auto).
    assert (gsep12: globals_separate g2 mu12 mu12') by assumption.
    assert (gsep23: globals_separate g2 mu23 mu23) by apply gsep_refl.
    intros  b1 b3 d3 map13 map13'.

  destruct (compose_sm_as_injD _ _ _ _ _ map13' WD12' WD23) as [b2 [d1 [d2 [map12 [map23 extra]]]]].
  destruct (compose_sm_as_injD_None _ _ _ WD12 WD23 GLUE map13) as [map12'| [b2' [d [map12' map23']]]].

  - assert (isGlobalBlock g2 b2 = false).
    eapply gsep12; eauto.
    destruct (isGlobalBlock g2 b3) eqn:isglob; [ | reflexivity].
    apply (meminj_preserves_globals_isGlobalBlock _ _ pglobals) in isglob.
    apply WD23 in isglob. destruct isglob as [extS extT].
    rewrite <- (as_inj_extBlocks _ _ _ _ WD23 map23) in extT.
    destruct GLUE as [GLUEloc GLUEext].
    rewrite <- GLUEext in extT.
    apply as_injD_None in map12'. destruct map12' as [extmap12 locmap12].
    rewrite (intern_incr_extern _ _ InjIncr12) in extmap12.
    rewrite (intern_incr_extBlocksTgt _ _ InjIncr12) in extT.
    unfold as_inj, join in map12. rewrite extmap12 in map12.
    apply WD12' in map12.
    destruct map12 as [locS locT].
    destruct WD12' as [disj_src disj_tgt _].
    destruct (disj_tgt b2) as [theFalse | theFalse];
    rewrite theFalse in * ; discriminate.
  - assert (HH:as_inj mu12' b1 = Some (b2', d))
      by (eapply INCR; auto).
    rewrite HH in map12; inversion map12; subst.
    eapply gsep23; eauto. }

   split.
   clear eff_diagram23.
     apply sm_locally_allocatedChar; simpl.
     split. apply LocAlloc12.
     split. extensionality b. rewrite freshloc_irrefl.
            rewrite orb_false_r. trivial.
     split. apply LocAlloc12.
     split. extensionality b. rewrite freshloc_irrefl.
            rewrite orb_false_r. trivial.
     intuition.
   split. exists st2'. exists m2'. exists mu12'. exists mu23.
       destruct LocAlloc12 as [LA1 [LA2 [LA3 [LA4 [LA5 LA6]]]]].
       intuition.
       rewrite LA4, INVa.
         extensionality b.
         rewrite freshloc_irrefl. apply orb_false_r.
       rewrite LA6. assumption.
       assert (pubBlocksTgt mu12 = pubBlocksTgt mu12') by eapply InjIncr12.
              rewrite <- H0 in *; clear H0.
              apply INVc. trivial.
       assert (frgnBlocksTgt mu12 = frgnBlocksTgt mu12') by eapply InjIncr12.
              rewrite H0 in *; clear H0.
              apply INVd. trivial.
    (*{ clear - pure InjIncr12.
       unfold pure_comp_ext, pure_composition, pure_composition_locat, pure_composition_block,
       replace_locals, DomSrc, exportedSrc, sharedSrc, shared_of,
       intern_incr in *;
         destruct mu12', mu12, mu23; simpl in *.
       destruct InjIncr12 as [injincr12 [exteq12 ?]].
       clear - pure exteq12.
       rewrite <- exteq12.
       destruct pure.
       split.
       + intros.
         ad_it.
       + apply H0.
     }*)
    (* Full HERE *)
    { apply intern_incr_extern in InjIncr12.
      unfold full_ext, full_comp.
      rewrite <- InjIncr12.
      exact full.
    }
    exists (fun b z => false).
    split. right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
    intros. inv Ub.
Qed.
End CoreDiagrams_trans.
*)