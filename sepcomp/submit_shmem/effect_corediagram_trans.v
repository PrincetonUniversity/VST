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
Require Import effect_semantics.

Require Import sepcomp.StructuredInjections.
Require Import effect_simulations.
Require Import effect_simulations_lemmas.
Require Import effect_properties.
Require Import sepcomp.forward_simulations_trans.
Require Import Wellfounded.
Require Import Relations.

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

Lemma core_diagram_trans: forall
(core_data12 : Type)
(match_core12 : core_data12 -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Injection)
                   (m2 : mem),
                 match_core12 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C2) (m2' : mem) (cd' : core_data12) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core12 cd' mu' st1' m1' st2' m2' /\
                   (*temporarily added:*) SM_wd mu' /\ sm_valid mu' m1' m2' /\
                   (corestep_plus Sem2 g2 st2 m2 st2' m2' \/
                    corestep_star Sem2 g2 st2 m2 st2' m2' /\
                    core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Injection)
                   (m2 : mem),
                 match_core23 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core23 cd' mu' st1' m1' st2' m2' /\
                   (*temporarily added:*) SM_wd mu' /\ sm_valid mu' m1' m2' /\
                   (corestep_plus Sem3 g3 st2 m2 st2' m2' \/
                    corestep_star Sem3 g3 st2 m2 st2' m2' /\
                    core_ord23 cd' cd))
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
  (CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
(MC23 : match_core23 d23 mu23 st2 m2 st3 m3),
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Injection),
  intern_incr (compose_sm mu12 mu23) mu' /\
  sm_inject_separated (compose_sm mu12 mu23) mu' m1 m3 /\
  sm_locally_allocated (compose_sm mu12 mu23) mu' m1 m3 m1' m2' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists
     (c0 : C2) (m0 : mem) (mu1 mu2 : SM_Injection),
     X = Some c0 /\
     mu' = compose_sm mu1 mu2 /\
     (locBlocksTgt mu1 = locBlocksSrc mu2 /\
      extBlocksTgt mu1 = extBlocksSrc mu2 /\
      (forall b : block,
       pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
      (forall b : block,
       frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\
     match_core12 d1 mu1 st1' m1' c0 m0 /\ match_core23 d2 mu2 c0 m0 st2' m2') /\
  (*temporarily added:*) SM_wd mu' /\ sm_valid mu' m1' m2' /\
  (corestep_plus Sem3 g3 st3 m3 st2' m2' \/
   corestep_star Sem3 g3 st3 m3 st2' m2' /\
   clos_trans
     (core_data12 * option C2 * core_data23)
     (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
     (d12, Some st2, d23)).
Proof.
  intros.
  destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [mu12' [InjIncr12 [InjSep12 [LocAlloc12
       [MC12' [WD12' [SMVal12' Y]]]]]]]]]]; clear core_diagram12.
  assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
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
    sm_inject_separated mu23 mu23' m2 m3 /\
    sm_locally_allocated mu23 mu23' m2 m3 m2' m3' /\
    match_core23 d23' mu23' st2' m2' st3' m3' /\
   (*temporarily added:*) SM_wd mu23' /\ sm_valid mu23' m2' m3' /\
    (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some st2', d23')
               (d12, Some st2, d23)))).
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [INV' [InjIncr23 [InjSep23
          (*[PUB13*) [LocAlloc23 [MC23' [WD23' [SMVal23' ZZ]]]]]]]]]]].
  exists st3'. exists m3'.
  exists (d12', Some st2', d23').
  exists (compose_sm mu12' mu23').
  split. solve [eapply compose_sm_intern_incr; eauto].
  destruct INV as [INVa [INVb [INVc INVd]]]; subst.
  split. solve [eapply compose_sm_intern_separated; eauto].
  split. clear ZZ. unfold compose_sm; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; simpl. eapply LocAlloc12.
         split; simpl. eapply LocAlloc23.
         split; simpl. eapply LocAlloc12. eapply LocAlloc23.
  split. exists st2', m2', mu12', mu23'.
     split. reflexivity.
     split; trivial.
     split. clear ZZ.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; trivial.
         split; trivial.
         split; assumption.
     split; assumption.
  split. eapply (compose_sm_wd _ _ WD12' WD23').
         eapply INV'. eapply INV'.
  split. eapply (compose_sm_valid _ _ _ _ _ _ SMVal12' SMVal23').
  simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         simpl in *. destruct LocAlloc12 as [? [? [? ?]]]. subst.
         simpl in *. destruct LocAlloc23 as [? [? [? ?]]]. subst.
         simpl in *. apply ZZ.

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
  clear MC12 InjIncr12 InjSep12 MC12' match_sm_wd12 match_validblock12 (*MatchHyp12*).
  clear LocAlloc12.
  destruct INV as [? [? [? ?]]].
  rewrite H0 in *. clear H0.
  rewrite H1 in *. clear H1.
  subst.
  rewrite pubAlloc12' in *; clear pubAlloc12'.
  rewrite frgnAlloc12' in *; clear frgnAlloc12'.
  clear st1 m1 st1' m1' SMVal12'.
  clear mu12.
  remember (pubBlocksTgt mu12') as pubTgt12'.
  remember (frgnBlocksTgt mu12') as frgnTgt12'.
  clear HeqpubTgt12' HeqfrgnTgt12'.
  clear mu12' WD12'.
  clear C1 Sem1 match_core12 g1.
  rename H2 into HypPubTgt12'.
  rename H3 into HypFrgnTgt12'.
  revert mu23 d23 st2 m2 st3 m3 H MC23 HypPubTgt12' HypFrgnTgt12'.
  induction x; intros.
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [? ?]]].
    inv H0.
    destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23)
      as [st3' [m3' [d23' [mu23' [InjInc23 [InjSep23
          [LocAlloc23 [? [WD23' [SMVal23' ?]]]]]]]]]]; clear core_diagram23.
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
    split; trivial.
    split; trivial.
    destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st2'' [m2'' [? ?]]]. subst x'.
    destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23)
      as [c3' [m3' [d23' [mu23' [InjInc23 [InjSep23
             [LocAlloc23 [? [WD23' [SMVal23' ?]]]]]]]]]]; clear core_diagram23.
    specialize (IHx mu23' d23' _ _ c3' m3' H0 H1).
    assert (pubSrc23: pubBlocksSrc mu23 = pubBlocksSrc mu23') by eapply InjInc23.
    assert (frgnSrc23: frgnBlocksSrc mu23 = frgnBlocksSrc mu23') by eapply InjInc23.
    destruct IHx as [c3'' [m3'' [d23'' [mu23'' [ZZ [InjIncr'
             [InjSep' [LocAlloc23' [MC' [WD23'' [SMVal23'' XX]]]]]]]]]]].
      rewrite pubSrc23 in *. assumption.
      rewrite frgnSrc23 in *. assumption.
    assert (FWD2: mem_forward m2 m2'').
        eapply corestep_fwd; eassumption.
    assert (FWD2': mem_forward m2'' m2').
        eapply corestepN_fwd; eassumption.
    assert (FWD3: mem_forward m3 m3').
        destruct H2 as [[n K] | [[n K] _]];
             eapply corestepN_fwd; eassumption.
    assert (FWD3': mem_forward m3' m3'').
        destruct XX as [[n K] | [[n K] _]];
             eapply corestepN_fwd; eassumption.
    exists c3''. exists m3''. exists d23''. exists mu23''.
    split. clear XX H1 H2 H0.
           rewrite pubSrc23 in *; clear pubSrc23.
           rewrite frgnSrc23 in *; clear frgnSrc23.
           destruct ZZ as [ZZa' [ZZb' [ZZc' ZZd']]].
           rewrite <- ZZa' in *.
           rewrite <- ZZb' in *.
           destruct mu23; destruct mu23'.
           destruct LocAlloc23 as [LA23a [LA23b [LA23c LA23d]]].
           simpl in *. subst; simpl in *. destruct mu23''.
           destruct LocAlloc23' as [LA23'a [LA23'b [LA23'c LA23'd]]].
           simpl in *. subst; simpl in *. intuition.
           extensionality b.
                  rewrite <- orb_assoc.
                  rewrite freshloc_trans; trivial.
    split. solve [eapply intern_incr_trans; eassumption].
    split. eapply intern_separated_incr_fwd2; try eassumption.
           eauto.
    split. eapply sm_locally_allocated_trans; eassumption.
    split. apply MC'.
    split; trivial.
    split; trivial.
    destruct H2; destruct XX.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*4/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
               eapply t_trans.
                 apply H5. clear H5.
                 apply t_step.
                 constructor 2. apply H4.
  (*case 2*)
   inv CS2.
   apply sm_locally_allocatedChar in LocAlloc12.
   exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_sm mu12' mu23).
   destruct INV as [INVa [INVb [INVc INVd]]]. subst.
   split. eapply compose_sm_intern_incr; eauto.
           apply intern_incr_refl.
   split. eapply compose_sm_intern_separated; eauto.
            apply intern_incr_refl.
            apply sm_inject_separated_same_sminj.
   split.
     clear core_diagram23.
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
   split. eapply compose_sm_wd.
                   assumption.
                   eauto.
                   assert (TGT: pubBlocksTgt mu12 = pubBlocksTgt mu12') by eapply InjIncr12.
                     rewrite <- TGT. assumption.
                   assert (TGT: frgnBlocksTgt mu12 = frgnBlocksTgt mu12') by eapply InjIncr12.
                     rewrite <- TGT. assumption.
   split. eapply compose_sm_valid. eassumption.  eauto. (*USE of match_WD is ok*)
   right. split. exists O. simpl; auto.
   apply t_step. constructor 1; auto.
Qed.

(*Not used - proof that the first preliminary version of effcore_diagram is transitive*)
Goal (*Lemma effdiagram_injinj:*) forall
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
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core12 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\
                        core_ord12 cd' cd))
                    /\ forall b ofs, U2 b ofs = true ->
                         (Mem.valid_block m2 b /\
                           (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true))))
(core_data23 : Type)
(match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(eff_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Injection)
                   (m2 : mem),
                 match_core23 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core23 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\
                        core_ord23 cd' cd))
                    /\ forall b ofs, U2 b ofs = true ->
                         (Mem.valid_block m2 b /\
                           (locBlocksTgt mu b = false->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true))))
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
  (MC23 : match_core23 d23 mu23 st2 m2 st3 m3),
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Injection),
  intern_incr (compose_sm mu12 mu23) mu' /\
  sm_inject_separated (compose_sm mu12 mu23) mu' m1 m3 /\
  sm_locally_allocated (compose_sm mu12 mu23) mu' m1 m3 m1' m2' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists
     (c0 : C2) (m0 : mem) (mu1 mu2 : SM_Injection),
     X = Some c0 /\
     mu' = compose_sm mu1 mu2 /\
     (locBlocksTgt mu1 = locBlocksSrc mu2 /\
      extBlocksTgt mu1 = extBlocksSrc mu2 /\
      (forall b : block,
       pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
      (forall b : block,
       frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\
     match_core12 d1 mu1 st1' m1' c0 m0 /\ match_core23 d2 mu2 c0 m0 st2' m2') /\
  (exists U3 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U3 st3 m3 st2' m2' \/
      effstep_star Sem3 g3 U3 st3 m3 st2' m2' /\
      clos_trans
        (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
        (d12, Some st2, d23)) /\
    (forall b ofs, U3 b ofs = true ->
     (Mem.valid_block m3 b /\
      (locBlocksTgt (compose_sm mu12 mu23) b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of (compose_sm mu12 mu23) b1 = Some (b, delta1) /\
         Mem.valid_block m1 b1 /\ U1 b1 (ofs - delta1) = true)))).
Proof.
  intros.
  destruct (eff_diagram12 _ _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [mu12' [InjIncr12 [InjSep12 [LocAlloc12
       [MC12' [U2 [Y MOD21]]]]]]]]]]; clear eff_diagram12.
  assert (ZZ: effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
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
    sm_inject_separated mu23 mu23' m2 m3 /\
    sm_locally_allocated mu23 mu23' m2 m3 m2' m3' /\
    match_core23 d23' mu23' st2' m2' st3' m3' /\
    (exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some st2', d23')
        (d12, Some st2, d23)))
    /\ forall b ofs, U3 b ofs = true ->
        (Mem.valid_block m3 b /\
           (locBlocksTgt mu23 b = false ->
           exists b2 delta2, foreign_of mu23 b2 = Some(b,delta2) /\
               Mem.valid_block m2 b2 /\ U2 b2 (ofs-delta2) = true)))).
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [INV' [InjIncr23 [InjSep23
          (*[PUB13*) [LocAlloc23 [MC23' [U3 [ZZ MOD32]]]]]]]]]]].
  exists st3'. exists m3'.
  exists (d12', Some st2', d23').
  exists (compose_sm mu12' mu23').
  split. solve [eapply compose_sm_intern_incr; eauto].
  destruct INV as [INVa [INVb [INVc INVd]]]; subst.
  split. solve [eapply compose_sm_intern_separated; eauto].
  split. clear ZZ. unfold compose_sm; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; simpl. eapply LocAlloc12.
         split; simpl. eapply LocAlloc23.
         split; simpl. eapply LocAlloc12. eapply LocAlloc23.
  split. exists st2', m2', mu12', mu23'.
     split. reflexivity.
     split; trivial.
     split. clear ZZ.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; trivial.
         split; trivial.
         split; assumption.
     split; assumption.
  exists U3.
  split; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         simpl in *. destruct LocAlloc12 as [? [? [? ?]]]. subst.
         simpl in *. destruct LocAlloc23 as [? [? [? ?]]]. clear H2. subst.
         simpl in *. apply ZZ.
    (*proof of MOD31*) intros b3 ofs HypU3. clear ZZ eff_diagram23.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         destruct (MOD32 _ _ HypU3) as [vb3 Uhyp32]; clear MOD32.
         split; trivial.
         intros.
         destruct (Uhyp32 H0) as [b2 [d2 [Frg2 [VB2 HypU2]]]]; clear Uhyp32.
         destruct (MOD21 _ _ HypU2) as [vb2 Uhyp21]; clear MOD21.
         rewrite INVa in Uhyp21; clear INVa.
         destruct Uhyp21 as [b1 [d1 [Frg1 [vb1 HypU1]]]].
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
  clear MC12 InjIncr12 InjSep12 MC12' match_sm_wd12 match_validblock12 (*MatchHyp12*).
  clear LocAlloc12.
  destruct INV as [? [? [? ?]]].
  rewrite H0 in *. clear H0.
  rewrite H1 in *. clear H1.
  subst.
  (*assert (UV2: forall b z, U2 b z = true -> Mem.valid_block m2 b). apply MOD21.*)
  clear st1 m1 st1' m1' MOD21.
  rewrite pubAlloc12' in *; clear pubAlloc12'.
  rewrite frgnAlloc12' in *; clear frgnAlloc12'.
  clear mu12.
  remember (pubBlocksTgt mu12') as pubTgt12'.
  remember (frgnBlocksTgt mu12') as frgnTgt12'.
  clear HeqpubTgt12' HeqfrgnTgt12'.
  clear mu12'.
  clear C1 Sem1 match_core12 g1.
  rename H2 into HypPubTgt12'.
  rename H3 into HypFrgnTgt12'.

  revert U2 mu23 d23 st2 m2 st3 m3 H MC23 HypPubTgt12' HypFrgnTgt12'.
  induction x; intros.
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [? ?]]].
    inv H0.
    destruct (eff_diagram23 _ _ _ _ _ H _ _ _ _ MC23)
      as [st3' [m3' [d23' [mu23' [InjInc23 [InjSep23
          [LocAlloc23 [? [U3 [? MOD32]]]]]]]]]]; clear eff_diagram23.
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
    exists U3.
    split. destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
    apply MOD32.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [Step2 StepN2]]]. subst x'.
    destruct (eff_diagram23 _ _ _ _ _ Step2 _ _ _ _ MC23)
      as [c3' [m3' [d23' [mu23' [InjInc23 [InjSep23
             [LocAlloc23 [MC23' [U3 [Steps3 MOD32]]]]]]]]]]; clear eff_diagram23.
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
             [InjSep' [LocAlloc23' [MC23'' [U3' [StepN3 MOD32']]]]]]]]]]]; clear IHx.
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
    split. eapply intern_separated_incr_fwd2; try eassumption.
           eauto.
    split. eapply sm_locally_allocated_trans; eassumption.
    split. apply MC23''.
    exists (fun b z => U3 b z || (U3' b z && valid_block_dec m3 b)).
    assert (Union1: forall b z, Mem.valid_block m3' b -> U3' b z = true -> (U3 b z || (U3' b z && valid_block_dec m3 b) || freshloc m3 m3' b) = true).
      intros. case_eq (U3 b z); simpl; intros; trivial. rewrite H0; simpl.
        apply orb_true_iff. unfold freshloc.
        destruct (valid_block_dec m3 b); simpl. left; trivial. right.
        destruct (valid_block_dec m3' b); simpl. trivial. contradiction.
    assert (Union2: forall b z, Mem.valid_block m3 b -> U3 b z = true -> (U3 b z || (U3' b z && valid_block_dec m3 b)) = true).
      intros. rewrite H0. trivial.
    split. clear MOD32 MOD32' ZZ.
           destruct Steps3; destruct StepN3.
           (*1/4*)
              left. destruct H as [n1 StepA]. destruct H0 as [n2 StepB].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite effstepN_add.
                      exists c3', m3'.
                      split; eapply effstepN_sub_val; try eassumption.
           (*2/4*)
               destruct H0 as [EFF3 CT].
               left. destruct H as [n1 StepA]. destruct EFF3 as [n2 StepB].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
          (*3/4*)
               left. destruct H as [EFF3 CORD].
                       destruct EFF3 as [n1 StepA]. destruct H0 as [n2 StepB].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
           (*4/4*)
               right. destruct H as [EFF3 CORD].
               destruct H0 as [EFF3' CT].
               split. destruct EFF3 as [n1 StepA]. destruct EFF3' as [n2 StepB].
                      exists (n1 + n2)%nat.
                      rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
               eapply t_trans.
                 apply CT. clear CT.
                 apply t_step.
                 constructor 2. apply CORD.
    (*MOD32-clause*) intros b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
        apply MOD32. apply H.
      apply andb_true_iff in H. destruct H.
         destruct (valid_block_dec m3 b3); try inv H0.
         split; trivial.
         destruct (MOD32' _ _ H) as [vb3' UHyp32']; clear MOD32' StepN3.
         intros. remember (locBlocksTgt mu23' b3) as d.
                 destruct d; apply eq_sym in Heqd.
                   apply sm_locally_allocatedChar in LocAlloc23.
                   destruct LocAlloc23 as [AA [BB [CC [DD [EE FF]]]]].
                   rewrite DD, H0 in Heqd. simpl in Heqd.
                   apply freshloc_charT in Heqd. destruct Heqd; contradiction.
                 destruct (UHyp32' (eq_refl _)) as [b2 [d2 [F23' [vb2' UU]]]]; clear UHyp32'.
                   exists b2, d2.
                   rewrite <- (intern_incr_foreign _ _ InjInc23) in F23'.
                   split; trivial.
                   assert (Mem.valid_block m2 b2).
                     apply (match_validblock23 _ _ _ _ _ _ MC23).
                       eapply foreign_DomRng. eauto. apply F23'.
                   split; trivial.
                   apply orb_true_iff in UU.
                   destruct UU; trivial.
                   apply freshloc_charT in H2. destruct H2; contradiction.
  (*case 2*)
   inv CS2.
   apply sm_locally_allocatedChar in LocAlloc12.
   exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_sm mu12' mu23).
   destruct INV as [INVa [INVb [INVc INVd]]]. subst.
   split. eapply compose_sm_intern_incr; eauto.
           apply intern_incr_refl.
   split. eapply compose_sm_intern_separated; eauto.
            apply intern_incr_refl.
            apply sm_inject_separated_same_sminj.
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
   exists (fun b z => false).
     split. right. split. exists O. simpl; auto.
            apply t_step. constructor 1; auto.
     intros. inv H.
Qed.

(*not used - proof that the second preliminary version of effcore_diagram is transitive*)
Goal (*Lemma effdiagram_strong_injinj:*) forall
(core_data12 : Type)
(match_core12 : core_data12 -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(eff_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Injection)
                   (m2 : mem),
                 (forall b ofs, U1 b ofs = true -> vis mu b = true) ->
                 match_core12 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C2) (m2' : mem) (cd' : core_data12) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core12 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\
                        core_ord12 cd' cd))
                    (*/\ (forall b ofs, U2 b ofs = true -> Mem.valid_block m2 b)*)
                    /\ (forall b ofs, U2 b ofs = true ->
                           (Mem.valid_block m2 b /\
                           (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true)))) )
(core_data23 : Type)
(match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(eff_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Injection)
                   (m2 : mem),
                 (forall b ofs, U1 b ofs = true -> vis mu b = true) ->
                 match_core23 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core23 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\
                        core_ord23 cd' cd))
                    /\ (forall b ofs, U2 b ofs = true ->
                          (Mem.valid_block m2 b /\
                           (locBlocksTgt mu b = false->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true)))))
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
  (UHyp : forall b ofs, U1 b ofs = true -> vis (compose_sm mu12 mu23) b = true),
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Injection),
  intern_incr (compose_sm mu12 mu23) mu' /\
  sm_inject_separated (compose_sm mu12 mu23) mu' m1 m3 /\
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
     match_core12 d1 mu1 st1' m1' c0 m0 /\ match_core23 d2 mu2 c0 m0 st2' m2') /\
  (exists U3 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U3 st3 m3 st2' m2' \/
      effstep_star Sem3 g3 U3 st3 m3 st2' m2' /\
      clos_trans
        (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
        (d12, Some st2, d23))
    /\ (forall b ofs, U3 b ofs = true ->
         (Mem.valid_block m3 b /\
      (locBlocksTgt (compose_sm mu12 mu23) b = false ->
      exists (b1 : block) (delta1 : Z),
        foreign_of (compose_sm mu12 mu23) b1 = Some (b, delta1) /\
        U1 b1 (ofs - delta1) = true)))).
Proof.
  intros. rewrite vis_compose_sm in UHyp. simpl in UHyp.
  intros.
  destruct (eff_diagram12 _ _ _ _ _ CS1 _ _ _ _ UHyp MC12)
    as [st2' [m2' [d12' [mu12' [InjIncr12 [InjSep12 [LocAlloc12
       [MC12' [U2 [Y MOD21]]]]]]]]]]; clear eff_diagram12.
  assert (ZZ: effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
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
    sm_inject_separated mu23 mu23' m2 m3 /\
    sm_locally_allocated mu23 mu23' m2 m3 m2' m3' /\
    match_core23 d23' mu23' st2' m2' st3' m3' /\
    (exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some st2', d23')
        (d12, Some st2,d23)))
    /\ forall b ofs, U3 b ofs = true ->
        (Mem.valid_block m3 b /\
           (locBlocksTgt mu23 b = false ->
           exists b2 delta2, foreign_of mu23 b2 = Some(b,delta2) /\
               U2 b2 (ofs-delta2) = true)))).
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [INV' [InjIncr23 [InjSep23
          (*[PUB13*) [LocAlloc23 [MC23' [U3 [ZZ MOD32]]]]]]]]]]].
  exists st3'. exists m3'.
  exists (d12', Some st2', d23').
  exists (compose_sm mu12' mu23').
  split. solve [eapply compose_sm_intern_incr; eauto].
  destruct INV as [INVa [INVb [INVc INVd]]]; subst.
  split. solve [eapply compose_sm_intern_separated; eauto].
  split. clear ZZ. unfold compose_sm; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; simpl. eapply LocAlloc12.
         split; simpl. eapply LocAlloc23.
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
     split; assumption.
  exists U3.
  split; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *. apply ZZ.
    (*proof of MOD31*) intros b3 ofs HypU3. clear ZZ eff_diagram23.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         destruct (MOD32 _ _ HypU3) as [vb3 Uhyp32]; clear MOD32.
         split; trivial.
         intros.
         destruct (Uhyp32 H0) as [b2 [d2 [Frg2 HypU2]]]; clear Uhyp32.
         destruct (MOD21 _ _ HypU2) as [vb2 Uhyp21]; clear MOD21.
         rewrite INVa in Uhyp21; clear INVa.
         destruct Uhyp21 as [b1 [d1 [Frg1 HypU1]]].
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
  (*proof of the cut*)
  assert (locLocAlloc12': locBlocksTgt mu12' =
                         fun b => orb (locBlocksTgt mu12 b) (freshloc m2 m2' b)).
         destruct mu12; destruct mu12'; simpl in *. subst.
         eapply LocAlloc12.
  assert (extLocAlloc12': extBlocksTgt mu12' =extBlocksTgt mu12).
         destruct mu12; destruct mu12'; simpl in *. subst.
         eapply LocAlloc12.
  assert (pubAlloc12': pubBlocksTgt mu12 = pubBlocksTgt mu12').
         eapply InjIncr12.
  assert (frgnAlloc12': frgnBlocksTgt mu12 = frgnBlocksTgt mu12').
         eapply InjIncr12.

  rewrite locLocAlloc12', extLocAlloc12' in *. clear locLocAlloc12' extLocAlloc12'.
  destruct INV as [? [? [? ?]]].
  rewrite H0 in *. clear H0.
  rewrite H1 in *. clear H1.
  subst.
  assert (UHyp2 : forall b2 z, U2 b2 z = true -> vis mu23 b2 = true).
      intros. unfold vis. destruct (MOD21 _ _ H0).
      remember (locBlocksSrc mu23 b2) as d.
      destruct d; apply eq_sym in Heqd; trivial.
      destruct (H4 (eq_refl _)) as [b1 [d1 [Frg1 HU1]]]; clear H2.
      simpl.
      apply H3.
      eapply (foreign_DomRng _ (match_sm_wd12 _ _ _ _ _ _ MC12) _ _ _ Frg1).
  clear MC12 InjIncr12 InjSep12 MC12' match_sm_wd12 match_validblock12 (*MatchHyp12*).
  clear LocAlloc12 (*FRGN12 mySrcTgt*).
  clear st1 m1 st1' m1' UHyp MOD21.
  rewrite pubAlloc12' in *; clear pubAlloc12'.
  rewrite frgnAlloc12' in *; clear frgnAlloc12'.
  clear mu12.
  remember (pubBlocksTgt mu12') as pubTgt12'.
  remember (frgnBlocksTgt mu12') as frgnTgt12'.
  clear HeqpubTgt12' HeqfrgnTgt12'.
  clear mu12'.
  clear C1 Sem1 match_core12 g1.
  rename H2 into HypPubTgt12'.
  rename H3 into HypFrgnTgt12'.
  revert U2 mu23 d23 st2 m2 st3 m3 H MC23 HypPubTgt12' HypFrgnTgt12' UHyp2.
  induction x; intros.
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [? ?]]].
    inv H0.
    destruct (eff_diagram23 _ _ _ _ _ H _ _ _ _ UHyp2 MC23)
      as [st3' [m3' [d23' [mu23' [InjInc23 [InjSep23
          [LocAlloc23 [? [U3 [? MOD32]]]]]]]]]]; clear eff_diagram23.
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
    exists U3.
    split. destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
    apply MOD32.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [Step2 StepN2]]]. subst x'.
    destruct (eff_diagram23 _ _ _ _ _ Step2 _ _ _ _ UHyp2 MC23)
      as [c3' [m3' [d23' [mu23' [InjInc23 [InjSep23
             [LocAlloc23 [MC23' [U3 [Steps3 MOD32]]]]]]]]]]; clear eff_diagram23.
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
    assert (U2'Hyp: forall b2 z, U2 b2 z || freshloc m2 m2' b2 = true ->
                vis mu23' b2 = true).
        intros. clear IHx StepN2.
        apply orb_true_iff in H.
        destruct H. apply UHyp2 in H. eapply intern_incr_vis; eassumption.
        unfold vis.
          assert (locBlocksSrc mu23' = (fun b : block => locBlocksSrc mu23 b || freshloc m2 m2' b)).
                   apply sm_locally_allocatedChar in LocAlloc23. eapply LocAlloc23.
          rewrite H0; clear H0. rewrite H. intuition.

    destruct (IHx _ _ d23' _ _ c3' m3' StepN2 MC23' XX1 XX2 U2'Hyp)
        as [c3'' [m3'' [d23'' [mu23'' [ZZ [InjIncr'
             [InjSep' [LocAlloc23' [MC23'' [U3' [StepN3 MOD32']]]]]]]]]]]; clear IHx.
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
    split. eapply intern_separated_incr_fwd2; try eassumption.
           eauto.
    split. eapply sm_locally_allocated_trans; eassumption.
    split. apply MC23''.
    exists (fun b z => U3 b z || (U3' b z && valid_block_dec m3 b)).
    assert (Union1: forall b z, Mem.valid_block m3' b -> U3' b z = true -> (U3 b z || (U3' b z && valid_block_dec m3 b) || freshloc m3 m3' b) = true).
      intros. case_eq (U3 b z); simpl; intros; trivial. rewrite H0; simpl.
        apply orb_true_iff. unfold freshloc.
        destruct (valid_block_dec m3 b); simpl. left; trivial. right.
        destruct (valid_block_dec m3' b); simpl. trivial. contradiction.
    assert (Union2: forall b z, Mem.valid_block m3 b -> U3 b z = true -> (U3 b z || (U3' b z && valid_block_dec m3 b)) = true).
      intros. rewrite H0. trivial.
    split. clear MOD32 MOD32' ZZ.
           destruct Steps3; destruct StepN3.
           (*1/4*)
              left. destruct H as [n1 StepA]. destruct H0 as [n2 StepB].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite effstepN_add.
                      exists c3', m3'.
                      split; eapply effstepN_sub_val; try eassumption.
           (*2/4*)
               destruct H0 as [EFF3 CT].
               left. destruct H as [n1 StepA]. destruct EFF3 as [n2 StepB].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
          (*3/4*)
               left. destruct H as [EFF3 CORD].
                       destruct EFF3 as [n1 StepA]. destruct H0 as [n2 StepB].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
           (*4/4*)
               right. destruct H as [EFF3 CORD].
               destruct H0 as [EFF3' CT].
               split. destruct EFF3 as [n1 StepA]. destruct EFF3' as [n2 StepB].
                      exists (n1 + n2)%nat.
                      rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
               eapply t_trans.
                 apply CT. clear CT.
                 apply t_step.
                 constructor 2. apply CORD.
    (*MOD32-clause*) intros b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
        apply MOD32. apply H.
      apply andb_true_iff in H. destruct H.
         destruct (valid_block_dec m3 b3); try inv H0.
         split; trivial.
         destruct (MOD32' _ _ H) as [vb3' UHyp32']; clear MOD32' StepN3.
         intros. remember (locBlocksTgt mu23' b3) as d.
                 destruct d; apply eq_sym in Heqd.
                   apply sm_locally_allocatedChar in LocAlloc23.
                   destruct LocAlloc23 as [AA [BB [CC [DD [EE FF]]]]].
                   rewrite DD, H0 in Heqd. simpl in Heqd.
                   apply freshloc_charT in Heqd. destruct Heqd; contradiction.
                 destruct (UHyp32' (eq_refl _)) as [b2 [d2 [F23' UU]]]; clear UHyp32'.
                   exists b2, d2.
                   rewrite <- (intern_incr_foreign _ _ InjInc23) in F23'.
                   split; trivial.
                   assert (Mem.valid_block m2 b2).
                     apply (match_validblock23 _ _ _ _ _ _ MC23).
                       eapply foreign_DomRng. eauto. apply F23'.
                   apply orb_true_iff in UU.
                   destruct UU; trivial.
                   apply freshloc_charT in H2. destruct H2; contradiction.
  (*case 2*)
   inv CS2.
   apply sm_locally_allocatedChar in LocAlloc12.
   exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_sm mu12' mu23).
   destruct INV as [INVa [INVb [INVc INVd]]]. subst.
   split. eapply compose_sm_intern_incr; eauto.
           apply intern_incr_refl.
   split. eapply compose_sm_intern_separated; eauto.
            apply intern_incr_refl.
            apply sm_inject_separated_same_sminj.
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
   exists (fun b z => false).
     split. right. split. exists O. simpl; auto.
            apply t_step. constructor 1; auto.
     intros. inv H.
Qed.

Lemma effcore_diagram_trans: forall
(core_data12 : Type)
(match_core12 : core_data12 -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(eff_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Injection)
                   (m2 : mem),
                 (forall b ofs, U1 b ofs = true -> Mem.valid_block m1 b ->
                                vis mu b = true) ->
                 match_core12 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C2) (m2' : mem) (cd' : core_data12) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core12 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\
                        core_ord12 cd' cd))
                    (*/\ (forall b ofs, U2 b ofs = true -> Mem.valid_block m2 b)*)
                    /\ (forall b ofs, U2 b ofs = true ->
                           (Mem.valid_block m2 b /\
                           (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))) )
(core_data23 : Type)
(match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(eff_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem)
                   (U1 : block -> Z -> bool),
                 effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Injection)
                   (m2 : mem),
                 (forall b ofs, U1 b ofs = true -> Mem.valid_block m1 b ->
                                vis mu b = true) ->
                 match_core23 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core23 cd' mu' st1' m1' st2' m2' /\
                   (exists U2 : block -> Z -> bool,
                      (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                       (effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\
                        core_ord23 cd' cd))
                    /\ (forall b ofs, U2 b ofs = true ->
                          (Mem.valid_block m2 b /\
                           (locBlocksTgt mu b = false->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))))
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
  (UHyp : forall b ofs, U1 b ofs = true -> Mem.valid_block m1 b ->
          vis (compose_sm mu12 mu23) b = true),
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Injection),
  intern_incr (compose_sm mu12 mu23) mu' /\
  sm_inject_separated (compose_sm mu12 mu23) mu' m1 m3 /\
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
     match_core12 d1 mu1 st1' m1' c0 m0 /\ match_core23 d2 mu2 c0 m0 st2' m2') /\
  (exists U3 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U3 st3 m3 st2' m2' \/
      effstep_star Sem3 g3 U3 st3 m3 st2' m2' /\
      clos_trans
        (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
        (d12, Some st2, d23))
    /\ (forall b ofs, U3 b ofs = true ->
         (Mem.valid_block m3 b /\
      (locBlocksTgt (compose_sm mu12 mu23) b = false ->
      exists (b1 : block) (delta1 : Z),
        foreign_of (compose_sm mu12 mu23) b1 = Some (b, delta1) /\
        U1 b1 (ofs - delta1) = true /\
        Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))).
Proof.
  intros. rewrite vis_compose_sm in UHyp. simpl in UHyp.
  intros.
  destruct (eff_diagram12 _ _ _ _ _ CS1 _ _ _ _ UHyp MC12)
    as [st2' [m2' [d12' [mu12' [InjIncr12 [InjSep12 [LocAlloc12
       [MC12' [U2 [Y MOD21]]]]]]]]]]; clear eff_diagram12.
  assert (ZZ: effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
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
    sm_inject_separated mu23 mu23' m2 m3 /\
    sm_locally_allocated mu23 mu23' m2 m3 m2' m3' /\
    match_core23 d23' mu23' st2' m2' st3' m3' /\
    (exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some st2', d23')
        (d12, Some st2,d23)))
    /\ forall b ofs, U3 b ofs = true ->
        (Mem.valid_block m3 b /\
           (locBlocksTgt mu23 b = false ->
           exists b2 delta2, foreign_of mu23 b2 = Some(b,delta2) /\
               U2 b2 (ofs-delta2) = true /\
               Mem.perm m2 b2 (ofs-delta2) Max Nonempty)))).
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [INV' [InjIncr23 [InjSep23
          (*[PUB13*) [LocAlloc23 [MC23' [U3 [ZZ MOD32]]]]]]]]]]].
  exists st3'. exists m3'.
  exists (d12', Some st2', d23').
  exists (compose_sm mu12' mu23').
  split. solve [eapply compose_sm_intern_incr; eauto].
  destruct INV as [INVa [INVb [INVc INVd]]]; subst.
  split. solve [eapply compose_sm_intern_separated; eauto].
  split. clear ZZ. unfold compose_sm; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         split; simpl. eapply LocAlloc12.
         split; simpl. eapply LocAlloc23.
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
     split; assumption.
  exists U3.
  split; simpl.
         destruct mu12. destruct mu12'. destruct mu23. destruct mu23'.
         simpl in *.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *. apply ZZ.
    (*proof of MOD31*) intros b3 ofs HypU3. clear ZZ eff_diagram23.
         destruct INV' as [INVa' [INVb' [INVc' INVd']]].
         subst. simpl in *.
         destruct (MOD32 _ _ HypU3) as [vb3 Uhyp32]; clear MOD32.
         split; trivial.
         intros.
         destruct (Uhyp32 H0) as [b2 [d2 [Frg2 [HypU2 HypPerm2]]]]; clear Uhyp32.
         destruct (MOD21 _ _ HypU2) as [vb2 Uhyp21]; clear MOD21.
         rewrite INVa in Uhyp21; clear INVa.
         destruct Uhyp21 as [b1 [d1 [Frg1 HypU1]]].
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
  destruct INV as [? [? [? ?]]].
  rewrite H0 in *. clear H0.
  rewrite H1 in *. clear H1.
  subst.
  assert (UHyp2 : forall b2 z, U2 b2 z = true -> Mem.valid_block m2 b2 ->
                          vis mu23 b2 = true).
      intros. clear H1. unfold vis.
      destruct (MOD21 _ _ H0).
      remember (locBlocksSrc mu23 b2) as d.
      destruct d; apply eq_sym in Heqd. trivial.
      destruct (H4 (eq_refl _)) as [b1 [d1 [Frg1 HU1]]]; clear H2.
      simpl.
      apply H3.
      eapply (foreign_DomRng _ (match_sm_wd12 _ _ _ _ _ _ MC12) _ _ _ Frg1).
  clear MC12 InjIncr12 InjSep12 MC12' match_sm_wd12 match_validblock12 (*MatchHyp12*).
  clear LocAlloc12 (*FRGN12 mySrcTgt*).
  clear st1 m1 st1' m1' UHyp MOD21.
  rewrite pubAlloc12' in *; clear pubAlloc12'.
  rewrite frgnAlloc12' in *; clear frgnAlloc12'.
  clear mu12.
  remember (pubBlocksTgt mu12') as pubTgt12'.
  remember (frgnBlocksTgt mu12') as frgnTgt12'.
  clear HeqpubTgt12' HeqfrgnTgt12'.
  clear mu12'.
  clear C1 Sem1 match_core12 g1.
  rename H2 into HypPubTgt12'.
  rename H3 into HypFrgnTgt12'.
  revert U2 mu23 d23 st2 m2 st3 m3 H MC23 HypPubTgt12' HypFrgnTgt12' UHyp2.
  induction x; intros.
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [? ?]]].
    inv H0.
    destruct (eff_diagram23 _ _ _ _ _ H _ _ _ _ UHyp2 MC23)
      as [st3' [m3' [d23' [mu23' [InjInc23 [InjSep23
          [LocAlloc23 [? [U3 [? MOD32]]]]]]]]]]; clear eff_diagram23.
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
    exists U3.
    split. destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
    apply MOD32.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [Step2 StepN2]]]. subst x'.
    destruct (eff_diagram23 _ _ _ _ _ Step2 _ _ _ _ UHyp2 MC23)
      as [c3' [m3' [d23' [mu23' [InjInc23 [InjSep23
             [LocAlloc23 [MC23' [U3 [Steps3 MOD32]]]]]]]]]]; clear eff_diagram23.
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
    assert (U2'Hyp: forall b2 z, (U2 b2 z && valid_block_dec m2 b2) || freshloc m2 m2' b2 = true ->
                Mem.valid_block m2' b2 ->
                vis mu23' b2 = true).
        intros. clear IHx StepN2.
        apply orb_true_iff in H.
        destruct H. apply andb_true_iff in H. destruct H.
          destruct (valid_block_dec m2 b2); simpl; inv H1.
            specialize (UHyp2 _ _ H v).
            eapply intern_incr_vis; eassumption.
          assert (locBlocksSrc mu23' = (fun b : block => locBlocksSrc mu23 b || freshloc m2 m2' b)).
                   apply sm_locally_allocatedChar in LocAlloc23. eapply LocAlloc23.
          unfold vis. rewrite H1; clear H1. rewrite H. intuition.

    destruct (IHx _ _ d23' _ _ c3' m3' StepN2 MC23' XX1 XX2)
        as [c3'' [m3'' [d23'' [mu23'' [ZZ [InjIncr'
             [InjSep' [LocAlloc23' [MC23'' [U3' [StepN3 MOD32']]]]]]]]]]]; clear IHx.
       intros. eapply U2'Hyp. apply orb_true_iff in H.
         destruct (valid_block_dec m2 b2); simpl.
           rewrite freshloc_charT in H.
           destruct H. apply orb_true_iff. left. apply andb_true_iff. split; trivial. apply H.
           destruct H. contradiction.
         apply orb_true_iff. right. rewrite freshloc_charT. split; trivial.
        assumption.
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
    split. eapply intern_separated_incr_fwd2; try eassumption.
           eauto.
    split. eapply sm_locally_allocated_trans; eassumption.
    split. apply MC23''.
    exists (fun b z => U3 b z || (U3' b z && valid_block_dec m3 b)).
    assert (Union1: forall b z, Mem.valid_block m3' b -> U3' b z = true -> (U3 b z || (U3' b z && valid_block_dec m3 b) || freshloc m3 m3' b) = true).
      intros. case_eq (U3 b z); simpl; intros; trivial. rewrite H0; simpl.
        apply orb_true_iff. unfold freshloc.
        destruct (valid_block_dec m3 b); simpl. left; trivial. right.
        destruct (valid_block_dec m3' b); simpl. trivial. contradiction.
    assert (Union2: forall b z, Mem.valid_block m3 b -> U3 b z = true -> (U3 b z || (U3' b z && valid_block_dec m3 b)) = true).
      intros. rewrite H0. trivial.
    split. clear MOD32 MOD32' ZZ.
           destruct Steps3; destruct StepN3.
           (*1/4*)
              left. destruct H as [n1 StepA]. destruct H0 as [n2 StepB].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite effstepN_add.
                      exists c3', m3'.
                      split; eapply effstepN_sub_val; try eassumption.
           (*2/4*)
               destruct H0 as [EFF3 CT].
               left. destruct H as [n1 StepA]. destruct EFF3 as [n2 StepB].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
          (*3/4*)
               left. destruct H as [EFF3 CORD].
                       destruct EFF3 as [n1 StepA]. destruct H0 as [n2 StepB].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
           (*4/4*)
               right. destruct H as [EFF3 CORD].
               destruct H0 as [EFF3' CT].
               split. destruct EFF3 as [n1 StepA]. destruct EFF3' as [n2 StepB].
                      exists (n1 + n2)%nat.
                      rewrite effstepN_add.
                       exists c3', m3'.
                       split; eapply effstepN_sub_val; try eassumption.
               eapply t_trans.
                 apply CT. clear CT.
                 apply t_step.
                 constructor 2. apply CORD.
    (*MOD32-clause*) intros b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
        apply MOD32. apply H.
      apply andb_true_iff in H. destruct H.
         destruct (valid_block_dec m3 b3); try inv H0.
         split; trivial.
         destruct (MOD32' _ _ H) as [vb3' UHyp32']; clear MOD32' StepN3.
         intros. remember (locBlocksTgt mu23' b3) as d.
                 destruct d; apply eq_sym in Heqd.
                   apply sm_locally_allocatedChar in LocAlloc23.
                   destruct LocAlloc23 as [AA [BB [CC [DD [EE FF]]]]].
                   rewrite DD, H0 in Heqd. simpl in Heqd.
                   apply freshloc_charT in Heqd. destruct Heqd; contradiction.
                 destruct (UHyp32' (eq_refl _)) as [b2 [d2 [F23' [UU UUPerm]]]]; clear UHyp32'.
                   exists b2, d2.
                   rewrite <- (intern_incr_foreign _ _ InjInc23) in F23'.
                   split; trivial.
                   assert (Mem.valid_block m2 b2).
                     apply (match_validblock23 _ _ _ _ _ _ MC23).
                       eapply foreign_DomRng. eauto. apply F23'.
                   apply orb_true_iff in UU.
                   split. destruct UU; trivial.
                          apply freshloc_charT in H2. destruct H2; contradiction.
                   apply FWD2. apply H1. apply UUPerm.
  (*case 2*)
   inv CS2.
   apply sm_locally_allocatedChar in LocAlloc12.
   exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_sm mu12' mu23).
   destruct INV as [INVa [INVb [INVc INVd]]]. subst.
   split. eapply compose_sm_intern_incr; eauto.
           apply intern_incr_refl.
   split. eapply compose_sm_intern_separated; eauto.
            apply intern_incr_refl.
            apply sm_inject_separated_same_sminj.
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
   exists (fun b z => false).
     split. right. split. exists O. simpl; auto.
            apply t_step. constructor 1; auto.
     intros. inv H.
Qed.
End CoreDiagrams_trans.