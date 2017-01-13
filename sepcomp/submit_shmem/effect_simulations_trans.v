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

Require Import sepcomp.StructuredInjections.
Require Import effect_semantics.
Require Import effect_simulations.
Require Import effect_simulations_lemmas.
Require Import sepcomp.forward_simulations_trans.
Require Import Wellfounded.
Require Import Relations.
Require Import effect_corediagram_trans.

Require Import effect_interpolants.
(*Require Import effect_interpolation_proofs. not necessary - interface suffices*)

Declare Module EFFAX : EffectInterpolationAxioms.

Import SM_simulation.

Lemma initial_inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
       (forall b1, (exists b3 d, compose_meminj j1 j2 b1 = Some(b3,d))
                   <-> (exists b2 d1, j1 b1 = Some(b2,d1))) /\
       (forall b2 b3 d2, j2 b2 =Some(b3,d2) ->
                   exists b1 d, compose_meminj j1 j2 b1 = Some(b3,d)) /\
      (forall b1 b2 ofs2, j1 b1 = Some(b2,ofs2) -> (b1=b2 /\ ofs2=0)) /\
      (forall b2 b3 ofs3, j2 b2 = Some (b3, ofs3) ->
               Mem.flat_inj 1%positive b2 = Some (b3, ofs3) \/
               (b2 = Mem.nextblock Mem.empty /\
                    compose_meminj j1 j2 (Mem.nextblock Mem.empty) = Some (b3, ofs3)) \/
               (exists m : positive,
                   b2 = (Mem.nextblock Mem.empty + m)%positive /\
                   compose_meminj j1 j2 (Mem.nextblock Mem.empty + m)%positive =
                   Some (b3, ofs3))).
Proof. intros.
  destruct (EFFAX.interpolate_II_strongHeqMKI _ _ _
     Forward_simulation_trans.empty_inj _ (Forward_simulation_trans.empty_fwd m1) _ _ Forward_simulation_trans.empty_inj _ (Forward_simulation_trans.empty_fwd m3) _ Inj)
  as [m2 [j1 [j2 [J [X [Y [Inc1 [Inc2 [Inj12 [_ [Inj23 AA]]]]]]]]]]].
intros b; intros.
  destruct (compose_meminjD_Some _ _ _ _ _ H) as [? [? [? [? [? ?]]]]].
    subst. destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
intros b; intros.
   unfold Mem.valid_block; simpl; split; intros N; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
subst. exists m2, j1, j2.
split; trivial.
split; trivial.
split; trivial.
destruct AA as [_ [_ [_ [_ [_ [XX YY]]]]]].
split. intros.
  split; intros. destruct H as [b3 [d COMP]].
    destruct (compose_meminjD_Some _ _ _ _ _ COMP) as
        [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear COMP.
    exists b2, d1; trivial.
  intros. destruct H as [b2 [d1 J1]].
    destruct (X _ _ _ J1) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H1. exfalso. xomega.
split. intros.
    destruct (Y _ _ _ H) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H2. exfalso. xomega.
split. intros.
  destruct (XX _ _ _ H) as [AA | [AA | AA]].
    apply flatinj_E in AA.
      destruct AA as [? [? ?]]; subst. intuition.
    destruct AA as [? [? ?]]; subst. intuition.
    destruct AA as [mm [[? ?] ?]]; subst. intuition.
apply YY.
Qed.
(*
Lemma initial_inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
       (forall b1, (exists b3 d, compose_meminj j1 j2 b1 = Some(b3,d))
                   <-> (exists b2 d1, j1 b1 = Some(b2,d1))) /\
       (forall b2 b3 d2, j2 b2 =Some(b3,d2) ->
                   exists b1 d, compose_meminj j1 j2 b1 = Some(b3,d)) /\
      (forall b1 b2 ofs2, j1 b1 = Some(b2,ofs2) -> (b1=b2 /\ ofs2=0)) /\
      (forall b2 b3 ofs3, j2 b2 = Some (b3, ofs3) ->
               Mem.flat_inj 1%positive b2 = Some (b3, ofs3) \/
               (b2 = Mem.nextblock Mem.empty /\
                    compose_meminj j1 j2 (Mem.nextblock Mem.empty) = Some (b3, ofs3)) \/
               (exists m : positive,
                   b2 = (Mem.nextblock Mem.empty + m)%positive /\
                   compose_meminj j1 j2 (Mem.nextblock Mem.empty + m)%positive =
                   Some (b3, ofs3))) /\
      (forall b1 b2 ofs2, j1 b1 = Some(b2,ofs2) -> (b1=b2 /\ ofs2=0)) /\
      (forall b2 b3 ofs3, j2 b2 = Some (b3, ofs3) ->
              Mem.flat_inj 1%positive b2 = Some (b3, ofs3) \/
              (b2 = Mem.nextblock Mem.empty /\
                compose_meminj j1 j2 (Mem.nextblock Mem.empty) = Some (b3, ofs3)) \/
              (exists m : positive,
                b2 = (Mem.nextblock Mem.empty + m)%positive /\
                compose_meminj j1 j2 (Mem.nextblock Mem.empty + m)%positive =
                Some (b3, ofs3))).
Proof. intros.
  destruct (EFFAX.interpolate_II_strong _ _ _ Forward_simulation_trans.empty_inj _ (Forward_simulation_trans.empty_fwd m1) _ _ Forward_simulation_trans.empty_inj _ (Forward_simulation_trans.empty_fwd m3) _ Inj)
  as [m2 [j1 [j2 [J [X [Y [Inc1 [Inc2 [Inj12 [_ [Inj23 _]]]]]]]]]]].
intros b; intros.
  destruct (compose_meminjD_Some _ _ _ _ _ H) as [? [? [? [? [? ?]]]]].
    subst. destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
intros b; intros.
   unfold Mem.valid_block; simpl; split; intros N; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
subst. exists m2, j1, j2.
split; trivial.
split; trivial.
split; trivial.
split. intros.
  split; intros. destruct H as [b3 [d COMP]].
    destruct (compose_meminjD_Some _ _ _ _ _ COMP) as
        [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear COMP.
    exists b2, d1; trivial.
  intros. destruct H as [b2 [d1 J1]].
    destruct (X _ _ _ J1) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H1. exfalso. xomega.
split. intros.
    destruct (Y _ _ _ H) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H2. exfalso. xomega.
split; intros.
  destruct (X _ _ _ H) as [AA | AA].
    apply flatinj_E in AA.
      destruct AA as [? [? ?]]; subst. intuition.

Qed.
*)

Section Eff_sim_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3)
        epts12 epts23 epts13
        (EPC : entrypoints_compose epts12 epts23 epts13).

Theorem eff_sim_trans: forall
        (SIM12: @SM_simulation_inject _ _ _ _ _ _ Sem1 Sem2 g1 g2 epts12)
        (SIM23: @SM_simulation_inject _ _ _ _ _ _ Sem2 Sem3 g2 g3 epts23),
        @SM_simulation_inject _ _ _ _ _ _ Sem1 Sem3 g1 g3 epts13.
Proof. (*follows structure of forward_simulations_trans.injinj*)
  intros.
  destruct SIM12
    as [core_data12 match_core12 core_ord12 core_ord_wf12
      match_sm_wd12 genvs_dom_eq12 match_genv12
      match_visible12 match_restrict12
      match_sm_valid12 (*match_protected12*) core_initial12
      core_diagram12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12].
  destruct SIM23
    as [core_data23 match_core23 core_ord23 core_ord_wf23
      match_sm_wd23 genvs_dom_eq23 match_genv23
      match_visible23 match_restrict23
      match_sm_valid23 (*match_protected23*) core_initial23
      core_diagram23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply Build_SM_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d mu c1 m1 c3 m3 =>
      match d with (d1,X,d2) =>
        exists c2, exists m2, exists mu1, exists mu2,
          X=Some c2 /\ mu = compose_sm mu1 mu2 /\
          (locBlocksTgt mu1 = locBlocksSrc mu2 /\
           extBlocksTgt mu1 = extBlocksSrc mu2 /\
           (forall b, pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
           (forall b, frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\
          match_core12 d1 mu1 c1 m1 c2 m2 /\ match_core23 d2 mu2 c2 m2 c3 m3
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
 (*match_sm_wd*) clear - match_sm_wd12 match_sm_wd23.
  intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  specialize (match_sm_wd12 _ _ _ _ _ _ MC12).
  specialize (match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct INV as [INVa [INVb [INVc INVd]]].
  eapply (compose_sm_wd); eauto.
 (*genvs_domain_eq*)
  eapply genvs_domain_eq_trans; eassumption.
 (*match_genv for definition using
       meminj_preserves_globals ge1 (foreign_of mu)
  clear - genvs_dom_eq12 match_sm_wd12 match_genv12 match_genv23.
  intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  specialize (match_genv12 _ _ _ _ _ _ MC12).
  specialize (match_genv23 _ _ _ _ _ _ MC23).
  apply meminj_preserves_genv2blocks.
  apply meminj_preserves_genv2blocks in match_genv12.
  apply meminj_preserves_genv2blocks in match_genv23.
  rewrite compose_sm_foreign.
    solve [eapply meminj_preserves_globals_ind_compose; eassumption].
    eapply INV.
    eauto.*)
 (*match_genv*)
  clear - genvs_dom_eq12 match_sm_wd12 match_genv12 match_genv23.
  intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct MC as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  destruct (match_genv12 _ _ _ _ _ _ MC12) as [GE12a GE12b].
  destruct (match_genv23 _ _ _ _ _ _ MC23) as [GE23a GE23b].
  split. apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in GE12a.
         apply meminj_preserves_genv2blocks in GE23a.
         rewrite compose_sm_extern.
         solve [eapply meminj_preserves_globals_ind_compose; eassumption].
  apply GE12b.
 (*match_visible*)
    clear - match_sm_wd12 match_visible12.
    intros. rename c2 into c3. rename m2 into m3.
      destruct d as [[d12 cc2] d23].
      destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
      simpl. rewrite vis_compose_sm. eapply match_visible12. eassumption.
 (*match_restrict*)
    clear - match_restrict12.
    intros. rename c2 into c3. rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [XX [J [INV [MC12 MC23]]]]]]]]; subst.
    simpl in *.
    exists c2, m2, (restrict_sm mu12 X), mu23.
    specialize (match_restrict12 _ _ _ _ _ _ X MC12 H0 H1).
    intuition.
    unfold compose_sm; simpl.
    f_equal; try (destruct mu12; reflexivity).
      destruct mu12; simpl in *.
        unfold compose_meminj, restrict. extensionality b.
        remember (X b) as d.
        destruct d; trivial.
      destruct mu12; simpl in *.
        unfold compose_meminj, restrict. extensionality b.
        remember (X b) as d.
        destruct d; trivial.
      destruct mu12; simpl in *. assumption.
      destruct mu12; simpl in *. assumption.
      destruct mu12; simpl in *. apply (H2 _ H4).
      destruct mu12; simpl in *. apply (H5 _ H4).
 (*sm_valid*)
    clear - match_sm_valid12 match_sm_valid23.
    intros. rename c2 into c3.  rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
    specialize (match_sm_valid12 _ _ _ _ _ _ MC12).
    specialize (match_sm_valid23 _ _ _ _ _ _ MC23).
    unfold sm_valid, compose_sm. destruct mu12; destruct mu23; simpl in *.
    split; intros. eapply match_sm_valid12. apply H.
    eapply match_sm_valid23. apply H.
 (*match_protected
    clear - match_sm_wd12 match_protected12
            match_sm_wd23 match_protected23.
    intros. rename c2 into c3.  rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
    simpl. apply (match_protected12 _ _ _ _ _ _ MC12 _ H0 H1).*)
 (*initial_core*)
   (*version where envirnment delivers structured injection:
     to complete this proof, we'd have to replace the call to
     initial_inject_split 3 line down to one to variant that merges
     the results of the two lemmas in effect_interpolants, namely
     effect_interp_II and interpolate_II_strongHeqMKI. That should be possible
     but is left as future work.
   clear - EPC genvs_dom_eq12 core_initial12 genvs_dom_eq23 core_initial23.
   intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3.
    rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
    (*assert (HT: Forall2 Val.has_type vals1 (sig_args sig)).
      eapply forall_valinject_hastype; eassumption.*)
    destruct (initial_inject_split _ _ _ H1)
       as [m2 [j1 [j2 [J [Inj12 [Inj23 [X [Y [XX YY]]]]]]]]].
    subst. rewrite J in *.
    destruct (Forward_simulation_trans.forall_val_inject_split _ _ _ _ H2)
       as [vals2 [ValsInj12 ValsInj23]].
    assert (PG1: meminj_preserves_globals g1 j1).
      clear - X Y XX YY H3 H4.
      apply meminj_preserves_genv2blocks.
      apply meminj_preserves_genv2blocks in H3.
      destruct H3 as [AA [BB CC]].
      split; intros.
         specialize (AA _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         destruct (XX _ _ _ J1); subst. trivial.
      split; intros.
         specialize (BB _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. trivial.
      destruct (XX _ _ _ H0); subst. trivial.
  assert (PG2: meminj_preserves_globals g2 j2).
    clear - XX YY X Y PG1 H3 genvs_dom_eq12.
    apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in H3.
      destruct H3 as [AA [BB CC]].
     apply meminj_preserves_genv2blocks in PG1.
      destruct PG1 as [AA1 [BB1 CC1]].
      destruct genvs_dom_eq12.
      split; intros.
         apply H in H1.
         specialize (AA1 _ H1). specialize (AA _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         rewrite J1 in AA1. inv AA1. simpl in D. subst. trivial.
      split; intros.
         apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         rewrite J1 in BB1. inv BB1. simpl in D. subst. trivial.
      apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1). rename b2 into b3.
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. simpl in D. subst.
         clear BB1 XX.
         destruct (YY _ _ _ H2) as [XX | [XX | XX]].
           apply flatinj_E in XX. destruct XX as [? [? ?]]; subst. trivial.
           destruct XX as [? ?]; subst.
             apply (CC _ _ _ H1 H4).
           destruct XX as [mm [? ?]]; subst.
             apply (CC _ _ _ H1 H4).
     exploit (core_initial12 _ _ _ EP12 vals1 _ _ _ vals2 _ H0 Inj12). with (vals2:=vals3); try eassumption.
         rewrite J. eassumption.
         rewrite J. eassumption.
         rewrite J. eassumption.
         (*eapply forall_valinject_hastype; eassumption.*)
         intros. eapply H6.
              rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in H.
              assumption.
       intros [d12 [c2 [Ini2 MC12]]].
     exploit (core_initial23 _ _ _ EP23 vals2); try eassumption.
         rewrite J. eassumption.
         rewrite J. eassumption.
         rewrite J. eassumption.
         (*eapply forall_valinject_hastype; eassumption.*)
         intros. eapply H6.
              rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in H.
              assumption.

        assert (Q: forall b,  isGlobalBlock g2 b || getBlocks vals2 b = true ->
                   exists jb d, j2 b = Some (jb, d) /\
                           isGlobalBlock g3 jb || getBlocks vals3 jb = true).
          intros b' Hb'. apply orb_true_iff in Hb'.
          destruct Hb' as [Hb' | Hb'].
            rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG2 _ Hb').
              exists b', 0.
              rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in Hb'.
              rewrite Hb'. intuition.
          destruct (getBlocks_inject _ _ _  ValsInj23 _ Hb') as [bb [ofs [J2 GB2]]].
              exists bb, ofs. intuition.
        specialize (REACH_inject _ _ _ Inj23
            (fun b' : block => isGlobalBlock g2 b' || getBlocks vals2 b')
            (fun b' : block => isGlobalBlock g3 b' || getBlocks vals3 b')
            Q). intros. as [b3 [d2 [J2 R3]]].
        rewrite J2.
        destruct (Y _ _ _ J2) as [b1 [d COMP]].
        apply (H4 _ _ _ COMP).
      intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption.
      (*eapply forall_valinject_hastype; eassumption.*)
      intros. destruct (X b1) as [_ J1Comp].
              destruct J1Comp as [b3 [dd COMP]]. exists b2, d; trivial.
              specialize (H4 _ _ _ COMP).
              destruct (compose_meminjD_Some _ _ _ _ _ COMP)
                as [bb2 [dd1 [dd2 [J1 [J2 D]]]]]; subst; clear COMP.
              rewrite J1 in H; inv H. rewrite J2. apply H4.
      intros.*)
 (*initial_core*)
   clear - EPC genvs_dom_eq12 core_initial12 genvs_dom_eq23 core_initial23.
   intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3.
    rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
    (*assert (HT: Forall2 Val.has_type vals1 (sig_args sig)).
      eapply forall_valinject_hastype; eassumption.*)
    destruct (initial_inject_split _ _ _ H1)
       as [m2 [j1 [j2 [J [Inj12 [Inj23 [X [Y [XX YY]]]]]]]]].
    subst.
    destruct (Forward_simulation_trans.forall_val_inject_split _ _ _ _ H2)
       as [vals2 [ValsInj12 ValsInj23]].
    assert (PG1: meminj_preserves_globals g1 j1).
      clear - X Y XX YY H3 H4.
      apply meminj_preserves_genv2blocks.
      apply meminj_preserves_genv2blocks in H3.
      destruct H3 as [AA [BB CC]].
      split; intros.
         specialize (AA _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         destruct (XX _ _ _ J1); subst. trivial.
      split; intros.
         specialize (BB _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. trivial.
      destruct (XX _ _ _ H0); subst. trivial.
  assert (PG2: meminj_preserves_globals g2 j2).
    clear - XX YY X Y PG1 H3 genvs_dom_eq12.
    apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in H3.
      destruct H3 as [AA [BB CC]].
     apply meminj_preserves_genv2blocks in PG1.
      destruct PG1 as [AA1 [BB1 CC1]].
      destruct genvs_dom_eq12.
      split; intros.
         apply H in H1.
         specialize (AA1 _ H1). specialize (AA _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         rewrite J1 in AA1. inv AA1. simpl in D. subst. trivial.
      split; intros.
         apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         rewrite J1 in BB1. inv BB1. simpl in D. subst. trivial.
      apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1). rename b2 into b3.
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. simpl in D. subst.
         clear BB1 XX.
         destruct (YY _ _ _ H2) as [XX | [XX | XX]].
           apply flatinj_E in XX. destruct XX as [? [? ?]]; subst. trivial.
           destruct XX as [? ?]; subst.
             apply (CC _ _ _ H1 H4).
           destruct XX as [mm [? ?]]; subst.
             apply (CC _ _ _ H1 H4).
    destruct (core_initial12 _ _ _ EP12 _ _ _ _ vals2 _
       DomS (fun b => match j2 b with None => false | Some (b3,d) => DomT b3 end) H0 Inj12)
     as [d12 [c2 [Ini2 MC12]]]; try assumption.
      (*eapply forall_valinject_hastype; eassumption.*)
      intros. destruct (X b1) as [_ J1Comp].
              destruct J1Comp as [b3 [dd COMP]]. exists b2, d; trivial.
              specialize (H4 _ _ _ COMP).
              destruct (compose_meminjD_Some _ _ _ _ _ COMP)
                as [bb2 [dd1 [dd2 [J1 [J2 D]]]]]; subst; clear COMP.
              rewrite J1 in H; inv H. rewrite J2. apply H4.
      intros.
        assert (Q: forall b,  isGlobalBlock g2 b || getBlocks vals2 b = true ->
                   exists jb d, j2 b = Some (jb, d) /\
                           isGlobalBlock g3 jb || getBlocks vals3 jb = true).
          intros b' Hb'. apply orb_true_iff in Hb'.
          destruct Hb' as [Hb' | Hb'].
            rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG2 _ Hb').
              exists b', 0.
              rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in Hb'.
              rewrite Hb'. intuition.
          destruct (getBlocks_inject _ _ _  ValsInj23 _ Hb') as [bb [ofs [J2 GB2]]].
              exists bb, ofs. intuition.
        destruct (REACH_inject _ _ _ Inj23
            (fun b' : block => isGlobalBlock g2 b' || getBlocks vals2 b')
            (fun b' : block => isGlobalBlock g3 b' || getBlocks vals3 b')
            Q _ H) as [b3 [d2 [J2 R3]]].
        rewrite J2.
        destruct (Y _ _ _ J2) as [b1 [d COMP]].
        apply (H4 _ _ _ COMP).
      intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption.
    destruct (core_initial23 _ _ _ EP23 _ _ _ _ vals3 _
       (fun b => match j2 b with None => false | Some (b3,d) => DomT b3 end) DomT Ini2 Inj23)
     as [d23 [c3 [Ini3 MC23]]]; try assumption.
       intros b2 b3 d2 J2. rewrite J2.
         destruct (Y _ _ _ J2) as [b1 [d COMP]].
         destruct (H4 _ _ _ COMP). split; trivial.
    intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption.
    remember (initial_SM DomS
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) (REACH m1 (fun b => isGlobalBlock g1 b || getBlocks vals1 b))
                  (REACH m2 (fun b => isGlobalBlock g2 b || getBlocks vals2 b))
            j1) as mu1.
  remember (initial_SM
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) DomT (REACH m2 (fun b => isGlobalBlock g2 b || getBlocks vals2 b))
                       (REACH m3 (fun b => isGlobalBlock g3 b || getBlocks vals3 b))
             j2) as mu2.
  exists (d12,Some c2,d23).
  exists c3.
  split; trivial.
  exists c2, m2, mu1, mu2.
  split; trivial.
  split. subst. unfold initial_SM, compose_sm; simpl.
           f_equal.
  split. subst; simpl. repeat (split; trivial).
  split; trivial.
 (*core_diagram*)
  clear - match_sm_wd12 match_sm_valid12 core_diagram12
          match_sm_wd23 match_sm_valid23 core_diagram23.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  eapply core_diagram_trans; try eassumption.
 (*effcore_diagram*)
  clear - match_sm_wd12 match_sm_valid12 effcore_diagram12
          match_sm_wd23 match_sm_valid23 effcore_diagram23.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  eapply effcore_diagram_trans; eassumption.
(*halted*)
  clear - match_sm_wd12 core_halted12 match_sm_wd23 core_halted23.
  intros. rename c2 into c3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  destruct (core_halted12 _ _ _ _ _ _ _ MC12 H0) as
     [v2 [MInj12 [RValsInject12 HaltedMid]]].
  destruct (core_halted23 _ _ _ _ _ _ _ MC23 HaltedMid) as
     [v3 [MInj23 [RValsInject23 HaltedTgt]]].
  exists v3.
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct INV as [INVa [INVb [INVc INVd]]].

  split. rewrite compose_sm_as_inj; trivial.
           eapply Mem.inject_compose; eassumption.
  split. rewrite compose_sm_as_inj; trivial.
         rewrite restrict_compose, vis_compose_sm; simpl.
         eapply val_inject_compose; try eassumption.
         eapply val_inject_incr; try eassumption.
         apply restrict_incr.
  assumption.
(*at_external*)
  clear - match_sm_wd12 core_at_external12 match_sm_wd23 core_at_external23.
  intros. rename c2 into c3. rename m2 into m3.
  rename H0 into AtExtSrc.
  destruct cd as [[d12 cc2] d23].
  destruct H as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]].
  subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [MInj12 [vals2 [ArgsInj12 (*[ArgsHT2*) AtExt2(*]*)]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [MInj23 [vals3 [ArgsInj23 (*[ArgsHTTgt*) AtExtTgt(*]*)]]]; clear core_at_external23.
  rewrite compose_sm_as_inj; try eauto.
    split. eapply Mem.inject_compose; eassumption.
    exists vals3.
    split. rewrite restrict_compose, vis_compose_sm; simpl.
           eapply forall_val_inject_compose; try eassumption.
           eapply forall_vals_inject_restrictD; eassumption.
    (*split;*) assumption.
  eapply GLUEINV.
  eapply GLUEINV.
(*after_external*)
  clear - match_sm_wd12 match_sm_valid12 core_at_external12 eff_after_external12
          match_visible12 match_restrict12
          match_sm_wd23 match_sm_valid23 core_at_external23 eff_after_external23.
  intros. rename st2 into st3. rename m2 into m3.
          rename vals2 into vals3'. rename m2' into m3'.
          rename UnchLOOR into UnchLOOR13.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]].
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  remember (fun b => locBlocksSrc mu12 b || frgnBlocksSrc mu12 b || mapped (as_inj (compose_sm mu12 mu23)) b)
      as RESTR.
  assert (NormMC12: match_core12 d12 (restrict_sm mu12 RESTR) st1 m1 st2 m2).
     apply match_restrict12. apply MC12.
     subst RESTR. clear. intuition.
     subst RESTR.
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu'
              SMvalNu' WDnu' SEP INC m3' ret2 m1' ret1 nu' NuHyp nu
              pubTgtHyp pubTgt' pubSrcHyp pubSrc' ValInjMu AtExtTgt
              AtExtSrc eff_after_external23 core_at_external23
              eff_after_external12 core_at_external12.
     subst. intros b Hb. rewrite REACHAX in Hb.
      destruct Hb as [L HL].
      generalize dependent b.
      induction L; simpl; intros; inv HL.
        apply H.
      specialize (IHL _ H1); clear H1.
        apply orb_true_iff in IHL. apply orb_true_iff.
        destruct IHL.
          left. eapply (match_visible12 _ _ _ _ _ _ MC12).
                eapply REACH_cons; try eassumption.
                apply REACH_nil. apply H.
          right. eapply (inject_REACH_closed _ _ _ MemInjMu).
                eapply REACH_cons; try eassumption.
                apply REACH_nil. apply H.
  remember (restrict_sm mu12 RESTR) as nmu12.
  assert (HmuNorm: mu = compose_sm nmu12 mu23).
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu'
              SMvalNu' WDnu' SEP INC m3' ret2 m1' ret1 nu' NuHyp nu
              pubTgtHyp pubTgt' pubSrcHyp pubSrc' ValInjMu AtExtTgt
              AtExtSrc eff_after_external23 core_at_external23
              eff_after_external12 core_at_external12.
      subst nmu12 mu RESTR. unfold compose_sm; simpl.
          rewrite restrict_sm_extern.
          rewrite (restrict_sm_local' _ WDmu12).
          Focus 2. clear. intuition.
          unfold restrict_sm; simpl.
          destruct mu12; simpl in *.
          f_equal.
          extensionality b. unfold compose_meminj, restrict, mapped, as_inj, join; simpl.
          remember (extern_of b) as d.
          specialize (disjoint_extern_local _ WDmu12 b); simpl; intros DD.
          destruct d; trivial; apply eq_sym in Heqd.
            destruct p as [b2 d1].
            destruct DD; try congruence.
            rewrite H.
            destruct (extern_DomRng _ WDmu12 _ _ _ Heqd); simpl in *.
            assert (EE:= extBlocksSrc_locBlocksSrc _ WDmu12 _ H0); simpl in *.
            rewrite EE; simpl.
            remember (frgnBlocksSrc b) as q.
            destruct q; apply eq_sym in Heqq; simpl in *. reflexivity.
            remember (StructuredInjections.extern_of mu23 b2) as w.
            destruct w; trivial. destruct p. rewrite <- Heqw. trivial.
         remember (locBlocksSrc b) as q.
         destruct q; simpl; trivial.
         remember (frgnBlocksSrc b) as w.
         destruct w; trivial; simpl; apply eq_sym in Heqw.
         remember (local_of b) as t.
         destruct t; simpl; trivial.
         destruct p; apply eq_sym in Heqt.
         destruct (local_DomRng _ WDmu12 _ _ _ Heqt); simpl in *. congruence.
  clear MC12.
  assert (WDnmu12:= match_sm_wd12 _ _ _ _ _ _ NormMC12).
  clear HMu.
  assert (WDmu: SM_wd (compose_sm nmu12 mu23)).
    eapply compose_sm_wd; try eassumption.
      subst. unfold restrict_sm, restrict; simpl. destruct mu12; simpl in *. apply GLUEINV.
      subst. unfold restrict_sm, restrict; simpl. destruct mu12; simpl in *. apply GLUEINV.
  clear match_restrict12 match_visible12.
  assert (mu12_valid:= match_sm_valid12 _ _ _ _ _ _ NormMC12).
  assert (mu23_valid:= match_sm_valid23 _ _ _ _ _ _ MC23).
  rename ret2 into ret3.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ NormMC12 AtExtSrc)
   as [MInj12 [vals2 [ArgsInj12 (*[ArgsHT2*) AtExt2(*]*)]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
   as [MInj23 [vals3 [ArgsInj23 (*[ArgsHT3*) AtExt3(*]*)]]]; clear core_at_external23.

  (*Prove uniqueness of e, ef_sig, vals3. We do this by hand, instead of
     rewrite AtExtTgt in AtExt3; inv Atext3 in order to avoid the subst
     taht's inherent in inv AtExt3. Probably there's a better way to do this..*)
  assert (e' = e /\ ef_sig' = ef_sig /\ vals3'=vals3).
     rewrite AtExtTgt in AtExt3. inv AtExt3. intuition.
  destruct H as [HH1 [HH2 HH3]].
  rewrite HH1, HH2, HH3 in *. clear HH1 HH2 HH3 e' ef_sig' vals3' AtExt3.

  (*clear MemInjMu. follows from MInj12 MInj23*)
  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ MInj12
        NormMC12 AtExtSrc AtExt2 ArgsInj12
        _ (eq_refl _) _ (eq_refl _) _ (eq_refl _)).
  specialize (eff_after_external23 _ _ _ _ _ _ _ _ _
      _ _ _ MInj23 MC23 AtExt2 AtExtTgt ArgsInj23 _ (eq_refl _)
      _ (eq_refl _) _ (eq_refl _)).
  assert (LeakedCompSrc: locBlocksSrc mu = locBlocksSrc nmu12 /\
                         extBlocksSrc mu = extBlocksSrc nmu12 /\
                        exportedSrc mu vals1 = exportedSrc nmu12 vals1).
     subst. clear - WDnmu12 WDmu. simpl.
        rewrite restrict_sm_locBlocksSrc.
        rewrite restrict_sm_extBlocksSrc.
        unfold exportedSrc.
        rewrite sharedSrc_iff_frgnpub; trivial. simpl.
        rewrite sharedSrc_iff_frgnpub; trivial.
        rewrite restrict_sm_frgnBlocksSrc, restrict_sm_pubBlocksSrc.
        intuition.
  destruct LeakedCompSrc as [LSa [LSb LSc]].
    rewrite LSa, LSc in *. clear LSa LSb LSc.
  assert (LeakedCompTgt: locBlocksTgt mu = locBlocksTgt mu23
                       /\ extBlocksTgt mu = extBlocksTgt mu23
                       /\ exportedTgt mu vals3 = exportedTgt mu23 vals3).
     subst. clear - WDmu23 WDmu. simpl.
        unfold exportedTgt, sharedTgt. simpl. intuition.
  destruct LeakedCompTgt as [LTa [LTb LTc]].
    rewrite LTa, LTc in *. clear LTa LTb LTc.
   remember (fun b => locBlocksTgt nmu12 b &&
             REACH m2 (exportedTgt nmu12 vals2) b) as pubTgtMid'.
   remember (fun b => locBlocksSrc mu23 b &&
             REACH m2 (exportedSrc mu23 vals2) b) as pubSrcMid'.
   assert (MID: forall b, pubTgtMid' b = true -> pubSrcMid' b = true).
        clear eff_after_external12 match_sm_valid23 eff_after_external23.
        rewrite HeqpubTgtMid', HeqpubSrcMid'.
        destruct GLUEINV as [GlueA [GlueB [GlueC GlueD]]].
        subst.
        clear UnchLOOR13 UnchPrivSrc SEP INC MemInjMu ArgsInj12 MInj12.

        rewrite restrict_sm_locBlocksTgt. (*sm_extern_normalize_exportedTgt; trivial.*)
           rewrite GlueA. intros b Hb. rewrite andb_true_iff in *.
        destruct Hb. split; trivial.
        eapply REACH_mono; try eassumption.
        unfold exportedTgt, exportedSrc, sharedTgt.
        rewrite restrict_sm_frgnBlocksTgt, restrict_sm_pubBlocksTgt.
        rewrite sharedSrc_iff_frgnpub; trivial.
        intros. repeat rewrite orb_true_iff in *.
        intuition.
  assert (NU: nu = compose_sm (replace_locals nmu12 pubSrc' pubTgtMid')
              (replace_locals mu23 pubSrcMid' pubTgt')).
     clear frgnSrcHyp frgnTgtHyp eff_after_external23.
     subst. unfold compose_sm; simpl.
     rewrite replace_locals_extern, replace_locals_local,
             replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
            replace_locals_extBlocksSrc, replace_locals_extBlocksTgt.
     rewrite replace_locals_extern, replace_locals_local.
     rewrite restrict_sm_extBlocksSrc, restrict_sm_locBlocksSrc,
             restrict_sm_local, restrict_sm_extern.
     f_equal.

  clear NuHyp.
  (*produce all the hypothesis necessary for applying interpolation*)
  assert (MinjNu12: Mem.inject (as_inj (replace_locals nmu12 pubSrc' pubTgtMid')) m1 m2).
     rewrite replace_locals_as_inj. assumption.
  assert (MinjNu23: Mem.inject (as_inj (replace_locals mu23 pubSrcMid' pubTgt')) m2 m3).
     rewrite replace_locals_as_inj. assumption.
  assert (ArgsInj12R: Forall2
    (val_inject
       (as_inj
          (restrict_sm mu12
             (fun b : block =>
              locBlocksSrc mu12 b || frgnBlocksSrc mu12 b
              || mapped (as_inj (compose_sm mu12 mu23)) b)))) vals1 vals2).
      clear - ArgsInj12 Heqnmu12 HeqRESTR.
      rewrite restrict_sm_all. subst. rewrite restrict_sm_all in ArgsInj12.
       rewrite restrict_nest in ArgsInj12.
       eapply val_list_inject_forall_inject.
       apply forall_inject_val_list_inject in ArgsInj12.
       eapply val_list_inject_incr; try eassumption.
       red; intros. destruct (restrictD_Some _ _ _ _ _ H); clear H.
          unfold vis in H1. rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc in H1.
          apply restrictI_Some; intuition.
    intros. rewrite effect_properties.vis_restrict_sm in H.
      unfold vis in H. intuition.
  clear ArgsInj12.
  assert (WDnu12: SM_wd (replace_locals nmu12 pubSrc' pubTgtMid')).
       subst.
       eapply replace_locals_wd; try eassumption.
         intros. apply andb_true_iff in H.
           destruct H as [locB R].
           destruct (REACH_local_REACH _ WDnmu12 _ _ _ _
              MInj12 ArgsInj12R _ R locB) as [b2 [d1 [LOC12 R2]]].
           exists b2, d1; split; trivial.
           rewrite andb_true_iff, R2.
           split; trivial.
           eapply local_locBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H.
  assert (ArgsInj23R: Forall2 (val_inject (as_inj mu23)) vals2 vals3).
       eapply val_list_inject_forall_inject.
       apply forall_inject_val_list_inject in ArgsInj23.
       eapply val_list_inject_incr; try eassumption.
       apply restrict_incr.
  clear ArgsInj23.
  assert (WDnu23: SM_wd (replace_locals mu23 pubSrcMid' pubTgt')).
       subst.
       eapply replace_locals_wd; try eassumption.
       destruct GLUEINV as [GIa [GIb [GIc GId]]]. subst.
       intros b2; intros. apply andb_true_iff in H.
           destruct H as [locB R].
           destruct (REACH_local_REACH _ WDmu23 _ _ _ _
              MInj23 ArgsInj23R _ R locB) as [b3 [d2 [LOC23 R3]]].
           exists b3, d2; split; trivial.
           rewrite andb_true_iff, R3.
           split; trivial.
           eapply local_locBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H.
  assert (nu12_valid: sm_valid (replace_locals nmu12 pubSrc' pubTgtMid') m1 m2).
     split. rewrite replace_locals_DOM. eapply mu12_valid.
     rewrite replace_locals_RNG. eapply mu12_valid.
  assert (nu23_valid: sm_valid (replace_locals mu23 pubSrcMid' pubTgt') m2 m3).
     split. rewrite replace_locals_DOM. eapply mu23_valid.
     rewrite replace_locals_RNG. eapply mu23_valid.
  rewrite NU in INC, SEP.
  destruct (EFFAX.effect_interp_II _ _ _ MinjNu12 _ FwdSrc
      _ _ MinjNu23 _ FwdTgt nu' WDnu' SMvalNu' MemInjNu'
      INC SEP nu12_valid nu23_valid)
     as [m2' [nu12' [nu23' [X [Incr12 [Incr23 [MInj12'
        [Fwd2 [MInj23' [Sep12 [Sep23 [nu12'valid
        [nu23'valid [GLUEINV' [Norm' [UnchMidA UnchMidB]]]]]]]]]]]]]]]]; simpl in *.
    (*discharge the unchOn application conditions*)
       subst; apply UnchPrivSrc.
       subst. apply UnchLOOR13.
    (*discharge the GLUE application condition*)
      rewrite replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
            replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
      destruct GLUEINV as [GLUEa [GLUEb [GLUEc GLUEd]]].
      repeat (split; trivial).
      subst. rewrite restrict_sm_locBlocksTgt; trivial.
      subst. rewrite restrict_sm_extBlocksTgt; trivial.
      subst. rewrite restrict_sm_frgnBlocksTgt; trivial.
    (*discharge the Norm Hypothesis*)
      rewrite Heqnmu12. do 2 rewrite replace_locals_extern.
      rewrite restrict_sm_extern.
      intros. destruct (restrictD_Some _ _ _ _ _ H) as [EX12 RR]; clear H.
      subst RESTR nmu12.
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu'
              SMvalNu' WDnu' SEP INC m3' m1' ret1 nu'
              pubTgtHyp pubSrcHyp ValInjMu AtExtTgt
              AtExtSrc eff_after_external23
              eff_after_external12 MinjNu23.
      destruct (extern_DomRng _ WDmu12 _ _ _ EX12).
      rewrite (extBlocksSrc_locBlocksSrc _ WDmu12 _ H) in RR; simpl in *.
      remember (frgnBlocksSrc mu12 b1) as d.
      destruct d; apply eq_sym in Heqd.
        destruct (frgnSrc _ WDmu12 _ Heqd) as [bb2 [dd1 [Frg1 FT2]]]; clear Heqd.
        apply foreign_in_extern in Frg1. rewrite Frg1 in EX12; inv EX12.
        destruct GLUEINV as [_ [_ [_ FF]]]. apply FF in FT2.
        destruct (frgnSrc _ WDmu23 _ FT2) as [b3 [d2 [Frg2 FT3]]]; clear FT2.
        rewrite (foreign_in_extern _ _ _ _ Frg2). exists b3, d2; trivial.
      simpl in RR. destruct (mappedD_true _ _ RR) as [[bb dd] M]; clear RR.
        destruct (joinD_Some _ _ _ _ _ M) as [EXT | [EXT LOC]]; clear M;
          rewrite compose_sm_extern in EXT.
          destruct (compose_meminjD_Some _ _ _ _ _ EXT) as [bb2 [dd1 [dd2 [E1 [E2 D]]]]].
          rewrite EX12 in E1. inv E1. rewrite E2. exists bb, dd2; trivial.
        rewrite compose_sm_local in LOC.
          destruct (compose_meminjD_Some _ _ _ _ _ LOC) as [bb2 [dd1 [dd2 [E1 [E2 D]]]]].
          destruct (disjoint_extern_local _ WDmu12 b1); congruence.
  assert (UnchMidC : Mem.unchanged_on (local_out_of_reach (replace_locals mu23 pubSrcMid' pubTgt') m2) m3 m3').
    clear - WDmu23 HeqpubTgtMid' HeqpubSrcMid' MinjNu12 UnchLOOR13 WDnu12 NU pubSrcHyp Heqnmu12 HeqRESTR GLUEINV.
    subst nmu12.
    remember (replace_locals (restrict_sm mu12 RESTR) pubSrc' pubTgtMid') as kappa12.
    remember (replace_locals mu23 pubSrcMid' pubTgt') as kappa23.
    assert (GluePubKappa : forall b : block,
          pubBlocksTgt kappa12 b = true -> pubBlocksSrc kappa23 b = true).
       clear UnchLOOR13 WDnu12 MinjNu12.
       subst kappa12 kappa23. rewrite replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt.
       subst. rewrite restrict_sm_locBlocksTgt; intros; trivial.
              apply andb_true_iff in H. destruct H.
              destruct GLUEINV as [Ga [Gb [Gc Gd]]]. rewrite Ga in H.
              rewrite H; simpl.
              eapply REACH_mono; try eassumption.
              unfold exportedTgt, exportedSrc, sharedTgt. rewrite sharedSrc_iff_frgnpub.
              rewrite restrict_sm_frgnBlocksTgt, restrict_sm_pubBlocksTgt.
              intros. do 2 rewrite orb_true_iff in H1.
                do 2 rewrite orb_true_iff. intuition.
           assumption.
    clear Heqkappa12 Heqkappa23 GLUEINV.
    subst.
    unfold local_out_of_reach.
    split; intros; rename b into b3.
      destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl.
        split; simpl; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc kappa12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePubKappa in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MinjNu12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
    destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl.
        split; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc kappa12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePubKappa in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MinjNu12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
  (*next, prepare for application of eff_after_external12*)
  destruct GLUEINV' as [WDnu12' [WDnu23' [GLUEa' [GLUEb' [GLUEc' GLUEd']]]]].
  assert (exists ret2, val_inject (as_inj nu12') ret1 ret2 /\
                       val_inject (as_inj nu23') ret2 ret3 (*/\
                       Val.has_type ret2 (proj_sig_res ef_sig)*)).
    subst. rewrite compose_sm_as_inj in RValInjNu'; trivial.
    destruct (val_inject_split _ _ _ _ RValInjNu')
      as [ret2 [RValInjNu12' RValInjNu23']].
    exists ret2. repeat (split; trivial).
    (*eapply valinject_hastype; eassumption.*)
  destruct H as [ret2 [RValInjNu12' (*[*)RValInjNu23' (*RetType2]*)]].
  subst.
  specialize (eff_after_external12 nu12' ret1
     m1' ret2 m2' Incr12 Sep12 WDnu12' nu12'valid MInj12' RValInjNu12'
     FwdSrc Fwd2 (*RetType2*)).

  destruct (eff_after_external12 _ (eq_refl _)
      _ (eq_refl _) _ (eq_refl _))
    as [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear eff_after_external12.
   (*discharge unchangedOn-application conditions*)
      apply UnchPrivSrc.
      apply UnchMidB.

  (*next, apply eff_after_external23*)
  specialize (eff_after_external23 nu23').
  destruct (eff_after_external23 ret2 m2'
       ret3 m3' Incr23 Sep23 WDnu23' nu23'valid
       MInj23' RValInjNu23' Fwd2 FwdTgt (*RetTypeTgt*)
     _ (eq_refl _) _ (eq_refl _) _ (eq_refl _)) as
     [d23' [c22' [c3' [AftExt22 [AftExt3 MC23']]]]];
    subst; clear eff_after_external23.
    (*discharge unchangedOn application conditions*)
      apply UnchMidA.
      apply UnchMidC.

  (*finally, instantiate the existentials, and establish conclusion*)
  rewrite AftExt22 in AftExt2. inv AftExt2.
  clear GLUEINV.
  exists (d12', Some c2', d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2'. exists m2'.
  exists (replace_externs nu12'
            (fun b => DomSrc nu12' b && (negb (locBlocksSrc nu12' b)
                                     && REACH m1' (exportedSrc nu12' (ret1::nil)) b))
            (fun b => DomTgt nu12' b && (negb (locBlocksTgt nu12' b)
                                     && REACH m2' (exportedTgt nu12' (ret2::nil)) b))).
  exists (replace_externs nu23'
            (fun b => DomSrc nu23' b && (negb (locBlocksSrc nu23' b)
                                     && REACH m2' (exportedSrc nu23' (ret2::nil)) b))
            (fun b => DomTgt nu23' b && (negb (locBlocksTgt nu23' b)
                                     && REACH m3' (exportedTgt nu23' (ret3::nil)) b))).
  split. reflexivity.
  unfold compose_sm. simpl.
         repeat rewrite replace_externs_extBlocksSrc, replace_externs_extBlocksTgt,
                 replace_externs_locBlocksSrc, replace_externs_locBlocksTgt,
                 replace_externs_pubBlocksSrc, replace_externs_pubBlocksTgt,
                 replace_externs_frgnBlocksSrc, replace_externs_frgnBlocksTgt.
        rewrite replace_externs_extern, replace_externs_local.
        rewrite replace_externs_extern, replace_externs_local.
  split. f_equal; trivial.
         unfold exportedSrc; simpl.
           rewrite sharedSrc_iff_frgnpub; trivial.
           rewrite sharedSrc_iff_frgnpub; trivial.
  clear UnchLOOR13 UnchPrivSrc SEP INC MID UnchMidB Incr12
        Sep12 WDnu12 nu12_valid MinjNu12 UnchMidC UnchMidA Sep23
        Incr23 nu23_valid WDnu23 MinjNu23 MemInjMu ValInjMu.
  split.
    clear MC23' MC12'.
    repeat (split; trivial). unfold DomTgt, DomSrc.
    rewrite GLUEa', GLUEb'.
         intros. do 2 rewrite andb_true_iff.
                 do 2 rewrite andb_true_iff in H.
                 destruct H as [HH1 [HH2 HH3]].
                 split; trivial. split; trivial.
                 eapply REACH_mono; try eassumption.
                 unfold exportedTgt, exportedSrc; intros.
                 apply orb_true_iff. apply orb_true_iff in H.
                 destruct H.
                   left; trivial.
                   right. unfold sharedTgt in H.
                          rewrite sharedSrc_iff_frgnpub.
                          apply orb_true_intro.
                          apply orb_prop in H.
                          destruct H.
                            left. intuition.
                            right. intuition.
               assumption.
   split; assumption.
Qed.

End Eff_sim_trans.