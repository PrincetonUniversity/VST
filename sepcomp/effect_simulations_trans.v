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

Lemma compose_sm_EraseUnknown: forall mu1 mu2 (WD1: SM_wd mu1)
   (F: forall b, frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true),
   EraseUnknown (compose_sm mu1 mu2) =
   compose_sm (EraseUnknown mu1) (EraseUnknown mu2).
Proof. intros.
  unfold compose_sm; simpl.
  do 2 rewrite EraseUnknown_extern.
  do 2 rewrite EraseUnknown_local.
  f_equal; try (destruct mu1; simpl; reflexivity).
  destruct mu2; simpl; reflexivity.
  destruct mu2; simpl; reflexivity.
  destruct mu2; simpl; reflexivity.
  destruct mu2; simpl; reflexivity.
  extensionality b. unfold compose_meminj.
  remember (frgnBlocksSrc mu1 b) as f.
  destruct f; trivial; apply eq_sym in Heqf.
  destruct (frgnSrc _ WD1 _ Heqf) as [b2 [d1 [F1 FT2]]].
  apply F in FT2; clear F.
  rewrite (foreign_in_extern _ _ _ _ F1), FT2. trivial.
Qed.

Lemma compose_sm_TrimUnknown: forall mu1 mu2,
   TrimUnknown (compose_sm mu1 mu2) =
   compose_sm mu1 (TrimUnknown mu2).
Proof. intros.
  unfold compose_sm; simpl.
  rewrite TrimUnknown_extern.
  rewrite TrimUnknown_local.
  f_equal; try (destruct mu1; simpl; reflexivity).
  destruct mu2; simpl; reflexivity.
  destruct mu2; simpl; reflexivity.
  destruct mu2; simpl; reflexivity.
  destruct mu2; simpl; reflexivity.
  extensionality b1. unfold compose_meminj.
  remember (extern_of mu1 b1) as d.
  destruct d; apply eq_sym in Heqd; trivial.
  destruct p as [b2 delta1].
  remember (extern_of mu2 b2) as w.
  destruct w; apply eq_sym in Heqw; trivial.
  destruct p as [b3 delta2].
  remember (frgnBlocksTgt mu2 b3) as f.
  destruct f; trivial.
Qed.


Lemma initial_inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
       (forall b1, (exists b3 d, compose_meminj j1 j2 b1 = Some(b3,d))
                   <-> (exists b2 d1, j1 b1 = Some(b2,d1))) /\
       forall b2 b3 d2, j2 b2 =Some(b3,d2) ->
                   exists b1 d, compose_meminj j1 j2 b1 = Some(b3,d).
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
  repeat (split; trivial).
  intros. destruct H as [b3 [d COMP]].
    destruct (compose_meminjD_Some _ _ _ _ _ COMP) as
        [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear COMP.
    exists b2, d1; trivial.
  intros. destruct H as [b2 [d1 J1]].
    destruct (X _ _ _ J1) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H1. exfalso. xomega.
  intros.
    destruct (Y _ _ _ H) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H2. exfalso. xomega.
Qed.

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
        (SIM12: @SM_simulation_inject _ _ _ _ _ Sem1 Sem2 g1 g2 epts12)
        (SIM23: @SM_simulation_inject _ _ _ _ _ Sem2 Sem3 g2 g3 epts23),
        @SM_simulation_inject _ _ _ _ _ Sem1 Sem3 g1 g3 epts13.
Proof. (*follows structure of forward_simulations_trans.injinj*)
  intros.
  destruct SIM12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      match_sm_wd12 match_norm12 (*match_eraseUnknown12*)
      match_validblock12 core_initial12 core_diagram12 eff_diagram12 strong_diagram12
      core_halted12 core_at_external12 eff_after_external12].  
  destruct SIM23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_sm_wd23 match_norm23 (*match_eraseUnknown23*)
      match_validblock23 core_initial23 core_diagram23 eff_diagram23 strong_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply Build_SM_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d mu c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists mu1, exists mu2, 
          X=Some c2 /\ mu = compose_sm mu1 mu2 /\
          (DomTgt mu1 = DomSrc mu2 /\
           myBlocksTgt mu1 = myBlocksSrc mu2 /\
           (forall b, pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
           (forall b, frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\ 
          match_core12 d1 mu1 c1 m1 c2 m2 /\ match_core23 d2 mu2 c2 m2 c3 m3 
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
 (*match_sm_wd*) intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  specialize (match_sm_wd12 _ _ _ _ _ _ MC12).
  specialize (match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct INV as [INVa [INVb [INVc INVd]]].
  eapply (compose_sm_wd); eauto.
 (*match_norm*)
    clear match_validblock12 match_validblock23 core_diagram23  core_halted23 
    core_at_external23 (*eff_after_external23*) core_diagram12 strong_diagram12
    core_halted12 core_at_external12 (*eff_after_external12*)
    eff_diagram12 strong_diagram23 eff_diagram23.
    clear eff_after_external23 core_initial23 eff_after_external12
          core_initial12.
    intros. rename c2 into c3.  rename m2 into m3.
      destruct d as [[d12 cc2] d23]. rename mu23 into downstreamMu.
      destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.

    specialize (match_norm23 _ _ _ _ _ _ MC23 downstreamMu H0).
    specialize (match_norm12 _ _ _ _ _ _ MC12 (sm_extern_normalize mu23 downstreamMu)).
    exists c2, m2.
    exists (sm_extern_normalize mu12 (sm_extern_normalize mu23 downstreamMu)). 
    exists (sm_extern_normalize mu23 downstreamMu). 
    simpl in *. split. trivial. 
    rewrite sm_extern_normalize_myBlocksTgt, sm_extern_normalize_DomTgt,
                    sm_extern_normalize_pubBlocksTgt, sm_extern_normalize_frgnBlocksTgt. 
    rewrite sm_extern_normalize_myBlocksSrc, sm_extern_normalize_DomSrc,
                    sm_extern_normalize_pubBlocksSrc, sm_extern_normalize_frgnBlocksSrc.
    split. destruct mu12; simpl in *. unfold compose_sm; simpl.
            rewrite sm_extern_normalize_myBlocksTgt, sm_extern_normalize_DomTgt,
                    sm_extern_normalize_pubBlocksTgt, sm_extern_normalize_frgnBlocksTgt.
           destruct mu23; simpl in *. rewrite <- normalize_compose_commute. 
           eapply f_equal.
       trivial.
    split. apply INV.
    split; try assumption.
    apply match_norm12.
      split. eapply sm_extern_normalize_WD.
                eauto. apply H0. apply H0.
      rewrite sm_extern_normalize_myBlocksSrc, sm_extern_normalize_DomSrc,
              sm_extern_normalize_pubBlocksSrc, sm_extern_normalize_frgnBlocksSrc.
      apply INV. 
 (*TrimUnknown
    clear match_norm12 match_norm23 core_diagram23  core_halted23 
       core_at_external23 (*eff_after_external23 *)
    core_diagram12  core_halted12 core_at_external12 (*eff_after_external12*)
    eff_diagram12 eff_diagram23 strong_diagram12 strong_diagram23.
    clear eff_after_external23 (*eff_after_external_ModEffects12 *)
     core_initial23  (*eff_after_external_ModEffects23 *)
     eff_after_external12 core_initial12.
    intros. rename c2 into c3.  rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.??*)
 (*eraseUnknown
    clear match_norm12 match_norm23 core_diagram23  core_halted23 
       core_at_external23 (*eff_after_external23 *)
    core_diagram12  core_halted12 core_at_external12 (*eff_after_external12*)
    eff_diagram12 eff_diagram23 strong_diagram12 strong_diagram23.
    clear eff_after_external23 (*eff_after_external_ModEffects12 *)
     core_initial23  (*eff_after_external_ModEffects23 *)
     eff_after_external12 core_initial12.
    intros. rename c2 into c3.  rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
    specialize (match_eraseUnknown12 _ _ _ _ _ _ MC12).
    specialize (match_eraseUnknown23 _ _ _ _ _ _ MC23).
    exists c2, m2, (EraseUnknown mu12), (EraseUnknown mu23).
    split; trivial.
    split. eapply compose_sm_EraseUnknown. eauto. eapply INV.
    split. destruct mu12; destruct mu23; simpl in *. apply INV.
    split; assumption.*)
 (*sm_valid*)
    clear match_norm12 match_norm23 core_diagram23  core_halted23 
       core_at_external23 (*eff_after_external23 *)
    core_diagram12  core_halted12 core_at_external12 (*eff_after_external12*)
    eff_diagram12 eff_diagram23 strong_diagram12 strong_diagram23.
    clear eff_after_external23 (*eff_after_external_ModEffects12 *)
     core_initial23  (*eff_after_external_ModEffects23 *)
     eff_after_external12 core_initial12.
    intros. rename c2 into c3.  rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
    specialize (match_validblock12 _ _ _ _ _ _ MC12).
    specialize (match_validblock23 _ _ _ _ _ _ MC23).
    unfold sm_valid, compose_sm. destruct mu12; destruct mu23; simpl in *.
    split; intros. eapply match_validblock12. apply H.
    eapply match_validblock23. apply H.
 (*initial_core*) 
  intros; trivial. 
  clear core_diagram23  core_halted23 core_at_external23 
    eff_after_external23 
    core_diagram12  core_halted12 core_at_external12 eff_after_external12
    eff_diagram12 eff_diagram23 strong_diagram12 strong_diagram23.
  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3. 
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). 
  eapply forall_valinject_hastype; eassumption.
  destruct (initial_inject_split _ _ _ H1) as [m2 [j1 [j2 [J [Inj12 [Inj23 [X Y]]]]]]].
  subst.
  destruct (Forward_simulation_trans.forall_val_inject_split _ _ _ _ H2) as [vals2 [ValsInj12 ValsInj23]].
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ vals2 _ 
      DomS (fun b => match j2 b with None => false | Some (b3,d) => DomT b3 end) H0 Inj12)
     as [d12 [c2 [Ini2 MC12]]]; try assumption.
      eapply forall_valinject_hastype; eassumption.
      intros. destruct (X b1) as [_ ?]. 
              destruct H6 as [b3 [dd COMP]]. exists b2, d; trivial.
              specialize (H4 _ _ _ COMP).
              destruct (compose_meminjD_Some _ _ _ _ _ COMP)
                as [bb2 [dd1 [dd2 [J1 [J2 D]]]]]; subst; clear COMP.
              rewrite J1 in H; inv H. rewrite J2. apply H4.
      intros. specialize (getBlocks_inject _ _ _  ValsInj23). intros.
        destruct (REACH_inject _ _ _ Inj23 (getBlocks vals2) (getBlocks vals3) H6 _ H) as [b3 [d2 [J2 R3]]].
        rewrite J2. apply (H5 _ R3).
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ vals3 _ 
       (fun b => match j2 b with None => false | Some (b3,d) => DomT b3 end) DomT Ini2 Inj23)
     as [d23 [c3 [Ini3 MC23]]]; try assumption. 
       intros b2 b3 d2 J2. rewrite J2.
         destruct (Y _ _ _ J2) as [b1 [d COMP]].
         destruct (H4 _ _ _ COMP). split; trivial.
  remember ((initial_SM DomS
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) (REACH m1 (getBlocks vals1)) (REACH m2 (getBlocks vals2))
            j1)) as mu1.
  remember (initial_SM
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) DomT (REACH m2 (getBlocks vals2))
            (REACH m3 (getBlocks vals3)) j2) as mu2.
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
  clear match_norm12 match_norm23 core_initial23 core_halted23 core_at_external23 
    (*eff_after_external23*)
    core_initial12  core_halted12 core_at_external12 (*eff_after_external12*)
    EPC epts12 epts23 epts13 eff_diagram12 eff_diagram23
   eff_after_external12 eff_after_external23 strong_diagram12 strong_diagram23
   (*eff_after_external_ModEffects12 eff_after_external_ModEffects23*).
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  eapply diagram_injinj; try eassumption.
 (*eff_diagram*)
  clear core_initial23 match_norm12 match_norm23 core_halted23 core_at_external23 
   (*eff_after_external23*)
    core_initial12  core_halted12 core_at_external12 (*eff_after_external12*)
    EPC epts12 epts23 epts13 core_diagram12 core_diagram23
    eff_after_external12 eff_after_external23 strong_diagram12 strong_diagram23
    (*eff_after_external_ModEffects12 eff_after_external_ModEffects23*).
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [m2 [j12 [j23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  eapply effdiagram_injinj; try eassumption.
 (*strong_diagram*)
  clear core_initial23 match_norm12 match_norm23 core_halted23 core_at_external23 
    (*eff_after_external23*)
    core_initial12  core_halted12 core_at_external12 (*eff_after_external12*)
    EPC epts12 epts23 epts13 core_diagram12 core_diagram23
    eff_after_external12 eff_after_external23 eff_diagram12 eff_diagram23
    (*eff_after_external_ModEffects12 eff_after_external_ModEffects23*).
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [m2 [j12 [j23 [X [J [INV [MC12 MC23]]]]]]]]; subst.
  eapply effdiagram_strong_injinj; try eassumption.
(*halted*)
  clear match_norm12 match_norm23 core_initial23 core_at_external23 eff_after_external23
    core_initial12  core_at_external12 eff_after_external12
    EPC epts12 epts23 epts13 core_diagram12 core_diagram23
    eff_diagram12 eff_diagram23 strong_diagram12 strong_diagram23.
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
           eapply val_inject_compose; eassumption.
  assumption.

(*at_external*)
  clear match_norm12 match_norm23 core_initial23 core_halted23 eff_after_external23 
    core_initial12  core_halted12 eff_after_external12
    EPC epts12 epts23 epts13 core_diagram12 core_diagram23
    eff_diagram12 eff_diagram23.
  intros. rename c2 into c3. rename m2 into m3.
  rename H0 into AtExtSrc. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]]. 
  subst. 
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [MInj12 [vals2 [ArgsInj12 [ArgsHT2 AtExt2]]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [MInj23 [vals3 [ArgsInj23 [ArgsHTTgt AtExtTgt]]]]; clear core_at_external23.
  rewrite compose_sm_as_inj; try eauto.   
    split. eapply Mem.inject_compose; eassumption.
    exists vals3.
    split. eapply forall_val_inject_compose; eassumption.
    split; assumption.
  (*apply (match_sm_wd12 _ _ _ _ _ _ MC12).
  apply (match_sm_wd23 _ _ _ _ _ _ MC23).*)
  eapply GLUEINV. 
(*eff_after_external - version using match_eraseUnknown
  clear core_diagram12 core_initial12 core_halted12 eff_diagram12 
        core_diagram23 core_initial23 core_halted23 eff_diagram23
        (*eff_after_external12 eff_after_external23
        eff_after_external_ModEffects12 eff_after_external_ModEffects23*)
        strong_diagram23 strong_diagram12 match_norm12 match_norm23.
    (*core_at_externalFAT1*) (*FAT0 core_at_externalFAT0*) 
  intros. rename st2 into st3. rename m2 into m3. 
          rename vals2 into vals3'. rename m2' into m3'.
          rename UnchLOOR into UnchLOOR13.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]].
  specialize (match_eraseUnknown12 _ _ _ _ _ _ MC12). 
  specialize (match_eraseUnknown23 _ _ _ _ _ _ MC23). clear match_eraseUnknown23.
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  clear MC12. remember (EraseUnknown mu12) as nmu12.
  assert (WDnmu12:= match_sm_wd12 _ _ _ _ _ _ match_eraseUnknown12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  assert (HmuNorm: mu = compose_sm nmu12 mu23).
     subst. apply sm_extern_normalize_compose_sm.
  clear HMu.
  assert (WDmu: SM_wd (compose_sm nmu12 mu23)).
    eapply compose_sm_wd; try eassumption.
      subst. rewrite sm_extern_normalize_pubBlocksTgt. apply GLUEINV.
      subst. rewrite sm_extern_normalize_frgnBlocksTgt. apply GLUEINV.
  clear match_norm12.
  assert (mu12_valid:= match_validblock12 _ _ _ _ _ _ NormMC12).
  assert (mu23_valid:= match_validblock23 _ _ _ _ _ _ MC23).
  rename ret2 into ret3.  
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ NormMC12 AtExtSrc)
   as [MInj12 [vals2 [ArgsInj12 [ArgsHT2 AtExt2]]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
   as [MInj23 [vals3 [ArgsInj23 [ArgsHT3 AtExt3]]]]; clear core_at_external23.
  
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
  assert (LeakedCompSrc: myBlocksSrc mu = myBlocksSrc nmu12 /\
                        exportedSrc mu vals1 = exportedSrc nmu12 vals1). 
     subst. clear - WDnmu12 WDmu. simpl.  
        rewrite sm_extern_normalize_myBlocksSrc.
        unfold exportedSrc. 
        rewrite sharedSrc_iff_frgnpub; trivial. simpl. 
        rewrite sharedSrc_iff_frgnpub; trivial.
        rewrite sm_extern_normalize_frgnBlocksSrc, sm_extern_normalize_pubBlocksSrc.
        intuition.
  destruct LeakedCompSrc as [LSa LSb]. rewrite LSa, LSb in *. clear LSa LSb.
  assert (LeakedCompTgt: myBlocksTgt mu = myBlocksTgt mu23 
                       /\ exportedTgt mu vals3 = exportedTgt mu23 vals3).
     subst. clear - WDmu23 WDmu. simpl.  
        unfold exportedTgt, sharedTgt. simpl. intuition. 
  destruct LeakedCompTgt as [LTa LTb]. rewrite LTa, LTb in *. clear LTa LTb.
   remember (fun b => myBlocksTgt nmu12 b && 
             REACH m2 (exportedTgt nmu12 vals2) b) as pubTgtMid'.
   remember (fun b => myBlocksSrc mu23 b && 
             REACH m2 (exportedSrc mu23 vals2) b) as pubSrcMid'.
   assert (MID: forall b, pubTgtMid' b = true -> pubSrcMid' b = true).
        clear eff_after_external12 match_validblock23 eff_after_external23.
        rewrite HeqpubTgtMid', HeqpubSrcMid'. 
        destruct GLUEINV as [? [? [? ?]]].
        subst.
        rewrite sm_extern_normalize_myBlocksTgt, sm_extern_normalize_exportedTgt; trivial.
           rewrite H0. intros. rewrite andb_true_iff in *.
        destruct H3. split; trivial.
        eapply REACH_mono; try eassumption.
        unfold exportedTgt, exportedSrc, sharedTgt.
        rewrite sharedSrc_iff_frgnpub; trivial.
        intros. repeat rewrite orb_true_iff in *.
        intuition.
  assert (NU: nu = compose_sm (replace_locals nmu12 pubSrc' pubTgtMid')
              (replace_locals mu23 pubSrcMid' pubTgt')).
     clear frgnSrcHyp frgnTgtHyp eff_after_external23.
     subst. unfold compose_sm; simpl.
     rewrite replace_locals_extern, replace_locals_local,
             replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
            replace_locals_DomSrc, replace_locals_DomTgt.
     rewrite replace_locals_extern, replace_locals_local.
     rewrite sm_extern_normalize_DomSrc, sm_extern_normalize_myBlocksSrc,
             sm_extern_normalize_local, sm_extern_normalize_extern.
     f_equal. 

  clear NuHyp.
  (*produce all the hypothesis necessary for applying interpolation*)
  assert (MinjNu12: Mem.inject (as_inj (replace_locals nmu12 pubSrc' pubTgtMid')) m1 m2).
     rewrite replace_locals_as_inj. assumption.
  assert (MinjNu23: Mem.inject (as_inj (replace_locals mu23 pubSrcMid' pubTgt')) m2 m3).
     rewrite replace_locals_as_inj. assumption.
  assert (WDnu12: SM_wd (replace_locals nmu12 pubSrc' pubTgtMid')).
       subst.
       eapply replace_locals_wd; try eassumption.
         intros. apply andb_true_iff in H.
           destruct H as [myB R].
           destruct (REACH_local_REACH _ WDnmu12 _ _ _ _ 
              MInj12 ArgsInj12 _ R myB) as [b2 [d1 [LOC12 R2]]].
           exists b2, d1; split; trivial.
           rewrite andb_true_iff, R2.
           split; trivial.
           eapply local_myBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H. 
  assert (WDnu23: SM_wd (replace_locals mu23 pubSrcMid' pubTgt')).
       subst. 
       eapply replace_locals_wd; try eassumption.
       destruct GLUEINV as [GIa [GIb [GIc GId]]]. subst. 
       intros b2; intros. apply andb_true_iff in H.
           destruct H as [myB R].
           destruct (REACH_local_REACH _ WDmu23 _ _ _ _ 
              MInj23 ArgsInj23 _ R myB) as [b3 [d2 [LOC23 R3]]].
           exists b3, d2; split; trivial.
           rewrite andb_true_iff, R3.
           split; trivial.
           eapply local_myBlocks; eassumption.
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
        [nu23'valid [GLUEINV' [Norm' [UnchMidA
        [UnchMidB UnchMidC]]]]]]]]]]]]]]]]]; simpl in *.
    (*discharge the unchOn application conditions*)
       subst; apply UnchPrivSrc.
       subst. apply UnchLOOR13. 
    (*discharge the GLUE application condition*)
      rewrite replace_locals_DomSrc, replace_locals_DomTgt,
            replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
      destruct GLUEINV as [GLUEa [GLUEb [GLUEc GLUEd]]].
      repeat (split; trivial).
      subst. rewrite sm_extern_normalize_DomTgt; trivial.
      subst. rewrite sm_extern_normalize_myBlocksTgt; trivial.
      subst. rewrite sm_extern_normalize_frgnBlocksTgt; trivial.
    (*discharge the Norm Hypothesis*)
      rewrite Heqnmu12. do 2 rewrite replace_locals_extern.
      intros.
      destruct (sm_extern_normalize_norm _ _ _ _ _ H) as [EXT1 [[b3 d2] EXT2]].
      exists b3, d2; trivial.

  (*next, prepare for application of eff_after_external12*)
  destruct GLUEINV' as [WDnu12' [WDnu23' [GLUEa' [GLUEb' [GLUEc' GLUEd']]]]].
  assert (exists ret2, val_inject (as_inj nu12') ret1 ret2 /\ 
                       val_inject (as_inj nu23') ret2 ret3 /\
                       Val.has_type ret2 (proj_sig_res ef_sig)(* /\
                       val_valid ret2 m2'*)). 
    subst. rewrite compose_sm_as_inj in RValInjNu'; trivial.
    destruct (val_inject_split _ _ _ _ RValInjNu')
      as [ret2 [RValInjNu12' RValInjNu23']].  
    exists ret2. repeat (split; trivial).
    eapply valinject_hastype; eassumption.
  destruct H as [ret2 [RValInjNu12' [RValInjNu23' RetType2]]].
  subst. 
  specialize (eff_after_external12 nu12' ret1 
     m1' ret2 m2' Incr12 Sep12 WDnu12' nu12'valid MInj12' RValInjNu12'
     FwdSrc Fwd2 RetType2).

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
       MInj23' RValInjNu23' Fwd2 FwdTgt RetTypeTgt
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
            (fun b => DomSrc nu12' b && (negb (myBlocksSrc nu12' b) 
                                     && REACH m1' (exportedSrc nu12' (ret1::nil)) b))
            (fun b => DomTgt nu12' b && (negb (myBlocksTgt nu12' b) 
                                     && REACH m2' (exportedTgt nu12' (ret2::nil)) b))).
  exists (replace_externs nu23'
            (fun b => DomSrc nu23' b && (negb (myBlocksSrc nu23' b) 
                                     && REACH m2' (exportedSrc nu23' (ret2::nil)) b))
            (fun b => DomTgt nu23' b && (negb (myBlocksTgt nu23' b) 
                                     && REACH m3' (exportedTgt nu23' (ret3::nil)) b))).
  split. reflexivity.
  unfold compose_sm. simpl.
         repeat rewrite replace_externs_DomSrc, replace_externs_DomTgt, 
                 replace_externs_myBlocksSrc, replace_externs_myBlocksTgt,
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
    repeat (split; trivial).
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
Qed.*)
(*eff_after_external - version using match_norm*)
  clear core_diagram12 core_initial12 core_halted12 eff_diagram12 
        core_diagram23 core_initial23 core_halted23 eff_diagram23
        strong_diagram23 strong_diagram12 match_norm23 
        (*match_eraseUnknown12 match_eraseUnknown23*).
  intros. rename st2 into st3. rename m2 into m3. 
          rename vals2 into vals3'. rename m2' into m3'.
          rename UnchLOOR into UnchLOOR13.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]].
  assert (NormMC12: match_core12 d12 (sm_extern_normalize mu12 mu23) st1 m1 st2 m2).
      eapply (match_norm12 _ _ _ _ _ _ MC12 mu23).
      split. eauto. apply GLUEINV.
  
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  clear MC12. remember (sm_extern_normalize mu12 mu23) as nmu12.
  assert (WDnmu12:= match_sm_wd12 _ _ _ _ _ _ NormMC12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  assert (HmuNorm: mu = compose_sm nmu12 mu23).
     subst. apply sm_extern_normalize_compose_sm.
  clear HMu.
  assert (WDmu: SM_wd (compose_sm nmu12 mu23)).
    eapply compose_sm_wd; try eassumption.
      subst. rewrite sm_extern_normalize_pubBlocksTgt. apply GLUEINV.
      subst. rewrite sm_extern_normalize_frgnBlocksTgt. apply GLUEINV.
  clear match_norm12.
  assert (mu12_valid:= match_validblock12 _ _ _ _ _ _ NormMC12).
  assert (mu23_valid:= match_validblock23 _ _ _ _ _ _ MC23).
  rename ret2 into ret3.  
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ NormMC12 AtExtSrc)
   as [MInj12 [vals2 [ArgsInj12 [ArgsHT2 AtExt2]]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
   as [MInj23 [vals3 [ArgsInj23 [ArgsHT3 AtExt3]]]]; clear core_at_external23.
  
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
  assert (LeakedCompSrc: myBlocksSrc mu = myBlocksSrc nmu12 /\
                        exportedSrc mu vals1 = exportedSrc nmu12 vals1). 
     subst. clear - WDnmu12 WDmu. simpl.  
        rewrite sm_extern_normalize_myBlocksSrc.
        unfold exportedSrc. 
        rewrite sharedSrc_iff_frgnpub; trivial. simpl. 
        rewrite sharedSrc_iff_frgnpub; trivial.
        rewrite sm_extern_normalize_frgnBlocksSrc, sm_extern_normalize_pubBlocksSrc.
        intuition.
  destruct LeakedCompSrc as [LSa LSb]. rewrite LSa, LSb in *. clear LSa LSb.
  assert (LeakedCompTgt: myBlocksTgt mu = myBlocksTgt mu23 
                       /\ exportedTgt mu vals3 = exportedTgt mu23 vals3).
     subst. clear - WDmu23 WDmu. simpl.  
        unfold exportedTgt, sharedTgt. simpl. intuition. 
  destruct LeakedCompTgt as [LTa LTb]. rewrite LTa, LTb in *. clear LTa LTb.
   remember (fun b => myBlocksTgt nmu12 b && 
             REACH m2 (exportedTgt nmu12 vals2) b) as pubTgtMid'.
   remember (fun b => myBlocksSrc mu23 b && 
             REACH m2 (exportedSrc mu23 vals2) b) as pubSrcMid'.
   assert (MID: forall b, pubTgtMid' b = true -> pubSrcMid' b = true).
        clear eff_after_external12 match_validblock23 eff_after_external23.
        rewrite HeqpubTgtMid', HeqpubSrcMid'. 
        destruct GLUEINV as [? [? [? ?]]].
        subst.
        rewrite sm_extern_normalize_myBlocksTgt, sm_extern_normalize_exportedTgt; trivial.
           rewrite H0. intros. rewrite andb_true_iff in *.
        destruct H3. split; trivial.
        eapply REACH_mono; try eassumption.
        unfold exportedTgt, exportedSrc, sharedTgt.
        rewrite sharedSrc_iff_frgnpub; trivial.
        intros. repeat rewrite orb_true_iff in *.
        intuition.
  assert (NU: nu = compose_sm (replace_locals nmu12 pubSrc' pubTgtMid')
              (replace_locals mu23 pubSrcMid' pubTgt')).
     clear frgnSrcHyp frgnTgtHyp eff_after_external23.
     subst. unfold compose_sm; simpl.
     rewrite replace_locals_extern, replace_locals_local,
             replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
            replace_locals_DomSrc, replace_locals_DomTgt.
     rewrite replace_locals_extern, replace_locals_local.
     rewrite sm_extern_normalize_DomSrc, sm_extern_normalize_myBlocksSrc,
             sm_extern_normalize_local, sm_extern_normalize_extern.
     f_equal. 

  clear NuHyp.
  (*produce all the hypothesis necessary for applying interpolation*)
  assert (MinjNu12: Mem.inject (as_inj (replace_locals nmu12 pubSrc' pubTgtMid')) m1 m2).
     rewrite replace_locals_as_inj. assumption.
  assert (MinjNu23: Mem.inject (as_inj (replace_locals mu23 pubSrcMid' pubTgt')) m2 m3).
     rewrite replace_locals_as_inj. assumption.
  assert (WDnu12: SM_wd (replace_locals nmu12 pubSrc' pubTgtMid')).
       subst.
       eapply replace_locals_wd; try eassumption.
         intros. apply andb_true_iff in H.
           destruct H as [myB R].
           destruct (REACH_local_REACH _ WDnmu12 _ _ _ _ 
              MInj12 ArgsInj12 _ R myB) as [b2 [d1 [LOC12 R2]]].
           exists b2, d1; split; trivial.
           rewrite andb_true_iff, R2.
           split; trivial.
           eapply local_myBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H. 
  assert (WDnu23: SM_wd (replace_locals mu23 pubSrcMid' pubTgt')).
       subst. 
       eapply replace_locals_wd; try eassumption.
       destruct GLUEINV as [GIa [GIb [GIc GId]]]. subst. 
       intros b2; intros. apply andb_true_iff in H.
           destruct H as [myB R].
           destruct (REACH_local_REACH _ WDmu23 _ _ _ _ 
              MInj23 ArgsInj23 _ R myB) as [b3 [d2 [LOC23 R3]]].
           exists b3, d2; split; trivial.
           rewrite andb_true_iff, R3.
           split; trivial.
           eapply local_myBlocks; eassumption.
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
        [nu23'valid [GLUEINV' [Norm' [UnchMidA
        [UnchMidB UnchMidC]]]]]]]]]]]]]]]]]; simpl in *.
    (*discharge the unchOn application conditions*)
       subst; apply UnchPrivSrc.
       subst. apply UnchLOOR13. 
    (*discharge the GLUE application condition*)
      rewrite replace_locals_DomSrc, replace_locals_DomTgt,
            replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
      destruct GLUEINV as [GLUEa [GLUEb [GLUEc GLUEd]]].
      repeat (split; trivial).
      subst. rewrite sm_extern_normalize_DomTgt; trivial.
      subst. rewrite sm_extern_normalize_myBlocksTgt; trivial.
      subst. rewrite sm_extern_normalize_frgnBlocksTgt; trivial.
    (*discharge the Norm Hypothesis*)
      rewrite Heqnmu12. do 2 rewrite replace_locals_extern.
      intros.
      destruct (sm_extern_normalize_norm _ _ _ _ _ H) as [EXT1 [[b3 d2] EXT2]].
      exists b3, d2; trivial.

  (*next, prepare for application of eff_after_external12*)
  destruct GLUEINV' as [WDnu12' [WDnu23' [GLUEa' [GLUEb' [GLUEc' GLUEd']]]]].
  assert (exists ret2, val_inject (as_inj nu12') ret1 ret2 /\ 
                       val_inject (as_inj nu23') ret2 ret3 /\
                       Val.has_type ret2 (proj_sig_res ef_sig)(* /\
                       val_valid ret2 m2'*)). 
    subst. rewrite compose_sm_as_inj in RValInjNu'; trivial.
    destruct (val_inject_split _ _ _ _ RValInjNu')
      as [ret2 [RValInjNu12' RValInjNu23']].  
    exists ret2. repeat (split; trivial).
    eapply valinject_hastype; eassumption.
  destruct H as [ret2 [RValInjNu12' [RValInjNu23' RetType2]]].
  subst. 
  specialize (eff_after_external12 nu12' ret1 
     m1' ret2 m2' Incr12 Sep12 WDnu12' nu12'valid MInj12' RValInjNu12'
     FwdSrc Fwd2 RetType2).

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
       MInj23' RValInjNu23' Fwd2 FwdTgt RetTypeTgt
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
            (fun b => DomSrc nu12' b && (negb (myBlocksSrc nu12' b) 
                                     && REACH m1' (exportedSrc nu12' (ret1::nil)) b))
            (fun b => DomTgt nu12' b && (negb (myBlocksTgt nu12' b) 
                                     && REACH m2' (exportedTgt nu12' (ret2::nil)) b))).
  exists (replace_externs nu23'
            (fun b => DomSrc nu23' b && (negb (myBlocksSrc nu23' b) 
                                     && REACH m2' (exportedSrc nu23' (ret2::nil)) b))
            (fun b => DomTgt nu23' b && (negb (myBlocksTgt nu23' b) 
                                     && REACH m3' (exportedTgt nu23' (ret3::nil)) b))).
  split. reflexivity.
  unfold compose_sm. simpl.
         repeat rewrite replace_externs_DomSrc, replace_externs_DomTgt, 
                 replace_externs_myBlocksSrc, replace_externs_myBlocksTgt,
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
    repeat (split; trivial).
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
(*stuff for more complex coreHalted-rule:

  eexists; eexists; eexists.
   split. reflexivity.
   split. reflexivity.
   split. reflexivity.
   assert (MidLeak: forall b,
                  REACH m2 (exportedTgt mu12 (v2 :: nil)) b = true ->
                  REACH m2 (exportedSrc mu23 (v2 :: nil)) b = true).
             intros. eapply REACH_mono; try eassumption.
             unfold exportedSrc, exportedTgt, sharedTgt.
             rewrite sharedSrc_iff_frgnpub.
             simpl; intros.
             destruct (getBlocks (v2 :: nil) b0); simpl in *. 
                trivial.
             remember (frgnBlocksTgt mu12 b0) as d.
             destruct d; apply eq_sym in Heqd; simpl in *.
                rewrite (INVf _ Heqd). trivial.
                rewrite (INVe _ H1).
                destruct (frgnBlocksSrc mu23 b0); trivial.
            eauto.
   assert (PUBnu12: forall b : block, pubBlocksTgt nu12 b = true -> pubBlocksSrc nu23 b = true).
            subst. clear MInjSH12 MInjSH23 RValsInject12 RValsInject23.
            rewrite replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt.
            intros. rewrite andb_true_iff. rewrite andb_true_iff in H.
            destruct H. split. rewrite <- INVc; trivial.
            apply (MidLeak _ H1). 
   assert (FRGNnu12:forall b : block, frgnBlocksTgt nu12 b = true -> frgnBlocksSrc nu23 b = true).
            subst. clear MInjSH12 MInjSH23 RValsInject12 RValsInject23.
            rewrite replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
            apply INVf.

   assert (WDnu12: SM_wd nu12).
      subst.
      apply replace_locals_wd; trivial.
      clear FRGNnu12. rewrite replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc in PUBnu12.
      intros. rewrite andb_true_iff in H. destruct H. 
      assert (VALS12: Forall2 (val_inject (as_inj mu12)) (v1 :: nil) (v2 :: nil)).
        constructor. assumption. constructor.
      destruct (REACH_local_REACH _ WDmu12 _ _ (v1::nil) (v2::nil) MInjMu12 VALS12 _ H1 H)
        as [b2 [d1 [LOC12 R2]]].
      exists b2, d1. rewrite LOC12, R2.
      destruct (local_myBlocks _ WDmu12 _ _ _ LOC12) as [_ [? _]].
      rewrite H2. intuition.
      intros. apply andb_true_iff in H. intuition.

    assert (SH: sharedSrc (compose_sm mu12 mu23) = sharedSrc mu12).
        clear MidLeak HpubTgt123' HpubSrc23' MInj12 MInj12 HpubTgt12' HpubSrc12'.
        rewrite sharedSrc_iff_frgnpub. simpl. 
        rewrite sharedSrc_iff_frgnpub. trivial.
        eauto. eauto. ??. (*TODO*)
    split. 
       assert (VI:= val_inject_compose _ _ _ _ _ RValsInject12 RValsInject23).
       rewrite <- compose_sm_shared in VI. subst. simpl.
       unfold compose_sm in VI. simpl in *.
       unfold shared_of. unfold shared_of in VI. simpl in *. 
       rewrite replace_locals_local, replace_locals_pubBlocksSrc, replace_locals_extern, replace_locals_frgnBlocksSrc in VI.
       rewrite replace_locals_local,replace_locals_extern in VI.  simpl.
       assert (exportedSrc (compose_sm mu12 mu23) (v1 :: nil) = exportedSrc mu12 (v1 :: nil)).
          unfold exportedSrc. rewrite SH. trivial.
       rewrite H1. apply VI.
       apply PUBnu12. 
       apply FRGNnu12. 
      eauto. eauto. eauto. eauto. 

       subst. eapply replace_locals_wd. eauto.
         intros. rewrite replace_locals_shared in MInj12.
         apply andb_true_iff in H1. destruct H1. 
         specialize (REACH_inject _ _ _ MInj12 
           (exportedSrc mu12 (v1 :: nil)) (exportedTgt mu12 (v2 :: nil))).
         intros.
        assert (forall b : block,
      exportedSrc mu12 (v1 :: nil) b = true ->
      exists (jb : block) (d : Z),
        join (foreign_of mu12)
          (fun b0 : block =>
           if myBlocksSrc mu12 b0 &&
              REACH m1 (exportedSrc mu12 (v1 :: nil)) b0
           then local_of mu12 b0
           else None) b = Some (jb, d) /\
        exportedTgt mu12 (v2 :: nil) jb = true).
           clear H6; intros. unfold exportedSrc in H6.
             

         eauto. assumption.       intros. apply andb_true_iff in H. destruct H.
        apply andb_true_iff. 
        destruct INV as [? [? [? [? [? ?]]]]]. rewrite H4 in *. rewrite <- H5 in *.
        split; trivial. unfold exportedSrc. unfold exportedTgt, sharedTgt in H1.
          rewrite sharedSrc_iff_frgnpub.
          eapply REACH_mono; try eassumption.
           simpl; intros.
           destruct (getBlocks (v2 :: nil) b0); simpl in *. 
              trivial.
           remember (frgnBlocksTgt mu12 b0) as d.
           destruct d; apply eq_sym in Heqd; simpl in *.
              rewrite (H7 _ Heqd). trivial.
              rewrite (H6 _ H8).
              destruct (frgnBlocksSrc mu23 b0); trivial.
            eauto.
              
           apply orb_true_iff in H8.
           destruct H8. rewrite H8. reflexivity.  apply H.
         eauto. intros. trivial. 
  split. eapply Mem.inject_compose; eassumption.
  assumption. subst.
   split.
  
(*eff_after_external_ModEffects*)
  clear core_diagram12 core_initial12 core_halted12 eff_diagram12 
        core_diagram23 core_initial23 core_halted23 eff_diagram23
        eff_after_external12 eff_after_external23
    (*core_at_externalFAT1*) (*FAT0 core_at_externalFAT0*). 
  intros. rename st2 into st3. rename m2 into m3. 
          rename vals2 into vals3'. rename m2' into m3'.
          rename M2 into M3.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [mu12 [mu23 [Dom2 [myBlocks2 
      [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]]]]. 
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  assert (WDmu: SM_wd (compose_sm mu12 mu23)).
    eapply compose_sm_wd; try eassumption.
      apply GLUEINV.
      apply GLUEINV.
  assert (mu12_valid:= match_validblock12 _ _ _ _ _ _ MC12).
  assert (mu23_valid:= match_validblock23 _ _ _ _ _ _ MC23).
  rename ret2 into ret3.  
  (*rename ValidSourceArgs into ValidArgs1.*)
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExtSrc (* ValidArgs1*))
   as [vals2 [MInj12 [ArgsInj12 [ArgsHT2 AtExt2 (*ValidArgs2*)]]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 (*ValidArgs2*))
   as [vals3 [MInj23 [ArgsInj23 [ArgsHT3 AtExt3 (*ValidArgs3*)]]]]; clear core_at_external23.
  
  (*Prove uniqueness of e, ef_sig, vals3. We do this by hand, instead of 
     rewrite AtExtTgt in AtExt3; inv Atext3 in order to avoid the subst
     taht's inherent in inv AtExt3. Probably there's a better way to do this..*)
  assert (e' = e /\ ef_sig' = ef_sig /\ vals3'=vals3).
     rewrite AtExtTgt in AtExt3. inv AtExt3. intuition.
  destruct H as [HH1 [HH2 HH3]].
  rewrite HH1, HH2, HH3 in *. clear HH1 HH2 HH3 e' ef_sig' vals3' AtExt3.

  (*clear MemInjMu. follows from MInj12 MInj23*)
  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ MInj12 
        MC12 AtExtSrc AtExt2 ArgsInj12 (*ValidArgs1*) 
        _ (eq_refl _) _ (eq_refl _)). 
   assert (LeakedCompSrc: myBlocksSrc mu = myBlocksSrc mu12 /\
                          exportedSrc mu vals1 = exportedSrc mu12 vals1). 
     subst. clear - WDmu12 WDmu. simpl.  
        unfold exportedSrc. 
        rewrite sharedSrc_iff_frgnpub; trivial. simpl. 
        rewrite sharedSrc_iff_frgnpub; trivial.
        intuition.
   destruct LeakedCompSrc as [LSa LSb]. rewrite LSa, LSb in *. clear LSa LSb.
   assert (LeakedCompTgt: myBlocksTgt mu = myBlocksTgt mu23 
                       /\ exportedTgt mu vals3 = exportedTgt mu23 vals3).
     subst. clear - WDmu23 WDmu. simpl.  
        unfold exportedTgt, sharedTgt. simpl. intuition. 
   destruct LeakedCompTgt as [LTa LTb]. rewrite LTa, LTb in *. clear LTa LTb.
   remember (fun b => myBlocksTgt mu12 b && 
             REACH m2 (exportedTgt mu12 vals2) b) as pubTgtMid'.
   remember (fun b => myBlocksSrc mu23 b && 
             REACH m2 (exportedSrc mu23 vals2) b) as pubSrcMid'.
   assert (MID: forall b, pubTgtMid' b = true -> pubSrcMid' b = true).
        rewrite HeqpubTgtMid', HeqpubSrcMid'. 
        destruct GLUEINV as [? [? [? [? [? ?]]]]].
        rewrite <- H2 in *; clear H2. rewrite <- H0 in *; clear H0.
        rewrite H1. intros. rewrite andb_true_iff in *.
        destruct H0. split; trivial.
        eapply REACH_mono; try eassumption.
        unfold exportedTgt, exportedSrc, sharedTgt.
        rewrite sharedSrc_iff_frgnpub; trivial.
        intros. repeat rewrite orb_true_iff in *.
        intuition.
  specialize (eff_after_external12 _ (eq_refl _)).
  (*produce all the hypothesis necessary for applying interpolation*)
  assert (MinjNu12: Mem.inject (as_inj (replace_locals mu12 pubSrc' pubTgtMid')) m1 m2).
     rewrite replace_locals_as_inj. assumption.
  assert (MinjNu23: Mem.inject (as_inj (replace_locals mu23 pubSrcMid' pubTgt')) m2 m3).
     rewrite replace_locals_as_inj. assumption.
  assert (ExternIncrNu: extern_incr
            (compose_sm (replace_locals mu12 pubSrc' pubTgtMid')
              (replace_locals mu23 pubSrcMid' pubTgt')) nu').
      subst. split; simpl. 
        do 2 rewrite replace_locals_extern.
         eapply INC.
      do 2 rewrite replace_locals_local.
        rewrite replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
            replace_locals_DomSrc, replace_locals_DomTgt.
        repeat (split; try eapply INC; trivial). (*WOW, that was cool*)

  assert (WDnu12: SM_wd (replace_locals mu12 pubSrc' pubTgtMid')).
       subst.
       eapply replace_locals_wd; try eassumption.
         intros. apply andb_true_iff in H.
           destruct H as [myB R].
           destruct (REACH_local_REACH _ WDmu12 _ _ _ _ 
              MInj12 ArgsInj12 _ R myB) as [b2 [d1 [LOC12 R2]]].
           exists b2, d1; split; trivial.
           rewrite andb_true_iff, R2.
           split; trivial.
           eapply local_myBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H. 
  assert (WDnu23: SM_wd (replace_locals mu23 pubSrcMid' pubTgt')).
       subst. 
       eapply replace_locals_wd; try eassumption.
       destruct GLUEINV as [GIa [GIb [GIc [GId [GIe GIf]]]]].
       rewrite <- GIb in *. clear GIb.
       rewrite <- GId in *. clear GId. subst. 
       intros b2; intros. apply andb_true_iff in H.
           destruct H as [myB R].
           destruct (REACH_local_REACH _ WDmu23 _ _ _ _ 
              MInj23 ArgsInj23 _ R myB) as [b3 [d2 [LOC23 R3]]].
           exists b3, d2; split; trivial.
           rewrite andb_true_iff, R3.
           split; trivial.
           eapply local_myBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H.
  assert (SepNu: sm_inject_separated
         (compose_sm (replace_locals mu12 pubSrc' pubTgtMid')
                     (replace_locals mu23 pubSrcMid' pubTgt')) nu' m1 m3).
     subst; clear eff_after_external_bare12 eff_after_external_bare23.
     destruct GLUEINV as [GIa [GIb [GIc [GId [GIe GIf]]]]].
     rewrite <- GIb in *. clear GIb.
     rewrite <- GId in *. clear GId. subst. 
     split; simpl.
       intros. 
       rewrite compose_sm_as_inj in H; trivial.
          rewrite replace_locals_DomSrc, replace_locals_DomTgt. 
            do 2 rewrite replace_locals_as_inj in H.
            eapply SEP; try eassumption.
            rewrite replace_locals_as_inj; trivial.
            rewrite compose_sm_as_inj; trivial.
          rewrite replace_locals_myBlocksSrc. rewrite replace_locals_myBlocksTgt. assumption.
     rewrite replace_locals_DomSrc, replace_locals_DomTgt.
       split; intros; eapply SEP.
         rewrite replace_locals_DomSrc. simpl. apply H. apply H0.
         rewrite replace_locals_DomTgt. simpl. apply H. apply H0.
  assert (nu12_valid: sm_valid (replace_locals mu12 pubSrc' pubTgtMid') m1 m2).
     split. rewrite replace_locals_DOM. eapply mu12_valid.
     rewrite replace_locals_RNG. eapply mu12_valid.
  assert (nu23_valid: sm_valid (replace_locals mu23 pubSrcMid' pubTgt') m2 m3).
     split. rewrite replace_locals_DOM. eapply mu23_valid.
     rewrite replace_locals_RNG. eapply mu23_valid.
  destruct (effect_interp _ _ _ MinjNu12 _ FwdSrc
      _ _ MinjNu23 _ FwdTgt nu' WDnu' SMvalNu' MemInjNu'
      ExternIncrNu SepNu nu12_valid nu23_valid _ _ UnchSrc UnchTgt)  
     as [m2' [nu12' [nu23' [X [Incr12 [Incr23 [MInj12'
          [Fwd2 [MInj23' [Sep12 [Sep23 [nu12'valid
            [nu23'valid [GLUEINV' [M2 [UnchMid [Priv2Noeffect Local2effect]]]]]]]]]]]]]]]]].
    (*discharge the application condition about effects M1*)
       unfold compose_sm; simpl; intros.
       eapply PrivSrcNoeffect.
         subst. clear H0. rewrite replace_locals_myBlocksSrc. 
                rewrite replace_locals_myBlocksSrc in H. apply H.
         unfold loc_unmapped in H0. rewrite replace_locals_pubBlocksSrc, replace_locals_local in H0.
              rewrite replace_locals_local in H0.
           subst. rewrite replace_locals_myBlocksSrc in H.
           unfold loc_unmapped, replace_locals; simpl. apply H0.
    (*discharge the application condition about effects M3->M1*)
       unfold compose_sm; simpl; subst. 
       rewrite replace_locals_pubBlocksSrc, replace_locals_local,
               replace_locals_myBlocksTgt, replace_locals_pub in *.
       rewrite replace_locals_local. simpl in *.
       apply LocalTgtReverseEffect.
    (*discharge the GLUE application condition*)
      rewrite replace_locals_DomSrc, replace_locals_DomTgt,
            replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
      destruct GLUEINV as [GLUEa [GLUEb [GLUEc [GLUEd [GLUEe Gluef]]]]].
        rewrite <-  GLUEb in *. rewrite <-  GLUEd in *.
        clear GLUEb GLUEd Dom2 myBlocks2.
      repeat (split; trivial).

  (*next, prepare for application of eff_after_external_bare12*)
  destruct GLUEINV' as [WDnu12' [WDnu23' [GLUEa' [GLUEb' [GLUEc' GLUEd']]]]].
  assert (exists ret2, val_inject (as_inj nu12') ret1 ret2 /\ 
                       val_inject (as_inj nu23') ret2 ret3 /\
                       Val.has_type ret2 (proj_sig_res ef_sig)(* /\
                       val_valid ret2 m2'*)). 
    subst. rewrite compose_sm_as_inj in RValInjNu'; trivial.
    destruct (val_inject_split _ _ _ _ RValInjNu')
      as [ret2 [RValInjNu12' RValInjNu23']].  
    exists ret2. repeat (split; trivial).
    (*split.*) eapply valinject_hastype; eassumption.
    (*eapply inject_valvalid; eassumption.*)
  destruct H as [ret2 [RValInjNu12' [RValInjNu23' RetType2 (*RetValid2*)]]].
  subst. 
  rewrite replace_locals_myBlocksSrc, replace_locals_myBlocksTgt, replace_locals_pub in *.
  specialize (eff_after_external_bare12 nu12' ret1 
     m1' ret2 m2' Incr12 Sep12 WDnu12' nu12'valid MInj12' RValInjNu12'
     FwdSrc Fwd2 RetType2 (*RValidSrc RetValid2*)).
  destruct (eff_after_external_bare12 _ (eq_refl _) 
      _ (eq_refl _) _ (eq_refl _) _ _ UnchSrc UnchMid)
    as [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear eff_after_external_bare12.
   (*discharge application condition on unmppaped blocks*)
      subst; clear eff_after_external_bare23 ExternIncrNu SepNu.  
      unfold loc_unmapped; unfold loc_unmapped in PrivSrcNoeffect. 
      intros. apply (PrivSrcNoeffect _ _ H).
              remember (myBlocksSrc mu12 b && REACH m1 (exportedSrc mu12 vals1) b) as d.
              destruct d; trivial. rewrite compose_sm_local.
              unfold compose_meminj. rewrite H0. trivial.

    (*discharge next application condition*)
         apply Local2effect. 

  (*next, apply eff_after_external23*)
  specialize (eff_after_external_bare23 _ _ _ _ _ _ _ _ _ 
      _ _ _ MInj23 MC23 AtExt2 AtExtTgt ArgsInj23 _ (eq_refl _) 
      _ (eq_refl _) _ (eq_refl _) nu23').
  rewrite replace_locals_myBlocksSrc, replace_locals_myBlocksTgt, 
          replace_locals_pub, replace_locals_as_inj in *.  
  destruct (eff_after_external_bare23 ret2 m2' 
       ret3 m3' Incr23 Sep23 WDnu23' nu23'valid
       MInj23' RValInjNu23' Fwd2 FwdTgt RetTypeTgt
     _ (eq_refl _) _ (eq_refl _) _ (eq_refl _)
     _ _ UnchMid UnchTgt) as
     [d23' [c22' [c3' [AftExt22 [AftExt3 MC23']]]]];
    subst; clear eff_after_external_bare23.
    (*discharge application condition on unmppaped blocks*)
      apply Priv2Noeffect. 
    (*discharge next application condition*)
       clear MC12' SepNu ExternIncrNu. simpl in *.
       intros b3 ofs myB3 MM3.
       destruct (LocalTgtReverseEffect _ _ myB3 MM3)
         as [b1 [d [PUB13 MM1]]]; clear LocalTgtReverseEffect.
       remember (myBlocksSrc mu12 b1 && REACH m1 (exportedSrc mu12 vals1) b1) as q.
       destruct q; try inv PUB13. apply eq_sym in Heqq.
         apply andb_true_iff in Heqq; destruct Heqq.
         destruct (compose_meminjD_Some _ _ _ _ _ H0)
           as [b2 [d1 [d2 [PUB12 [PUB13 D]]]]]; subst; clear H0.
         exists b2, d2.
         assert (myBlocksSrc mu23 b2 && REACH m2 (exportedSrc mu23 vals2) b2 = true).
           apply MID.
           rewrite andb_true_iff.
           split. eapply (local_DomRng _ WDmu12 _ _ _ PUB12).
                  eapply (REACH_local_REACH' _ _ _ _ H1); eassumption.
         rewrite H0. split; trivial. ??. (*Strengthen interpolation, or add
            hypotheis to afterexternal saying that M1 b ofs -> pub_of mu b = b2,d2 -> M2 b2 (d+ofs)*)
                   
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some (c2', (DomTgt nu12', myBlocksSrc nu23')), d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2'. exists m2'.
  exists (replace_externs nu12'
            (fun b => DomSrc nu12' b && (negb (myBlocksSrc nu12' b) 
                                     && REACH m1' (exportedSrc nu12' (ret1::nil)) b))
            (fun b => DomTgt nu12' b && (negb (myBlocksTgt nu12' b) 
                                     && REACH m2' (exportedTgt nu12' (ret2::nil)) b))).
  exists (replace_externs nu23'
            (fun b => DomSrc nu23' b && (negb (myBlocksSrc nu23' b) 
                                     && REACH m2' (exportedSrc nu23' (ret2::nil)) b))
            (fun b => DomTgt nu23' b && (negb (myBlocksTgt nu23' b) 
                                     && REACH m3' (exportedTgt nu23' (ret3::nil)) b))).
  eexists; eexists; split. reflexivity.
  unfold compose_sm. simpl.
         repeat rewrite replace_externs_DomSrc, replace_externs_DomTgt, 
                 replace_externs_myBlocksSrc, replace_externs_myBlocksTgt,
                 replace_externs_pubBlocksSrc, replace_externs_pubBlocksTgt,  
                 replace_externs_frgnBlocksSrc, replace_externs_frgnBlocksTgt.
        rewrite replace_externs_extern, replace_externs_local.
        rewrite replace_externs_extern, replace_externs_local.
  split. f_equal; trivial. 
         unfold exportedSrc; simpl.
           rewrite sharedSrc_iff_frgnpub; trivial.
           rewrite sharedSrc_iff_frgnpub; trivial.
  split. rewrite GLUEa', GLUEb'.
         repeat (split; trivial).
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




      m2' m3 m3' ret3 _ MC23 AtExt2). VV2 _ sharedInj23 
      sharedValsInject3 sharedPG2 _ Incr23 Sep23 MInj23'
      injRet23 Fwd2 Fwd3 HTRet3 RetValid2' RetValid3' M2 M3
      UnchM2 UnchM3 unmapped23_M2 Unch2B (*HypFrgn32 *) PermM2 PermM3).
  destruct eff_after_external23 as 
 
    frgnSrc' frgnSrcHyp).



  assert (FRGN_EQ:
             (fun b0 : block =>
                (exists z : int, In (Vptr b0 z) (ret1 :: nil)) \/
                (exists (b2 : block) (d : Z),
                   shared_of (compose_sm nu12' nu23') b0 = Some (b2, d)))
           = (fun b0 : block =>
                (exists z : int, In (Vptr b0 z) (ret1 :: nil)) \/
                (exists (b2 : block) (d : Z),
                   shared_of nu12' b0 = Some (b2, d)))).
      (*as the proof of LKD_SH, except for the use of nu12'/nu23' in
          place of mu12/mu23, and GLUEINV' instead of GLUEINV*)
      clear eff_after_external_bare12 eff_after_external_bare23.
      extensionality b. apply prop_ext.
       rewrite compose_sm_shared.
         split; intros; destruct H; try (left; assumption).
           (*direction ->*)
           destruct H as [b3 [d SHC]].
           destruct (compose_meminjD_Some _ _ _ _ _ SHC)
              as [b2 [d1 [d2 [SH1 [SH2 DD]]]]]; subst; clear SHC.
           right. exists b2, d1. apply SH1.
           (*direction <-*)
           destruct H as [b2 [d1 SH1]]. right.
           destruct (joinD_Some _ _ _ _ _ SH1).
           (*foreign*)
             assert (F: frgnBlocksSrc nu23' b2 = true).
               eapply GLUEd'. eapply foreign_DomRng; eassumption.
             destruct (frgnSrc _ WDnu23' _ F) as [b3 [d2 [FRG2 fTgt3]]].
             unfold compose_meminj. rewrite SH1.
             rewrite (foreign_in_shared _ _ _ _ FRG2). eauto. 
           (*pub*)
             destruct H.
             assert (F: pubBlocksSrc nu23' b2 = true).
               eapply GLUEc'. eapply pub_myBlocks; eassumption. 
             destruct (pubSrc _ WDnu23' _ F) as [b3 [d2 [PUB2 pTgt3]]].
             unfold compose_meminj. rewrite SH1.
              rewrite (pub_in_shared _ WDnu23' _ _ _ PUB2). eauto. 
         eapply GLUEc'.
         eapply GLUEd'.
         assumption. assumption.
  subst. 

  rewrite FRGN_EQ in frgnSrcHyp. simpl in frgnSrcHyp.
  specialize (eff_after_external_bare12 _ (eq_refl _) nu12' ret1 
     m1' ret2 m2' Incr12 Sep12 WDnu12' nu12'valid MInj12' RValInjNu12'
     FwdSrc Fwd2 RetType2 RValidSrc RetValid2).
  specialize (eff_after_external_bare12 _ (eq_refl _) _ (eq_refl _) 
    frgnSrc' frgnSrcHyp).
  assert (exists frgnTgtMid', (forall b2 : block,
                             frgnTgtMid' b2 = true <->
                             frgnBlocksTgt nu12' b2 = true \/
                             (exists (b1 : block) (d : Z),
                                frgnSrc' b1 = true /\
                                extern_of nu12' b1 = Some (b2, d)))). 
 ??. (*bool vs prop...*)
  destruct H as [frgnTgtMid' HypFrgnTgtMid'].
  specialize (eff_after_external_bare12 _ HypFrgnTgtMid' _ (eq_refl _)).
  destruct eff_after_external_bare12 as 
     [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]].
  assert (exists pubSrcMid'', forall b ,pubSrcMid'' b = true <->
  leakedBlock m2
    (fun b0 : block =>
     (exists z : int, In (Vptr b0 z) vals2) \/
     (exists (b2 : block) (d : Z), shared_of mu23 b0 = Some (b2, d))) b /\
  myBlocksSrc mu23 b = true).
 ??. (*bool vs prop...*)
  destruct H as [pubSrcMid'' HypPubSrcMid''].
  specialize (eff_after_external_bare23 _ _ _ _ _ _ _ _ _ 
       MInj23 MC23 AtExt2 ValidArgs2 _ (eq_refl _) _ (eq_refl _) 
       _ HypPubSrcMid'').
 assert (exists pubTgt'', forall b2, pubTgt'' b2 = true<->
                             pubBlocksTgt mu23 b2 = true \/
                             (exists (b1 : block) (d : Z),
                                pubSrcMid'' b1 = true /\
                                local_of mu23 b1 = Some (b2, d))).
 ??. (*bool vs prop...*)
  destruct H as [pubTgt'' HypPubTgt''].
  specialize (eff_after_external_bare23 _ HypPubTgt''
   _ (eq_refl _)).
  assert (extern_incr (replace_locals mu23 pubSrcMid'' pubTgt'') nu23').
    unfold extern_incr in Incr23. 
    split.
      rewrite replace_locals_extern in *. eapply Incr23. 
    split.
      rewrite replace_locals_local in *. eapply Incr23. 
    split.
      rewrite replace_locals_DomSrc in *. eapply Incr23. 
    split.
      rewrite replace_locals_DomTgt in *. eapply Incr23. 
    split.
      rewrite replace_locals_myBlocksSrc in *. eapply Incr23. 
    split.
      rewrite replace_locals_myBlocksTgt in *. eapply Incr23. 
    split.
      rewrite replace_locals_pubBlocksSrc in *. eapply Incr23. 

eassumption.
    split. rewrite replace_locals

 subst.
 xx
  assert (nu12'valid: sm_valid nu12' m1' m2').xx
    split; subst; intros.
       eapply SMvalNu'; apply H.
       eapply SMvalNu'; apply H.
xx      _ _ _ ret2 _  

(eq_refl _)
        _ LKDSRC _ HypPubTgt2' _ (eq_refl _)).
(*assert (Unch111':  Mem.unchanged_on
           
                     
         
  assert (exists pubSrcMid', forall b, 
            pubSrcMid' b = true <->
            leakedBlock m2
              (fun b0 : block =>
               (exists z : int, In (Vptr b0 z) vals2) \/
               (exists (b2 : block) (d : Z), shared_of mu23 b0 = Some (b2, d)))
              b /\ pubBlocksTgt mu12 b = true). (*WAS: myBlocksSrc23 b*)
 ??. (*bool vs prop...*)
  destruct H as [pubSrcMid' HypPubSrcMid']. 
  assert (MinjNu12: Mem.inject (as_inj (replace_locals mu12 pubSrc' pubTgtMid')) m1 m2).
     rewrite replace_locals_as_inj. assumption.
  assert (MinjNu23: Mem.inject (as_inj (replace_locals mu23 pubSrcMid' pubTgt')) m2 m3).
     rewrite replace_locals_as_inj. assumption.
(*  assert (SEPnu : sm_inject_separated (compose_sm mu12 mu23) nu' m1 m3).
    eapply eff_after_check5a. reflexivity. apply SEP.*)

  assert (ExternIncrNu: extern_incr
            (compose_sm (replace_locals mu12 pubSrc' pubTgtMid')
              (replace_locals mu23 pubSrcMid' pubTgt')) nu').
      split; simpl. 
        do 2 rewrite replace_locals_extern.
         eapply INC.
      do 2 rewrite replace_locals_local.
        rewrite replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
            replace_locals_DomSrc, replace_locals_DomTgt.
        repeat (split; try eapply INC; trivial). (*WOW, that was cool*)

  assert (WDnu12': SM_wd (replace_locals mu12 pubSrc' pubTgtMid')).
       eapply replace_locals_wd; try eassumption.
         intros. apply pubSrcHyp in H. 
           destruct H as [[z HH] MM].
           destruct (reach_local mu12 WDmu12 _ _ _ _ MInj12 ArgsInj12 _ _ HH MM) as [b2 [d1 LOC12]].
           exists b2, d1; split; trivial.
           apply HypPubTgtMid'.
           right. exists b1, d1. split; trivial.
           apply pubSrcHyp. split; trivial.
           exists z. apply HH.
         intros. apply HypPubTgtMid' in H.
           destruct H. eapply (pubBlocksLocalTgt _ WDmu12 _ H).
           destruct H as [b1 [d1 [PUB LOC]]].
           eapply WDmu12. apply LOC.
  assert (WDnu23': SM_wd (replace_locals mu23 pubSrcMid' pubTgt')).
       eapply replace_locals_wd; try eassumption.
       destruct GLUEINV as [GIa [GIb [GIc [GId [GIe GIf]]]]].
       rewrite <- GIb in *. clear GIb.
       rewrite <- GId in *. clear GId. subst. 
       intros b2; intros. apply HypPubSrcMid' in H. 
           destruct H as [[z HH] MM].
           apply GIe in MM.
           assert (SRC2: myBlocksSrc mu23 b2 = true).
              eapply (pubBlocksLocalSrc _ WDmu23 _ MM).
           destruct (reach_local mu23 WDmu23 _ _ _ _ MInj23 ArgsInj23 _ _ HH SRC2) as [b3 [d2 LOC23]].
           exists b3, d2; split; trivial.
           apply pubTgtHyp.
              destruct (pubSrc _ WDmu23 _ MM) as [bb3 [dd3 [PUB3 PUBT3]]].
              rewrite (pub_in_local _ _ _ _ PUB3) in LOC23. inv LOC23. 
              left; assumption.
       intros b3; intros. apply pubTgtHyp in H. 
           destruct H. eapply (pubBlocksLocalTgt _ WDmu23 _ H).
           destruct H as [b1 [d [PUB LOC]]].
           apply pubSrcHyp in PUB. destruct PUB as [[z R] MM].
           destruct (reach_local mu12 WDmu12 _ _ _ _ MInj12 ArgsInj12 _ _ R MM) as [b2 [d1 LOC12]].
           destruct (compose_meminjD_Some _ _ _ _ _ LOC) 
             as [b2' [da [db [LOCa [LOCb VV]]]]].
           rewrite LOC12 in LOCa. inv LOCa.
           eapply (local_DomRng _ WDmu23 _ _ _ LOCb).

  assert (SepNu: sm_inject_separated
         (compose_sm (replace_locals mu12 pubSrc' pubTgtMid')
                     (replace_locals mu23 pubSrcMid' pubTgt')) nu' m1 m3).
     clear eff_after_external_bare12 eff_after_external_bare23.
     destruct GLUEINV as [GIa [GIb [GIc [GId [GIe GIf]]]]].
     rewrite <- GIb in *. clear GIb.
     rewrite <- GId in *. clear GId. subst. 
     split; simpl.
       intros. 
       rewrite compose_sm_as_inj in H; trivial.
          rewrite replace_locals_DomSrc, replace_locals_DomTgt. 
            do 2 rewrite replace_locals_as_inj in H.
            eapply SEP; try eassumption.
            rewrite replace_locals_as_inj; trivial.
            rewrite compose_sm_as_inj; trivial.
          rewrite replace_locals_myBlocksSrc. rewrite replace_locals_myBlocksTgt. assumption.
     rewrite replace_locals_DomSrc, replace_locals_DomTgt.
       split; intros; eapply SEP.
         rewrite replace_locals_DomSrc. simpl. apply H. apply H0.
         rewrite replace_locals_DomTgt. simpl. apply H. apply H0.
  assert (nu12'_valid: sm_valid (replace_locals mu12 pubSrc' pubTgtMid') m1 m2).
     split. rewrite replace_locals_DOM. eapply mu12_valid.
     rewrite replace_locals_RNG. eapply mu12_valid.
  assert (nu23'_valid: sm_valid (replace_locals mu23 pubSrcMid' pubTgt') m2 m3).
     split. rewrite replace_locals_DOM. eapply mu23_valid.
     rewrite replace_locals_RNG. eapply mu23_valid.
  destruct (effect_interp _ _ _ MinjNu12 _ FwdSrc
      _ _ MinjNu23 _ FwdTgt nu' WDnu' SMvalNu' MemInjNu'
      ExternIncrNu SepNu nu12'_valid nu23'_valid)
     as [m2' [nu12' [nu23' [X [Incr12 [Incr23 [MInj12'
          [Fwd2 [MInj23' [Sep12 Sep23]]]]]]]]]].
    split; trivial.
    split; trivial.
    rewrite replace_locals_DomSrc, replace_locals_DomTgt,
            replace_locals_myBlocksSrc, replace_locals_myBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
    destruct GLUEINV as [GLUEa [GLUEb [GLUEc [GLUEd [GLUEe Gluef]]]]].
       rewrite <-  GLUEb in *. rewrite <-  GLUEd in *.
       clear GLUEb GLUEd Dom2 myBlocks2.
    split; trivial.
    split; trivial.
    split; trivial.
    intros. apply HypPubTgtMid' in H. apply HypPubSrcMid'.
            remember (pubBlocksTgt mu12 b) as q.
            destruct q. Focus 2. destruct H. inv H.
               exfalso. destruct H as [b1 [d1 [PUB LOC]]].
               apply pubSrcHyp in PUB. destruct PUB.xx
            destruct H. split; trivial.
            assert (K: pubBlocksSrc mu23 b = true).
               apply (GLUEe _ H).
            exists 0.
            eapply reachBase. reflexivity.
              right. destruct (pubSrc _ WDmu23 _ K) as [b3 [d2 [PUB23 TGT3]]].
                     apply (pub_in_shared _ WDmu23) in PUB23.
                     rewrite PUB23. eauto.
              ??. (*TODO: public blocks have at least one nonempty offset - or change def of leaked/reach*)
          destruct H as [b1 [d1 [PUBSRC' LOC12]]].
          apply pubSrcHyp in PUBSRC'.
              
                     
         
        
      (* [M2 [UnchM2 [PermM2 [unmapped23_M2 [Unch2B (*[*)Unch2C (*[HypFrgn21 HypFrgn32]]*)]]]]]]]]]]]]]]]].*)
xx
  subst.
  assert (exists ret2, val_inject (as_inj nu12') ret1 ret2 /\ 
                       val_inject (as_inj nu23') ret2 ret3 /\
                       Val.has_type ret2 (proj_sig_res ef_sig) /\
                       val_valid ret2 m2'). 
    subst. rewrite compose_sm_as_inj in RValInjNu'.
(SM_wd nu12' /\ SM_wd nu23' /\
 DomTgt nu12' = DomSrc nu23' /\ 
 myBlocksTgt nu12' = myBlocksSrc nu23' /\
 (forall b, pubBlocksTgt nu12' b = true -> 
            pubBlocksSrc nu23' b = true) /\
 (forall b, frgnBlocksTgt nu12' b = true -> 
            frgnBlocksSrc nu23' b = true))

xx RetInject13'.
    rewrite JPub in RetInject13'.
    apply val_inject_split in RetInject13'.
    destruct RetInject13' as [ret2 [injRet12 injRet23]].  
    exists ret2. split; trivial. split; trivial. 
    split. eapply valinject_hastype; eassumption.
    eapply inject_valvalid; eassumption.
    eauto.
    eauto.
    assumption. 
  destruct H as [ret2 [injRet12 [injRet23 [HTRet2 RetValid2']]]].

  specialize (eff_after_external_bare12 _ eq9_refl _) nu12' ret1 m1' ret2 m2').
 (*. replace_locals mu12 pubSrc' pubTgtMid' nu12'
continue here
  specialize (eff_after_external_bare23 _ _ _ _ _ _ _ _ _ MInj23 
        MC23 AtExt2 ValidArgs2 _ (eq_refl _) _ (eq_refl _)). 

  assert (TGT: forall b2 : block,
                             pubTgt' b2 = true <->
                             pubBlocksTgt mu12 b2 = true \/
                             (exists (b1 : block) (d : Z),
                                pubSrc' b1 = true /\
                                local_of mu12 b1 = Some (b2, d))).
     clear eff_after_external_bare23 eff_after_external_bare12.
     intros. specialize (pubTgtHyp b2).
     assert ((exists (b1 : block) (d : Z),
               pubSrc' b1 = true /\
               local_of (compose_sm mu12 mu23) b1 = Some (b2, d))
           = (exists (b1 : block) (d : Z),
               pubSrc' b1 = true /\ 
               local_of mu12 b1 = Some (b2, d))). ??.
     rewrite <- H. clear H. clear pubSrcHyp. assumption. 
    
    
  specialize (eff_after_external_bare12 _  pubSrcHyp pubTgt').
  simpl in pubTgtHyp. assert ().
  

  assert (LKDSRC: (forall b : block,
                             (fun b0 : block =>
                              leakedBlockBool m1
                                (fun b1 : block =>
                                 (exists z : int, In (Vptr b1 z) vals1) \/
                                 (exists (b2 : block) (d : Z),
                                    shared_of mu12 b1 = Some (b2, d))) b0 &&
                              myBlocksSrc mu12 b0) b = true <->
                             leakedBlock m1
                               (fun b0 : block =>
                                (exists z : int, In (Vptr b0 z) vals1) \/
                                (exists (b2 : block) (d : Z),
                                   shared_of mu12 b0 = Some (b2, d))) b /\
                             myBlocksSrc mu12 b = true)).
     intros. split; intros.
         apply andb_true_iff in H. rewrite leakedBlock_char in H. assumption.
         apply andb_true_iff. rewrite leakedBlock_char. assumption.
  assert (LKD2: exists pubTgt2', (forall b2 : block,
                             pubTgt2' b2 = true <->
                             (pubBlocksTgt mu12 b2 = true \/
                             (exists (b1 : block) (d : Z),
                                (fun b0 : block =>
                                 leakedBlockBool m1
                                   (fun b3 : block =>
                                    (exists z : int, In (Vptr b3 z) vals1) \/
                                    (exists (b4 : block) (d0 : Z),
                                       shared_of mu12 b3 = Some (b4, d0))) b0 &&
                                 myBlocksSrc mu12 b0) b1 = true /\
                                local_of mu12 b1 = Some (b2, d))))).
        ??.  
   destruct LKD2 as [pubTgt2' HypPubTgt2'].
   
   specialize (eff_after_external_bare12 _ (eq_refl _) _ (eq_refl _)
        _ LKDSRC _ HypPubTgt2' _ (eq_refl _)).
   with  (pubSrc':=fun b => andb (leakedBlockBool m1 (fun b0 : block =>
                                (fun b1 : block =>
                                 exists z : int, In (Vptr b1 z) vals1) b0 \/
                                (exists (b2 : block) (d : Z),
                                   shared_of mu12 b0 = Some (b2, d))) b)
                 (myBlocksSrc mu12 b))
         (pubTgt':=fun b => false).
    
  rename H into AtExt1. rename H1 into MInj13. rename H2 into ValInject13.
  rename H3 into shPG1. rename H4 into MInj13'. rename H5 into RetInject13'.
  rename H6 into Fwd1. rename H7 into Fwd3.  
  rename H8 into HTRet3.
  rename H9 into RetValid1'. rename H10 into RetValid3'.
  rename H11 into UnchM1. 
  rename M2 into M3. rename H12 into UnchM3.
  rename H13 into unmapped13_M1. rename H14 into PubM3M1.
  rename H15 into PermM1. rename H16 into PermM3.
(*  rename H15 into HypFrgn31.*)
  (*assert (ZZ1 : Mem.unchanged_on
                  (fun (b : block) (ofs : Z) =>
                   myBlocksSrc mu b /\ loc_unmapped (local_of mu) b ofs) m1 m1').
    eapply mem_unchanged_on_sub. eassumption.
    intros. destruct H; simpl. split; trivial.
    unfold loc_unmapped in *.
    destruct mu as [BSrc BTgt pSrc pTgt frgn pub priv]. simpl in *.
    unfold join in H1.
    remember (pub b) as d; destruct d; trivial.
       destruct p. inv H1. *)
  destruct MS as [st2 [m2 [mu1 [mu2 [myBlocks2 (*[pubBlocks2*) [X [J [TgtB1
          [SrcB2 (*[pTgtB1 [pSrcB2*) [MC12 MC23]]]]]]]]]](*]]]*); subst.
  rename H0 into VV1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1 VV1) 
   as [vals2 [HTVals2 [AtExt2
         [VV2 [sharedInj12 [sharedValsInject2 sharedPG1]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 VV2) 
   as [vals [HTVals3 [AtExt3
         [VV3 [sharedInj23 [sharedValsInject3 sharedPG2]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
  eapply forall_valinject_hastype; eassumption.
  assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). 
  eapply valinject_hastype; eassumption.
  apply eq_sym in SrcB2.
  assert (CSS:shared_of (compose_sm mu1 mu2) = compose_meminj (shared_of mu1) (shared_of mu2)).
      apply compose_sm_shared; eauto.
  rewrite CSS in *. 
  assert(unmapped12_M1 : forall (b : block) (ofs : Z),
      myBlocksSrc mu1 b ->
      loc_unmapped (pub_of mu1) b ofs -> ~ M1 b ofs).
   intros. eapply unmapped13_M1. simpl. apply H.
        unfold loc_unmapped in H0. unfold loc_unmapped.
          simpl. unfold compose_meminj. 
        destruct mu1. simpl in *. rewrite H0. trivial.
  assert (SMV12:= match_validblock12 _ _ _ _ _ _ MC12).
  assert (SMV23:= match_validblock23 _ _ _ _ _ _ MC23).
  assert (SMWD12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (SMWD23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct (effect_interp _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ _ _ MInj13' INC SEP SMV12 SMV23 SMWD12 SMWD23 
     SrcB2 M1 M3 UnchM1 (eq_refl _) (eq_refl _) UnchM3 unmapped13_M1 PubM3M1
     (*HypFrgn31*) unmapped12_M1 PermM1 PermM3)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Sep12 [Sep23 [M2 [UnchM2 [PermM2 [unmapped23_M2 [Unch2B (*[*)Unch2C (*[HypFrgn21 HypFrgn32]]*)]]]]]]]]]]]]]]]].
 (*
  assert (UU1: Mem.unchanged_on
        (loc_unmapped (compose_meminj (shared_of mu1) (shared_of mu2))) m1 m1').
     later
  assert (UU2: Mem.unchanged_on
        (loc_out_of_reach (compose_meminj (shared_of mu1) (shared_of mu2)) m1) m3 m3').
      later
  destruct (MEMAX.interpolate_II _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ MInj13' INC SEP UU1 UU2)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' [Unch2233' WD22']]]]]]]]]]]]]].
    eauto. eauto. eauto. eauto. eauto.  *) 

  assert (JPub: join (compose_meminj j12' j23')
                     (compose_meminj (pub_of mu1) (pub_of mu2))
           = compose_meminj (join j12' (pub_of mu1)) (join j23' (pub_of mu2))).
    specialize (match_validblock23 _ _ _ _ _ _ MC23).
    specialize (match_validblock12 _ _ _ _ _ _ MC12).
    solve[eapply compose_pub_join; eauto].
  assert (exists ret2, val_inject (join j12' (pub_of mu1)) ret1 ret2 /\ 
                       val_inject (join j23' (pub_of mu2)) ret2 ret3 /\
    Val.has_type ret2 (proj_sig_res ef_sig) /\ val_valid ret2 m2'). 
    subst. rewrite compose_sm_pub in RetInject13'.
    rewrite JPub in RetInject13'.
    apply val_inject_split in RetInject13'.
    destruct RetInject13' as [ret2 [injRet12 injRet23]].  
    exists ret2. split; trivial. split; trivial. 
    split. eapply valinject_hastype; eassumption.
    eapply inject_valvalid; eassumption.
    eauto.
    eauto.
    assumption. 
  destruct H as [ret2 [injRet12 [injRet23 [HTRet2 RetValid2']]]].
(*assert (Unch111':  Mem.unchanged_on
            (fun b ofs => myBlocksSrc mu1 b /\ 
                          loc_unmapped (local_of mu1) b ofs) m1 m1').
     eapply mem_unchanged_on_sub; try eassumption.
     intros; simpl. destruct H.
     split; trivial.
     unfold loc_unmapped in *.
     destruct (match_sm_wd12 _ _ _ _ _ _ MC12) as [DST12 _].
     destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
     destruct mu2 as [BSrc2 BTgt2 psrc2 pTgt2 frgn2 pub2 priv2].
     simpl in *.
     unfold compose_meminj, join.
          specialize (joinD _ _ DST12 b). rewrite H0. intros.
     destruct H1 as [HH KK]; rewrite HH, KK. trivial.*)  
   (*Mem.unchanged_on (loc_unmapped (shared_of mu1)) m1 m1').
     later
     split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
     rewrite H0. trivial. trivial. 
     intros. rewrite H0. trivial. trivial.*)
  specialize (eff_after_external12 _ _ _ _ _ _ _ ret1 
      m1' m2 m2' ret2 _ MC12 AtExt1 VV1 _ sharedInj12 
      sharedValsInject2 sharedPG1 _ Incr12 Sep12 MInj12'
      injRet12 Fwd1 Fwd2 HTRet2 RetValid1' RetValid2' M1 M2 
      UnchM1 UnchM2 unmapped12_M1 Unch2C (*HypFrgn21 *) PermM1 PermM2). 
  destruct eff_after_external12 as 
     [d12' [c1' [c2' [AftExt1 [AftExt2 [nu12 [NU12 MC12']]]]]]].
    subst.

  specialize (eff_after_external23 _ _ _ _ _ _ _ ret2
      m2' m3 m3' ret3 _ MC23 AtExt2 VV2 _ sharedInj23 
      sharedValsInject3 sharedPG2 _ Incr23 Sep23 MInj23'
      injRet23 Fwd2 Fwd3 HTRet3 RetValid2' RetValid3' M2 M3
      UnchM2 UnchM3 unmapped23_M2 Unch2B (*HypFrgn32 *) PermM2 PermM3).
  destruct eff_after_external23 as 
     [d23' [cc2' [c3' [AftExt22 [AftExt3 [nu23 [NU23 MC23']]]]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some (c2', myBlocksSrc mu2), d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  eexists. split. reflexivity.
  exists c2'. exists m2'. exists (extend_foreign mu1 j12' m1 m2). 
     exists (extend_foreign mu2 j23' m2 m3).
     exists (myBlocksSrc mu2). 
     split. trivial.
     split. solve [eapply compose_sm_foreign_extend_foreign; eauto].
     split. solve [rewrite extend_foreign_myBlocksTgt; assumption].
     split. solve [apply extend_foreign_myBlocksSrc].
     split; assumption.
(*eff_after_external*)
  clear core_diagram12 core_initial12 core_halted12 eff_diagram12 
        core_diagram23 core_initial23 core_halted23 eff_diagram23
        eff_after_external12 eff_after_external23
    (*core_at_externalFAT1*) (*FAT0 core_at_externalFAT0*). 
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23]. rename vals2 into vals3.
  destruct MatchMu as [st2 [m2 [mu12 [mu23 [Dom2 [myBlocks2 
      [Hst2 [HMu [GLUEINV [MC12 MC23]]]]]]]]]]. subst.
  assert (Check1: SM_wd (replace_locals (compose_sm mu12 mu23) pubSrc' pubTgt') /\
                  sm_valid (replace_locals (compose_sm mu12 mu23) pubSrc' pubTgt') m1 m3 /\
                  Mem.inject (as_inj (replace_locals (compose_sm mu12 mu23) pubSrc' pubTgt')) m1 m3 /\
                  Forall2 (val_inject (as_inj (replace_locals (compose_sm mu12 mu23) pubSrc' pubTgt'))) vals1 vals3).
     clear core_at_external12 core_at_external23 eff_after_external12 eff_after_external23.
     eapply eff_after_check1 with
       (pubSrc':= pubSrc')
       (pubTgt':= pubTgt'). (* fun b => orb (pubBlocksTgt m23 b) (pubTgt' b)).*)
       apply MemInjMu. apply ValInjMu.
       reflexivity. reflexivity.
       intros b. simpl in *.
          destruct (pubSrcHyp b) as [Shypa Shypb]; clear pubSrcHyp pubTgtHyp. 
          split; intros.
            right. apply (Shypa H).
          destruct H. 
            apply Shypb. split.
               clear Shypb Shypa. unfold leakedBlock.
                 exists 0. eapply reachBase. reflexivity. right.
                 rewrite compose_sm_shared.
                 destruct (pubSrc _ (match_sm_wd12 _ _ _ _ _ _ MC12) _ H)
                   as [b2 [d2 [LOC12 PUB2]]]. apply pub_in_local in LOCC12. rewrite LOC12 in LOCC12. apply eq_sym in LOCC12. inv LOCC12.
              assert (pubBlocksSrc mu23 b2 = true).
                 eapply GLUEINV. apply PUB2.
              destruct (pubSrc _ (match_sm_wd23 _ _ _ _ _ _ MC23) _ H0)
                as [bb3 [dd3 [LOCC23 PUB3]]]. apply pub_in_local in LOCC23. rewrite LOC23 in LOCC23. apply eq_sym in LOCC23. inv LOCC23. 
              apply Thypb. left; trivial.
               Focus 2. apply (pubBlocksLocalSrc _ (match_sm_wd12 _ _ _ _ _ _ MC12) _ H). appl rewrite H; trivial.
            apply (Shypb H). apply orb_true_r.
       intros b. simpl in *. 
          destruct (pubTgtHyp b) as [Thypa Thypb]; clear pubTgtHyp. 
          split; intros.
            destruct (Thypa H); clear Thypa.
            left; assumption.
            destruct H0 as [b1 [d [pubSRC LOC13]]].
            right. exists b1, d. rewrite pubSRC. rewrite orb_true_r. split; trivial.
          destruct H.
            apply Thypb. left; assumption.
            destruct H as [b1 [d [pubSRC LOC13]]].            
            destruct (orb_prop _ _ pubSRC); clear pubSRC. 
              destruct (compose_meminjD_Some _ _ _ _ _ LOC13)
                as [b2 [d1 [d2 [LOC12 [LOC23 DD]]]]]; subst; clear LOC13.
              destruct (pubSrc _ (match_sm_wd12 _ _ _ _ _ _ MC12) _ H)
                as [bb2 [dd2 [LOCC12 PUB2]]]. apply pub_in_local in LOCC12. rewrite LOC12 in LOCC12. apply eq_sym in LOCC12. inv LOCC12.
              assert (pubBlocksSrc mu23 b2 = true).
                 eapply GLUEINV. apply PUB2.
              destruct (pubSrc _ (match_sm_wd23 _ _ _ _ _ _ MC23) _ H0)
                as [bb3 [dd3 [LOCC23 PUB3]]]. apply pub_in_local in LOCC23. rewrite LOC23 in LOCC23. apply eq_sym in LOCC23. inv LOCC23. 
              apply Thypb. left; trivial.
            apply Thypb. right. exists b1, d. split; assumption. 
           eapply eff_after_check1 with
       (pubSrc':= fun b => orb (pubBlocksSrc mu12 b) (pubSrc' b))
       (pubTgt':= pubTgt'). (* fun b => orb (pubBlocksTgt m23 b) (pubTgt' b)).*)
       apply MemInjMu. apply ValInjMu.
       reflexivity. reflexivity.
       intros b. simpl in *.
          destruct (pubSrcHyp b) as [Shypa Shypb]; clear pubSrcHyp pubTgtHyp. 
          split; intros.
            destruct (orb_prop _ _ H); clear H. 
            left; assumption. 
            right. apply (Shypa H0).
          destruct H.
            rewrite H; trivial.
            rewrite (Shypb H). apply orb_true_r.
       intros b. simpl in *. 
          destruct (pubTgtHyp b) as [Thypa Thypb]; clear pubTgtHyp. 
          split; intros.
            destruct (Thypa H); clear Thypa.
            left; assumption.
            destruct H0 as [b1 [d [pubSRC LOC13]]].
            right. exists b1, d. rewrite pubSRC. rewrite orb_true_r. split; trivial.
          destruct H.
            apply Thypb. left; assumption.
            destruct H as [b1 [d [pubSRC LOC13]]].            
            destruct (orb_prop _ _ pubSRC); clear pubSRC. 
              destruct (compose_meminjD_Some _ _ _ _ _ LOC13)
                as [b2 [d1 [d2 [LOC12 [LOC23 DD]]]]]; subst; clear LOC13.
              destruct (pubSrc _ (match_sm_wd12 _ _ _ _ _ _ MC12) _ H)
                as [bb2 [dd2 [LOCC12 PUB2]]]. apply pub_in_local in LOCC12. rewrite LOC12 in LOCC12. apply eq_sym in LOCC12. inv LOCC12.
              assert (pubBlocksSrc mu23 b2 = true).
                 eapply GLUEINV. apply PUB2.
              destruct (pubSrc _ (match_sm_wd23 _ _ _ _ _ _ MC23) _ H0)
                as [bb3 [dd3 [LOCC23 PUB3]]]. apply pub_in_local in LOCC23. rewrite LOC23 in LOCC23. apply eq_sym in LOCC23. inv LOCC23. 
              apply Thypb. left; trivial.
            apply Thypb. right. exists b1, d. split; assumption. 
            

right. apply (Thypa H0).
          destruct H.
            rewrite H; trivial.
            rewrite (Shypb H). apply orb_true_r.

  split. eapply eff_after_check1.
           apply MemInjMu. apply ValInjMu.
           apply ArgBlocksHyp.
           reflexivity.
  rename ret2 into ret3. rename m2' into m3'. 
  rename H into AtExt1. rename H1 into MInj13. rename H2 into ValInject13.
  rename H3 into shPG1. rename H4 into MInj13'. rename H5 into RetInject13'.
  rename H6 into Fwd1. rename H7 into Fwd3.  
  rename H8 into HTRet3.
  rename H9 into RetValid1'. rename H10 into RetValid3'.
  rename H11 into UnchM1. 
  rename M2 into M3. rename H12 into UnchM3.
  rename H13 into unmapped13_M1. rename H14 into PubM3M1.
  rename H15 into PermM1. rename H16 into PermM3.
(*  rename H15 into HypFrgn31.*)
  (*assert (ZZ1 : Mem.unchanged_on
                  (fun (b : block) (ofs : Z) =>
                   myBlocksSrc mu b /\ loc_unmapped (local_of mu) b ofs) m1 m1').
    eapply mem_unchanged_on_sub. eassumption.
    intros. destruct H; simpl. split; trivial.
    unfold loc_unmapped in *.
    destruct mu as [BSrc BTgt pSrc pTgt frgn pub priv]. simpl in *.
    unfold join in H1.
    remember (pub b) as d; destruct d; trivial.
       destruct p. inv H1. *)
  destruct MS as [st2 [m2 [mu1 [mu2 [myBlocks2 (*[pubBlocks2*) [X [J [TgtB1
          [SrcB2 (*[pTgtB1 [pSrcB2*) [MC12 MC23]]]]]]]]]](*]]]*); subst.
  rename H0 into VV1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1 VV1) 
   as [vals2 [HTVals2 [AtExt2
         [VV2 [sharedInj12 [sharedValsInject2 sharedPG1]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 VV2) 
   as [vals [HTVals3 [AtExt3
         [VV3 [sharedInj23 [sharedValsInject3 sharedPG2]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
  eapply forall_valinject_hastype; eassumption.
  assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). 
  eapply valinject_hastype; eassumption.
  apply eq_sym in SrcB2.
  assert (CSS:shared_of (compose_sm mu1 mu2) = compose_meminj (shared_of mu1) (shared_of mu2)).
      apply compose_sm_shared; eauto.
  rewrite CSS in *. 
  assert(unmapped12_M1 : forall (b : block) (ofs : Z),
      myBlocksSrc mu1 b ->
      loc_unmapped (pub_of mu1) b ofs -> ~ M1 b ofs).
   intros. eapply unmapped13_M1. simpl. apply H.
        unfold loc_unmapped in H0. unfold loc_unmapped.
          simpl. unfold compose_meminj. 
        destruct mu1. simpl in *. rewrite H0. trivial.
  assert (SMV12:= match_validblock12 _ _ _ _ _ _ MC12).
  assert (SMV23:= match_validblock23 _ _ _ _ _ _ MC23).
  assert (SMWD12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (SMWD23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct (effect_interp _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ _ _ MInj13' INC SEP SMV12 SMV23 SMWD12 SMWD23 
     SrcB2 M1 M3 UnchM1 (eq_refl _) (eq_refl _) UnchM3 unmapped13_M1 PubM3M1
     (*HypFrgn31*) unmapped12_M1 PermM1 PermM3)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Sep12 [Sep23 [M2 [UnchM2 [PermM2 [unmapped23_M2 [Unch2B (*[*)Unch2C (*[HypFrgn21 HypFrgn32]]*)]]]]]]]]]]]]]]]].
 (*
  assert (UU1: Mem.unchanged_on
        (loc_unmapped (compose_meminj (shared_of mu1) (shared_of mu2))) m1 m1').
     later
  assert (UU2: Mem.unchanged_on
        (loc_out_of_reach (compose_meminj (shared_of mu1) (shared_of mu2)) m1) m3 m3').
      later
  destruct (MEMAX.interpolate_II _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ MInj13' INC SEP UU1 UU2)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' [Unch2233' WD22']]]]]]]]]]]]]].
    eauto. eauto. eauto. eauto. eauto.  *) 

  assert (JPub: join (compose_meminj j12' j23')
                     (compose_meminj (pub_of mu1) (pub_of mu2))
           = compose_meminj (join j12' (pub_of mu1)) (join j23' (pub_of mu2))).
    specialize (match_validblock23 _ _ _ _ _ _ MC23).
    specialize (match_validblock12 _ _ _ _ _ _ MC12).
    solve[eapply compose_pub_join; eauto].
  assert (exists ret2, val_inject (join j12' (pub_of mu1)) ret1 ret2 /\ 
                       val_inject (join j23' (pub_of mu2)) ret2 ret3 /\
    Val.has_type ret2 (proj_sig_res ef_sig) /\ val_valid ret2 m2'). 
    subst. rewrite compose_sm_pub in RetInject13'.
    rewrite JPub in RetInject13'.
    apply val_inject_split in RetInject13'.
    destruct RetInject13' as [ret2 [injRet12 injRet23]].  
    exists ret2. split; trivial. split; trivial. 
    split. eapply valinject_hastype; eassumption.
    eapply inject_valvalid; eassumption.
    eauto.
    eauto.
    assumption. 
  destruct H as [ret2 [injRet12 [injRet23 [HTRet2 RetValid2']]]].
(*assert (Unch111':  Mem.unchanged_on
            (fun b ofs => myBlocksSrc mu1 b /\ 
                          loc_unmapped (local_of mu1) b ofs) m1 m1').
     eapply mem_unchanged_on_sub; try eassumption.
     intros; simpl. destruct H.
     split; trivial.
     unfold loc_unmapped in *.
     destruct (match_sm_wd12 _ _ _ _ _ _ MC12) as [DST12 _].
     destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
     destruct mu2 as [BSrc2 BTgt2 psrc2 pTgt2 frgn2 pub2 priv2].
     simpl in *.
     unfold compose_meminj, join.
          specialize (joinD _ _ DST12 b). rewrite H0. intros.
     destruct H1 as [HH KK]; rewrite HH, KK. trivial.*)  
   (*Mem.unchanged_on (loc_unmapped (shared_of mu1)) m1 m1').
     later
     split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
     rewrite H0. trivial. trivial. 
     intros. rewrite H0. trivial. trivial.*)
  specialize (eff_after_external12 _ _ _ _ _ _ _ ret1 
      m1' m2 m2' ret2 _ MC12 AtExt1 VV1 _ sharedInj12 
      sharedValsInject2 sharedPG1 _ Incr12 Sep12 MInj12'
      injRet12 Fwd1 Fwd2 HTRet2 RetValid1' RetValid2' M1 M2 
      UnchM1 UnchM2 unmapped12_M1 Unch2C (*HypFrgn21 *) PermM1 PermM2). 
  destruct eff_after_external12 as 
     [d12' [c1' [c2' [AftExt1 [AftExt2 [nu12 [NU12 MC12']]]]]]].
    subst.

  specialize (eff_after_external23 _ _ _ _ _ _ _ ret2
      m2' m3 m3' ret3 _ MC23 AtExt2 VV2 _ sharedInj23 
      sharedValsInject3 sharedPG2 _ Incr23 Sep23 MInj23'
      injRet23 Fwd2 Fwd3 HTRet3 RetValid2' RetValid3' M2 M3
      UnchM2 UnchM3 unmapped23_M2 Unch2B (*HypFrgn32 *) PermM2 PermM3).
  destruct eff_after_external23 as 
     [d23' [cc2' [c3' [AftExt22 [AftExt3 [nu23 [NU23 MC23']]]]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some (c2', myBlocksSrc mu2), d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  eexists. split. reflexivity.
  exists c2'. exists m2'. exists (extend_foreign mu1 j12' m1 m2). 
     exists (extend_foreign mu2 j23' m2 m3).
     exists (myBlocksSrc mu2). 
     split. trivial.
     split. solve [eapply compose_sm_foreign_extend_foreign; eauto].
     split. solve [rewrite extend_foreign_myBlocksTgt; assumption].
     split. solve [apply extend_foreign_myBlocksSrc].
     split; assumption.
 (*halted*)
  intros. rename c2 into c3. rename m2 into m3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [j12 [j23 [myBlocks2 (*[pubBlocks2*) [X [J [TgtB1
          [SrcB2 (*[pTgtB1 [pSrcB2*) [MC12 MC23]]]]]]]]]](*]]]*); subst.
  apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [v2 [ValsInj12 [SH2 [Minj12 VV2]]]].
  apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2; try assumption. 
  destruct SH2 as [v3 [ValsInj23 [SH3 [MInj23 VV3]]]].
  exists v3. rewrite compose_sm_shared; eauto.
  split.
    apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
  split. trivial. 
  split. eapply Mem.inject_compose; eassumption.
  assumption.
(*atexternal*)
  intros. rename c2 into c3. rename m2 into m3. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [j12 [j23 [myBlocks2 (*[pubBlocks2*) [X [J [TgtB1
          [SrcB2 (*[pTgtB1 [pSrcB2*) [MC12 MC23]]]]]]]]]](*]]]*); subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [vals2 [HTVals2 [AtExt2 
       [VV2 [sharedMInj12 [sharedValsInject2 sharedPG1]]]]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
  destruct AtExt2 as [vals3 [HTVals3 [AtExt3 
       [VV3 [sharedMInj23 [sharedValsInject3 sharedPG2]]]]]].
  exists vals3. 
  split; try assumption.
  split; try assumption.
  split; try assumption.
  rewrite compose_sm_shared; eauto.
  split. (*new condition Mem.inject (shared (compose_sm j1 j2)) m1 m3*)
    eapply Mem.inject_compose; eassumption.
  split. eapply forall_val_inject_compose; eassumption.
  ??. (*another preserves_globals*)
 (*after_external*)
  clear core_diagram12 core_initial12 core_halted12 
    core_diagram23 core_initial23 core_halted23
    (*core_after_externalFAT1 core_at_externalFAT1*)
    (*core_after_externalFAT0 core_at_externalFAT0*). 
  intros. rename st2 into st3. rename m2 into m3.
  rename ret2 into ret3. rename m2' into m3'. 
  destruct cd as [[d12 cc2] d23]. rename vals2 into vals3.
  rename H into AtExt1. rename H1 into MInj13. rename H2 into ValInject13.
  rename H3 into shPG1. rename H4 into MInj13'. rename H5 into RetInject13'.
  rename H6 into Fwd1. rename H7 into UnchLocalSrc1.
  rename H8 into Fwd3. rename H9 into UnchLocalTgt3.  
  rename H10 into HTRet3.
  rename H11 into RetValid1'. rename H12 into RetValid3'.
  (*assert (ZZ1 : Mem.unchanged_on
                  (fun (b : block) (ofs : Z) =>
                   myBlocksSrc mu b /\ loc_unmapped (local_of mu) b ofs) m1 m1').
    eapply mem_unchanged_on_sub. eassumption.
    intros. destruct H; simpl. split; trivial.
    unfold loc_unmapped in *.
    destruct mu as [BSrc BTgt pSrc pTgt frgn pub priv]. simpl in *.
    unfold join in H1.
    remember (pub b) as d; destruct d; trivial.
       destruct p. inv H1. *)
  destruct MS as [st2 [m2 [mu1 [mu2 [myBlocks2 (*[pubBlocks2*) [X [J [TgtB1
          [SrcB2 (*[pTgtB1 [pSrcB2*) [MC12 MC23]]]]]]]]]](*]]]*); subst.
  rename H0 into VV1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1 VV1) 
   as [vals2 [HTVals2 [AtExt2
         [VV2 [sharedInj12 [sharedValsInject2 sharedPG1]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 VV2) 
   as [vals [HTVals3 [AtExt3
         [VV3 [sharedInj23 [sharedValsInject3 sharedPG2]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
  eapply forall_valinject_hastype; eassumption.
  assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). 
  eapply valinject_hastype; eassumption.
  apply eq_sym in SrcB2.
  assert (CSS:shared_of (compose_sm mu1 mu2) = compose_meminj (shared_of mu1) (shared_of mu2)).
      apply compose_sm_shared; eauto.
  rewrite CSS in *. 
  destruct (interp _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ MInj13' INC SEP mu1 mu2 
     UnchLocalSrc1 (eq_refl _) (eq_refl _) UnchLocalTgt3)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' Unch2233']]]]]]]]]]]]].
    eauto. eauto. eauto. eauto. eauto.  
(*
  assert (UU1: Mem.unchanged_on
        (loc_unmapped (compose_meminj (shared_of mu1) (shared_of mu2))) m1 m1').
     later
  assert (UU2: Mem.unchanged_on
        (loc_out_of_reach (compose_meminj (shared_of mu1) (shared_of mu2)) m1) m3 m3').
      later
  destruct (MEMAX.interpolate_II _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ MInj13' INC SEP UU1 UU2)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' [Unch2233' WD22']]]]]]]]]]]]]].
    eauto. eauto. eauto. eauto. eauto.  *)
  assert (exists ret2, val_inject j12' ret1 ret2 /\ val_inject j23' ret2 ret3 /\
    Val.has_type ret2 (proj_sig_res ef_sig) /\ val_valid ret2 m2'). 
  subst. apply val_inject_split in RetInject13'.
         destruct RetInject13' as [ret2 [injRet12 injRet23]]. 
  exists ret2. split; trivial. split; trivial. 
  split. eapply valinject_hastype; eassumption.
  eapply inject_valvalid; eassumption. 
  destruct H as [ret2 [injRet12 [injRet23 [HTRet2 RetValid2']]]].
  assert (Unch111':  Mem.unchanged_on
            (fun b ofs => myBlocksSrc mu1 b /\ 
                          loc_unmapped (pub_of mu1) b ofs) m1 m1').
     eapply mem_unchanged_on_sub; try eassumption.
     intros; simpl. destruct H.
     split; trivial.
     unfold loc_unmapped in *.
     unfold compose_meminj, join.
     destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1]. simpl in *.
     rewrite H0. trivial.
(*assert (Unch111':  Mem.unchanged_on
            (fun b ofs => myBlocksSrc mu1 b /\ 
                          loc_unmapped (local_of mu1) b ofs) m1 m1').
     eapply mem_unchanged_on_sub; try eassumption.
     intros; simpl. destruct H.
     split; trivial.
     unfold loc_unmapped in *.
     destruct (match_sm_wd12 _ _ _ _ _ _ MC12) as [DST12 _].
     destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
     destruct mu2 as [BSrc2 BTgt2 psrc2 pTgt2 frgn2 pub2 priv2].
     simpl in *.
     unfold compose_meminj, join.
          specialize (joinD _ _ DST12 b). rewrite H0. intros.
     destruct H1 as [HH KK]; rewrite HH, KK. trivial.*)  
   (*Mem.unchanged_on (loc_unmapped (shared_of mu1)) m1 m1').
     later
     split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
     rewrite H0. trivial. trivial. 
     intros. rewrite H0. trivial. trivial.*)
  specialize (core_after_external12 _ _ _ _ _ _ _ ret1 
      m1' m2 m2' ret2 _ MC12 AtExt1 VV1 _ sharedInj12 
      sharedValsInject2 sharedPG1 _ Incr12 Sep12 MInj12'
      injRet12 Fwd1 Unch111' Fwd2 Unch22 HTRet2
      RetValid1' RetValid2').
  destruct core_after_external12 as 
     [d12' [c1' [c2' [AftExt1 [AftExt2 [nu12 [NU12 MC12']]]]]]].
    subst.

  specialize (core_after_external23 _ _ _ _ _ _ _ ret2
      m2' m3 m3' ret3 _ MC23 AtExt2 VV2 _ sharedInj23 
      sharedValsInject3 sharedPG2 _ Incr23 Sep23 MInj23'
      injRet23 Fwd2 Unch222' Fwd3 Unch2233' HTRet3
      RetValid2' RetValid3').
  destruct core_after_external23 as 
     [d23' [cc2' [c3' [AftExt22 [AftExt3 [nu23 [NU23 MC23']]]]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some (c2', myBlocksSrc mu2), d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  eexists. split. reflexivity.
  exists c2'. exists m2'. exists (extend_foreign mu1 j12' m1 m2). 
     exists (extend_foreign mu2 j23' m2 m3).
     exists (myBlocksSrc mu2). 
     split. trivial.
     split. eapply compose_sm_extend_foreign; eauto.
     split. rewrite extend_foreign_myBlocksTgt. assumption.
     split. apply extend_foreign_myBlocksSrc.
     split; assumption.

(*eff_after_external*)
  clear core_diagram12 core_initial12 core_halted12 
    core_diagram23 core_initial23 core_halted23
    eff_diagram12 eff_diagram23
    core_after_external12 (*core_at_externalFAT1*)
    core_after_external23 (*FAT0 core_at_externalFAT0*). 
  intros. rename st2 into st3. rename m2 into m3.
  rename ret2 into ret3. rename m2' into m3'. 
  destruct cd as [[d12 cc2] d23]. rename vals2 into vals3.
  rename H into AtExt1. rename H1 into MInj13. rename H2 into ValInject13.
  rename H3 into shPG1. rename H4 into MInj13'. rename H5 into RetInject13'.
  rename H6 into Fwd1. rename H7 into Fwd3.  
  rename H8 into HTRet3.
  rename H9 into RetValid1'. rename H10 into RetValid3'.
  rename H11 into UnchM1. 
  rename M2 into M3. rename H12 into UnchM3.
  rename H13 into unmapped13_M1. rename H14 into PubM3M1.
  rename H15 into PermM1. rename H16 into PermM3.
(*  rename H15 into HypFrgn31.*)
  (*assert (ZZ1 : Mem.unchanged_on
                  (fun (b : block) (ofs : Z) =>
                   myBlocksSrc mu b /\ loc_unmapped (local_of mu) b ofs) m1 m1').
    eapply mem_unchanged_on_sub. eassumption.
    intros. destruct H; simpl. split; trivial.
    unfold loc_unmapped in *.
    destruct mu as [BSrc BTgt pSrc pTgt frgn pub priv]. simpl in *.
    unfold join in H1.
    remember (pub b) as d; destruct d; trivial.
       destruct p. inv H1. *)
  destruct MS as [st2 [m2 [mu1 [mu2 [myBlocks2 (*[pubBlocks2*) [X [J [TgtB1
          [SrcB2 (*[pTgtB1 [pSrcB2*) [MC12 MC23]]]]]]]]]](*]]]*); subst.
  rename H0 into VV1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1 VV1) 
   as [vals2 [HTVals2 [AtExt2
         [VV2 [sharedInj12 [sharedValsInject2 sharedPG1]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 VV2) 
   as [vals [HTVals3 [AtExt3
         [VV3 [sharedInj23 [sharedValsInject3 sharedPG2]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
  eapply forall_valinject_hastype; eassumption.
  assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). 
  eapply valinject_hastype; eassumption.
  apply eq_sym in SrcB2.
  assert (CSS:shared_of (compose_sm mu1 mu2) = compose_meminj (shared_of mu1) (shared_of mu2)).
      apply compose_sm_shared; eauto.
  rewrite CSS in *. 
  assert(unmapped12_M1 : forall (b : block) (ofs : Z),
      myBlocksSrc mu1 b ->
      loc_unmapped (pub_of mu1) b ofs -> ~ M1 b ofs).
   intros. eapply unmapped13_M1. simpl. apply H.
        unfold loc_unmapped in H0. unfold loc_unmapped.
          simpl. unfold compose_meminj. 
        destruct mu1. simpl in *. rewrite H0. trivial.
  assert (SMV12:= match_validblock12 _ _ _ _ _ _ MC12).
  assert (SMV23:= match_validblock23 _ _ _ _ _ _ MC23).
  assert (SMWD12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (SMWD23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct (effect_interp _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ _ _ MInj13' INC SEP SMV12 SMV23 SMWD12 SMWD23 
     SrcB2 M1 M3 UnchM1 (eq_refl _) (eq_refl _) UnchM3 unmapped13_M1 PubM3M1
     (*HypFrgn31*) unmapped12_M1 PermM1 PermM3)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Sep12 [Sep23 [M2 [UnchM2 [PermM2 [unmapped23_M2 [Unch2B (*[*)Unch2C (*[HypFrgn21 HypFrgn32]]*)]]]]]]]]]]]]]]]].
 (*
  assert (UU1: Mem.unchanged_on
        (loc_unmapped (compose_meminj (shared_of mu1) (shared_of mu2))) m1 m1').
     later
  assert (UU2: Mem.unchanged_on
        (loc_out_of_reach (compose_meminj (shared_of mu1) (shared_of mu2)) m1) m3 m3').
      later
  destruct (MEMAX.interpolate_II _ _ _ sharedInj12 _ 
     Fwd1 _ _ sharedInj23 _ Fwd3 _ MInj13' INC SEP UU1 UU2)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' [Unch2233' WD22']]]]]]]]]]]]]].
    eauto. eauto. eauto. eauto. eauto.  *) 

  assert (JPub: join (compose_meminj j12' j23')
                     (compose_meminj (pub_of mu1) (pub_of mu2))
           = compose_meminj (join j12' (pub_of mu1)) (join j23' (pub_of mu2))).
    specialize (match_validblock23 _ _ _ _ _ _ MC23).
    specialize (match_validblock12 _ _ _ _ _ _ MC12).
    solve[eapply compose_pub_join; eauto].
  assert (exists ret2, val_inject (join j12' (pub_of mu1)) ret1 ret2 /\ 
                       val_inject (join j23' (pub_of mu2)) ret2 ret3 /\
    Val.has_type ret2 (proj_sig_res ef_sig) /\ val_valid ret2 m2'). 
    subst. rewrite compose_sm_pub in RetInject13'.
    rewrite JPub in RetInject13'.
    apply val_inject_split in RetInject13'.
    destruct RetInject13' as [ret2 [injRet12 injRet23]].  
    exists ret2. split; trivial. split; trivial. 
    split. eapply valinject_hastype; eassumption.
    eapply inject_valvalid; eassumption.
    eauto.
    eauto.
    assumption. 
  destruct H as [ret2 [injRet12 [injRet23 [HTRet2 RetValid2']]]].
(*assert (Unch111':  Mem.unchanged_on
            (fun b ofs => myBlocksSrc mu1 b /\ 
                          loc_unmapped (local_of mu1) b ofs) m1 m1').
     eapply mem_unchanged_on_sub; try eassumption.
     intros; simpl. destruct H.
     split; trivial.
     unfold loc_unmapped in *.
     destruct (match_sm_wd12 _ _ _ _ _ _ MC12) as [DST12 _].
     destruct mu1 as [BSrc1 BTgt1 pSrc1 pTgt1 frgn1 pub1 priv1].
     destruct mu2 as [BSrc2 BTgt2 psrc2 pTgt2 frgn2 pub2 priv2].
     simpl in *.
     unfold compose_meminj, join.
          specialize (joinD _ _ DST12 b). rewrite H0. intros.
     destruct H1 as [HH KK]; rewrite HH, KK. trivial.*)  
   (*Mem.unchanged_on (loc_unmapped (shared_of mu1)) m1 m1').
     later
     split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
     rewrite H0. trivial. trivial. 
     intros. rewrite H0. trivial. trivial.*)
  specialize (eff_after_external12 _ _ _ _ _ _ _ ret1 
      m1' m2 m2' ret2 _ MC12 AtExt1 VV1 _ sharedInj12 
      sharedValsInject2 sharedPG1 _ Incr12 Sep12 MInj12'
      injRet12 Fwd1 Fwd2 HTRet2 RetValid1' RetValid2' M1 M2 
      UnchM1 UnchM2 unmapped12_M1 Unch2C (*HypFrgn21 *) PermM1 PermM2). 
  destruct eff_after_external12 as 
     [d12' [c1' [c2' [AftExt1 [AftExt2 [nu12 [NU12 MC12']]]]]]].
    subst.

  specialize (eff_after_external23 _ _ _ _ _ _ _ ret2
      m2' m3 m3' ret3 _ MC23 AtExt2 VV2 _ sharedInj23 
      sharedValsInject3 sharedPG2 _ Incr23 Sep23 MInj23'
      injRet23 Fwd2 Fwd3 HTRet3 RetValid2' RetValid3' M2 M3
      UnchM2 UnchM3 unmapped23_M2 Unch2B (*HypFrgn32 *) PermM2 PermM3).
  destruct eff_after_external23 as 
     [d23' [cc2' [c3' [AftExt22 [AftExt3 [nu23 [NU23 MC23']]]]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some (c2', myBlocksSrc mu2), d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  eexists. split. reflexivity.
  exists c2'. exists m2'. exists (extend_foreign mu1 j12' m1 m2). 
     exists (extend_foreign mu2 j23' m2 m3).
     exists (myBlocksSrc mu2). 
     split. trivial.
     split. solve [eapply compose_sm_foreign_extend_foreign; eauto].
     split. solve [rewrite extend_foreign_myBlocksTgt; assumption].
     split. solve [apply extend_foreign_myBlocksSrc].
     split; assumption.
(*case AT_EXTERNAL_FAT*)
(*case AFTER_EXTERNAL_FAT*)
Qed.*)
*)*)