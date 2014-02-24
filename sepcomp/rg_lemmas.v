Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import compcert.common.Globalenvs.

Require Import compcert.lib.Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.reach.
Require Import sepcomp.effect_simulations.

Definition FLIP mu := 
  match mu with
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern =>
    Build_SM_Injection extBSrc extBTgt fSrc fTgt extern locBSrc locBTgt pSrc pTgt local 
  end.

Lemma SAWP_wd: forall mu (WD: SM_wd mu), SM_wd (FLIP mu).
intros.
destruct mu; simpl in *.
destruct WD.
split; intros; simpl in *; try solve[auto]. 
  destruct (disjoint_extern_local_Src b); intuition.
  destruct (disjoint_extern_local_Tgt b); intuition.
  apply (extern_DomRng _ _ _ H). 
  apply (local_DomRng _ _ _ H).
Qed.

Lemma FLIPlocBlocksSrc: forall mu,
  locBlocksSrc (FLIP mu) = extBlocksSrc mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPlocBlocksTgt: forall mu,
  locBlocksTgt (FLIP mu) = extBlocksTgt mu.
Proof. intros. destruct mu; reflexivity. Qed.

Lemma FLIPextBlocksSrc: forall mu,
  extBlocksSrc (FLIP mu) = locBlocksSrc mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPextBlocksTgt: forall mu,
  extBlocksTgt (FLIP mu) = locBlocksTgt mu.
Proof. intros. destruct mu; reflexivity. Qed.

Lemma FLIPpubBlocksSrc: forall mu,
  pubBlocksSrc (FLIP mu) = frgnBlocksSrc mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPpubBlocksTgt: forall mu,
  pubBlocksTgt (FLIP mu) = frgnBlocksTgt mu.
Proof. intros. destruct mu; reflexivity. Qed.

Lemma FLIPfrgnBlocksSrc: forall mu,
  frgnBlocksSrc (FLIP mu) = pubBlocksSrc mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPfrgnBlocksTgt: forall mu,
  frgnBlocksTgt (FLIP mu) = pubBlocksTgt mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPlocal: forall mu,
  local_of (FLIP mu) = extern_of mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPextern: forall mu,
  extern_of (FLIP mu) = local_of mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma RelyGuaranteeSrc: forall mu (WD: SM_wd mu) Esrc m m'
              (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                                     vis mu b = true)
               (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m'),
         Mem.unchanged_on (fun b ofs => locBlocksSrc (FLIP mu) b = true /\ 
                                        pubBlocksSrc (FLIP mu) b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros. simpl.
  rewrite FLIPlocBlocksSrc, FLIPpubBlocksSrc in H.
  case_eq (Esrc b ofs); intros; trivial; simpl in *.
  destruct H.
  destruct (disjoint_extern_local_Src _ WD b). 
  apply SrcHyp in H0. unfold vis in H0. rewrite H2, H1 in H0. discriminate. 
  congruence.
Qed.

Lemma unchanged_on_perm: forall (P:block -> Z -> Prop) m m'
      (Unch: Mem.unchanged_on P m m'),
      Mem.unchanged_on (fun b z => P b z /\ Mem.perm m b z Max Nonempty) m m'.
Proof. intros.
split; intros; eapply Unch; eauto.
apply H. apply H.
Qed.

Lemma unchanged_on_perm': forall (P:block -> Z -> Prop) m m'
      (Unch: Mem.unchanged_on (fun b z => P b z \/ ~ Mem.perm m b z Max Nonempty) m m'),
      Mem.unchanged_on P m m'.
Proof. intros.
split; intros; eapply Unch; eauto.
Qed. 

Lemma RelyGuaranteeTgtPerm: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)
            (*m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty)*),
            Mem.unchanged_on (local_out_of_reach (FLIP mu) m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl.
  case_eq (Etgt b ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  rewrite FLIPlocBlocksTgt in H. 
  destruct F as [b1 [d1 [Frg [ES P]]]].
    apply (extBlocksTgt_locBlocksTgt _ WD _ H).
  destruct (H1 b1 d1); clear H1.
     rewrite FLIPlocal.
     apply foreign_in_extern; assumption.
     congruence. 
  rewrite FLIPpubBlocksSrc in H2.
    apply (foreign_DomRng _ WD) in Frg. intuition.
    rewrite H6 in H2. inv H2.
Qed.

Lemma RelyGuaranteeTgt: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu)
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)
            m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty),
            Mem.unchanged_on (local_out_of_reach (FLIP mu) m1) m2 m2'.
Proof. intros. 
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  rewrite FLIPlocBlocksTgt in H.
  destruct F as [b1 [d1 [Frg ES]]].
    apply (extBlocksTgt_locBlocksTgt _ WD _ H).
  rewrite FLIPlocal in H1.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
(*  apply SrcHyp in ES. unfold vis in ES.
    rewrite CC in ES; simpl in ES.(* rewrite H2 in *. inv CC.*)*)
  specialize (SrcPerm _ _ ES).
  destruct (H1 b1 d1); clear H1.
     apply foreign_in_extern; assumption.
     contradiction.
  rewrite FLIPpubBlocksSrc in H2. congruence. 
Qed.


(*Once these RG results are used in a linker/concurrency machine,
  we will need to remove all blocks b with isGlobalBlock ge from pubBlocks*)
Lemma RGSrc_multicore: forall mu Esrc m m'
         (SrcHyp: forall b ofs, Esrc b ofs = true -> Mem.valid_block m b -> vis mu b = true)
         (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m')
          nu
         (VAL: smvalid_src nu m)
         (LB: forall b, locBlocksSrc nu b = true -> locBlocksSrc mu b = false) 
         (PB: forall b, frgnBlocksSrc mu b && locBlocksSrc nu b = true ->
                        pubBlocksSrc nu b = true),
         Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
                                        pubBlocksSrc nu b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros b1 ofs H2. simpl.
  case_eq (Esrc b1 ofs); intros; trivial; simpl in *. 
  apply SrcHyp in H. unfold vis in H.  
  clear Unch SrcHyp.
  destruct H2. 
  rewrite LB in H; trivial; clear LB.
  rewrite PB in H1; trivial. intuition.
  destruct H2.
  apply (VAL b1). unfold DOM, DomSrc. rewrite H0; auto.
Qed.

Lemma RGSrc_multicore'': forall mu Esrc m m'
         (SrcHyp: forall b ofs, Esrc b ofs = true -> Mem.valid_block m b -> vis mu b = true)
         (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m')
          nu
(*         (VAL: smvalid_src nu m)*)
         (LB: forall b, locBlocksSrc nu b = true -> locBlocksSrc mu b = false) 
         (PB: forall b, frgnBlocksSrc mu b && locBlocksSrc nu b = true ->
                        pubBlocksSrc nu b = true),
         Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
                                        pubBlocksSrc nu b = false) m m'.
Proof. intros.
  eapply unchanged_on_validblock; try eassumption.
  intros b1 ofs VAL H2. simpl.
  case_eq (Esrc b1 ofs); intros; trivial; simpl in *. 
  apply SrcHyp in H; trivial. unfold vis in H.  
  clear Unch SrcHyp.
  destruct H2. 
  rewrite LB in H; trivial; clear LB.
  rewrite PB in H1; trivial. intuition.
Qed.

Lemma RGSrc_multicore': forall mu (WDmu: SM_wd mu) Esrc m m'
         (SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)
         (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m')
          nu (WDnu: SM_wd nu) 
         (LB: forall b, locBlocksSrc nu b = true -> locBlocksSrc mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksSrc nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
         Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
                                        pubBlocksSrc nu b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros b1 ofs H2. simpl.
  case_eq (Esrc b1 ofs); intros; trivial; simpl in *. 
  apply SrcHyp in H. unfold vis in H.  
  clear Unch SrcHyp.
  destruct H2. 
  rewrite LB in H; trivial; clear LB.
  simpl in H.
  destruct (frgnSrc _ WDmu _ H) as [b2 [d [Frg FT]]].
  apply X2 in Frg.
     destruct (pubChar _ WDnu _ _ _ Frg).
     rewrite H1 in H2. discriminate.
  rewrite H0; reflexivity.
Qed.

Lemma RGSrc_multicoreLICSpaper: forall mu (WDmu: SM_wd mu) Esrc m m'
         (SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)
         (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m')
          nu (WDnu: SM_wd nu) 
         (LB: forall b, locBlocksSrc nu b = true -> locBlocksSrc mu b = true -> False)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksSrc nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
         Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
                                        pubBlocksSrc nu b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros b1 ofs H2. simpl.
  case_eq (Esrc b1 ofs); intros; trivial; simpl in *. 
  apply SrcHyp in H. unfold vis in H.  
  clear Unch SrcHyp.
  destruct H2. 
  specialize (LB b1 H0).
  remember (locBlocksSrc mu b1) as d.
  destruct d; simpl in *; try contradiction. clear LB.
  destruct (frgnSrc _ WDmu _ H) as [b2 [d [Frg FT]]].
  apply X2 in Frg.
     destruct (pubChar _ WDnu _ _ _ Frg).
     rewrite H1 in H2. discriminate.
  rewrite H0; reflexivity.
Qed.

Lemma RGTgt_multicore: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu)
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (*(SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)*)
            m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty)
            nu
         (X1: forall b, locBlocksTgt nu b = true -> locBlocksTgt mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksSrc nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
            Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  specialize (X1 _ H). 
  destruct (F X1) as [b1 [d1 [Frg ES]]]; clear F.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  clear DD.
(*  apply SrcHyp in ES. clear SrcHyp.
    rewrite H2 in *. inv CC.
  clear H2.*)
  specialize (X2 _ _ _ Frg). rewrite H in X2.
  rewrite orb_true_r in X2. specialize (X2 (eq_refl _)). 
  destruct (H1 b1 d1).
    apply pub_in_local. apply X2.
    specialize (SrcPerm _ _ ES). contradiction.
  rewrite (pubSrcContra _ _ H2) in X2. inv X2. 
Qed.

Lemma RGTgt_multicorePerm': forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            nu (WDnu: SM_wd nu) (AI: inject_incr (as_inj nu) (as_inj mu))
             (SEP: sm_inject_separated nu mu m1 m2)
         (X1: forall b, locBlocksTgt nu b = true -> locBlocksTgt mu b = false)
         (PB: forall b, frgnBlocksSrc mu b && locBlocksSrc nu b = true ->
                        pubBlocksSrc nu b = true),
            Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  specialize (X1 _ H). 
  destruct (F X1) as [b1 [d1 [Frg [ES P]]]]; clear F.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  clear DD.
  assert (LOC: local_of nu b1 = Some (b2, d1)).
    apply foreign_in_all in Frg.
    remember (as_inj nu b1) as d.
    destruct d; apply eq_sym in Heqd.
      destruct p. rewrite (AI _ _ _ Heqd) in Frg. inv Frg.
      destruct (joinD_Some _ _ _ _ _ Heqd); try eauto.
        assert (locBlocksTgt nu b2 = false)
           by eapply (extern_DomRng' _ WDnu _ _ _ H2).
        rewrite H3 in H; discriminate.
      apply H2.
    destruct SEP as [SEPa [SEPb SEPc]].
      destruct (SEPa _ _ _ Heqd Frg).
      eelim SEPc; try eassumption.
      eapply (as_inj_DomRng); eassumption.
  destruct (local_DomRng _ WDnu _ _ _ LOC).
  specialize (PB b1); rewrite EE, H2 in PB; simpl in PB.
  destruct (H1 _ _ LOC). contradiction.
  rewrite PB in H4; intuition. 
Qed.

Lemma RGTgt_multicorePerm: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (*(SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)*)
            nu
         (X1: forall b, locBlocksTgt nu b = true -> locBlocksTgt mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksSrc nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
            Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  specialize (X1 _ H). 
  destruct (F X1) as [b1 [d1 [Frg [ES P]]]]; clear F.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  clear DD.
  (*destruct (SrcHyp _ _ ES); clear SrcHyp.
    rewrite H2 in *. inv CC.
  clear H2.*)
  specialize (X2 _ _ _ Frg). rewrite H in X2.
  rewrite orb_true_r in X2. specialize (X2 (eq_refl _)). 
  destruct (H1 b1 d1).
    apply pub_in_local. apply X2.
    contradiction.
  rewrite (pubSrcContra _ _ H2) in X2. inv X2. 
Qed.

Lemma RGTgt_multicoreNOEFFECTS: forall mu m2 m2' (WD: SM_wd mu)
            (TgtHyp1: Mem.unchanged_on (fun b2 ofs => extBlocksTgt mu b2 = true /\
                                           ~ exists b1 d, foreign_of mu b1=Some (b2,d)) m2 m2')
            m1 m1' 
            (TgtHyp2: forall b ofs, Mem.unchanged_on (fun b' ofs' => b'=b /\ ofs'=ofs) m1 m1' ->
                      forall b2 d, foreign_of mu b = Some(b2,d) -> 
                           Mem.unchanged_on (fun b' ofs' => b'=b2 /\ ofs'=ofs+d) m2 m2')
            nu (WDnu: SM_wd nu)
           (FWD1: mem_forward m1 m1')
           (X1: forall b, locBlocksTgt nu b = true ->
                        DomTgt mu b = true /\ locBlocksTgt mu b = false)
           (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksSrc nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d))
            (Unch1: Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
                                           pubBlocksSrc nu b = false) m1 m1')
           (DECIDABILITYAXIOM: forall b2 (E: extBlocksTgt mu b2 = true),
                (exists b1 d, foreign_of mu b1 = Some(b2,d)) \/
                (~ exists b1 d, foreign_of mu b1=Some (b2,d))),
            Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'.
Proof. intros. 
split; intros b2; intros.
(*permissions*)
  destruct H.
  destruct (X1 _ H); clear X1.
  assert (extBlocksTgt mu b2 = true).
    unfold DomTgt in H2. rewrite H3 in H2; simpl in H2. assumption.
  destruct (DECIDABILITYAXIOM _ H4); clear DECIDABILITYAXIOM.
    destruct H5 as [b1 [dd FRGN]].
    specialize (X2 _ _ _ FRGN). rewrite H in X2.
    assert (local_of nu b1 = Some(b2,dd)). apply pub_in_local. apply X2; intuition. 
    eapply TgtHyp2; clear TgtHyp2; try eassumption.
    Focus 2. split. trivial. instantiate (1:=ofs-dd). omega.
    destruct (H1 _ _ H5); clear H1.
      eapply forward_unchanged_on; assumption.      
    eapply mem_unchanged_on_sub; try eassumption.
      intros. destruct H1; subst. split; trivial.
      eapply (local_DomRng _ WDnu _ _ _ H5).
  eapply TgtHyp1. split; trivial. assumption.
(*Values - same proof*)
  destruct H.
  destruct (X1 _ H); clear X1.
  assert (extBlocksTgt mu b2 = true).
    unfold DomTgt in H2. rewrite H3 in H2; simpl in H2. assumption.
  destruct (DECIDABILITYAXIOM _ H4); clear DECIDABILITYAXIOM.
    destruct H5 as [b1 [dd FRGN]].
    specialize (X2 _ _ _ FRGN). rewrite H in X2.
    assert (local_of nu b1 = Some(b2,dd)). apply pub_in_local. apply X2; intuition. 
    eapply TgtHyp2; clear TgtHyp2; try eassumption.
    Focus 2. split. trivial. instantiate (1:=ofs-dd). omega.
    destruct (H1 _ _ H5); clear H1.
      eapply forward_unchanged_on; assumption.      
    eapply mem_unchanged_on_sub; try eassumption.
      intros. destruct H1; subst. split; trivial.
      eapply (local_DomRng _ WDnu _ _ _ H5).
  eapply TgtHyp1. split; trivial. assumption.
Qed.

Record LinkInv (mu0 mu: SM_Injection) :=
  { LinkInv_WD0: SM_wd mu0;
    LinkInv_WD:  SM_wd mu;
    LinkInv_DomSrc: forall b, DomSrc mu0 b = true -> DomSrc mu b = true;
    LinkInv_DomTgt: forall b, DomTgt mu0 b = true -> DomTgt mu b = true;
    LinkInv_Restrict: restrict (as_inj mu) (DomSrc mu0) = as_inj mu0;
    LinkInv_Sep: forall b1 b2 d, as_inj mu0 b1 = None -> as_inj mu b1 = Some(b2,d) ->
                       (DomSrc mu0 b1 = false /\ DomTgt mu0 b2 = false) }.

Lemma LinkInv_sound: forall mu0 mu (LI : LinkInv mu0 mu)
         nu (NU: nu = reestablish mu0 mu), 
      SM_wd nu /\ DomSrc nu = DomSrc mu /\ DomTgt nu = DomTgt mu /\ 
      extern_incr mu0 nu /\ as_inj nu = as_inj mu /\
      (forall m1 m2, sm_inject_separated mu0 mu m1 m2 ->
              sm_inject_separated mu0 nu m1 m2) /\
      (forall m1 m2, sm_valid mu m1 m2 ->
              sm_valid (reestablish mu0 mu) m1 m2) /\
      (forall mu', SM_wd mu' -> intern_incr mu mu' -> 
                   extern_incr mu0 (reestablish mu0 mu')).
Proof. intros. subst.
assert (LocSrc: forall b, locBlocksSrc mu0 b = true -> DomSrc mu b = true).
   intros. eapply (LinkInv_DomSrc _ _ LI); unfold DomSrc; intuition.
assert (ExtSrc: forall b, extBlocksSrc mu0 b = true -> DomSrc mu b = true).
   intros. eapply (LinkInv_DomSrc _ _ LI); unfold DomSrc; intuition.
assert (LocTgt: forall b, locBlocksTgt mu0 b = true -> DomTgt mu b = true).
   intros. eapply (LinkInv_DomTgt _ _ LI); unfold DomTgt; intuition.
assert (ExtTgt: forall b, extBlocksTgt mu0 b = true -> DomTgt mu b = true).
   intros. eapply (LinkInv_DomTgt _ _ LI); unfold DomTgt; intuition.
assert (DS:= reestablish_DomSrc _ _ LocSrc).
assert (DT:= reestablish_DomTgt _ _ LocTgt).
intuition.
  eapply reestablish_wd; try eassumption; eapply LI.
  eapply reestablish_extern_incr; eassumption.
  eapply reestablish_as_inj; eassumption.
  eapply reestablish_sm_injsep; try eassumption.
  eapply reestablish_sm_valid; try eassumption.
  eapply (reestablish_internstep mu0 mu mu'); try eassumption.
Qed.

Lemma atExternal_Protected: forall mu m1
         (MatchProtected: forall b, REACH m1 (extBlocksSrc mu) b = true ->
                        locBlocksSrc mu b = true ->
                        REACH m1 (sharedSrc mu) b = true)
        vals1 vals2
        (ValInjMu: Forall2 (val_inject (as_inj mu)) vals1 vals2)  
        pubSrc' (pubSrcHyp: pubSrc' = fun b => andb (locBlocksSrc mu b)
                                                    (REACH m1 (exportedSrc mu vals1) b))

        pubTgt' 
        nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),
    forall b, REACH m1 (extBlocksSrc nu) b = true ->
                        locBlocksSrc nu b = true ->
                        pubBlocksSrc nu b = true.
Proof. intros. subst.
  rewrite replace_locals_pubBlocksSrc.
  rewrite replace_locals_locBlocksSrc in H0.
  rewrite replace_locals_extBlocksSrc in H.
  rewrite H0; simpl.
  specialize (MatchProtected _ H H0).
  eapply REACH_mono; try eapply MatchProtected.
  unfold exportedSrc. intuition.
Qed.

