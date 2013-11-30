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
Require Import sepcomp.effect_simulations.


(***** Some results on meminj_preserves_globals and variants of 
        LSR-clause match_genv  ************************************)
Lemma match_genv_meminj_preserves_globals_extern_implies_foreign: 
      forall {F V} (ge: Genv.t F V) mu (WDmu : SM_wd mu)
             (PG: meminj_preserves_globals ge (extern_of mu) /\
                 (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)),
      meminj_preserves_globals ge (foreign_of mu).
Proof. intros.
destruct PG as [PG GF].
apply meminj_preserves_genv2blocks in PG.
destruct PG as [PGa [PGb PGc]].
apply meminj_preserves_genv2blocks.
  split; intros.
    specialize (PGa _ H).
    destruct (frgnSrc _ WDmu b) as [b2 [d [Frg1 FT2]]].
      apply GF. unfold isGlobalBlock.
      apply genv2blocksBool_char1 in H. rewrite H. intuition.
    rewrite (foreign_in_extern _ _ _ _ Frg1) in PGa.
      inv PGa. assumption.
  split; intros.
    specialize (PGb _ H).
    destruct (frgnSrc _ WDmu b) as [b2 [d [Frg1 FT2]]].
      apply GF. unfold isGlobalBlock.
      apply genv2blocksBool_char2 in H. rewrite H. intuition.
    rewrite (foreign_in_extern _ _ _ _ Frg1) in PGb.
      inv PGb. assumption.
  apply foreign_in_extern in H0. apply (PGc _ _ _ H H0).
Qed.

Lemma match_genv_meminj_preserves_extern_iff_all: 
      forall {F V} (ge: Genv.t F V) mu (WDmu : SM_wd mu)
             (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true),
      meminj_preserves_globals ge (as_inj mu) =
      meminj_preserves_globals ge (extern_of mu).
Proof. intros.
  apply prop_ext.
split; intros PG;
       apply meminj_preserves_genv2blocks;
       apply meminj_preserves_genv2blocks in PG;
       destruct PG as [PGa [PGb PGc]].
  split; intros. 
    destruct (frgnSrc _ WDmu b) as [b2 [dd [Frg1 FT2]]].
      apply GF. unfold isGlobalBlock.
      apply genv2blocksBool_char1 in H. intuition.
    specialize (PGa _ H).
    rewrite (foreign_in_all _ _ _ _ Frg1) in PGa. inv PGa.
    apply foreign_in_extern; eassumption.
  split; intros. 
    destruct (frgnSrc _ WDmu b) as [b2 [dd [Frg1 FT2]]].
      apply GF. unfold isGlobalBlock.
      apply genv2blocksBool_char2 in H. intuition.
    specialize (PGb _ H).
    rewrite (foreign_in_all _ _ _ _ Frg1) in PGb. inv PGb.
    apply foreign_in_extern; eassumption.
  apply extern_in_all in H0. eauto.
split; intros.
  apply extern_in_all. eauto.
split; intros.
  apply extern_in_all. eauto.
specialize (PGb _ H).
  destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [EXT LOC]]; clear H0.
    eauto.
  destruct (extern_DomRng _ WDmu _ _ _ PGb) as [? ?].
    destruct (local_DomRng _ WDmu _ _ _ LOC).
    destruct (disjoint_extern_local_Tgt _ WDmu b2); congruence.
Qed.

Lemma meminj_preserves_globals_initSM_all: forall {F1 V1} (ge: Genv.t F1 V1) j
                  (PG : meminj_preserves_globals ge j) DomS DomT X Y,
      meminj_preserves_globals ge (as_inj (initial_SM DomS DomT X Y j)).
Proof. intros. 
    apply meminj_preserves_genv2blocks.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    unfold initial_SM; split; intros; unfold as_inj; simpl in *.
       apply joinI; left. eauto.
    split; intros; simpl in *.
       apply joinI; left. eauto.
    destruct (joinD_Some _ _ _ _ _ H0) as [HH | [_ HH]]; clear H0.
       eauto. inv HH.
Qed.

(*version of Lemma meminj_preserves_globals_initSM, for a 
  definition of clause match_genv that uses foreign_of*)
Lemma meminj_preserves_globals_initSM_frgn: forall {F1 V1} (ge: Genv.t F1 V1) j
                  (PG : meminj_preserves_globals ge j) DomS DomT m R Y
                  (HR: forall b, isGlobalBlock ge b = true -> R b = true),
      meminj_preserves_globals ge (foreign_of (initial_SM DomS DomT (REACH m R) Y j)).
Proof. intros. 
    apply meminj_preserves_genv2blocks.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    unfold initial_SM; split; intros; simpl in *.
       specialize (PGa _ H). rewrite PGa.
       assert (REACH m R b = true).
         apply REACH_nil. apply HR. 
         unfold isGlobalBlock, genv2blocksBool; simpl.
         destruct H as [id ID].
         apply Genv.find_invert_symbol in ID. rewrite ID. reflexivity.
       rewrite H0; trivial.
    split; intros; simpl in *.
       specialize (PGb _ H). rewrite PGb.
       assert (REACH m R b = true).
         apply REACH_nil. apply HR. 
         unfold isGlobalBlock, genv2blocksBool; simpl.
         destruct H as [id ID]. rewrite ID. intuition.
       rewrite H0; trivial.
     apply (PGc _ _ delta H).
       remember (REACH m R b1) as d.
       destruct d; congruence.
Qed.

Lemma core_initial_wd_as_inj : forall {F1 V1 F2 V2} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) 
                               vals1 m1 j vals2 m2 DomS DomT
          (MInj: Mem.inject j m1 m2)
          (VInj: Forall2 (val_inject j) vals1 vals2)
          (HypJ: forall b1 b2 d, j b1 = Some (b2, d) -> DomS b1 = true /\ DomT b2 = true)
          (R: forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> 
                        DomT b = true)
          (PG: meminj_preserves_globals ge1 j)
          (GenvsDomEQ: genvs_domain_eq ge1 ge2)
          (HS: forall b, DomS b = true -> Mem.valid_block m1 b)
          (HT: forall b, DomT b = true -> Mem.valid_block m2 b)
          mu (Hmu: mu = initial_SM DomS DomT
                         (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
                         (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j),
       (forall b, REACH m1 (fun b' => isGlobalBlock ge1 b' || getBlocks vals1 b') b = true -> 
                  DomS b = true) /\
       SM_wd mu /\ sm_valid mu m1 m2 /\ 
       meminj_preserves_globals ge1 (as_inj mu) /\
       (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true).
Proof. intros.
  destruct (core_initial_wd _ _ _ _ _ _ _ _ _ MInj 
             VInj HypJ R PG GenvsDomEQ HS HT _ Hmu)
    as [RDom [WDmu [SMVmu [PGext GF]]]].
  intuition.
  rewrite match_genv_meminj_preserves_extern_iff_all; assumption. 
Qed.

Lemma intern_incr_meminj_preserves_globals_frgn: 
      forall {F V} (ge: Genv.t F V) mu
             (PG: meminj_preserves_globals ge (foreign_of mu))
             mu' (Inc: intern_incr mu mu'),
      meminj_preserves_globals ge (foreign_of mu').
Proof. intros.
  rewrite (intern_incr_foreign _ _ Inc) in PG. trivial.
Qed.

Lemma intern_incr_meminj_preserves_globals_as_inj: 
      forall {F V} (ge: Genv.t F V) mu (WDmu: SM_wd mu)
             (PG: meminj_preserves_globals ge (as_inj mu) /\
                  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true))
             mu' (WDmu': SM_wd mu') (Inc: intern_incr mu mu'),
      meminj_preserves_globals ge (as_inj mu') /\
      (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu' b = true).
Proof. intros.
  rewrite match_genv_meminj_preserves_extern_iff_all in PG.
    destruct (intern_incr_meminj_preserves_globals _ _ PG _ Inc).
    rewrite match_genv_meminj_preserves_extern_iff_all; eauto.
  assumption. apply PG.
Qed.

Lemma replace_externs_meminj_preserves_globals_as_inj:
      forall {F V} (ge: Genv.t F V) nu (WDnu: SM_wd nu)
          (PG: meminj_preserves_globals ge (as_inj nu) /\
               (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc nu b = true))
          mu  fSrc fTgt (Hyp: mu = replace_externs nu fSrc fTgt)
          (WDmu: SM_wd mu)
          (FRG: forall b, frgnBlocksSrc nu b = true -> fSrc b = true),
      meminj_preserves_globals ge (as_inj mu) /\
      (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof. intros.
  rewrite match_genv_meminj_preserves_extern_iff_all in PG.
    destruct (replace_externs_meminj_preserves_globals _ _ PG _ _ _ Hyp FRG).
    rewrite match_genv_meminj_preserves_extern_iff_all; eauto.
  assumption. apply PG.
Qed.

Lemma after_external_meminj_preserves_globals_as_inj: 
      forall {F V} (ge: Genv.t F V) mu (WDmu : SM_wd mu)
             (PG: meminj_preserves_globals ge (as_inj mu) /\
                 (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true))
             nu pubSrc' pubTgt' vals1 m1
             (pubSrcHyp: pubSrc' = fun b => andb (locBlocksSrc mu b)
                                                (REACH m1 (exportedSrc mu vals1) b))

      
             (Hnu: nu = replace_locals mu pubSrc' pubTgt')
             nu' (WDnu' : SM_wd nu') (INC: extern_incr nu nu')  
             m2 (SMV: sm_valid mu m1 m2) (SEP: sm_inject_separated nu nu' m1 m2)
             frgnSrc' ret1 m1'
             (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (locBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

             frgnTgt' ret2 m2'
             (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (locBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

             mu' (WDmu': SM_wd mu') (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt'),
      meminj_preserves_globals ge (as_inj mu') /\
     (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu' b = true).
Proof. intros.
  rewrite match_genv_meminj_preserves_extern_iff_all in PG.
    destruct (after_external_meminj_preserves_globals
          _ _ WDmu PG _ _ _ _ _ pubSrcHyp Hnu _ WDnu' INC _ SMV 
         SEP _ _ _ frgnSrcHyp _ _ _ frgnTgtHyp _ Mu'Hyp).
    rewrite match_genv_meminj_preserves_extern_iff_all; eauto.
  assumption. apply PG.
Qed.

Lemma match_genv_meminj_preserves_globals_foreign_and_extern: 
      forall {F V} (ge: Genv.t F V) mu (WDmu : SM_wd mu)
             (PG: meminj_preserves_globals ge (as_inj mu) /\
                 (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)),
      meminj_preserves_globals ge (foreign_of mu) /\
      meminj_preserves_globals ge (extern_of mu).
Proof. intros.
  rewrite match_genv_meminj_preserves_extern_iff_all in PG; intuition.
  apply match_genv_meminj_preserves_globals_extern_implies_foreign; intuition.
Qed.

(***********************************************************************)

Goal forall mu (WD: SM_wd mu) m1 m2 m2' 
(U: Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'),
Mem.unchanged_on (fun b ofs => pubBlocksTgt mu b = true /\ 
                  loc_out_of_reach (pub_of mu) m1 b ofs) m2 m2'.
Proof.
intros.
eapply mem_unchanged_on_sub; try eassumption.
intros. destruct H.
unfold local_out_of_reach.
split. apply (pubBlocksLocalTgt _ WD _ H). 
intros.
remember (pubBlocksSrc mu b0) as d.
destruct d; try (right; reflexivity).
left.
eapply H0. unfold pub_of.
destruct mu; simpl in *. rewrite <- Heqd. assumption.
Qed. 

Goal forall mu (WD: SM_wd mu) m1 m2 m2'
(U: Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'),
Mem.unchanged_on (fun b ofs => locBlocksTgt mu b = true /\ 
                    pubBlocksTgt mu b = false) m2 m2'.
intros.
eapply mem_unchanged_on_sub; try eassumption.
intros. unfold local_out_of_reach. destruct H. 
split; trivial. intros.
remember (pubBlocksSrc mu b0) as d.
destruct d; try (right; reflexivity).
apply eq_sym in Heqd.
destruct (pubSrc _ WD _ Heqd) as [b2 [dd [PUB TGT]]].
apply pub_in_local in PUB. rewrite PUB in H1. inv H1.
rewrite TGT in H0. discriminate.
Qed.

Goal forall mu m1 m2 m2' (WD:SM_wd mu)
  (U1: Mem.unchanged_on (fun b ofs => locBlocksTgt mu b = true /\ 
                    pubBlocksTgt mu b = false) m2 m2')
  (U2: Mem.unchanged_on (fun b ofs => pubBlocksTgt mu b = true /\ 
                  loc_out_of_reach (pub_of mu) m1 b ofs) m2 m2'),
Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'.
intros.
destruct U1 as [P1 C1]. destruct U2 as [P2 C2].
split; intros.
  clear C1 C2.
  specialize (P1 b ofs k p). specialize (P2 b ofs k p).
  remember (locBlocksTgt mu b) as d.
  destruct d; apply eq_sym in Heqd; simpl in *.
    remember (pubBlocksTgt mu b) as q.
    destruct q; apply eq_sym in Heqq; simpl in *.
      clear P1.
      apply P2; trivial. split; trivial. 
      intros b0; intros.
      destruct H. destruct (H2 b0 delta).
        apply pub_in_local; trivial.
        assumption.
        unfold pub_of in H1. destruct mu. simpl in *.  rewrite H3 in H1.  discriminate.
    apply P1; trivial. split; trivial.
  clear P1.
  remember (pubBlocksTgt mu b) as q.
    destruct q; apply eq_sym in Heqq; simpl in *.
      assert (locBlocksTgt mu b = true). eapply (pubBlocksLocalTgt _ WD). eassumption.
      rewrite H1 in Heqd. discriminate.
  destruct H. rewrite H in Heqd. discriminate. 
destruct H.
  clear P1 P2.
  specialize (C1 b ofs). specialize (C2 b ofs).
  rewrite H in *.
  remember (pubBlocksTgt mu b) as d.
  destruct d; apply eq_sym in Heqd.
    clear C1. apply C2; trivial; clear C2.
    split; trivial. intros b1; intros.
     destruct (pub_locBlocks _ WD _ _ _ H2).
     apply pub_in_local in H2.
     destruct (H1 _ _ H2). assumption. rewrite H5 in *. inv H3.
  clear C2. apply C1; eauto.
Qed.

Lemma eff_atexternal_check: 
      forall {F1 V1 C1 F2 V2 C2:Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2)
         mu (WDmu: SM_wd mu)
         (GenvsDomEq: genvs_domain_eq ge1 ge2)
         m1 m2 (MemInjMu: Mem.inject (as_inj mu) m1 m2)
         vals1 vals2 (ValInjMu: Forall2 (val_inject (as_inj mu)) vals1 vals2)  
         (MatchGenv: meminj_preserves_globals ge1 (extern_of mu) /\
                        (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)), 
      (forall b, isGlobalBlock ge1 b = true -> REACH m1 (exportedSrc mu vals1) b = true) /\ 
      (forall b, isGlobalBlock ge2 b = true -> REACH m2 (exportedTgt mu vals2) b = true).
Proof. intros.
destruct MatchGenv as [PG GF].
assert (forall b,
       isGlobalBlock ge1 b = true -> REACH m1 (exportedSrc mu vals1) b = true).
  intros.
  apply REACH_nil. unfold exportedSrc.
  apply GF in H. rewrite (frgnSrc_shared _ WDmu _ H). intuition.
split; trivial. intros.
  rewrite <- (genvs_domain_eq_isGlobal _ _ GenvsDomEq) in *.
  specialize (H _ H0).
  destruct (REACH_as_inj_REACH _ WDmu _ _ _ _ MemInjMu ValInjMu _ H) as [b2 [d [A R]]].
  specialize (meminj_preserves_globals_isGlobalBlock _ _ PG _ H0). intros.
  rewrite (extern_in_all _ _ _ _ H1) in A. inv A.
  trivial.
Qed.

Lemma eff_after_check1: 
      forall mu (WD: SM_wd mu) m1 m2 (SMValMu: sm_valid mu m1 m2) 
          (*selected standard assumptions:*)
          (MemInjMu: Mem.inject (as_inj mu) m1 m2)
          vals1 vals2 (ValInjMu: Forall2 (val_inject (as_inj mu)) vals1 vals2) 

          pubSrc' (pubSrcHyp: pubSrc' = fun b => andb (locBlocksSrc mu b)
                                                    (REACH m1 (exportedSrc mu vals1) b))

          pubTgt' (pubTgtHyp: pubTgt' = fun b => andb (locBlocksTgt mu b)
                                                    (REACH m2 (exportedTgt mu vals2) b))

          nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),
       SM_wd nu /\ sm_valid nu m1 m2 /\
       Mem.inject (as_inj nu) m1 m2 /\
       Forall2 (val_inject (as_inj nu)) vals1 vals2.
Proof. intros. subst.
split. eapply replace_locals_wd; trivial.
      intros. apply andb_true_iff in H. destruct H as [locBSrc ReachSrc].
        destruct (REACH_local_REACH _ WD _ _ _ _  MemInjMu ValInjMu _ ReachSrc locBSrc)
            as [b2 [d [Loc ReachTgt]]]; clear ReachSrc.
        exists b2, d; split; trivial. 
        destruct (local_DomRng _ WD _ _ _ Loc). rewrite H0, ReachTgt. trivial.
      intros. apply andb_true_iff in H. apply H. 
split. 
  split; intros.
    rewrite replace_locals_DOM in H. 
    eapply SMValMu; apply H.
  rewrite replace_locals_RNG in H. 
    eapply SMValMu; apply H.
rewrite replace_locals_as_inj. split; assumption.
Qed.  

Lemma eff_after_check2: 
      forall nu' ret1 m1' m2' ret2
         (MemInjNu': Mem.inject (as_inj nu') m1' m2')
         (RValInjNu': val_inject (as_inj nu') ret1 ret2)

         frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                  (andb (negb (locBlocksSrc nu' b)) 
                                                        (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

         frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                  (andb (negb (locBlocksTgt nu' b))
                                                        (REACH m2' (exportedTgt nu' (ret2::nil)) b)))
   
         mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
         (WD: SM_wd nu') (SMValid: sm_valid nu' m1' m2'),

      SM_wd mu' /\ sm_valid mu' m1' m2'. 
Proof. intros. subst.
split.
eapply replace_externs_wd. assumption.
  intros. do 2 rewrite andb_true_iff in H.
          destruct H as [DomB1 [notMyB1 ReachB1]].
          assert (VALS: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
            constructor. assumption. constructor. 
          apply negb_true_iff in notMyB1.
          destruct (REACH_extern_REACH _ WD _ _ _ _ MemInjNu' VALS _ 
                    ReachB1 notMyB1) as [b2 [d [EXT ReachB2]]].
          exists b2, d; split; trivial.
          do 2 rewrite andb_true_iff. rewrite negb_true_iff.
          destruct (extern_DomRng _ WD _ _ _ EXT) as [? ?].
          unfold DomTgt. intuition.
          destruct (disjoint_extern_local_Tgt _ WD b2); congruence.
  intros. do 2 rewrite andb_true_iff in H. rewrite negb_true_iff in H.
          unfold DomTgt in H. destruct H as [? [? ?]].
          rewrite H0 in H; simpl in H. assumption.
split; intros.
  rewrite replace_externs_DOM in H. apply SMValid. apply H.
  rewrite replace_externs_RNG in H. apply SMValid. apply H.
Qed.
         
Lemma eff_after_check3: 
      forall nu' ret1 m1' m2' ret2
        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)


        frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (locBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

        frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (locBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt'),

     Mem.inject (as_inj mu') m1' m2' /\ val_inject (as_inj mu') ret1 ret2.
Proof. intros. subst. rewrite replace_externs_as_inj. split; assumption. Qed.  

Lemma eff_after_check4: 
      forall mu pubSrc' pubTgt'
             nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             nu' (INC: extern_incr nu nu')  
             mu' frgnSrc' frgnTgt'
            (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
            (SMwdNu': SM_wd nu'),
      inject_incr (as_inj mu) (as_inj mu').
Proof. intros. subst.
  rewrite replace_externs_as_inj.
  intros b; intros.
    eapply extern_incr_as_inj. apply INC. assumption.
    rewrite replace_locals_as_inj. apply H.
Qed.

Lemma eff_after_check5a: 
      forall mu pubSrc' pubTgt' nu
             (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             kappa m1 m2
            (SEP: sm_inject_separated nu kappa m1 m2),
      sm_inject_separated mu kappa m1 m2.
Proof. intros. subst.
destruct SEP as [SEPa [SEPb SEPc]].
rewrite replace_locals_as_inj, 
        replace_locals_DomSrc, 
        replace_locals_DomTgt in *.
split; intros; eauto.
Qed.

Lemma eff_after_check5b: 
      forall nu' mu' frgnSrc' frgnTgt'
             (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
             kappa m1 m2 (SEP: sm_inject_separated kappa nu' m1 m2),
      sm_inject_separated kappa mu' m1 m2.
Proof. intros. subst.
destruct SEP as [SEPa [SEPb SEPc]].
split; intros. 
  rewrite replace_externs_as_inj in H0.
  apply (SEPa _ _ _ H H0).
split; intros.
  rewrite replace_externs_DomSrc in *.
  apply (SEPb _ H H0).
rewrite replace_externs_DomTgt in *.
  apply (SEPc _ H H0).
Qed.

Lemma eff_after_check5: 
      forall mu pubSrc' pubTgt' nu
             (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             nu' mu' frgnSrc' frgnTgt'
             (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
             m1 m2 (SEP: sm_inject_separated nu nu' m1 m2),
      sm_inject_separated mu mu' m1 m2.
Proof. intros.
eapply eff_after_check5b; try eassumption.
eapply eff_after_check5a; try eassumption.
Qed.

Lemma eff_after_check5_explicitProof: 
      forall mu pubSrc' pubTgt' nu
             (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             nu' mu' frgnSrc' frgnTgt'
             (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
             m1 m2 (SEP: sm_inject_separated nu nu' m1 m2),
      sm_inject_separated mu mu' m1 m2.
Proof. intros. subst.
destruct SEP as [SEPa [SEPb SEPc]].
rewrite replace_locals_as_inj in *.
rewrite replace_locals_DomSrc, replace_locals_DomTgt in *.
split; intros. 
  rewrite replace_externs_as_inj in H0.
  apply (SEPa _ _ _ H H0).
split; intros.
  rewrite replace_externs_DomSrc in *.
  apply (SEPb _ H H0).
rewrite replace_externs_DomTgt in *.
  apply (SEPc _ H H0).
Qed.

    (*One might consider variants that require Mem.inject j ma m2 on smaller 
        injections j than as_inj mu, omething like this: 
    core_halted : forall cd mu c1 m1 c2 m2 v1,
      match_state cd mu c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->

      exists v2, 
             Mem.inject (locvisible_of mu) m1 m2 /\
             val_inject (locvisible_of mu) v1 v2;

     (-follows from halted_loc_check:-) 
      /\
      exists pubSrc' pubTgt' nu, 
        (pubSrc' = fun b => (locBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (locBlocksTgt mu b) &&
                            (REACH m2 (exportedTgt mu (v2::nil)) b))
        /\
        (nu = replace_locals mu pubSrc' pubTgt')
         /\
        val_inject (shared_of nu) v1 v2 /\
        halted Sem2 c2 = Some v2 /\
        Mem.inject (shared_of nu) m1 m2; (*/\ val_valid v2 m2*)
     But this would mean to carry the invariant Mem.inject (locvisible_of mu) m1 m2
         around, ie through corediagram, afterexternal etc (ie require match_state 
         to imply Mem.inject loc_visible ... 
       This maybe possible, but is maybe not required.
    *)
 
Lemma halted_check_aux: forall mu m1 v1 b1 b2 delta (WD: SM_wd mu),
      join (foreign_of mu)
           (fun b =>
              if locBlocksSrc mu b && REACH m1 (exportedSrc mu (v1 :: nil)) b
              then local_of mu b
              else None) b1 = Some (b2, delta) ->
      as_inj mu b1= Some (b2, delta).
Proof. intros; apply joinI.
  destruct (joinD_Some _ _ _ _ _ H) as [FRG | [FRG LOC]]; clear H.
    left. apply foreign_in_extern; eassumption.
    right. 
    remember (locBlocksSrc mu b1 && REACH m1 (exportedSrc mu (v1 :: nil)) b1) as d.
    destruct d; inv LOC; apply eq_sym in Heqd. rewrite H0.
    destruct (disjoint_extern_local _ WD b1). rewrite H. split; trivial.
    rewrite H in H0; discriminate.
Qed.

Goal (*Lemma halted_check:*) forall mu m1 m2 v1 v2
      (MInj: Mem.inject (as_inj mu) m1 m2)
      (VInj: val_inject (locvisible_of mu) v1 v2) (WD: SM_wd mu),
      exists pubSrc' pubTgt' nu, 
        (pubSrc' = fun b => (locBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (locBlocksTgt mu b) &&
                            (REACH m2 (exportedTgt mu (v2::nil)) b))
        /\
        (nu = replace_locals mu pubSrc' pubTgt')
         /\ SM_wd nu /\
        val_inject (shared_of nu) v1 v2 /\
        Mem.inject (shared_of nu) m1 m2. (*/\ val_valid v2 m2*)
Proof. intros. eexists; eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. 
      apply replace_locals_wd; trivial.
      intros. rewrite andb_true_iff in H. destruct H. 
      assert (VALS12: Forall2 (val_inject (as_inj mu)) (v1 :: nil) (v2 :: nil)).
        constructor. eapply val_inject_incr; try eassumption.
                      unfold locvisible_of, join; simpl.
                      intros b; intros. remember (foreign_of mu b). 
                      destruct o; apply eq_sym in Heqo.
                         destruct p. inv H1. apply foreign_in_all; eassumption.
                      apply local_in_all; eassumption.
        constructor.
      destruct (REACH_local_REACH _ WD _ _ (v1::nil) (v2::nil) MInj VALS12 _ H0 H)
        as [b2 [d1 [LOC12 R2]]].
      exists b2, d1. rewrite LOC12, R2.
      destruct (local_locBlocks _ WD _ _ _ LOC12) as [_ [? _]].
      rewrite H1. intuition.
      intros. apply andb_true_iff in H. intuition.
  rewrite replace_locals_shared. 
  split. inv VInj; try constructor.
         econstructor.
         unfold locvisible_of in H.
         apply joinI.
         destruct (joinD_Some _ _ _ _ _ H); clear H.
            left; eassumption.
         destruct H0. right. split; trivial.
         remember (locBlocksSrc mu b1 && REACH m1 (exportedSrc mu (Vptr b1 ofs1 :: nil)) b1) as d. 
              destruct d; apply eq_sym in Heqd. assumption.
         apply andb_false_iff in Heqd. 
              destruct (local_locBlocks _ WD _ _ _ H0) as [? [? [? [? ?]]]].
              rewrite H1 in *.
              destruct Heqd; try discriminate.
              assert (REACH m1 (exportedSrc mu (Vptr b1 ofs1 :: nil)) b1 = true).
                apply REACHAX. exists nil. constructor.
                unfold exportedSrc, sharedSrc, getBlocks. simpl.
                 destruct (eq_block b1 b1). simpl. trivial.
                 exfalso. apply n; trivial.
              rewrite H7 in H6. inv H6.
           reflexivity.
    split.
         (*goal Mem.mem_inj*) 
           split; intros. 
           (*subgoal mi_perm*)
             apply halted_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_align*)
             apply halted_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_memval*)
             assert (X:= halted_check_aux _ _ _ _ _ _ WD H); trivial.
             assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MInj) _ _ _ _ X H0). clear X.
             inv MV; try econstructor; try reflexivity.
                   apply joinI.
                   remember (foreign_of mu b0) as f.
                   destruct f; apply eq_sym in Heqf.
                      destruct p. rewrite (foreign_in_all _ _ _ _ Heqf) in H3. left; trivial.
                   right. split; trivial.
                  admit. (*ok -- it's in a GOAL; 
                      claim need not hold -- b0 might only be mapped by unknown_of mu*) 
 admit. admit. admit. admit. (*all 4 admits are OK - it's a GOAL*)
(*THIS Need not hold - if we want to enforce that there are no
pointers to unknown, we can probably do so by adding
 the match_inject_clause: 
    match_validblocks: forall d j c1 m1 c2 m2, 
          match_state d j c1 m1 c2 m2 ->
          mem_inject (as_inj mu) m1 m2 /\
          mem_inject (locvisible mu) m1 m2,
   or add an invariant reach_closed 

and /or tweaking match_norm. cf the Lemma halted_loc_check below.
*)
Qed.

Lemma halted_loc_check_aux: forall mu m1 v1 b1 b2 delta (WD: SM_wd mu),
      join (foreign_of mu)
           (fun b =>
              if locBlocksSrc mu b && REACH m1 (exportedSrc mu (v1 :: nil)) b
              then local_of mu b
              else None) b1 = Some (b2, delta) ->
      locvisible_of mu b1= Some (b2, delta).
Proof. intros; apply joinI.
  destruct (joinD_Some _ _ _ _ _ H) as [FRG | [FRG LOC]]; 
     rewrite FRG; clear H.
    left; trivial.
    right; split; trivial. 
    remember (locBlocksSrc mu b1 && REACH m1 (exportedSrc mu (v1 :: nil)) b1) as d.
    destruct d; inv LOC; apply eq_sym in Heqd. trivial.
Qed.

Lemma halted_loc_check: forall mu m1 m2 v1 v2
      (MInj: Mem.inject (locvisible_of mu)  m1 m2)
      (VInj: val_inject (locvisible_of mu) v1 v2) (WD: SM_wd mu),
      exists pubSrc' pubTgt' nu, 
        (pubSrc' = fun b => (locBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (locBlocksTgt mu b) &&
                            (REACH m2 (exportedTgt mu (v2::nil)) b))
        /\
        (nu = replace_locals mu pubSrc' pubTgt')
         /\ SM_wd nu /\
        val_inject (shared_of nu) v1 v2 /\
        Mem.inject (shared_of nu) m1 m2. (*/\ val_valid v2 m2*)
Proof. intros. eexists; eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. 
      apply replace_locals_wd; trivial.
      intros. rewrite andb_true_iff in H. destruct H.
      assert (X: forall b, exportedSrc mu (v1 :: nil) b = true ->
                 exists jb d, locvisible_of mu b = Some (jb, d) /\ 
                              exportedTgt mu (v2 :: nil) jb = true).
          intros. unfold exportedSrc in H1. unfold exportedTgt. 
          apply orb_true_iff in H1. 
          destruct H1. unfold getBlocks in H1; simpl in H1. destruct v1; inv H1. 
               destruct (eq_block b0 b); inv H3. 
               inv VInj.  exists b2, delta. split; trivial. 
                    simpl. apply orb_true_iff. left. unfold getBlocks; simpl.
                  destruct (eq_block b2 b2); trivial. exfalso. apply n; trivial.
               rewrite locvisible_sharedprivate.
                unfold join.
                destruct (shared_SrcTgt _ WD _ H1) as [b2 [d1 [SH TGT]]].
                rewrite SH. exists b2, d1; split; trivial.
                rewrite TGT. destruct (getBlocks (v2 :: nil) b2); trivial.
 
      destruct (REACH_inject _ _ _ MInj _ (exportedTgt mu (v2 :: nil)) X _ H0)
           as [b2 [d1 [lv exp]]].
        clear X. destruct (joinD_Some _ _ _ _ _ lv).
            destruct (foreign_DomRng _ WD _ _ _ H1) as [? [? [? ?]]].
            rewrite H in H4. inv H4.
         destruct H1. rewrite H2. exists b2, d1. rewrite exp.
            destruct (local_locBlocks _ WD _ _ _ H2) as [? [? [? [? ?]]]].
             rewrite H4. intuition.
     intros. apply andb_true_iff in H. destruct H; trivial.
   split. rewrite replace_locals_shared.
          inv VInj; try econstructor; trivial.
          apply joinI. 
          destruct (joinD_Some _ _ _ _ _ H); clear H.
             left; trivial.
          destruct H0 as [FRG LOC]. rewrite FRG, LOC.
          right; split; trivial.
          destruct (local_locBlocks _ WD _ _ _ LOC) as [? [? [? [? [? ?]]]]].
          rewrite H. simpl.
          assert (R: REACH m1 (exportedSrc mu (Vptr b1 ofs1:: nil)) b1 = true).
            apply REACHAX. exists nil.
            constructor. unfold exportedSrc, getBlocks; simpl.
            apply orb_true_iff; left.
            destruct (eq_block b1 b1); trivial. exfalso. apply n; trivial.              
          rewrite R. trivial.
    split. rewrite replace_locals_shared.
         (*goal Mem.mem_inj*) 
           split; intros. 
           (*subgoal mi_perm*) apply halted_loc_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_align*) apply halted_loc_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_memval*)
             assert (X:= halted_loc_check_aux _ _ _ _ _ _ WD H); trivial.
             assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MInj) _ _ _ _ X H0). clear X.
             inv MV; try econstructor; try reflexivity.
                   apply joinI.
                   destruct (joinD_Some _ _ _ _ _ H3) as [FRG | [FRG LOC]]; clear H3; rewrite FRG.
                     left; reflexivity.
                     right; split; trivial.
                      destruct (local_locBlocks _ WD _ _ _ LOC) as [? [? [? [? [? ?]]]]]. 
                      rewrite H3, LOC. simpl.
                      destruct (joinD_Some _ _ _ _ _ H) as [FRG1 | [FRG1 LOC1]]; clear H.
                        assert (REACH m1 (exportedSrc mu (v1 :: nil)) b0 = true).
                        apply REACHAX. exists ((b1,ofs)::nil).
                          apply eq_sym in H1.
                          econstructor. constructor.
                            unfold exportedSrc. apply orb_true_iff; right.  
                            apply sharedSrc_iff. unfold shared_of, join; simpl. rewrite FRG1. exists b2, delta; trivial.
                            assumption. apply H1. rewrite H. trivial. 
                      remember (locBlocksSrc mu b1 && REACH m1 (exportedSrc mu (v1 :: nil)) b1) as d.
                        destruct d; apply eq_sym in Heqd; inv LOC1.
                          apply andb_true_iff in Heqd. destruct Heqd.
                          assert (REACH m1 (exportedSrc mu (v1 :: nil)) b0 = true).
                          apply REACHAX. apply REACHAX in H10. destruct H10 as [L RL].
                          eexists. eapply reach_cons. apply RL. 
                          eassumption. rewrite <- H1. reflexivity.
                          rewrite H11. trivial.
    intros. rewrite replace_locals_shared.
            assert (LV:= Mem.mi_freeblocks _ _ _ MInj _ H).
            apply joinD_None in LV. destruct LV as [FRG LOC].
            apply joinI_None. trivial.
            rewrite LOC.
            destruct (locBlocksSrc mu b && REACH m1 (exportedSrc mu (v1 :: nil)) b); trivial.
    intros. rewrite replace_locals_shared in H.
            eapply (Mem.mi_mappedblocks _ _ _ MInj b b' delta).
            apply halted_loc_check_aux in H; trivial.
    rewrite replace_locals_shared. intros b1; intros. 
            apply halted_loc_check_aux in H0; trivial.
            apply halted_loc_check_aux in H1; trivial.
            eapply MInj; eassumption.
    rewrite replace_locals_shared; intros.
            apply halted_loc_check_aux in H; trivial.
            eapply MInj; eassumption. 
Qed.

  
Lemma get_freelist:
  forall fbl m m' (FL: Mem.free_list m fbl = Some m') b
  (H: forall b' lo hi, In (b', lo, hi) fbl -> b' <> b) z,
  ZMap.get z (Mem.mem_contents m') !! b = 
  ZMap.get z (Mem.mem_contents m) !! b.
Proof. intros fbl.
  induction fbl; simpl; intros; inv FL; trivial.
  destruct a. destruct p.
  remember (Mem.free m b0 z1 z0) as d.
  destruct d; inv H1. apply eq_sym in Heqd.
  rewrite (IHfbl _ _ H2 b).
     clear IHfbl H2.
     case_eq (eq_block b0 b); intros.
      exfalso. eapply (H b0). left. reflexivity. assumption.
     apply Mem.free_result in Heqd. subst. reflexivity.
  eauto.
Qed.

Lemma intern_incr_vis_inv: forall mu nu (WDmu: SM_wd mu) (WDnu: SM_wd nu)
      (INC: intern_incr mu nu) 
       b1 b2 d (AI: as_inj mu b1 = Some(b2,d))
      (VIS: vis nu b1 = true), vis mu b1 = true.
Proof. unfold vis; simpl. intros.
  destruct INC as [L [E [LS [_ [_ [_ [F _]]]]]]].
  rewrite F in *.
  apply orb_true_iff in VIS. destruct VIS; intuition.
  destruct (joinD_Some _ _ _ _ _ AI) as [EXT | [_ LOC]]; clear AI.
    rewrite E in EXT.
    destruct (extern_DomRng _ WDnu _ _ _ EXT) as [? ?].
    rewrite (extBlocksSrc_locBlocksSrc _ WDnu _ H0) in H. discriminate.
  destruct (local_DomRng _ WDmu _ _ _ LOC).
    intuition. 
Qed.

Lemma intern_incr_vis: forall mu nu (INC: intern_incr mu nu) 
       b (VIS: vis mu b = true), vis nu b = true.
Proof. unfold vis; simpl. intros.
  destruct INC as [_ [_ [L [_ [_ [_ [F _]]]]]]].
    apply orb_true_iff in VIS. destruct VIS.
    apply L in H. intuition.
    rewrite F in H. intuition.
Qed.

Lemma restrict_sm_intern_incr: forall mu1 mu2 (WD2 : SM_wd mu2)
          (INC : intern_incr mu1 mu2),
      intern_incr (restrict_sm mu1 (vis mu1))
                  (restrict_sm mu2 (vis mu2)).
Proof.
     red; intros. destruct INC. 
     destruct mu1; destruct mu2; simpl in *.
        unfold restrict_sm, vis in *; simpl in *. intuition.
     red; intros. 
       destruct (restrictD_Some _ _ _ _ _ H8) as [f M]; clear H8.
       eapply restrictI_Some. eapply H; eassumption.
       apply orb_true_iff in M.
       destruct M as [M | M]. apply H0 in M. intuition.
       rewrite H5 in M. rewrite M. intuition.
     rewrite <- H1 in *.
       extensionality b.
       remember (restrict extern_of (fun b0 : block => locBlocksSrc b0 || frgnBlocksSrc b0) b) as d.
       destruct d; apply eq_sym in Heqd.
         destruct p. destruct (restrictD_Some _ _ _ _ _ Heqd) as [f M]; clear Heqd.
         apply eq_sym. eapply restrictI_Some; try eassumption.
         apply orb_true_iff in M.
         destruct M as [M | M]. apply H0 in M. intuition.
         rewrite H5 in M. rewrite M. intuition.
       apply eq_sym. apply restrictI_None.
         apply restrictD_None' in Heqd. destruct Heqd.
         left; trivial.
         destruct H8 as [b2 [dd [EXT M]]].
         apply orb_false_iff in M. destruct M.
         destruct (extern_DomRng _ WD2 _ _ _ EXT). simpl in *.
           apply (extBlocksSrc_locBlocksSrc _ WD2) in H11. simpl in H11.
           rewrite H5 in H10. rewrite H10, H11. right; reflexivity.
Qed.
Lemma intern_incr_restrict: forall mu1 mu2 (WD2 : SM_wd mu2)
          (INC : intern_incr mu1 mu2),
      inject_incr (restrict (as_inj mu1) (vis mu1))
                  (restrict (as_inj mu2) (vis mu2)).
Proof.
     red; intros. destruct (restrictD_Some _ _ _ _ _ H).
     apply (intern_incr_as_inj _ _ INC) in H0; trivial.
     eapply restrictI_Some; try eassumption.
     eapply intern_incr_vis; eassumption.
Qed.

Lemma vis_restrict_sm: forall mu X, 
      vis (restrict_sm mu X) = vis mu.
Proof. intros. unfold vis. destruct mu; trivial. Qed.

Lemma REACH_split: forall m X Y b
      (RCH:REACH m (fun b' => X b' || Y b') b = true),
      REACH m X b = true \/ REACH m Y b = true.
Proof. intros.
  rewrite REACHAX in RCH.
  destruct RCH as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
    apply orb_true_iff in H. 
    destruct H.
       left. apply REACH_nil. trivial. 
       right. apply REACH_nil. trivial.
  destruct (IHL _ H1); clear IHL H1.
    left. eapply REACH_cons; try eassumption.
    right. eapply REACH_cons; try eassumption.
Qed.

Lemma REACH_Store: forall m chunk b i v m'
     (ST: Mem.store chunk m b (Int.unsigned i) v = Some m')
     Roots (VISb: Roots b = true)
     (VISv : forall b', getBlocks (v :: nil) b' = true -> 
             Roots b' = true)
     (R: REACH_closed m Roots),
     REACH_closed m' Roots.
Proof. intros.
intros bb Hbb.
assert (REQ: Roots = (fun b' : Values.block =>
       eq_block b' b || (if eq_block b' b then false else Roots b'))).
  extensionality b'.
  remember (eq_block b' b).
  destruct s; simpl; trivial. subst; trivial.
rewrite REQ in Hbb; clear REQ.
apply REACH_split in Hbb.
destruct Hbb.
(*bb is reachable in m' from b*)
   admit.
(*bb is reachable in m' from Roots - b*)
  admit.
Qed.

Lemma REACH_load_vis: forall chunk m b i b1 ofs1
        (LD: Mem.load chunk m b (Int.unsigned i) = Some (Vptr b1 ofs1))
        mu b2 delta (AI: as_inj mu b = Some (b2, delta))
        (VIS: vis mu b = true),
      REACH m (vis mu) b1 = true.
Proof. 
  intros.
  eapply REACH_cons with(z:=Int.unsigned i)(off:=ofs1). 
    apply REACH_nil. apply VIS.
    eapply Mem.load_valid_access. apply LD. 
    split. omega. destruct chunk; simpl; omega.
    apply Mem.load_result in LD. 
    apply eq_sym in LD. 
    destruct (decode_val_pointer_inv _ _ _ _ LD); clear LD; subst.
    simpl in *.
    inv H0. eassumption. 
Qed.