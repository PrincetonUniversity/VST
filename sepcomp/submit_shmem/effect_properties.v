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

Goal forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true ->
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (*(SrcHyp: forall b ofs, Esrc b ofs = true -> vis mu b = true)*)
            nu (WDnu: SM_wd nu)
         (X1: forall b, locBlocksTgt nu b = true -> locBlocksTgt mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) ->
                              locBlocksSrc nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
   Mem.unchanged_on (fun b2 z => locBlocksTgt nu b2 = true /\
                      forall b1 d, (as_inj nu) b1 = Some (b2,d) ->
                                 loc_out_of_bounds m1 b1 (z-d)) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  unfold loc_out_of_bounds; simpl; intros. rename b into b2.
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
    apply pub_in_all in X2; trivial.
  assumption.
Qed.



Lemma FreeEffect_validblock: forall m lo hi sp b ofs
        (EFF: FreeEffect m lo hi sp b ofs = true),
      Mem.valid_block m b.
Proof. intros.
  unfold FreeEffect in EFF.
  destruct (valid_block_dec m b); trivial; inv EFF.
Qed.

Lemma FreelistEffect_validblock: forall l m b ofs
        (EFF: FreelistEffect m l b ofs = true),
      Mem.valid_block m b.
Proof. intros l.
  induction l; unfold FreelistEffect; simpl; intros.
     unfold EmptyEffect in EFF. inv EFF.
  destruct a as [[bb lo] hi].
  apply orb_true_iff in EFF.
  destruct EFF.
  apply IHl in H. assumption.
  eapply FreeEffect_validblock; eassumption.
Qed.

Lemma StoreEffectD: forall vaddr v b ofs
      (STE: StoreEffect vaddr v b ofs = true),
      exists i, vaddr = Vptr b i /\
        (Int.unsigned i) <= ofs < (Int.unsigned i + Z.of_nat (length v)).
Proof. intros.
  unfold StoreEffect in STE. destruct vaddr; inv STE.
  destruct (eq_block b0 b); inv H0.
  exists i.
  destruct (zle (Int.unsigned i) ofs); inv H1.
  destruct (zlt ofs (Int.unsigned i + Z.of_nat (length v))); inv H0.
  intuition.
Qed.

Lemma StoreEffect_PropagateLeft: forall chunk m vaddr v m'
          (ST: Mem.storev chunk m vaddr v = Some m')
          mu m2 (WD: SM_wd mu) (INJ : Mem.inject (as_inj mu) m m2)
          vaddr'
          (VINJ : val_inject (restrict (as_inj mu) (vis mu)) vaddr vaddr')
          v' m2' (ST2: Mem.storev chunk m2 vaddr' v' = Some m2')
          b2 ofs
          (EFF : StoreEffect vaddr' (encode_val chunk v') b2 ofs = true)
          (LBT2: locBlocksTgt mu b2 = false),
      exists b1 delta, foreign_of mu b1 = Some (b2, delta) /\
          StoreEffect vaddr (encode_val chunk v) b1 (ofs - delta) = true /\
          Mem.perm m b1 (ofs - delta) Max Nonempty.
Proof. intros.
      apply StoreEffectD in EFF. destruct EFF as [i [VADDR' Hoff]]. subst.
        simpl in ST2. inv VINJ. Focus 2. inv ST.
      destruct (restrictD_Some _ _ _ _ _ H2); clear H2.
      exists b1, delta.
      split. destruct (joinD_Some _ _ _ _ _ H) as [EXT | [EXT LOC]]; clear H.
             unfold vis in H0.
             destruct (extern_DomRng' _ WD _ _ _ EXT) as [_ [_ [? _]]].
             rewrite H in H0. simpl in H0.
             destruct (frgnSrc _ WD _ H0) as [bb [dd [FF FT]]].
             rewrite (foreign_in_extern _ _ _ _ FF) in EXT. inv EXT.
             trivial.
          destruct (local_DomRng _ WD _ _ _ LOC).
            congruence.
      rewrite encode_val_length in Hoff. rewrite <- size_chunk_conv in Hoff.
      assert (Arith: Int.unsigned ofs1 <= ofs - delta < Int.unsigned ofs1 + size_chunk chunk).
         assert (DD: delta >= 0 /\ 0 <= Int.unsigned ofs1 + delta <= Int.max_unsigned).
                 eapply INJ. apply H. left.
                 apply Mem.store_valid_access_3 in ST.
                 eapply Mem.perm_implies. eapply Mem.valid_access_perm. eassumption. constructor.
         destruct DD as [DD1 DD2].
         specialize (Int.unsigned_range ofs1); intros I.
         assert (URdelta: Int.unsigned (Int.repr delta) = delta).
            apply Int.unsigned_repr. split. omega. omega.

         rewrite Int.add_unsigned in Hoff. rewrite URdelta in Hoff.
         rewrite (Int.unsigned_repr _ DD2) in Hoff. omega.

      split. unfold StoreEffect.
        destruct (eq_block b1 b1); try congruence. simpl; clear e.
        destruct Arith. rewrite encode_val_length . rewrite <- size_chunk_conv.
        destruct (zle (Int.unsigned ofs1) (ofs - delta)); try omega.
          destruct (zlt (ofs - delta) (Int.unsigned ofs1 + size_chunk chunk)); try omega. trivial.
      apply Mem.store_valid_access_3 in ST.
            eapply Mem.perm_implies.
            eapply Mem.perm_max. eapply ST. eassumption. constructor.
Qed.

Lemma free_free_inject : forall f m1 m1' m2 b1 lo hi b2 d m2'
       (INJ: Mem.inject f m1 m2)
       (FREE1: Mem.free m1 b1 lo hi = Some m1')
       (FREE2: Mem.free m2 b2 (lo+d) (hi+d) = Some m2')
       (B: f b1 = Some(b2,d)),
      Mem.inject f m1' m2'.
Proof. intros.
       eapply Mem.free_inject with (l:=(b1,lo,hi)::nil); try eassumption.
       simpl. rewrite FREE1. trivial.
       intros.
          destruct (eq_block b0 b1); subst. rewrite H in B. inv B.
            exists lo, hi. intuition.
          assert (P1: Mem.perm m1 b0 ofs Max Nonempty).
            eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. apply perm_any_N.
          assert (PM: Mem.perm m1 b1 (ofs - d + delta) Max Nonempty).
            eapply Mem.perm_implies. eapply Mem.perm_max.
              eapply (Mem.free_range_perm _ _ _ _ _ FREE1). omega.
              constructor.
          exfalso.
          destruct (Mem.mi_no_overlap _ _ _ INJ b0 _ _ _ _ _ _ _ n
               H B P1 PM) as [X | X]; apply X; trivial. omega.
Qed.

Lemma free_free_inject_same_block : forall f m1 m1' m2 b lo hi m2'
       (INJ: Mem.inject f m1 m2)
       (FREE1: Mem.free m1 b lo hi = Some m1')
       (FREE2: Mem.free m2 b lo hi = Some m2')
       (B: f b = Some(b,0)),
      Mem.inject f m1' m2'.
Proof. intros. eapply free_free_inject; try eassumption.
   repeat rewrite Zplus_0_r. trivial.
Qed.

Inductive match_freelists (j:meminj): list (block * Z * Z) -> list (block * Z * Z) -> Prop :=
  match_freelists_nil: match_freelists j nil nil
| match_freelists_cons: forall b1 lo1 hi1 t1 b2 lo2 hi2 t2 delta,
        j b1 = Some (b2,delta) ->
        lo2 = lo1+delta -> hi2 = hi1+delta ->
        match_freelists j t1 t2 ->
        match_freelists j ((b1,lo1,hi1)::t1) ((b2,lo2,hi2)::t2).

Lemma freelist_freelist_inject : forall f l1 l2
       (F: match_freelists f l1 l2)  m1 m1' m2 m2'
       (INJ: Mem.inject f m1 m2)
       (FREE1: Mem.free_list m1 l1 = Some m1')
       (FREE2: Mem.free_list m2 l2 = Some m2'),
      Mem.inject f m1' m2'.
Proof. intros f l1 l2 F.
  induction F; simpl; intros.
    inv FREE1; inv FREE2. assumption.
  remember (Mem.free m1 b1 lo1 hi1) as F1.
  destruct F1; inv FREE1; apply eq_sym in HeqF1.
  remember (Mem.free m2 b2 (lo1 + delta) (hi1 + delta)) as F2.
  destruct F2; inv FREE2; apply eq_sym in HeqF2.
  assert (Mem.inject f m m0).
    eapply free_free_inject; eassumption.
  eapply (IHF _ _ _ _ H0); try eassumption.
Qed.

Lemma FreeEffect_PropagateLeft: forall
   m sp lo hi m'
   (FREE : Mem.free m sp lo hi = Some m')
   mu m2 (SMV : sm_valid mu m m2)
   (WD: SM_wd mu) spb'
   (AI: as_inj mu sp = Some (spb', 0))
   (VIS : vis mu sp = true) b2 ofs
   (EFF : FreeEffect m2 lo hi spb' b2 ofs = true)
   (LB: locBlocksTgt mu b2 = false),
  exists b1 delta,
    foreign_of mu b1 = Some (b2, delta) /\
    FreeEffect m lo hi sp b1 (ofs - delta) = true /\
    Mem.perm m b1 (ofs - delta) Max Nonempty.
Proof. intros.
      unfold FreeEffect in EFF.
        destruct (valid_block_dec m2 b2); inv EFF.
        destruct (eq_block b2 spb'); simpl in *; inv H0.
        exists sp, 0. rewrite Zminus_0_r.
        split. unfold vis in VIS.
               destruct (joinD_Some _ _ _ _ _ AI) as [EXT | [NEXT LOC]]; clear H1.
                 assert (LSP: locBlocksSrc mu sp = false). eapply (extern_DomRng' _ WD _ _ _ EXT).
                 rewrite LSP in *. simpl in VIS.
                 destruct (frgnSrc _ WD _ VIS) as [bb2 [dd [F1 F2]]].
                   rewrite (foreign_in_extern _ _ _ _ F1) in EXT. inv EXT. apply F1.
               destruct (local_DomRng _ WD _ _ _ LOC); congruence.
        split. unfold FreeEffect.
               destruct (valid_block_dec m sp).
                 destruct (eq_block sp sp); trivial. elim n; trivial.
               elim n; clear n. apply SMV. eapply as_inj_DomRng; eassumption.
        eapply Mem.perm_implies. eapply Mem.perm_max.
           eapply (Mem.free_range_perm _ _ _ _ _ FREE).
              destruct (zle lo ofs); simpl in H1; try discriminate.
              destruct (zlt ofs hi); try discriminate. split; trivial.
             constructor.
Qed.

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
      meminj_preserves_globals ge (as_inj mu) <->
      meminj_preserves_globals ge (extern_of mu).
Proof. intros.
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

(* Goal (*Lemma halted_check:*) forall mu m1 m2 v1 v2 *)
(*       (MInj: Mem.inject (as_inj mu) m1 m2) *)
(*       (VInj: val_inject (locvisible_of mu) v1 v2) (WD: SM_wd mu), *)
(*       exists pubSrc' pubTgt' nu,  *)
(*         (pubSrc' = fun b => (locBlocksSrc mu b) && *)
(*                             (REACH m1 (exportedSrc mu (v1::nil)) b)) *)
(*         /\ *)
(*         (pubTgt' = fun b => (locBlocksTgt mu b) && *)
(*                             (REACH m2 (exportedTgt mu (v2::nil)) b)) *)
(*         /\ *)
(*         (nu = replace_locals mu pubSrc' pubTgt') *)
(*          /\ SM_wd nu /\ *)
(*         val_inject (shared_of nu) v1 v2 /\ *)
(*         Mem.inject (shared_of nu) m1 m2. (*/\ val_valid v2 m2*) *)
(* Proof. intros. eexists; eexists; eexists. *)
(*   split. reflexivity. *)
(*   split. reflexivity. *)
(*   split. reflexivity. *)
(*   split.  *)
(*       apply replace_locals_wd; trivial. *)
(*       intros. rewrite andb_true_iff in H. destruct H.  *)
(*       assert (VALS12: Forall2 (val_inject (as_inj mu)) (v1 :: nil) (v2 :: nil)). *)
(*         constructor. eapply val_inject_incr; try eassumption. *)
(*                       unfold locvisible_of, join; simpl. *)
(*                       intros b; intros. remember (foreign_of mu b).  *)
(*                       destruct o; apply eq_sym in Heqo. *)
(*                          destruct p. inv H1. apply foreign_in_all; eassumption. *)
(*                       apply local_in_all; eassumption. *)
(*         constructor. *)
(*       destruct (REACH_local_REACH _ WD _ _ (v1::nil) (v2::nil) MInj VALS12 _ H0 H) *)
(*         as [b2 [d1 [LOC12 R2]]]. *)
(*       exists b2, d1. rewrite LOC12, R2. *)
(*       destruct (local_locBlocks _ WD _ _ _ LOC12) as [_ [? _]]. *)
(*       rewrite H1. intuition. *)
(*       intros. apply andb_true_iff in H. intuition. *)
(*   rewrite replace_locals_shared.  *)
(*   split. inv VInj; try constructor. *)
(*          econstructor. *)
(*          unfold locvisible_of in H. *)
(*          apply joinI. *)
(*          destruct (joinD_Some _ _ _ _ _ H); clear H. *)
(*             left; eassumption. *)
(*          destruct H0. right. split; trivial. *)
(*          remember (locBlocksSrc mu b1 && REACH m1 (exportedSrc mu (Vptr b1 ofs1 :: nil)) b1) as d.  *)
(*               destruct d; apply eq_sym in Heqd. assumption. *)
(*          apply andb_false_iff in Heqd.  *)
(*               destruct (local_locBlocks _ WD _ _ _ H0) as [? [? [? [? ?]]]]. *)
(*               rewrite H1 in *. *)
(*               destruct Heqd; try discriminate. *)
(*               assert (REACH m1 (exportedSrc mu (Vptr b1 ofs1 :: nil)) b1 = true). *)
(*                 apply REACHAX. exists nil. constructor. *)
(*                 unfold exportedSrc, sharedSrc, getBlocks. simpl. *)
(*                  destruct (eq_block b1 b1). simpl. trivial. *)
(*                  exfalso. apply n; trivial. *)
(*               rewrite H7 in H6. inv H6. *)
(*            reflexivity. *)
(*     split. *)
(*          (*goal Mem.mem_inj*)  *)
(*            split; intros.  *)
(*            (*subgoal mi_perm*) *)
(*              apply halted_check_aux in H; trivial.  *)
(*              eapply MInj; try eassumption. *)
(*            (*subgoal mi_align*) *)
(*              apply halted_check_aux in H; trivial.  *)
(*              eapply MInj; try eassumption. *)
(*            (*subgoal mi_memval*) *)
(*              assert (X:= halted_check_aux _ _ _ _ _ _ WD H); trivial. *)
(*              assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MInj) _ _ _ _ X H0). clear X. *)
(*              inv MV; try econstructor; try reflexivity. *)
(*                    apply joinI. *)
(*                    remember (foreign_of mu b0) as f. *)
(*                    destruct f; apply eq_sym in Heqf. *)
(*                       destruct p. rewrite (foreign_in_all _ _ _ _ Heqf) in H3. left; trivial. *)
(*                    right. split; trivial. *)
(* (*THIS Need not hold - if we want to enforce that there are no *)
(* pointers to unknown, we can probably do so by adding *)
(*  the match_inject_clause:  *)
(*     match_validblocks: forall d j c1 m1 c2 m2,  *)
(*           match_state d j c1 m1 c2 m2 -> *)
(*           mem_inject (as_inj mu) m1 m2 /\ *)
(*           mem_inject (locvisible mu) m1 m2, *)
(*    or add an invariant reach_closed  *)

(* and /or tweaking match_norm. cf the Lemma halted_loc_check below. *)
(* *) *)
(* Qed. *)

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

Lemma reachD: forall m R L b (RCH :reach m (fun u => R u = true) L b),
      exists r, R r = true /\ reach m (fun bb => bb=r) L b.
Proof. intros m R L.
  induction L; simpl; intros; inv RCH.
    exists b. split; trivial. constructor. trivial.
  destruct (IHL _ H1) as [r [Rr RCH]]; clear IHL H1.
    exists r. split; trivial.
    econstructor; eassumption.
Qed.

Lemma reachD': forall m R L b (RCH :reach m (fun u => R u = true)  L b),
      exists r, R r = true /\ reach m (fun bb => bb=r) L b /\
         match rev L with nil => True
           | HD::TL => exists z, HD = (r,z)
         end.
Proof. intros m R L.
  induction L; simpl; intros; inv RCH.
    exists b. intuition. constructor. trivial.
  destruct (IHL _ H1) as [r [Rr [RCH1 RCH2]]]; clear IHL H1.
    exists r. split; trivial.
    split. econstructor; eassumption.
    remember (rev L) as d. destruct d; simpl in *.
      destruct L; simpl in *. inv RCH1. eexists; reflexivity.
      apply app_cons_not_nil in Heqd. contradiction.
    apply RCH2.
Qed.

(*We can always "normalize" a reach-chain so that there's only a single root,
  and the root at most occurs once in the chain*)
Lemma reachD'': forall m R L b (RCH :reach m (fun u => R u = true) L b),
      exists r M, R r = true /\ reach m (fun bb => bb=r) M b /\
         match rev M with nil => True
           | HD::TL => exists z, HD = (r,z) /\ (forall zz, ~ In (r,zz) TL) /\
                       (forall x zx, R x = true -> In (x,zx) M -> x=r)
         end.
Proof. intros m R L.
  induction L; simpl; intros; inv RCH.
    exists b, nil; simpl. intuition. constructor. trivial.
  destruct (IHL _ H1) as [r [M [Rr [RCH1 RCH2]]]]; clear IHL H1.
    remember (R b) as Rb.
    destruct Rb; apply eq_sym in HeqRb.
      exists b, nil; simpl. intuition. constructor; trivial.
    remember (R b') as Rb'.
    destruct Rb'; apply eq_sym in HeqRb'.
      exists b'; eexists. split; trivial.
      split. eapply reach_cons; try eassumption.
               eapply reach_nil. trivial.
      simpl. exists z; intuition. inv H1. trivial.
    exists r; eexists.
      split. trivial.
      split. eapply reach_cons; try eassumption.
      simpl.
      remember (rev M) as d. destruct d; simpl in *.
        destruct M. inv RCH1. congruence.
        simpl in Heqd. apply app_cons_not_nil in Heqd. contradiction.
      destruct RCH2 as [zz [Hzz1 [Hzz2 Hzz3]]].
      exists zz; intuition.
      apply in_app_or in H.
        destruct H. apply (Hzz2 _ H).
        destruct H; try contradiction. inv H. congruence.
      subst. inv H1. congruence.
      subst. apply (Hzz3 _ _ H H1).
Qed.

Lemma encode_val_pointer_inv':
  forall chunk v b ofs n B1 mvl,
  encode_val chunk v = B1++Pointer b ofs n :: mvl ->
  chunk = Mint32 /\ v = Vptr b ofs.
Proof.
  intros until B1.
  assert (A: forall mvl, list_repeat (size_chunk_nat chunk) Undef = B1++Pointer b ofs n :: mvl ->
            chunk = Mint32 /\ v = Vptr b ofs).
    intros. destruct (size_chunk_nat_pos chunk) as [sz SZ]. rewrite SZ in H. simpl in H.
         clear SZ. generalize dependent sz.
         induction B1. simpl; intros. inv H.
         simpl; intros. inv H.
           destruct sz; simpl in *. destruct B1; inv H2.
         apply (IHB1 _ H2).
  intros mvl.
  assert (B: forall bl, inj_bytes bl = B1++Pointer b ofs n :: mvl ->
            chunk = Mint32 /\ v = Vptr b ofs).
    clear A. intros bl. generalize dependent B1.
       induction bl. simpl; intros. destruct B1; inv H.
       simpl; intros.
       destruct B1; simpl in *. inv H.
       inv H. eapply IHbl. eassumption.
  intros.
  specialize (A mvl).
  unfold encode_val; destruct v; destruct chunk;
  (apply A; assumption) ||
  (eapply B; rewrite encode_int_length; congruence) || idtac.

  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  eapply B. simpl in H. eassumption.
  simpl in H. clear -H.
  assert (forall L, (forall mv, In mv L -> exists n, mv = Pointer b0 i n) ->
          forall  mv, In mv L -> exists n, mv = Pointer b0 i n).
    intros. apply H0. trivial.
  assert (exists k, Pointer b ofs n = Pointer b0 i k).
    apply (H0 (B1 ++ Pointer b ofs n :: mvl)).
    intros. rewrite <- H in H1. clear -H1.
    destruct H1. subst. eexists; reflexivity.
    destruct H. subst. eexists; reflexivity.
    destruct H. subst. eexists; reflexivity.
    destruct H. subst. eexists; reflexivity.
    inv H.
  apply in_or_app. right. left. trivial.
  destruct H1. inv H1. split; trivial.
Qed.

Lemma list_split: forall {A} n (L:list A) (Hn : (n < length L)%nat),
      exists vl1 u vl2,
                     L = vl1 ++ u :: vl2 /\
                     length vl1 = n.
Proof. intros A n.
  induction n; simpl; intros.
    exists nil; simpl. destruct L; simpl in *. inv Hn.
     exists a, L. split; trivial.
  destruct L; simpl in Hn. inv Hn.
    destruct (IHn L) as [L1 [u [L2 [HL LL]]]].
       omega.
    subst. exists (a::L1), u, L2; simpl. split; trivial.
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
apply R. clear R.
rewrite REACHAX.
remember (Roots bb) as Rb. destruct Rb; apply eq_sym in HeqRb.
  eexists. eapply reach_nil; trivial.
rewrite REACHAX in Hbb.
destruct Hbb as [L HL].
destruct (reachD'' _ _ _ _ HL) as [r [M [Rr [RCH HM]]]]; clear HL L.
destruct (eq_block r b); subst.
(*we stored into the root of the access path to bb*)
  clear VISb.
  generalize dependent bb.
  induction M; simpl in *; intros.
  inv RCH. congruence.
  inv RCH.
  apply (Mem.perm_store_2 _ _ _ _ _ _ ST) in H2.
  remember (rev M) as rm.
  destruct rm; simpl in *. destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
        inv Hzz1.
        intuition.
        assert (M= nil). destruct M; trivial.
             assert (@length (block * Z) nil = length (rev (p :: M))). rewrite Heqrm; trivial.
             rewrite rev_length in H3. simpl in H3. inv H3.
        subst. simpl in *. clear H Heqrm H0 H1.
          specialize (Mem.loadbytes_store_same _ _ _ _ _ _ ST). intros LD.
          apply loadbytes_D in LD. destruct LD.

     rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST) in H4, H0.
          apply Mem.store_valid_access_3 in ST. destruct ST as [RP ALGN].
          rewrite PMap.gss in H4.
          destruct (zlt zz (Int.unsigned i)).
            rewrite Mem.setN_outside in H4.
            eexists. eapply reach_cons; try eassumption.
                     apply reach_nil. assumption.
            left; trivial.
          destruct (zlt zz ((Int.unsigned i) + Z.of_nat (length (encode_val chunk v)))).
          Focus 2.
            rewrite Mem.setN_outside in H4.
            eexists. eapply reach_cons; try eassumption.
                     apply reach_nil. assumption.
            right; trivial.
          rewrite encode_val_length in *. rewrite <- size_chunk_conv in *.
            rewrite PMap.gss in H0.
            remember ((Mem.setN (encode_val chunk v) (Int.unsigned i)
          (Mem.mem_contents m) !! b)) as c. apply eq_sym in H0.
          specialize (getN_aux (nat_of_Z ((size_chunk chunk))) (Int.unsigned i) c).
          assert (exists z, zz = Int.unsigned i + z /\ z>=0 /\ z < size_chunk chunk).
            exists (zz - Int.unsigned i). omega.
          destruct H1 as [z [Z1 [Z2 Z3]]]. clear g l. subst zz.
          rewrite <- (nat_of_Z_eq _ Z2) in H4.
          assert (SPLIT: exists vl1 u vl2,
                     encode_val chunk v = vl1 ++ u :: vl2 /\
                     length vl1 = nat_of_Z z).
            eapply list_split. rewrite encode_val_length.
                 rewrite size_chunk_conv in Z3.
            remember (size_chunk_nat chunk) as k. clear Heqk H2 H4 Hzz3.
            specialize (Z2Nat.inj_lt z (Z.of_nat k)); intros.
            rewrite Nat2Z.id in H1. apply H1. omega. omega.  assumption.

          destruct SPLIT as [B1 [u [B2 [EE LL]]]].
          rewrite EE in *. rewrite <- LL in H4.
          intros. apply H1 in H0. clear H1.
          rewrite <- H0 in H4. clear H0. subst u.
          destruct (encode_val_pointer_inv' _ _ _ _ _ _ _ EE).
          subst.
          rewrite VISv in HeqRb. discriminate.
             rewrite getBlocks_char. exists off; left. trivial.
  destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
    subst.
    remember (Roots b') as q.
    destruct q; apply eq_sym in Heqq.
      assert (b' = b). apply (Hzz3 _ z Heqq). left; trivial.
      subst. elim (Hzz2 z). apply in_or_app. right. left. trivial.
    destruct (eq_block b' b); try congruence.
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST) in H4.
        rewrite PMap.gso in H4; trivial.
        assert (Hb': exists L : list (block * Z),
            reach m (fun bb0 : block => Roots bb0 = true) L b').
          apply IHM; trivial. clear IHM.
          exists zz. intuition.
          eapply (Hzz2 zz0). apply in_or_app. left; trivial.
          eapply (Hzz3 _ zx H). right; trivial.
        destruct Hb' as [L HL].
          eexists. eapply reach_cons; try eassumption.
(*we stored elsewhere*)
generalize dependent bb.
induction M; simpl in *; intros.
  inv RCH. congruence.
  inv RCH.
  apply (Mem.perm_store_2 _ _ _ _ _ _ ST) in H2.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST) in H4.
  remember (rev M) as rm.
  destruct rm; simpl in *. destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
        inv Hzz1.
        rewrite PMap.gso in H4; trivial.
        eexists. eapply reach_cons; try eassumption.
           apply reach_nil. assumption.
  destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
    subst.
    remember (Roots b') as q.
    destruct q; apply eq_sym in Heqq.
      assert (b' = r). apply (Hzz3 _ z Heqq). left; trivial.
      subst.
        rewrite PMap.gso in H4; trivial.
          eexists. eapply reach_cons; try eassumption.
           apply reach_nil. assumption.
    destruct (eq_block b' b); try congruence.
        rewrite PMap.gso in H4; trivial.
        assert (Hb': exists L : list (block * Z),
            reach m (fun bb0 : block => Roots bb0 = true) L b').
          apply IHM; trivial. clear IHM.
          exists zz. intuition.
          eapply (Hzz2 zz0). apply in_or_app. left; trivial.
          eapply (Hzz3 _ zx H). right; trivial.
        destruct Hb' as [L HL].
          eexists. eapply reach_cons; try eassumption.
Qed.

(*similar proof as Lemma REACH_Store. *)
Lemma REACH_Storebytes: forall m b i bytes m'
     (ST: Mem.storebytes m b (Int.unsigned i) bytes = Some m')
     Roots (VISb: Roots b = true)
     (VISv : forall b' z n, In (Pointer b' z n) bytes ->
             Roots b' = true)
     (R: REACH_closed m Roots),
     REACH_closed m' Roots.
Proof. intros.
intros bb Hbb.
apply R. clear R.
rewrite REACHAX.
remember (Roots bb) as Rb. destruct Rb; apply eq_sym in HeqRb.
  eexists. eapply reach_nil; trivial.
rewrite REACHAX in Hbb.
destruct Hbb as [L HL].
destruct (reachD'' _ _ _ _ HL) as [r [M [Rr [RCH HM]]]]; clear HL L.
destruct (eq_block r b); subst.
(*we stored into the root of the access path to bb*)
  clear VISb.
  generalize dependent bb.
  induction M; simpl in *; intros.
  inv RCH. congruence.
  inv RCH.
  apply (Mem.perm_storebytes_2 _ _ _ _ _ ST) in H2.
  remember (rev M) as rm.
  destruct rm; simpl in *. destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
        inv Hzz1.
        intuition.
        assert (M= nil). destruct M; trivial.
             assert (@length (block * Z) nil = length (rev (p :: M))). rewrite Heqrm; trivial.
             rewrite rev_length in H3. simpl in H3. inv H3.
        subst. simpl in *. clear H Heqrm H0 H1.
          specialize (Mem.loadbytes_storebytes_same _ _ _ _ _ ST). intros LD.
          apply loadbytes_D in LD. destruct LD.

     rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST) in H4, H0.
          apply Mem.storebytes_range_perm in ST. (*destruct ST as [RP ALGN].*)
          rewrite PMap.gss in H4.
          destruct (zlt zz (Int.unsigned i)).
            rewrite Mem.setN_outside in H4.
            eexists. eapply reach_cons; try eassumption.
                     apply reach_nil. assumption.
            left; trivial.
          destruct (zlt zz ((Int.unsigned i) + Z.of_nat (length bytes))).
          Focus 2.
            rewrite Mem.setN_outside in H4.
            eexists. eapply reach_cons; try eassumption.
                     apply reach_nil. assumption.
            right; trivial.
          rewrite nat_of_Z_of_nat in H0. rewrite PMap.gss in H0.
            remember ((Mem.setN bytes (Int.unsigned i)
          (Mem.mem_contents m) !! b)) as c. apply eq_sym in H0.
          specialize (getN_aux (length bytes) (Int.unsigned i) c).
          assert (exists z, zz = Int.unsigned i + z /\ z>=0 /\ z < Z.of_nat(length bytes)).
            exists (zz - Int.unsigned i). omega.
          destruct H1 as [z [Z1 [Z2 Z3]]]. clear g l. subst zz.
          rewrite <- (nat_of_Z_eq _ Z2) in H4.
          assert (SPLIT: exists vl1 u vl2,
                     bytes = vl1 ++ u :: vl2 /\
                     length vl1 = nat_of_Z z).
            eapply list_split.
            specialize (Z2Nat.inj_lt z (Z.of_nat (length bytes))); intros.
            rewrite Nat2Z.id in H1. apply H1. omega. omega.  assumption.
          destruct SPLIT as [B1 [u [B2 [EE LL]]]].
          rewrite EE in *. rewrite <- LL in H4.
          intros. apply H1 in H0. clear H1.
          rewrite <- H0 in H4. clear H0. subst u.
          subst.
          rewrite (VISv bb off n) in HeqRb. discriminate.
             eapply in_or_app. right. left. trivial.
  destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
    subst.
    remember (Roots b') as q.
    destruct q; apply eq_sym in Heqq.
      assert (b' = b). apply (Hzz3 _ z Heqq). left; trivial.
      subst. elim (Hzz2 z). apply in_or_app. right. left. trivial.
    destruct (eq_block b' b); try congruence.
        rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST) in H4.
        rewrite PMap.gso in H4; trivial.
        assert (Hb': exists L : list (block * Z),
            reach m (fun bb0 : block => Roots bb0 = true) L b').
          apply IHM; trivial. clear IHM.
          exists zz. intuition.
          eapply (Hzz2 zz0). apply in_or_app. left; trivial.
          eapply (Hzz3 _ zx H). right; trivial.
        destruct Hb' as [L HL].
          eexists. eapply reach_cons; try eassumption.
(*we stored elsewhere*)
generalize dependent bb.
induction M; simpl in *; intros.
  inv RCH. congruence.
  inv RCH.
  apply (Mem.perm_storebytes_2 _ _ _ _ _ ST) in H2.
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST) in H4.
  remember (rev M) as rm.
  destruct rm; simpl in *. destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
        inv Hzz1.
        rewrite PMap.gso in H4; trivial.
        eexists. eapply reach_cons; try eassumption.
           apply reach_nil. assumption.
  destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
    subst.
    remember (Roots b') as q.
    destruct q; apply eq_sym in Heqq.
      assert (b' = r). apply (Hzz3 _ z Heqq). left; trivial.
      subst.
        rewrite PMap.gso in H4; trivial.
          eexists. eapply reach_cons; try eassumption.
           apply reach_nil. assumption.
    destruct (eq_block b' b); try congruence.
        rewrite PMap.gso in H4; trivial.
        assert (Hb': exists L : list (block * Z),
            reach m (fun bb0 : block => Roots bb0 = true) L b').
          apply IHM; trivial. clear IHM.
          exists zz. intuition.
          eapply (Hzz2 zz0). apply in_or_app. left; trivial.
          eapply (Hzz3 _ zx H). right; trivial.
        destruct Hb' as [L HL].
          eexists. eapply reach_cons; try eassumption.
Qed.

Lemma REACH_load_vis: forall chunk m b i b1 ofs1
        (LD: Mem.load chunk m b (Int.unsigned i) = Some (Vptr b1 ofs1))
         mu (VIS: vis mu b = true),
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

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: Values.block.
Hypothesis ALLOC: Mem.alloc m1 lo hi = (m2, b).

Transparent Mem.alloc.
Lemma AllocContentsUndef:
     (Mem.mem_contents m2) !! b = ZMap.init Undef.
Proof.
   injection ALLOC. simpl; intros. subst.
   simpl. rewrite PMap.gss. reflexivity.
Qed.
Opaque Mem.alloc.

Lemma AllocContentsUndef1: forall z,
     ZMap.get z (Mem.mem_contents m2) !! b = Undef.
Proof. intros. rewrite AllocContentsUndef . apply ZMap.gi. Qed.

End ALLOC.

(*The following 2 lemmas are from Cminorgenproof.v*)
Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros. destruct addr; try discriminate.
  eapply Mem.nextblock_store; eauto.
Qed.
Lemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi].
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed.
Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.


Lemma store_freshloc: forall ch m addr v m'
         (ST: Mem.storev ch m addr v = Some m'),
         freshloc m m' = fun b => false.
Proof. intros.
  extensionality b.
  apply nextblock_storev in ST.
  (*specialize (storev_valid_block_2 _ _ _ _ _ ST b); intros.
  specialize (storev_valid_block_1 _ _ _ _ _ ST b); intros.*)
  apply freshloc_charF.
  unfold Mem.valid_block. rewrite ST. xomega.
Qed.

Lemma freshloc_alloc: forall m1 lo hi m2 b
      (ALLOC: Mem.alloc m1 lo hi = (m2, b)),
      freshloc m1 m2 = fun bb => eq_block bb b.
Proof. intros.
  unfold freshloc. extensionality bb.
  destruct (eq_block bb b); subst; simpl.
    specialize (Mem.valid_new_block _ _ _ _ _ ALLOC).
    apply Mem.fresh_block_alloc in ALLOC.
    intros.
    destruct (valid_block_dec m2 b); try contradiction; simpl.
    destruct (valid_block_dec m1 b); try contradiction; trivial.
  destruct (valid_block_dec m2 bb); simpl; trivial.
    destruct (Mem.valid_block_alloc_inv _ _ _ _ _ ALLOC _ v); try contradiction.
    destruct (valid_block_dec m1 bb); try contradiction; trivial.
Qed.

Lemma freshloc_free: forall m sp i n m'
      (F: Mem.free m sp i n = Some m'),
      freshloc m m' = fun b => false.
Proof. intros.
  unfold freshloc. extensionality b.
  remember (valid_block_dec m' b) as d'.
  destruct d'; simpl; trivial; clear Heqd'.
    apply (Mem.valid_block_free_2 _ _ _ _ _ F ) in v.
    remember (valid_block_dec m b) as d.
    destruct d; trivial. congruence.
Qed.

Lemma freshloc_free_list: forall m n m'
      (F: Mem.free_list m n = Some m'),
      freshloc m m' = fun b => false.
Proof. intros.
  unfold freshloc. apply nextblock_freelist in F.
  extensionality b.
  remember (valid_block_dec m' b) as d'.
  destruct d'; simpl; trivial; clear Heqd'.
    remember (valid_block_dec m b) as d.
    destruct d; trivial. unfold Mem.valid_block in *.
    rewrite F in v. congruence.
Qed.

(*new lemma*)
Lemma free_parallel_inject:
  forall j (m1 m2 : mem) (b : block) (lo hi : Z) (m1' : mem) ,
  Mem.inject j m1 m2 ->
  Mem.free m1 b lo hi = Some m1' ->
  forall b2 d (J: j b = Some(b2,d)),
    exists m2' : mem, Mem.free m2 b2 (lo+d) (hi+d) = Some m2' /\
                Mem.inject j m1' m2'.
Proof. intros.
  destruct (Mem.range_perm_free m2 b2 (lo+d) (hi+d)) as [m2' Hm2'].
    intros. intros off; intros.
    specialize (Mem.perm_inject _ _ _ _ _ _ (off-d) Cur Freeable J H). intros.
    assert (off - d + d = off) by omega. rewrite H3 in H2.
    apply H2. clear H2 H3.
    eapply (Mem.free_range_perm _ _ _ _ _ H0). omega.
  exists m2'; split; trivial.
  eapply (Mem.free_inject _ _ ((b,lo,hi)::nil)); try eassumption.
    simpl. rewrite H0. trivial.
  intros.
  destruct (eq_block b1 b); subst.
    rewrite H1 in J; inv J. exists lo, hi; split. left; trivial. omega.
  assert (P: Mem.perm m1 b (ofs + delta - d) Max Nonempty).
    eapply Mem.perm_implies.
      eapply Mem.perm_max.
      apply (Mem.free_range_perm _ _ _ _ _ H0). omega.
    constructor.
  assert (P1: Mem.perm m1 b1 ofs Max Nonempty).
    eapply Mem.perm_implies.
      eapply Mem.perm_max. eassumption. eapply perm_any_N.
  exfalso.
  destruct (Mem.mi_no_overlap _ _ _ H b1 _ _ _ _ _ _ _ n H1 J P1 P)
    as [X | X]; apply X; trivial. omega.
Qed.

Lemma REACH_closed_free: forall m1 b lo hi m2
       (F: Mem.free m1 b lo hi = Some m2) X
       (RC: REACH_closed m1 X),
      REACH_closed m2 X.
Proof. intros.
      red; intros. apply RC; clear RC.
          rewrite REACHAX in H. destruct H as [L HL].
          generalize dependent b0.
          induction L; simpl; intros; inv HL.
            apply REACH_nil. assumption.
          specialize (IHL _ H1); clear H1.
            eapply REACH_cons; try eassumption.
            eapply Mem.perm_free_3; eassumption.
            rewrite (Mem.free_result _ _ _ _ _ F) in H4.
            apply H4.
Qed.

Lemma REACH_closed_freelist: forall X l m m'
  (FL : Mem.free_list m l = Some m')
  (RC : REACH_closed m X),
  REACH_closed m' X.
Proof. intros X l.
 induction l; simpl; intros.
   inv FL. trivial.
 destruct a as [[b lo] hi].
 remember (Mem.free m b lo hi).
 destruct o; inv FL. apply eq_sym in Heqo.
 eapply (IHl _ _ H0).
 eapply REACH_closed_free; eassumption.
Qed.

Definition alloc_right_sm (mu: SM_Injection) sp: SM_Injection :=
  Build_SM_Injection (locBlocksSrc mu)
                     (fun b => eq_block b sp || locBlocksTgt mu b)
                     (pubBlocksSrc mu) (pubBlocksTgt mu)
                     (local_of mu)
                     (extBlocksSrc mu) (extBlocksTgt mu)
                     (frgnBlocksSrc mu) (frgnBlocksTgt mu) (extern_of mu).

Lemma alloc_right_sm_wd: forall mu sp (WD: SM_wd mu)
      (NEW1: DomTgt mu sp = false),
      SM_wd (alloc_right_sm mu sp).
Proof. intros.
econstructor; simpl in *; try solve [eapply WD].
  intros. unfold DomTgt in NEW1.
    apply orb_false_iff in NEW1.
    destruct NEW1.
    remember (eq_block b sp) as d.
    destruct d; simpl in *; apply eq_sym in Heqd.
      subst. right. assumption.
      eapply WD.
  intros.
    destruct (local_DomRng _ WD _ _ _ H). intuition.
  intros. rewrite (pubBlocksLocalTgt _ WD _ H). intuition.
Qed.

Lemma alloc_right_sm_locBlocksTgt: forall mu sp,
  locBlocksTgt (alloc_right_sm mu sp) = fun b => eq_block b sp || locBlocksTgt mu b.
Proof. intros. reflexivity. Qed.

Lemma alloc_right_sm_DomSrc: forall mu sp,
      DomSrc (alloc_right_sm mu sp) = DomSrc mu.
Proof. intros. extensionality b.
  unfold DomSrc, alloc_right_sm; simpl. trivial.
Qed.

Lemma alloc_right_sm_DomTgt: forall mu sp,
      DomTgt (alloc_right_sm mu sp) = fun b => eq_block b sp || DomTgt mu b.
Proof. intros. extensionality b.
  unfold DomTgt, alloc_right_sm; simpl.
  rewrite <- orb_assoc. trivial.
Qed.

Lemma alloc_right_sm_as_inj: forall mu sp,
      as_inj (alloc_right_sm mu sp) = as_inj mu.
Proof. intros. unfold alloc_right_sm, as_inj; reflexivity. Qed.

Lemma alloc_right_sm_intern_incr: forall mu sp,
      intern_incr mu (alloc_right_sm mu sp).
Proof. intros. red; intros. simpl. intuition. Qed.


Definition alloc_left_sm (mu: SM_Injection) b1 b2 delta: SM_Injection :=
  Build_SM_Injection (fun b => eq_block b b1 || locBlocksSrc mu b)
                     (locBlocksTgt mu) (*b2 is already in locBlocksTgt!*)
                     (pubBlocksSrc mu) (pubBlocksTgt mu)
                     (fun b => if eq_block b b1 then Some(b2, delta)
                               else local_of mu b)
                     (extBlocksSrc mu) (extBlocksTgt mu)
                     (frgnBlocksSrc mu) (frgnBlocksTgt mu) (extern_of mu).

Lemma alloc_left_sm_wd: forall mu b1 b2 delta (WD: SM_wd mu)
      (NEW1: DomSrc mu b1 = false) (NEW2: locBlocksTgt mu b2 = true),
      SM_wd (alloc_left_sm mu b1 b2 delta).
Proof. intros.
econstructor; simpl in *; try solve [eapply WD].
  intros. apply orb_false_iff in NEW1.
    remember (eq_block b b1) as d.
    destruct d; simpl in *; apply eq_sym in Heqd.
      subst. right. apply NEW1.
      apply WD.
  intros.
    remember (eq_block b0 b1) as d.
      destruct d; simpl in *; apply eq_sym in Heqd. inv H. split; trivial.
    apply (local_DomRng _ WD _ _ _ H).
  intros.
    destruct (pubSrc _ WD _ H) as [bb [dd [PB PT]]].
    exists bb, dd.
    remember (eq_block b0 b1) as d.
      destruct d; simpl in *; apply eq_sym in Heqd.
        subst. unfold DomSrc in NEW1.
        rewrite (pubBlocksLocalSrc _ WD _ H) in NEW1. simpl in *. discriminate.
      rewrite (pub_in_local _ _ _ _ PB).
      split; trivial.
Qed.

Lemma alloc_left_sm_as_inj_same: forall mu b1 b2 delta (WD: SM_wd mu)
      (NEW1: DomSrc mu b1 = false),
      as_inj (alloc_left_sm mu b1 b2 delta) b1 = Some(b2,delta).
Proof. intros.
  unfold as_inj, join; simpl.
  remember (extern_of mu b1) as d.
  destruct d; apply eq_sym in Heqd; simpl. destruct p.
    destruct (extern_DomRng' _ WD _ _ _ Heqd). rewrite NEW1 in H0. intuition.
  destruct (eq_block b1 b1); subst; trivial.
    elim n. trivial.
Qed.

Lemma alloc_left_sm_as_inj_other: forall mu b1 b2 delta b (H: b<>b1),
      as_inj (alloc_left_sm mu b1 b2 delta) b = as_inj mu b.
Proof. intros.
  unfold as_inj, join; simpl.
  destruct (eq_block b b1); subst; trivial. elim H. trivial.
Qed.

Lemma alloc_left_sm_intern_incr:
      forall mu b1 b2 delta (H: as_inj mu b1 = None) (WD: SM_wd mu),
      intern_incr mu (alloc_left_sm mu b1 b2 delta).
Proof. intros.
  specialize (local_in_all _ WD); intros.
  red; intros. destruct mu; simpl in *.
  intuition.
  red; intros.
  destruct (eq_block b b1); subst.
     rewrite (H0 _ _ _ H1) in H. inv H.
  assumption.
Qed.

Lemma alloc_left_sm_inject_incr:
      forall mu b1 b2 delta (H: as_inj mu b1 = None),
      inject_incr (as_inj mu) (as_inj (alloc_left_sm mu b1 b2 delta)).
Proof. intros.
  red; intros.
  destruct (eq_block b b1); subst. congruence.
  rewrite alloc_left_sm_as_inj_other; trivial.
Qed.

Lemma alloc_DomSrc: forall mu m1 m2 (SMV: sm_valid mu m1 m2) lo hi m1' b1
      (ALLOC: Mem.alloc m1 lo hi = (m1', b1)),
      DomSrc mu b1 = false.
Proof. intros.
  remember (DomSrc mu b1) as d.
  destruct d; trivial; apply eq_sym in Heqd.
  apply Mem.fresh_block_alloc in ALLOC.
  elim ALLOC. apply SMV. apply Heqd.
Qed.

Lemma alloc_left_sm_DomSrc: forall mu b1 b2 delta,
      DomSrc (alloc_left_sm mu b1 b2 delta) = fun b => eq_block b b1 || DomSrc mu b.
Proof. intros. extensionality b.
  unfold DomSrc, alloc_left_sm; simpl.
  rewrite <- orb_assoc. trivial.
Qed.

Lemma alloc_left_sm_DomTgt: forall mu b1 b2 delta,
      DomTgt (alloc_left_sm mu b1 b2 delta) = DomTgt mu.
Proof. intros. reflexivity. Qed.

Lemma REACH_closed_alloc_left_sm: forall m lo hi sp m'
          (ALLOC : Mem.alloc m lo hi = (m', sp))
          mu (RC: REACH_closed m (vis mu)) b' delta,
      REACH_closed m' (vis (alloc_left_sm mu sp b' delta)).
Proof.
  red; intros.
  unfold vis. simpl.
  destruct (eq_block b sp); try subst b. trivial.
  simpl.
  apply RC. rewrite REACHAX in H.
  destruct H as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
    apply REACH_nil.
      unfold vis in H. simpl in H.
      destruct (eq_block b sp); try subst b. elim n; trivial.
      apply H.
    destruct (eq_block b'0 sp); try subst b'0.
      clear - ALLOC H2 H4 n.
      rewrite (AllocContentsUndef1 _ _ _ _ _ ALLOC) in H4. inv H4.
    specialize (IHL _ H1 n1); clear H1.
      apply (Mem.perm_alloc_4 _ _ _ _ _ ALLOC) in H2; trivial.
      destruct (Mem.alloc_unchanged_on (fun bb zz => True)
         _ _ _ _ _ ALLOC) as [UP UC].
      rewrite UC in H4; trivial.
        eapply REACH_cons; eassumption.
Qed.

Theorem alloc_left_mapped_sm_inject:
  forall mu m1 m2 lo hi m1' b1 b2 delta (WD: SM_wd mu)
        (SMV: sm_valid mu m1 m2) (RC: REACH_closed m1 (vis mu))
        (Locb2: locBlocksTgt mu b2 = true),
  Mem.inject (as_inj mu) m1 m2 ->
  Mem.alloc m1 lo hi = (m1', b1) ->
  Mem.valid_block m2 b2 ->
  0 <= delta <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Int.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> Mem.perm m2 b2 (ofs + delta) k p) ->
  Mem.inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   as_inj mu b = Some (b2, delta') ->
   Mem.perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists mu',
     Mem.inject (as_inj mu') m1' m2
  /\ intern_incr mu mu'
  /\ as_inj mu' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> as_inj mu' b = as_inj mu b)
  /\ SM_wd mu' /\ sm_valid mu' m1' m2
  /\ sm_locally_allocated mu mu' m1 m2 m1' m2
  /\ REACH_closed m1' (vis mu').
Proof.
  intros. inversion H.
  assert (AIb: as_inj mu b1 = None). eauto with mem.
  assert (DS:= alloc_DomSrc _ _ _ SMV _ _ _ _ H0).
  set (mu' := alloc_left_sm mu b1 b2 delta).
  assert (intern_incr mu mu').
    red; unfold mu'; intros. simpl.
    intuition.
    red; intros. destruct (eq_block b b1). subst b.
       apply (local_in_all _ WD) in H2. congruence.
    auto.
  assert (Mem.mem_inj (as_inj mu') m1 m2).
    inversion mi_inj; constructor; eauto with mem.
    unfold mu'; intros. destruct (eq_block b0 b1).
      subst b0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
    rewrite alloc_left_sm_as_inj_other in H8; trivial.
      eauto.
    unfold mu'; simpl. intros. destruct (eq_block b0 b1).
      subst b0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0).
      eapply Mem.perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega.
    rewrite alloc_left_sm_as_inj_other in H8; trivial.
      eauto.
    unfold mu'; simpl; intros. destruct (eq_block b0 b1).
      subst b0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
    rewrite alloc_left_sm_as_inj_other in H8; trivial.
      apply memval_inject_incr with (as_inj mu); auto.
      apply alloc_left_sm_inject_incr; assumption.
  exists mu'. split. constructor.
(* inj *)
  eapply Mem.alloc_left_mapped_inj; eauto.
  unfold mu'; simpl. rewrite alloc_left_sm_as_inj_same; trivial.
(* freeblocks *)
  unfold mu'; simpl; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  rewrite alloc_left_sm_as_inj_other; trivial.
  eauto with mem.
(* mappedblocks *)
  unfold mu'; simpl; intros.
  destruct (eq_block b b1).
    subst. rewrite alloc_left_sm_as_inj_same in H9; trivial.
     congruence. eauto.
  rewrite alloc_left_sm_as_inj_other in H9; trivial.
    eauto.
(* overlap *)
  unfold mu'; red; intros.
  exploit Mem.perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit Mem.perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); try subst b0; destruct (eq_block b3 b1); try subst b3.
    elim H9; trivial.
    rewrite alloc_left_sm_as_inj_same in H10; trivial.
    inversion H10. subst b1' delta1.
    rewrite alloc_left_sm_as_inj_other in H11; trivial.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. omega.

  rewrite alloc_left_sm_as_inj_same in H11; trivial.
    rewrite alloc_left_sm_as_inj_other in H10; trivial.
    inversion H11. subst b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. omega.
  rewrite alloc_left_sm_as_inj_other in H10; trivial.
  rewrite alloc_left_sm_as_inj_other in H11; trivial.
  eauto.
(* representable *)
  unfold mu'; intros.
  destruct (eq_block b b1).
   subst.
    rewrite alloc_left_sm_as_inj_same in H9; trivial.
    injection H9; intros; subst b' delta0. clear H9; destruct H10.
    exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Int.unsigned_range_2 ofs). omega.
   exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Int.unsigned_range_2 ofs). omega.
  rewrite alloc_left_sm_as_inj_other in H9; trivial.
  eapply mi_representable; try eassumption.
  destruct H10; eauto using Mem.perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold mu'; simpl.
    rewrite alloc_left_sm_as_inj_same; trivial.
(* image of others *)
  split. intros. unfold mu'; simpl.
  rewrite alloc_left_sm_as_inj_other; trivial.
(* SM_wd*)
  split. unfold mu'. eapply alloc_left_sm_wd; try eassumption.
 (* sm_valid*)
  split. red.
  split; intros. unfold mu' in H9; simpl in H9.
    unfold DOM, DomSrc in H9; simpl in H9.
    destruct (eq_block b0 b1); try subst b0.
      apply (Mem.valid_new_block _ _ _ _ _ H0).
    simpl in H9.
    apply (Mem.valid_block_alloc _ _ _ _ _ H0).
    apply SMV. apply H9.
  unfold mu' in H9; simpl in H9. unfold RNG, DomTgt in H9; simpl in H9.
    destruct (eq_block b0 b2); try subst b0.
      assumption.
    simpl in H9.
    apply SMV. apply H9.
(*sm_locally_allocated*)
  split. apply sm_locally_allocatedChar. unfold mu'; simpl.
  repeat split; extensionality bb;
   try rewrite (freshloc_irrefl m2);
   try rewrite (freshloc_alloc _ _ _ _ _ H0); simpl.
  unfold DomSrc; simpl. rewrite <- orb_assoc. rewrite orb_comm. trivial.
  unfold DomTgt; simpl. destruct (eq_block bb b2); try subst bb; simpl.
    rewrite Locb2. trivial.
    intuition.
  intuition.
  destruct (eq_block bb b2); try subst bb; simpl.
    rewrite Locb2. trivial.
  intuition.
(* REACH_closed*)
  clear - RC H0.
  eapply REACH_closed_alloc_left_sm; eassumption.
Qed.

Lemma genv_find_add_globals_fresh: forall {F V} defs (g:Genv.t F V) i
  (G: ~ In i (map fst defs)),
  Genv.find_symbol (Genv.add_globals g defs) i =  Genv.find_symbol g i.
Proof. intros F V defs.
  induction defs; simpl; intros. trivial.
  destruct a.
  rewrite IHdefs.
    unfold Genv.find_symbol, Genv.genv_symb. simpl. rewrite PTree.gso. reflexivity.
    intros N. apply G; left. subst; simpl; trivial.
  intros N. apply G; right; trivial.
Qed.

Lemma add_globals_find_symbol: forall {F V} (defs : list (ident * globdef F V))
    (R: list_norepet (map fst defs)) (g: Genv.t F V) m0 m
    (G: Genv.alloc_globals (Genv.add_globals g defs) m0 defs = Some m)
    (N: Genv.genv_next g = Mem.nextblock m0)
    b (VB: Mem.valid_block m b),
    Mem.valid_block m0 b \/
    exists id, Genv.find_symbol (Genv.add_globals g defs) id = Some b.
Proof. intros F V defs.
induction defs; simpl; intros.
  inv G. left; trivial.
remember (Genv.alloc_global (Genv.add_globals (Genv.add_global g a) defs) m0 a) as d.
  destruct d; inv G. apply eq_sym in Heqd.
  inv R.
  specialize (IHdefs H3 _ _ _ H0). simpl in *.
  rewrite N in *.
  assert (P: Pos.succ (Mem.nextblock m0) = Mem.nextblock m1).
    clear IHdefs N VB H0.
    rewrite (@Genv.alloc_global_nextblock _ _ _ _ _ _ Heqd). trivial.
  destruct (IHdefs P _ VB); try (right; assumption).
  clear IHdefs P VB H0.
  destruct a. destruct g0. simpl in Heqd.
   remember (Mem.alloc m0 0 1) as t.
   destruct t; inv Heqd. apply eq_sym in Heqt.
   apply (Mem.drop_perm_valid_block_2 _ _ _ _ _ _ H1) in H. clear H1.
   apply (Mem.valid_block_alloc_inv _ _ _ _ _ Heqt) in H.
   destruct H; subst; try (left; assumption).
     right. apply Mem.alloc_result in Heqt. subst.
     exists i. rewrite genv_find_add_globals_fresh; trivial.
     unfold Genv.find_symbol, Genv.genv_symb. simpl.
     rewrite PTree.gss. rewrite N. trivial.
simpl in *.
  remember (Mem.alloc m0 0 (Genv.init_data_list_size (gvar_init v))) as t.
  destruct t; inv Heqd. apply eq_sym in Heqt.
  remember (store_zeros m2 b0 0 (Genv.init_data_list_size (gvar_init v))) as q.
  destruct q; inv H1. apply eq_sym in Heqq.
  remember (Genv.store_init_data_list
         (Genv.add_globals (Genv.add_global g (i, Gvar v)) defs) m3 b0 0
         (gvar_init v)) as w.
  destruct w; inv H4. apply eq_sym in Heqw.
  apply (Mem.drop_perm_valid_block_2 _ _ _ _ _ _ H1) in H. clear H1.
  assert (VB3: Mem.valid_block m3 b). unfold Mem.valid_block.
    rewrite <- (@Genv.store_init_data_list_nextblock _ _ _ _ _ _ _ _ Heqw).
    apply H.
  clear H Heqw.
  assert (VB2: Mem.valid_block m2 b). unfold Mem.valid_block.
    rewrite <- (@Genv.store_zeros_nextblock _ _ _ _ _ Heqq).
    apply VB3.
  clear VB3 Heqq.
  apply (Mem.valid_block_alloc_inv _ _ _ _ _ Heqt) in VB2.
   destruct VB2; subst; try (left; assumption).
     right. apply Mem.alloc_result in Heqt. subst.
     exists i. rewrite genv_find_add_globals_fresh; trivial.
     unfold Genv.find_symbol, Genv.genv_symb. simpl.
     rewrite PTree.gss. rewrite N. trivial.
Qed.

Lemma valid_init_is_global :
  forall {F V} (prog:AST.program F V)
         (R: list_norepet (map fst (prog_defs prog)))
  m (G: Genv.init_mem prog = Some m)
  b (VB: Mem.valid_block m b),
  exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b.
Proof. intros.
  unfold Genv.init_mem, Genv.globalenv in G. simpl in *.
  destruct (add_globals_find_symbol _ R (@Genv.empty_genv _ _ ) _ _ G (eq_refl _) _ VB)
    as [VBEmpty | X]; trivial.
  exfalso. clear - VBEmpty. unfold Mem.valid_block in VBEmpty.
    rewrite Mem.nextblock_empty in VBEmpty. xomega.
Qed.

Lemma find_symbol_isGlobal: forall {V F} (ge : Genv.t F V) x b
       (Find: Genv.find_symbol ge x = Some b),
     isGlobalBlock ge b = true.
Proof. intros.
  unfold isGlobalBlock.
  unfold genv2blocksBool. simpl.
  rewrite (Genv.find_invert_symbol _ _ Find). reflexivity.
Qed.


(*New Lemma, based on (proof of) Mem.alloc_parallel_inject*)
Theorem alloc_parallel_intern:
  forall mu m1 m2 lo1 hi1 m1' b1 lo2 hi2
        (SMV: sm_valid mu m1 m2) (WD: SM_wd mu),
  Mem.inject (as_inj mu) m1 m2 ->
  Mem.alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists mu', exists m2', exists b2,
  Mem.alloc m2 lo2 hi2 = (m2', b2)
  /\ Mem.inject (as_inj mu') m1' m2'
  /\ intern_incr mu mu'
  /\ as_inj mu' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> as_inj mu' b = as_inj mu b)
  /\ sm_inject_separated mu mu' m1 m2
  /\ sm_locally_allocated mu mu' m1 m2 m1' m2'
  /\ SM_wd mu' /\ sm_valid mu' m1' m2' /\
  (REACH_closed m1 (vis mu) -> REACH_closed m1' (vis mu')).
Proof.
  intros.
  case_eq (Mem.alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit Mem.alloc_left_mapped_inject.
  eapply Mem.alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Int.max_unsigned. generalize Int.modulus_pos; omega.
  auto.
  intros. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto. omega.
  red; intros. apply Zdivide_0.
  intros. eapply Mem.fresh_block_alloc; try eassumption.
          eapply SMV. eapply as_inj_DomRng in H3. eapply H3. assumption.
  intros [j' [A [B [C D]]]].
  exists (alloc_left_sm (alloc_right_sm mu b2) b1 b2 0).
  assert (WDr: SM_wd (alloc_right_sm mu b2)).
    eapply alloc_right_sm_wd; try eassumption.
      remember (DomTgt mu b2) as d.
      destruct d; trivial. apply eq_sym in Heqd.
      exfalso. apply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).
                 apply SMV. apply Heqd.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H0).
  assert (TgtB2: DomTgt mu b2 = false).
    remember (DomTgt mu b2) as d.
    destruct d; trivial; apply eq_sym in Heqd.
    elim (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).
      apply SMV. assumption.
  exists m2'; exists b2; auto.
  assert (J': (as_inj (alloc_left_sm (alloc_right_sm mu b2) b1 b2 0)) = j').
    extensionality b.
     destruct (eq_block b b1); subst.
        rewrite alloc_left_sm_as_inj_same, C; trivial.
     rewrite alloc_left_sm_as_inj_other; trivial.
        rewrite alloc_right_sm_as_inj. rewrite <- (D _ n). trivial.
  rewrite J'. intuition.
  split; simpl; intuition.
  red; intros.
       destruct (eq_block b b1); subst.
         assert (DomSrc mu b1 = true).
           eapply as_inj_DomRng. eapply local_in_all; eassumption.
           assumption.
         congruence.
       assumption.
(*inject_separated*)
  red. split; intros.
    destruct (eq_block b0 b1); subst.
      rewrite alloc_left_sm_as_inj_same in H4. inv H4.
      split; trivial.
      trivial.
      rewrite alloc_right_sm_DomSrc. assumption.
    rewrite (D _ n) in H4. congruence.
  split; intros. rewrite alloc_left_sm_DomSrc, alloc_right_sm_DomSrc in H4.
    destruct (eq_block b0 b1); subst; simpl in *.
      eapply (Mem.fresh_block_alloc _ _ _ _ _ H0).
    congruence.
  rewrite alloc_left_sm_DomTgt, alloc_right_sm_DomTgt in H4.
    destruct (eq_block b0 b2); subst; simpl in *.
      eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).
    congruence.
(*locally_separated*)
  rewrite sm_locally_allocatedChar. unfold DomSrc, DomTgt.
  rewrite (freshloc_alloc _ _ _ _ _ H0).
  rewrite (freshloc_alloc _ _ _ _ _ ALLOC).
  destruct mu; simpl. intuition.
    extensionality b. rewrite <- orb_assoc. rewrite orb_comm. trivial.
    extensionality b. rewrite <- orb_assoc. rewrite orb_comm. trivial.
    extensionality b. rewrite orb_comm. trivial.
    extensionality b. rewrite orb_comm. trivial.
(*SM_wd*)
  eapply alloc_left_sm_wd. assumption. apply DomSP.
   destruct mu; simpl. destruct (eq_block b2 b2); try reflexivity.
   elim n; trivial.
(*sm_valid*)
  split; intros. unfold DOM in H3. rewrite alloc_left_sm_DomSrc in H3.
    destruct (eq_block b0 b1); simpl in *; subst.
       eapply (Mem.valid_new_block _ _ _ _ _ H0).
     eapply (Mem.valid_block_alloc _ _ _ _ _ H0).
       eapply SMV. apply H3.
  unfold RNG in H3. rewrite alloc_left_sm_DomTgt, alloc_right_sm_DomTgt in H3.
    destruct (eq_block b0 b2); simpl in *; subst.
       eapply (Mem.valid_new_block _ _ _ _ _ ALLOC).
     eapply (Mem.valid_block_alloc _ _ _ _ _ ALLOC).
       eapply SMV. apply H3.
(*REACH_closed*)
  eapply REACH_closed_alloc_left_sm; eassumption.
Qed.

Lemma freelist_right_inject: forall j m1 l m2 m2'
       (F:Mem.free_list m2 l = Some m2')
       (Inj : Mem.inject j m1 m2)
       (Hyp: forall b2 lo2 hi2 (L:In ((b2,lo2),hi2) l)
                    b1 delta ofs k p
                    (J:j b1 = Some (b2, delta))
                    (P: Mem.perm m1 b1 ofs k p)
                    (OFS: lo2 <= ofs + delta < hi2),
                    False),
     Mem.inject j m1 m2'.
Proof. intros j m1 l.
  induction l; simpl; intros.
    inv F; trivial.
  destruct a as [[b2 lo2] hi2].
  remember (Mem.free m2 b2 lo2 hi2) as d.
  destruct d; inv F; apply eq_sym in Heqd.
  eapply (IHl _ _ H0).
  eapply Mem.free_right_inject; try eassumption.
    intros. eapply Hyp; try eassumption. left; trivial.
  intros. eapply Hyp; try eassumption. right; trivial.
Qed.
