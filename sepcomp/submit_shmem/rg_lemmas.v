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

Lemma RGTgt_multicoreLICSpaper: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true ->
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
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

