Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Axioms.

Require Import FiniteMaps.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolation_defs.

Definition AccessMap_EI_Property (j:meminj) (m1 m1' m2 : mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2,
    (Mem.valid_block m2 b2 -> forall k ofs2,
       match j b2 with
         None => PMap.get b2 AM ofs2 k  =
                        PMap.get b2 m2.(Mem.mem_access) ofs2 k
       | Some (b3,d3) =>
          (Mem.perm m1 b2 ofs2 Max Nonempty ->
           PMap.get b2 AM ofs2 k = PMap.get b2 m1'.(Mem.mem_access) ofs2 k)
       /\ (~Mem.perm m1 b2 ofs2 Max Nonempty ->
           PMap.get b2 AM ofs2 k  = PMap.get b2 m2.(Mem.mem_access) ofs2 k)
     end)
  /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
         (Mem.perm m1' b2 ofs2 Max Nonempty ->
           PMap.get b2 AM ofs2 k = PMap.get b2 m1'.(Mem.mem_access) ofs2 k)
       /\ (~Mem.perm m1' b2 ofs2 Max Nonempty -> PMap.get b2 AM ofs2 k = None)).

Definition Content_EI_Property (j:meminj) (m1 m1' m2:Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2,
      (Mem.valid_block m2 b2 -> forall ofs2,
             match j b2 with
               None =>  ZMap.get ofs2 (PMap.get b2 CM) =
                           ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
             | Some (b3,delta3) =>
                     (Mem.perm m1 b2 ofs2 Max Nonempty ->
                            ZMap.get ofs2 (PMap.get b2 CM) =
                           ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents)))
                 /\ (~Mem.perm m1 b2 ofs2 Max Nonempty ->
                          ZMap.get ofs2 (PMap.get b2 CM) =
                         ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents)))
            end)
    /\ (~ Mem.valid_block m2 b2 -> forall (HM1': Mem.valid_block m1' b2) ofs2,
           (Mem.perm m1' b2 ofs2 Cur Readable ->
                ZMap.get ofs2 (PMap.get b2 CM) =
                ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents)))
        /\ (~Mem.perm m1' b2 ofs2 Cur Readable ->
                ZMap.get ofs2 (PMap.get b2 CM) =Undef))
    /\ fst CM !! b2 = Undef.

Lemma EI_ok: forall (m1 m2 m1':mem)
               (Ext12: Mem.extends m1 m2)
               (Fwd1: mem_forward m1 m1') m3 j
               (Inj23: Mem.inject j m2 m3)
               m3' (Fwd3: mem_forward m3 m3') j'
               (Inj13': Mem.inject j' m1' m3')
               (UnchOn3: Mem.unchanged_on (loc_out_of_reach j m1) m3 m3')
               (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
               (UnchOn1: Mem.unchanged_on (loc_unmapped j) m1 m1') m2'
               (NB: m2'.(Mem.nextblock)=m1'.(Mem.nextblock))
               (CONT: Content_EI_Property j m1 m1' m2 (m2'.(Mem.mem_contents)))
               (ACCESS: AccessMap_EI_Property j m1 m1' m2 (m2'.(Mem.mem_access))),
        mem_forward m2 m2' /\
               Mem.extends m1' m2' /\
               Mem.inject j' m2' m3' /\
               Mem.unchanged_on (loc_out_of_bounds m1) m2 m2' /\
               Mem.unchanged_on (loc_unmapped j) m2 m2'.
Proof. intros.
assert (VB' : forall b : block, Mem.valid_block m1' b = Mem.valid_block m2' b).
  intros; unfold Mem.valid_block. rewrite NB. trivial.
assert (Inj13:= Mem.extends_inject_compose _ _ _ _ Ext12 Inj23).
assert (MMU_LU: Mem.unchanged_on (loc_unmapped j) m2 m2' ).
   split. intros.
       destruct (ACCESS b) as [Val _].
        specialize (Val H0 k ofs). rewrite H in Val.
        rewrite (perm_subst _ _ _ _ _ _ _ Val). split; auto.
    intros. assert (Val2:= Mem.perm_valid_block _ _ _ _ _ H0).
        destruct (CONT b) as [ContVal _]. rewrite H in ContVal.
        apply (ContVal Val2 ofs).
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext12) in H.
        apply Fwd1 in H. destruct H as[H _]. rewrite <- VB'. apply H.
      (*max*)
      apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
           specialize (H2 Max ofs).
           remember (j b) as jb.
           destruct jb; apply eq_sym in Heqjb.
                destruct p0.
                apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                    rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                    unfold Mem.perm. rewrite po_oo in *.
                       eapply po_trans. apply (extends_permorder _ _ Ext12).
                       destruct (Fwd1 b). apply (Mem.perm_valid_block _ _ _ _ _ H2).
                       apply (H4 ofs _ H0).
                   rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. apply H0.
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in *. apply H0.
      exfalso. apply (H1 H).
assert (MMU_LOOB: Mem.unchanged_on (loc_out_of_bounds m1) m2 m2').
   split; intros.
      apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
         specialize (H2 k ofs).
         remember (j b) as jb.
         destruct jb; apply eq_sym in Heqjb.
              destruct p0.
              destruct H2 as [_ NoMax].
              rewrite (perm_subst _ _ _ _ _ _ _ (NoMax H)).
              split; auto.
         rewrite (perm_subst _ _ _ _ _ _ _ H2) in *.
           split; auto.
      contradiction.
  destruct (CONT b) as [ValC _].
       destruct (ACCESS b) as [ValA _].
       specialize (ValC (Mem.perm_valid_block _ _ _ _ _ H0) ofs).
       specialize (ValA (Mem.perm_valid_block _ _ _ _ _ H0) Cur ofs).
       unfold loc_out_of_bounds in H.
       remember (j b) as jb.
       destruct jb; apply eq_sym in Heqjb.
          destruct p.
          eapply (perm_split _ _ _ _ _ _ _ ValC); clear ValC; intros.
             exfalso. apply H. apply H1.
         apply H2.
      apply ValC.
split; trivial.
assert (Ext12':  Mem.extends m1' m2').
    split.
    (*nextblock*)
        rewrite NB. trivial.
    (*mem_inj*)
         assert (Perm12': forall b ofs k p, Mem.perm m1' b ofs k p ->
                                            Mem.perm m2' b ofs k p).
              intros.
              apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
                  assert (Val1: Mem.valid_block m1 b).
                     apply (Mem.valid_block_extends _ _ _ Ext12). apply H0.
                  assert (Perm1: Mem.perm m1 b ofs Max Nonempty).
                        apply Fwd1. apply Val1.
                        eapply Mem.perm_max. eapply Mem.perm_implies.
                        apply H. constructor.
                  specialize (H1 k ofs).
                  remember (j b) as jb.
                  destruct jb; apply eq_sym in Heqjb.
                     destruct p0.
                     apply (perm_split _ _ _ _ _ _ _ H1); clear H1; intros.
                        rewrite (perm_subst _ _ _ _ _ _ _ H2). assumption.
                      exfalso. apply (H1 Perm1). (*rewrite (perm_subst _ _ _ _ _ _ _ H2). assumption.*)
            rewrite (perm_subst _ _ _ _ _ _ _ H1) in *. clear H1.
                 destruct UnchOn1 as [UP _].
                 eapply (extends_perm _ _ Ext12).
                 rewrite (UP _ _ _ p Heqjb Val1). apply H.
             destruct (H1 k ofs) as [Val _]; clear H1.
                  assert (Perm1: Mem.perm m1' b ofs Max Nonempty).
                          eapply Mem.perm_max. eapply Mem.perm_implies.
                          apply H. constructor.
                  rewrite (perm_subst _ _ _ _ _ _ _ (Val Perm1)). assumption.
         split.
         (*mi_perm*) intros. inv H. rewrite Zplus_0_r.
                     apply (Perm12' _ _ _ _ H0).
         (*mi_align*) intros. inv H. apply Z.divide_0_r.
         (*mi_memval *) intros. inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [ContVal [ContInval Default]]; clear CONT.
            apply (valid_split _ _ _ _  (ACCESS b2)); clear ACCESS; intros.
                clear ContInval.
                assert (Perm: Mem.perm m1 b2 ofs Max Nonempty).
                    clear H1 ContVal. apply Fwd1.
                     apply (Mem.valid_block_extends _ _ _ Ext12). apply H.
                    eapply Mem.perm_max. eapply Mem.perm_implies.
                       apply H0. constructor.
               specialize (ContVal H ofs). specialize (H1 Cur ofs).
                  remember (j b2) as jb2.
                  destruct jb2; apply eq_sym in Heqjb2.
                          destruct p.
                          destruct ContVal as [Cont _]. rewrite (Cont Perm). clear Cont.
                          apply memval_inject_id_refl.
                  rewrite ContVal. clear ContVal.
                         destruct UnchOn1 as [UP UV].
                         apply (Mem.valid_block_extends _ _ _ Ext12) in H.
                         rewrite <- (UP _ _ _ _ Heqjb2 H) in H0.
                         rewrite (UV _ _ Heqjb2 H0).
                         specialize (Mem.mi_memval _ _ _ (Mem.mext_inj _ _
                                      Ext12) b2 ofs _ _ (eq_refl _) H0).
                         rewrite Zplus_0_r; trivial.
                assert (VB1':= Mem.perm_valid_block _ _ _ _ _ H0).
                destruct (ContInval H VB1' ofs) as [Cont _].
                  clear ContVal ContInval.
                  rewrite (Cont H0); clear Cont.
                  apply memval_inject_id_refl.
split; trivial.
assert (Inj23': Mem.inject j' m2' m3').
    assert (MI: Mem.mem_inj j' m2' m3').
        assert (MiPerm: forall b1 b2 delta ofs k p,  j' b1 = Some (b2, delta) ->
                       Mem.perm m2' b1 ofs k p ->
                       Mem.perm m3' b2 (ofs + delta) k p).
          intros.
          assert (NP: Mem.perm m2' b1 ofs Max Nonempty).
            eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor.
          apply (valid_split _ _ _ _  (ACCESS b1)); clear ACCESS; intros.
              assert (Val1: Mem.valid_block m1 b1).
                 apply (Mem.valid_block_extends _ _ _ Ext12). apply H1.
              assert (J: j b1 = Some (b2, delta)).
                  remember (j b1) as d. destruct d; apply eq_sym in Heqd.
                    destruct p0. rewrite (InjInc _ _ _ Heqd) in H.  apply H.
                  destruct (injSep _ _ _ Heqd H). exfalso. apply (H3 Val1).
              rewrite J in H2.
              destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
              specialize (H2 k ofs).
              apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                  clear Perm2'MaxNop.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                  eapply Inj13'. apply H. apply H0.
              clear Perm2'MaxP.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxNop H2)) in *;
                          clear Perm2'MaxNop.
                  destruct UnchOn3 as [U3Perm _].
                  assert (loc_out_of_reach j m1 b2 (ofs + delta)).
                        unfold loc_out_of_reach; intros. intros N.
                           destruct (eq_block b0 b1); subst.
                               rewrite H3 in J; inv J.
                               assert (ofs + delta - delta = ofs). omega.
                               rewrite H4 in N. apply (H2 N).
                           assert (N2: Mem.perm m2 b0 (ofs + delta - delta0)
                                       Max Nonempty).
                               specialize (Mem.mi_perm _ _ _ (Mem.mext_inj _ _  Ext12) b0 b0 Z0
                                                      (ofs + delta - delta0)). rewrite Zplus_0_r. intros.
                               apply (H4 _ _ (eq_refl _) N).
                           destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _
                                                 _ _ _ _ _ _ n H3 J N2 NP).
                              apply H4; trivial.
                              apply H4. omega.
                  assert (Val3:=Mem.valid_block_inject_2 _ _ _ _ _ _ J Inj23).
              rewrite <- (U3Perm _ _ _ p H3 Val3).
                eapply Inj23. apply J. apply H0.
          assert (NVal1: ~Mem.valid_block m1 b1). intros N. apply H1.
                 apply (Mem.valid_block_extends _ _ _ Ext12). apply N.
          assert (J: j b1 = None).
              remember (j b1) as d. destruct d; apply eq_sym in Heqd; trivial.
                  destruct p0. exfalso. apply H1.
                     apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
          destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
          specialize (H2 k ofs).
          apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
              clear Perm2'MaxNop.
              rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
              rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H2)) in NP;
                      clear Perm2'MaxP.
              eapply Inj13'. apply H. apply H0.
          clear Perm2'MaxP.
              unfold Mem.perm in NP.
              rewrite (Perm2'MaxNop H2) in NP. inv NP.
         (*end of proof of MiPerm*)
    split.
    (*mi_perm*) apply MiPerm.
    (*mi_align*)
       intros.
       apply (valid_split _ _ _ _  (ACCESS b1)); clear ACCESS; intros.
         specialize (H2 Max).
         remember (j b1) as q.
         destruct q; apply eq_sym in Heqq.
           destruct p0.
           assert (J':= InjInc _ _ _ Heqq). rewrite J' in H. inv H.
           assert (RNG: Mem.range_perm m2 b1 ofs (ofs + size_chunk chunk) Max p).
             intros z; intros.
             destruct (H2 z) as [Perm NoPerm].
             specialize (H0 _ H). clear H2.
             destruct (Mem.perm_dec m1 b1 z Max Nonempty).
               rewrite (perm_subst _ _ _ _ _ _ _ (Perm p0)) in *; clear Perm NoPerm.
                 eapply (extends_perm _ _ Ext12).
                 eapply Fwd1. eapply Mem.valid_block_inject_1. apply Heqq. eassumption.
                      assumption.
             rewrite (perm_subst _ _ _ _ _ _ _ (NoPerm n)) in *; clear Perm NoPerm.
               assumption.
           eapply Inj23. apply Heqq. eassumption.
         destruct (injSep _ _ _ Heqq H).
            exfalso. apply H3.
            eapply (Mem.valid_block_extends _ _ b1 Ext12). assumption.
       assert (RNG: Mem.range_perm m1' b1 ofs (ofs + size_chunk chunk) Max p).
             intros z; intros.
             destruct (H2 Max z) as [Perm NoPerm]. clear H2.
             specialize (H0 _ H3).
             destruct (Mem.perm_dec m1' b1 z Max Nonempty).
               rewrite (perm_subst _ _ _ _ _ _ _ (Perm p0)) in *; clear Perm NoPerm. assumption.
             unfold Mem.perm in H0. rewrite (NoPerm n) in H0. simpl in H0. intuition.
        eapply Inj13'. apply H. apply RNG.
       (*mi_memval *) intros.
           destruct (CONT b1) as [ContVal [ContInval Default]]; clear CONT.
           assert (NP: Mem.perm m2' b1 ofs Max Nonempty).
                   eapply Mem.perm_max. eapply Mem.perm_implies.
                   apply H0. constructor.
           apply (valid_split _ _ _ _  (ACCESS b1)); clear ACCESS; intros.
              clear ContInval.
              specialize (ContVal H1 ofs).
              apply (Mem.valid_block_extends _ _ _ Ext12) in H1.
              assert (J: j b1 = Some (b2, delta)).
                  remember (j b1) as d. destruct d; apply eq_sym in Heqd.
                    destruct p. rewrite (InjInc _ _ _ Heqd) in H.  apply H.
                  destruct (injSep _ _ _ Heqd H). exfalso. apply (H3 H1).
              rewrite J in ContVal. destruct ContVal as [ContPerm ContNoperm].
              rewrite J in H2.
              destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
              specialize (H2 Cur ofs).
              apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                  clear Perm2'MaxNop ContNoperm.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                  rewrite (ContPerm H2). clear ContPerm.
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H2)) in *;
                          clear Perm2'MaxP.
                  eapply Inj13'. apply H. apply H0.
              clear Perm2'MaxP ContPerm.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxNop H2)) in *;
                          clear Perm2'MaxNop.
                  rewrite (ContNoperm H2). clear ContNoperm.
                  destruct UnchOn3 as [U3Perm U3Val].
                  assert (loc_out_of_reach j m1 b2 (ofs + delta)).
                    unfold loc_out_of_reach; intros. intros N.
                       destruct (eq_block b0 b1); subst.
                           rewrite H3 in J; inv J.
                           assert (ofs + delta - delta = ofs). omega.
                           rewrite H4 in N. apply (H2 N).
                       assert (N2: Mem.perm m2 b0 (ofs + delta - delta0)
                                   Max Nonempty).
                          (*rewrite EP12. apply N. apply N.*)
                               specialize (Mem.mi_perm _ _ _ (Mem.mext_inj _ _  Ext12) b0 b0 Z0
                                                      (ofs + delta - delta0)). rewrite Zplus_0_r. intros.
                               apply (H4 _ _ (eq_refl _) N).
                       destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _
                                                   _ _ _ _ _ n H3 J N2 NP).
                              apply H4; trivial.
                              apply H4. omega.
              assert (Val3:=Mem.valid_block_inject_2 _ _ _ _ _ _ J Inj23).
              assert (Perm3:  Mem.perm m3 b2 (ofs+delta) Cur Readable).
                  eapply Inj23. apply J. apply H0.
            rewrite (U3Val _ _ H3 Perm3).
              eapply memval_inject_incr.
                 apply (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Inj23)
                                      _ _ _ _ J H0).
                   assumption.
           clear ContVal.
              assert (NVal1: ~Mem.valid_block m1 b1). intros N. apply H1.
                   apply (Mem.valid_block_extends _ _ _ Ext12). apply N.
              assert (J: j b1 = None).
                remember (j b1) as d.
                destruct d; apply eq_sym in Heqd; trivial.
                    destruct p. exfalso. apply H1.
                    apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
              destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
              assert (VB1': Mem.valid_block m1' b1).
                 rewrite VB'. apply (Mem.perm_valid_block _ _ _ _ _ H0).
              destruct (ContInval H1 VB1' ofs) as [ContPerm ContNoPerm];
                       clear ContInval.
              specialize (H2 Cur ofs).
              apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                  clear Perm2'MaxNop ContNoPerm.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H2)) in NP;
                          clear Perm2'MaxP.
                  rewrite (ContPerm H0); clear ContPerm.
                  eapply Inj13'. apply H. apply H0.
              clear Perm2'MaxP ContPerm.
                  unfold Mem.perm in NP.
                  rewrite (Perm2'MaxNop H2) in NP. inv NP.
    (*end of proof of MI: Mem.mem_inj j' m2' m3'*)
    split; intros.
        (*mi_inj*)
           apply MI.
        (*mi_freeblocks*)
           eapply Inj13'. rewrite VB'. apply H.
        (* mi_mappedblocks*)
           eapply Inj13'. apply H.
        (* mi_no_overlap*)
           intros b1 b1' delta1 b2 b2'; intros.
           remember (j b1) as jb1.
           destruct jb1; apply eq_sym in Heqjb1.
           (*j b = Some p*)
              destruct p. rewrite (InjInc _ _ _ Heqjb1) in H0. inv H0.
              assert (ValB1:=Mem.valid_block_inject_1 _ _ _ _ _ _ Heqjb1 Inj23).
              assert (Perm1: Mem.perm m2 b1 ofs1 Max Nonempty).
                     eapply Fwd2. apply ValB1. apply H2.
              remember (j b2) as jb2.
              destruct jb2; apply eq_sym in Heqjb2.
              (*j b2 = Some p*)
                 destruct p. rewrite (InjInc _ _ _ Heqjb2) in H1. inv H1.
                 assert (ValB2:= Mem.valid_block_inject_1 _ _ _ _ _ _
                                 Heqjb2 Inj23).
                 assert (Perm2: Mem.perm m2 b2 ofs2 Max Nonempty).
                    eapply Fwd2. apply ValB2. apply H3.
                 eapply (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ _ _ _
                                    _ _ H Heqjb1 Heqjb2 Perm1 Perm2).
              (*j b2 = None*)
                 destruct (injSep _ _ _ Heqjb2 H1).
                 left. intros N; subst.
                 apply H4.
                 apply (Mem.valid_block_inject_2 _ _ _ _ _ _ Heqjb1 Inj13).
           (*j b = None*)
              destruct (injSep _ _ _ Heqjb1 H0).
              remember (j b2) as jb2.
              destruct jb2; apply eq_sym in Heqjb2.
              (*j b2 = Some p*)
                 destruct p. rewrite (InjInc _ _ _ Heqjb2) in H1. inv H1.
                 left. intros N; subst.
                 apply H5.
                 apply (Mem.valid_block_inject_2 _ _ _ _ _ _ Heqjb2 Inj13).
              (*j b2 = None*)
                 destruct (injSep _ _ _ Heqjb2 H1).
                 apply (valid_split _ _ _ _  (ACCESS b1)); intros.
                     exfalso. apply H4.
                        apply (Mem.valid_block_extends _ _ _ Ext12). apply H8.
                 specialize (H9 Max ofs1).
                 apply (valid_split _ _ _ _  (ACCESS b2)); intros.
                     exfalso. apply H6.
                        apply (Mem.valid_block_extends _ _ _ Ext12). apply H10.
                 specialize (H11 Max ofs2).
                 apply (perm_split _ _ _ _ _ _ _ H9); clear H9; intros.
                    rewrite (perm_subst _ _ _ _ _ _ _ H12) in *; clear H12.
                    apply (perm_split _ _ _ _ _ _ _ H11); clear H11; intros.
                       rewrite (perm_subst _ _ _ _ _ _ _ H12) in *; clear H12.
                       eapply (Mem.mi_no_overlap _ _ _ Inj13' _ _ _
                                 _ _ _  _ _ H H0 H1 H2 H3).
                    unfold Mem.perm in H3. rewrite H12 in H3. inv H3.
                 unfold Mem.perm in H2. rewrite H12 in H2. inv H2.
        (*mi_representable*)
           apply (valid_split _ _ _ _  (ACCESS b)); intros.
           (*case valid*)
             assert (J: j b = Some (b', delta)).
               remember (j b) as d. destruct d; apply eq_sym in Heqd.
                 destruct p. rewrite (InjInc _ _ _ Heqd) in H.  apply H.
                 destruct (injSep _ _ _ Heqd H). exfalso.
                 apply (Mem.valid_block_extends _ _ _ Ext12) in H1. apply (H3 H1).
             (* weak_valid_pointer*)
             rewrite J in H2.
             destruct H0.
             (*location ofs*)
               specialize (H2 Max (Int.unsigned ofs)).
               apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                 rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                 eapply Inj13'. apply H. left. apply H0.
               rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                 eapply Inj23. apply J. left. apply H0.
             (*location ofs -1*)
               specialize (H2 Max (Int.unsigned ofs -1)).
               apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                 rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                 eapply Inj13'. apply H. right. apply H0.
               rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                 eapply Inj23. apply J. right. apply H0.
           (*case invalid*)
             assert (J: j b = None).
               remember (j b) as d. destruct d; apply eq_sym in Heqd; trivial.
                  destruct p. exfalso. apply H1.
                  apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
             (* weak_valid_pointer*)
             destruct H0.
             (*location ofs*)
               specialize (H2 Max (Int.unsigned ofs)).
               apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                 rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                 eapply Inj13'. apply H. left. apply H0.
               unfold Mem.perm in H0. rewrite H3 in H0. contradiction.
             (*location ofs -1*)
               specialize (H2 Max (Int.unsigned ofs -1)).
               apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                 rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. clear H3.
                 eapply Inj13'. apply H. right. apply H0.
               unfold Mem.perm in H0. rewrite H3 in H0. contradiction.
split; trivial.
split; trivial.
Qed.

Definition AccessMap_EI_FUN (j:meminj) (m1 m1' m2 : mem) (b2:block):
           Z -> perm_kind -> option permission :=
  if plt b2 (Mem.nextblock m2)
  then (fun ofs2 k =>
       match j b2 with
         None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
       | Some (b3,d3) =>
          if Mem.perm_dec m1 b2 ofs2 Max Nonempty
          then PMap.get b2 m1'.(Mem.mem_access) ofs2 k
          else PMap.get b2 m2.(Mem.mem_access) ofs2 k
        end)
  else (fun ofs2 k =>
         if Mem.perm_dec m1' b2 ofs2 Max Nonempty
         then PMap.get b2 m1'.(Mem.mem_access) ofs2 k
         else None).

Lemma mkAccessMap_EI_existsT: forall j (m1 m1' m2:Mem.mem)
       (VB : (Mem.nextblock m2 <= Mem.nextblock m1')%positive),
      { M : PMap.t (Z -> perm_kind -> option permission) |
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = AccessMap_EI_FUN j m1 m1' m2 b}.
Proof. intros.
  apply (pmap_construct_c _ (AccessMap_EI_FUN j m1 m1' m2)
              (Mem.nextblock m1') (fun ofs k => None)).
    intros. unfold AccessMap_EI_FUN.
    remember (plt n (Mem.nextblock m2)) as d.
    destruct d; clear Heqd; trivial.
       exfalso. xomega.
    extensionality ofs. extensionality k.
      destruct (Mem.perm_dec m1' n ofs Max Nonempty); trivial.
      apply Mem.perm_valid_block in p.
      exfalso. unfold Mem.valid_block in p. xomega.
Qed.

Definition ContentMap_EI_ValidBlock_FUN (j:meminj) m1 m1' m2 b2 ofs2: memval :=
             match j b2 with
               None => ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
             | Some (b3,delta3) =>
                  if Mem.perm_dec m1 b2 ofs2 Max Nonempty
                  then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
                  else ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
             end.

Definition ContentMap_EI_InvalidBlock_FUN m1' b2 ofs2: memval :=
    if Mem.perm_dec m1' b2 ofs2 Cur Readable
    then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
    else Undef.

Definition ContentMap_EI_Block_FUN j m1 m1' m2 b ofs : memval:=
  if plt b (Mem.nextblock m2)
  then ContentMap_EI_ValidBlock_FUN j m1 m1' m2 b ofs
  else ContentMap_EI_InvalidBlock_FUN m1' b ofs.

Lemma CM_block_EI_existsT: forall j (m1 m1' m2:Mem.mem) b,
      { M : ZMap.t memval |
          fst M = Undef /\
          forall ofs, ZMap.get ofs M =
                      ContentMap_EI_Block_FUN j m1 m1' m2 b ofs}.
Proof. intros.
  remember (zmap_finite_c _ (PMap.get b m1'.(Mem.mem_contents))) as LH1.
  apply eq_sym in HeqLH1. destruct LH1 as [lo1 hi1].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH1).
  intros Bounds1; clear HeqLH1.
  remember (zmap_finite_c _ (PMap.get b m2.(Mem.mem_contents))) as LH2.
  apply eq_sym in HeqLH2. destruct LH2 as [lo2 hi2].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH2).
  intros Bounds2; clear HeqLH2.
   assert (Undef2: fst (Mem.mem_contents m2) !! b = Undef). apply m2.
   assert (Undef1: fst (Mem.mem_contents m1') !! b = Undef). apply m1'.
   rewrite Undef2 in *. rewrite Undef1 in *. clear Undef1 Undef2.

  destruct (zmap_construct_c _ (ContentMap_EI_Block_FUN j m1 m1' m2 b)
             (Z.min lo1 lo2) (Z.max hi1 hi2) Undef) as [M PM].
    intros. unfold ContentMap_EI_Block_FUN; simpl.
        unfold ContentMap_EI_ValidBlock_FUN.
        unfold ContentMap_EI_InvalidBlock_FUN.
   rewrite Bounds1.
   rewrite Bounds2.
     destruct (plt b (Mem.nextblock m2)); trivial.
       destruct (j b); trivial.
         destruct p0.
         destruct (Mem.perm_dec m1 b n Max Nonempty); trivial.
     destruct (Mem.perm_dec m1' b n Cur Readable); trivial.

     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi1 hi2 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi1 hi2 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
  exists M. apply PM.
Qed.

Definition ContentsMap_EI_FUN (j:meminj) (m1 m1' m2:Mem.mem) (b:block):
            ZMap.t memval.
destruct (plt b (Mem.nextblock m1')).
  apply(CM_block_EI_existsT j m1 m1' m2 b).
  apply (ZMap.init Undef).
Defined.


Lemma ContentsMap_EI_existsT: forall (j:meminj) (m1 m1' m2:Mem.mem),
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M = ContentsMap_EI_FUN j m1 m1' m2 b}.
Proof. intros.
  apply (pmap_construct_c _ (ContentsMap_EI_FUN j m1 m1' m2)
              (Mem.nextblock m1') (ZMap.init Undef)).
    intros. unfold ContentsMap_EI_FUN. simpl.
    remember (plt n (Mem.nextblock m1')) as d.
    destruct d; clear Heqd; trivial.
      exfalso. xomega.
Qed.

Definition mkEI (j j': meminj) (m1 m2 m1':mem)
                (Ext12: Mem.extends m1 m2)
                (Fwd1: mem_forward m1 m1') m3
                (Inj23: Mem.inject j m2 m3)
                m3' (Fwd3: mem_forward m3 m3')
                (Inj13': Mem.inject j' m1' m3')
                (UnchOn3: Mem.unchanged_on (loc_out_of_reach j m1) m3 m3')
                (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                (UnchOn1: Mem.unchanged_on (loc_unmapped j) m1 m1')
             : Mem.mem'.
assert (VB: (Mem.nextblock m2 <= Mem.nextblock m1')%positive).
   destruct Ext12. rewrite <- mext_next.
   apply (forward_nextblock _ _ Fwd1).
destruct (mkAccessMap_EI_existsT j m1 m1' m2) as [AM [ADefault PAM]].
   assumption.
destruct (ContentsMap_EI_existsT j m1 m1' m2) as [CM [CDefault PCM]].
eapply Mem.mkmem with (nextblock:=m1'.(Mem.nextblock))
                      (mem_access:=AM)
                      (mem_contents:=CM).
  (*apply (mkContentsMap_EI_exists j m1 m1' m2).*)
(*  apply m1'.*)
  (*access_max*)
     intros. rewrite PAM. unfold AccessMap_EI_FUN.
     destruct (plt b (Mem.nextblock m2)).
     (*valid_block m2 b*)
        destruct (j b).
          destruct p0.
          destruct (Mem.perm_dec m1 b ofs Max Nonempty).
             apply m1'.
             apply m2.
        apply m2.
     (*~ valid_block m2 b*)
        destruct (Mem.perm_dec m1' b ofs Max Nonempty).
           apply m1'.
           reflexivity.
  (*nextblock_noaccess*)
    intros. rewrite PAM.
    unfold AccessMap_EI_FUN.
    destruct (plt b (Mem.nextblock m2)).
      exfalso. apply H; clear - VB p. xomega.
    destruct (Mem.perm_dec m1' b ofs Max Nonempty); trivial.
      exfalso. apply H. apply (Mem.perm_valid_block _ _ _ _ _ p).
  (*contents_default*)
    intros. rewrite PCM.
    unfold ContentsMap_EI_FUN.
    destruct (plt b (Mem.nextblock m1')).
     remember (CM_block_EI_existsT j m1 m1' m2 b).
     destruct s. apply a.
    reflexivity.
Defined.

Lemma interpolate_EI: forall (m1 m2 m1':mem)
                   (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
                   m3 j (Inj23: Mem.inject j m2 m3) m3'
                   (Fwd3: mem_forward m3 m3') j'
                   (Inj13': Mem.inject j' m1' m3')
                   (UnchOn3: Mem.unchanged_on (loc_out_of_reach j m1) m3 m3')
                   (InjInc: inject_incr j j')
                   (injSep: inject_separated j j' m1 m3)
                   (UnchOn1:  Mem.unchanged_on (loc_unmapped j) m1 m1'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\
                   Mem.inject j' m2' m3' /\
                   Mem.unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   Mem.unchanged_on (loc_unmapped j) m2 m2'.
Proof. intros.
  assert (VB: Mem.nextblock
    (mkEI j j' m1 m2 m1' Ext12 Fwd1 m3 Inj23 m3' Fwd3 Inj13' UnchOn3 InjInc
       injSep UnchOn1) = Mem.nextblock m1').
    unfold mkEI.
   destruct (mkAccessMap_EI_existsT j m1 m1' m2) as [AM [ADefault PAM]].
   simpl.
   destruct (ContentsMap_EI_existsT j m1 m1' m2) as [CM [CDefault PCM]].
   simpl. reflexivity.
  exists (mkEI j j' m1 m2 m1' Ext12 Fwd1 _ Inj23 _ Fwd3 Inj13'
              UnchOn3 InjInc injSep UnchOn1).
  apply (EI_ok m1 m2 m1' Ext12 Fwd1 _ _ Inj23 _ Fwd3 _ Inj13'
            UnchOn3 InjInc injSep UnchOn1
            (mkEI j j' m1 m2 m1' Ext12 Fwd1 m3 Inj23 m3' Fwd3
                  Inj13' UnchOn3 InjInc injSep UnchOn1)
            VB).
(*ContentMapOK*)
   unfold Content_EI_Property, mkEI.
   destruct (mkAccessMap_EI_existsT j m1 m1' m2) as [AM [ADef AP]]; simpl.
        destruct (ContentsMap_EI_existsT j m1 m1' m2) as [CM [CDef CP]]. simpl.
   intros.
   split; intros.
   (*valid_block m2 b*)
     rewrite CP. unfold ContentsMap_EI_FUN.
     destruct (CM_block_EI_existsT j m1 m1' m2 b2) as [CMb [CMbDef CMbP]]; simpl.
     destruct (plt b2 (Mem.nextblock m1')).
       remember (j b2).
       destruct o.
         destruct p0.
         rewrite CMbP.
         unfold ContentMap_EI_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)).
           unfold ContentMap_EI_ValidBlock_FUN.
           rewrite <- Heqo.
           destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
           split; intros; trivial. contradiction.
           split; intros; trivial. contradiction.
         contradiction.
       rewrite CMbP.
         unfold ContentMap_EI_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)); try contradiction.
         unfold ContentMap_EI_ValidBlock_FUN.
         rewrite <- Heqo. trivial.
    exfalso. apply n. apply Fwd1.
      rewrite Mem.valid_block_extends. apply H. assumption.
  split; intros.
     rewrite CP. unfold ContentsMap_EI_FUN.
     destruct (CM_block_EI_existsT j m1 m1' m2 b2) as [CMb [CMbDef CMbP]]; simpl.
     destruct (plt b2 (Mem.nextblock m1')); try contradiction.
     split; intros.
       rewrite CMbP. unfold ContentMap_EI_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)); try contradiction.
         unfold ContentMap_EI_InvalidBlock_FUN.
         destruct (Mem.perm_dec m1' b2 ofs2 Cur Readable); try contradiction.
         trivial.
       rewrite CMbP. unfold ContentMap_EI_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)); try contradiction.
         unfold ContentMap_EI_InvalidBlock_FUN.
         destruct (Mem.perm_dec m1' b2 ofs2 Cur Readable); try contradiction.
         trivial.
  (*default*)
     rewrite CP.
     unfold ContentsMap_EI_FUN.
     destruct ( plt b2 (Mem.nextblock m1')).
       destruct (CM_block_EI_existsT j m1 m1' m2 b2) as [CMb [CMbDef CMbP]]; simpl.
       assumption.
       reflexivity.
(*AccessMapOK*)
   unfold AccessMap_EI_Property, mkEI.
   destruct (mkAccessMap_EI_existsT j m1 m1' m2) as [AM [ADef AP]]; simpl.
        destruct (ContentsMap_EI_existsT j m1 m1' m2) as [CM [CDef CP]]. simpl.
   intros.
   split; intros.
   (*valid_block m2 b*)
     rewrite AP. unfold AccessMap_EI_FUN.
     destruct (plt b2 (Mem.nextblock m2)); try contradiction.
     destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
       remember (j b2).
       destruct o; trivial.
       destruct p1.
          split; intros; try contradiction. trivial.
     remember (j b2).
       destruct o; trivial.
       destruct p0.
          split; intros; try contradiction. trivial.

  (*invalid_block m2 b*)
   rewrite AP. unfold AccessMap_EI_FUN.
   destruct (plt b2 (Mem.nextblock m2)); try contradiction.
   destruct (Mem.perm_dec m1' b2 ofs2 Max Nonempty).
     split; intros; try contradiction. trivial.
     split; intros; try contradiction. trivial.
Qed.
