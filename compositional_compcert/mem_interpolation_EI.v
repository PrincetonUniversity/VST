Load loadpath.
(*CompCert imports*) 

Require Import Events. (*is needed for some definitions (loc_unmapped etc, and
  also at the very end of this file, in order to convert between the 
  tweaked and the standard definitions of mem_unchanged_on etc, and for
  being able to remove/add inject_permorder/extends_permorder etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.

Require Import compositional_compcert.mem_lemmas.
Require Import compositional_compcert.mem_interpolation_defs.

Definition AccessMap_EI_Property  (m1 m1' m2 : mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> forall k ofs2,
         (Mem.perm m1 b2 ofs2 Max Nonempty -> 
           ZMap.get b2 AM ofs2 k = ZMap.get b2 m1'.(Mem.mem_access) ofs2 k) 
       /\ (~Mem.perm m1 b2 ofs2 Max Nonempty -> 
           ZMap.get b2 AM ofs2 k  = ZMap.get b2 m2.(Mem.mem_access) ofs2 k))
  /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
         (Mem.perm m1' b2 ofs2 Max Nonempty ->
           ZMap.get b2 AM ofs2 k = ZMap.get b2 m1'.(Mem.mem_access) ofs2 k)
       /\ (~Mem.perm m1' b2 ofs2 Max Nonempty -> ZMap.get b2 AM ofs2 k = None)).

Definition Content_EI_Property (j:meminj) (m1 m1' m2:Mem.mem) 
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2, 
      (Mem.valid_block m2 b2 -> forall ofs2,
         (Mem.perm m1 b2 ofs2 Max Nonempty -> 
             match j b2 with
                 Some (b3,delta3) => ZMap.get ofs2 (ZMap.get b2 CM) =
                          ZMap.get ofs2 (ZMap.get b2 m1'.(Mem.mem_contents))
              | None => ZMap.get ofs2 (ZMap.get b2 CM) = 
                        ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents))
               end)
    /\ (~Mem.perm m1 b2 ofs2 Max Nonempty -> 
            ZMap.get ofs2 (ZMap.get b2 CM) = 
            ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents))))
  /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
           (Mem.perm m1' b2 ofs2 Max Nonempty ->
                ZMap.get ofs2 (ZMap.get b2 CM) =
                ZMap.get ofs2 (ZMap.get b2 m1'.(Mem.mem_contents)))
        /\ (~Mem.perm m1' b2 ofs2 Max Nonempty -> 
                ZMap.get ofs2 (ZMap.get b2 CM) =Undef)).

Lemma EI_ok: forall (m1 m2 m1':mem)
               (Ext12: Mem.extends m1 m2) (EP12: extends_perm_nonempty m1 m2)
               (Fwd1: mem_forward m1 m1') m3 j
               (Inj23: Mem.inject j m2 m3) (IP23: inject_perm_nonempty j m2 m3)
               m3' (Fwd3: mem_forward m3 m3') j'
               (Inj13': Mem.inject j' m1' m3')
               (IP13': inject_perm_nonempty j' m1' m3')
               (UnchOn3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
               (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
               (UnchOn1: my_mem_unchanged_on (loc_unmapped j) m1 m1')
               (WD1': mem_wd m1') 
               (WD2: mem_wd m2) (WD3': mem_wd m3') m2'
               (NB: m2'.(Mem.nextblock)=m1'.(Mem.nextblock))
               (CONT: Content_EI_Property j m1 m1' m2 (m2'.(Mem.mem_contents)))
               (ACCESS: AccessMap_EI_Property m1 m1' m2 (m2'.(Mem.mem_access))),
        mem_forward m2 m2' /\ 
               Mem.extends m1' m2' /\ extends_perm_nonempty m1' m2' /\
               Mem.inject j' m2' m3' /\  inject_perm_nonempty j' m2' m3' /\
               my_mem_unchanged_on (my_loc_out_of_bounds m1) m2 m2' /\
               my_mem_unchanged_on (loc_unmapped j) m2 m2' /\
               (mem_wd m2 -> mem_wd m2').
Proof. intros.
assert (VB: forall b, Mem.valid_block m1 b = Mem.valid_block m2 b).
     intros. apply prop_ext. apply (Mem.valid_block_extends _ _ b Ext12). 
assert (VB' : forall b : block, Mem.valid_block m1' b = Mem.valid_block m2' b).
  intros; unfold Mem.valid_block. rewrite NB. trivial.
assert (Inj13:= extends_inject_compose _ _ _ _ Ext12 Inj23).
assert (MMU_LU: my_mem_unchanged_on (loc_unmapped j) m2 m2' ).
   split; intros. 
       destruct (ACCESS b) as [Val _].
        specialize (Val H k ofs).
        apply (perm_split _ _ _ _ _ Val); clear Val; intros.
            rewrite (perm_subst _ _ _ _ _ _ _ H1) in *. clear H1. 
            rewrite <- VB in H.
            destruct UnchOn1 as [UPerm _].
                rewrite <- (UPerm _ _ _ HP H). eapply EP12. apply H0.
         rewrite (perm_subst _ _ _ _ _ _ _ H1) in *. trivial.
    assert (Val2:= Mem.perm_valid_block _ _ _ _ _ HMeperm).
        destruct (ACCESS b) as [Val _].
        specialize (Val Val2 Cur ofs).
        destruct (CONT b) as [ContVal _].
        destruct (ContVal Val2 ofs) as [ContValPerm ContValNoperm]; 
                  clear ContVal.
        apply (perm_split _ _ _ _ _ Val); clear Val; intros.
            clear ContValNoperm.
            specialize (ContValPerm H0). 
            rewrite HP in ContValPerm.
            rewrite ContValPerm; clear ContValPerm. trivial.
        clear  ContValPerm.
            rewrite (ContValNoperm H0). trivial.
assert (EP12': extends_perm_nonempty m1' m2').
      intros b2; intros.
      assert (Val2': Mem.valid_block m2' b2). 
             rewrite <-VB'. apply (Mem.perm_valid_block _ _ _ _ _ H).
      apply (valid_split _ _ _ _  (ACCESS b2)); clear ACCESS; intros.
           specialize (H1 k ofs).
           apply (perm_split _ _ _ _ _ H1); clear H1; intros.
              rewrite (perm_subst _ _ _ _ _ _ _ H2). trivial.
           exfalso. apply H1. apply Fwd1. rewrite VB. apply H0.  apply H.
      destruct (H1 k ofs) as [Val _]; clear H1.
              rewrite (perm_subst _ _ _ _ _ _ _ (Val H)). trivial.
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext12) in H. 
        apply Fwd1 in H. destruct H as[H _]. rewrite <- VB'. apply H. 
      (*max*)
      apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
           specialize (H2 Max ofs).
           apply (perm_split _ _ _ _ _ H2); clear H2; intros.
              rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. 
              rewrite EP12. apply Fwd1. rewrite VB; trivial. trivial.
                                      apply H2.
           rewrite (perm_subst _ _ _ _ _ _ _ H3) in *. apply H0. 
      exfalso. apply (H1 H).
assert (MMU_LOOB: my_mem_unchanged_on (my_loc_out_of_bounds m1) m2 m2'). 
   split; intros; destruct HP as [VB1 NE1].
      apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
           destruct (H1 k ofs) as [_ Inval]; clear H1.
           rewrite (perm_subst _ _ _ _ _ _ _ (Inval NE1)). trivial.
      exfalso. apply (H0 H).
  destruct (CONT b) as [Val _].
      destruct (Val (Mem.perm_valid_block _ _ _ _ _ HMeperm) ofs)
               as [_ NoPerm]; clear Val.
      rewrite (NoPerm NE1). assumption.
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
                  assert (Val1: Mem.valid_block m1 b). rewrite VB. trivial.
                  assert (Perm1: Mem.perm m1 b ofs Max Nonempty).
                        apply Fwd1. apply Val1.
                        eapply Mem.perm_max. eapply Mem.perm_implies.
                        apply H. constructor.
                  destruct (H1 k ofs) as [Val _]; clear H1.
                     rewrite (perm_subst _ _ _ _ _ _ _ (Val Perm1)). assumption.
             destruct (H1 k ofs) as [Val _]; clear H1.
                  assert (Perm1: Mem.perm m1' b ofs Max Nonempty). 
                          eapply Mem.perm_max. eapply Mem.perm_implies.
                          apply H. constructor.
                  rewrite (perm_subst _ _ _ _ _ _ _ (Val Perm1)). assumption.
         split. 
         (*mi_perm*) intros. inv H. rewrite Zplus_0_r. 
                     apply (Perm12' _ _ _ _ H0). 
         (*mi_access*) unfold Mem.valid_access; intros. 
             destruct H0. inv H. rewrite Zplus_0_r.
             split; trivial. 
             intros off Hoff. specialize (H0 _ Hoff). 
             apply (Perm12' _ _ _ _ H0). 
         (*mi_memval *) intros. inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [ContVal ContInval]; clear CONT.
            apply (valid_split _ _ _ _  (ACCESS b2)); clear ACCESS; intros.
                clear ContInval.
                destruct (ContVal H ofs) as [ContVperm ContVNoPerm];
                         clear ContVal.
                specialize (H1 Cur ofs).
                apply (perm_split _ _ _ _ _ H1); clear H1; intros.
                     clear  ContVNoPerm.
                     specialize (ContVperm H1).
                     remember (j b2) as jb.
                     destruct jb; apply eq_sym in Heqjb.
                         destruct p. rewrite ContVperm. 
                                     apply memval_inject_id_refl.
                     rewrite ContVperm; clear ContVperm.
                         destruct UnchOn1 as [U1Perm U1Val].
                         assert (Val1:= Mem.perm_valid_block _ _ _ _ _ H1).
                         assert (Perm1Cur:  Mem.perm m1 b2 ofs Cur Readable).
                             rewrite U1Perm. apply H0. apply Heqjb. apply Val1.
                         specialize (Mem.mi_memval _ _ _ (Mem.mext_inj _ _ 
                                      Ext12) b2 ofs _ _ (eq_refl _) Perm1Cur).
                         rewrite Zplus_0_r; intros.
                         rewrite (U1Val _ _ Heqjb Perm1Cur _ (eq_refl _)).
                         apply H3.
                   clear  ContVperm ContVNoPerm H2.
                        exfalso. apply H1; clear H1.
                        apply Fwd1. rewrite VB. apply H. eapply Mem.perm_max. 
                                    eapply Mem.perm_implies. apply H0.
                                    constructor.
             clear ContVal H1.
                destruct (ContInval H ofs) as [ContVperm _]; clear ContInval.
                rewrite ContVperm. apply memval_inject_id_refl.
                       eapply Mem.perm_max. eapply Mem.perm_implies.
                       apply H0. constructor.
split; trivial.
split; trivial.
assert (IP23': inject_perm_nonempty j' m2' m3').
    intros b; intros.
    apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
        assert (Val1: Mem.valid_block m1 b). rewrite VB. trivial.
        assert (J: j b = Some (b2, delta)).
            remember (j b) as d. destruct d; apply eq_sym in Heqd. 
              destruct p. rewrite (InjInc _ _ _ Heqd) in F.  apply F. 
            destruct (injSep _ _ _ Heqd F). exfalso. apply (H1 Val1).
        destruct (H0 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
        specialize (H0 k ofs).
        apply (perm_split _ _ _ _ _ H0); clear H0; intros.
            clear Perm2'MaxNop.
            rewrite (perm_subst _ _ _ _ _ _ _ H1); clear H1. 
            rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H0))
               in NP; clear Perm2'MaxP.
            apply IP13'. apply NP. apply F.
        clear Perm2'MaxP.
            rewrite (perm_subst _ _ _ _ _ _ _ H1); clear H1. 
            rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxNop H0)) 
               in NP; clear Perm2'MaxNop.
            destruct UnchOn3 as [U3Perm _].
            assert (loc_out_of_reach j m1 b2 (ofs + delta)).
                unfold loc_out_of_reach; intros. intros N.
                   destruct (eq_block b0 b); subst.
                       rewrite H1 in J; inv J.
                       assert (ofs + delta - delta = ofs). omega.
                       rewrite H2 in N. apply (H0 N).
                   assert (N2:Mem.perm m2 b0 (ofs+delta-delta0) Max Nonempty).
                      rewrite EP12. apply N. apply N.
                   destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ _ _ _ _ _ 
                                               n H1 J N2 NP).
                        apply H2; trivial.
                        apply H2. omega.
            assert (Val3: Mem.valid_block m3 b2). 
                apply (Mem.valid_block_inject_2 _ _ _ _ _ _ J Inj23).
            rewrite <- (U3Perm _ _ _ H1 Val3).
            apply IP23. apply NP. apply J.
   assert (NVal1: ~Mem.valid_block m1 b). rewrite VB. trivial.
        assert (J: j b = None).
            remember (j b) as d. destruct d; apply eq_sym in Heqd; trivial. 
              destruct p. exfalso. apply H. 
                       apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
        destruct (H0 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
        specialize (H0 k ofs).
        apply (perm_split _ _ _ _ _ H0); clear H0; intros.
            clear Perm2'MaxNop.
            rewrite (perm_subst _ _ _ _ _ _ _ H1); clear H1. 
            rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H0)) in NP; 
                    clear Perm2'MaxP.
            apply IP13'. apply NP. apply F.
        clear Perm2'MaxP.
            unfold Mem.perm in NP. rewrite (Perm2'MaxNop H0) in NP. inv NP. 
assert (Inj23': Mem.inject j' m2' m3').
    assert (MI: Mem.mem_inj j' m2' m3').
        assert (MiPerm: forall b1 b2 delta ofs k p,  j' b1 = Some (b2, delta) ->
                       Mem.perm m2' b1 ofs k p -> 
                       Mem.perm m3' b2 (ofs + delta) k p).
          intros.
          assert (NP: Mem.perm m2' b1 ofs Max Nonempty).
            eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor.
          apply (valid_split _ _ _ _  (ACCESS b1)); clear ACCESS; intros.
              assert (Val1: Mem.valid_block m1 b1). rewrite VB. trivial.
              assert (J: j b1 = Some (b2, delta)).
                  remember (j b1) as d. destruct d; apply eq_sym in Heqd. 
                    destruct p0. rewrite (InjInc _ _ _ Heqd) in H.  apply H. 
                  destruct (injSep _ _ _ Heqd H). exfalso. apply (H3 Val1).
              destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
              specialize (H2 k ofs).
              apply (perm_split _ _ _ _ _ H2); clear H2; intros.
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
                              rewrite EP12. apply N. apply N.
                           destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _
                                                 _ _ _ _ _ _ n H3 J N2 NP).
                              apply H4; trivial.
                              apply H4. omega.
                  assert (Val3:=Mem.valid_block_inject_2 _ _ _ _ _ _ J Inj23).
              rewrite <- (U3Perm _ _ _ H3 Val3).
              rewrite (IP23 b1). apply H0.  apply NP. apply J.
          assert (NVal1: ~Mem.valid_block m1 b1). rewrite VB. trivial.
          assert (J: j b1 = None).
              remember (j b1) as d. destruct d; apply eq_sym in Heqd; trivial.
                  destruct p0. exfalso. apply H1.
                     apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
          destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
          specialize (H2 k ofs).
          apply (perm_split _ _ _ _ _ H2); clear H2; intros.
              clear Perm2'MaxNop.
              rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3. 
              rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H2)) in NP; 
                      clear Perm2'MaxP.
              rewrite (IP13' b1). apply H0. apply NP. apply H.
          clear Perm2'MaxP.
              unfold Mem.perm in NP. 
              rewrite (Perm2'MaxNop H2) in NP. inv NP. 
         (*end of proof of MiPerm*)
    split. 
    (*mi_perm*) apply MiPerm.
    (*mi_access*)
       intros. destruct H0.
       split; intros.
       (*range_perm*) intros off Hoff. 
           assert (HoffDelta: ofs <= off - delta < ofs + size_chunk chunk). 
                    omega. 
           specialize (H0 _ HoffDelta).
           specialize (MiPerm _ _ _ _ _ _ H H0).
           assert (off - delta + delta = off). omega.
           rewrite H2 in MiPerm. apply MiPerm.
       (*align*)  
           eapply inject_aligned_ofs. 
           apply (inj_implies_inject_aligned _ _ _ Inj13'). apply H. apply H1.
       (*mi_memval *) intros.
           destruct (CONT b1) as [ContVal ContInval]; clear CONT.
           assert (NP: Mem.perm m2' b1 ofs Max Nonempty).
                   eapply Mem.perm_max. eapply Mem.perm_implies. 
                   apply H0. constructor.
           apply (valid_split _ _ _ _  (ACCESS b1)); clear ACCESS; intros.
              clear ContInval.
              destruct (ContVal H1 ofs) as [ContPerm ContNoPerm]; clear ContVal.
              assert (Val1: Mem.valid_block m1 b1). rewrite VB. trivial.
              assert (J: j b1 = Some (b2, delta)).
                  remember (j b1) as d. destruct d; apply eq_sym in Heqd. 
                    destruct p. rewrite (InjInc _ _ _ Heqd) in H.  apply H. 
                  destruct (injSep _ _ _ Heqd H). exfalso. apply (H3 Val1).
              rewrite J in ContPerm.
              destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
              specialize (H2 Cur ofs).
              apply (perm_split _ _ _ _ _ H2); clear H2; intros.
                  clear Perm2'MaxNop ContNoPerm.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                  rewrite (ContPerm H2). clear ContPerm. 
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H2)) in *; 
                          clear Perm2'MaxP.
                  eapply Inj13'. apply H. apply H0.
              clear Perm2'MaxP ContPerm.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3. 
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxNop H2)) in *; 
                          clear Perm2'MaxNop.
                  rewrite (ContNoPerm H2). clear ContNoPerm. 
                  destruct UnchOn3 as [U3Perm U3Val].
                  assert (loc_out_of_reach j m1 b2 (ofs + delta)).
                    unfold loc_out_of_reach; intros. intros N.
                       destruct (eq_block b0 b1); subst.
                           rewrite H3 in J; inv J. 
                           assert (ofs + delta - delta = ofs). omega.
                           rewrite H4 in N. apply (H2 N).
                       assert (N2: Mem.perm m2 b0 (ofs + delta - delta0) 
                                   Max Nonempty).
                          rewrite EP12. apply N. apply N.
                       destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ 
                                                   _ _ _ _ _ n H3 J N2 NP).
                              apply H4; trivial.
                              apply H4. omega.
              assert (Val3:=Mem.valid_block_inject_2 _ _ _ _ _ _ J Inj23).
              assert (Perm3:  Mem.perm m3 b2 (ofs+delta) Cur Readable).
                    rewrite (IP23 b1). apply H0. apply NP. apply J.
              rewrite (U3Val _ _ H3 Perm3 _ (eq_refl _)).
              eapply memval_inject_incr.
                 apply (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Inj23) 
                                      _ _ _ _ J H0).
                   assumption. 
           clear ContVal. 
              assert (NVal1: ~Mem.valid_block m1 b1). rewrite VB. trivial.
              assert (J: j b1 = None).
                remember (j b1) as d. 
                destruct d; apply eq_sym in Heqd; trivial. 
                    destruct p. exfalso. apply H1.
                    apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
              destruct (H2 Max ofs) as [Perm2'MaxP Perm2'MaxNop].
              destruct (ContInval H1 ofs) as [ContPerm ContNoPerm]; 
                       clear ContInval.
              specialize (H2 Cur ofs).
              apply (perm_split _ _ _ _ _ H2); clear H2; intros.
                  clear Perm2'MaxNop ContNoPerm.
                  rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3. 
                  rewrite (perm_subst _ _ _ _ _ _ _ (Perm2'MaxP H2)) in NP; 
                          clear Perm2'MaxP.
                  rewrite (ContPerm H2); clear ContPerm.
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
                     exfalso. rewrite <- VB in H8. apply (H4 H8).
                 specialize (H9 Max ofs1).
                 apply (valid_split _ _ _ _  (ACCESS b2)); intros.
                     exfalso. rewrite <- VB in H10. apply (H6 H10).
                 specialize (H11 Max ofs2).
                 apply (perm_split _ _ _ _ _ H9); clear H9; intros.
                    rewrite (perm_subst _ _ _ _ _ _ _ H12) in *; clear H12.
                    apply (perm_split _ _ _ _ _ H11); clear H11; intros.
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
                 destruct p0. rewrite (InjInc _ _ _ Heqd) in H.  apply H.   
                 destruct (injSep _ _ _ Heqd H). exfalso. 
                 rewrite VB in H3. apply (H3 H1).
             specialize (H2 k (Int.unsigned ofs)).
             apply (perm_split _ _ _ _ _ H2); clear H2; intros.
                   rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                   eapply Inj13'. apply H. apply H0.
             rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                       eapply Inj23. apply J. apply H0.
           (*case invalid*)
             assert (J: j b = None).
               remember (j b) as d. destruct d; apply eq_sym in Heqd; trivial. 
                  destruct p0. exfalso. apply H1.
                  apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
             specialize (H2 k (Int.unsigned ofs)).
             apply (perm_split _ _ _ _ _ H2); clear H2; intros.
                 rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                     eapply Inj13'. apply H. apply H0.
             unfold Mem.perm in H0. rewrite H3 in H0. inv H0.
split; trivial.
split; trivial.
split; trivial.
split; trivial.
(*mem_wd m2'*) intros.
    apply mem_wdI. intros.
    remember ((ZMap.get ofs (ZMap.get b (Mem.mem_contents m2')))) as v.
    destruct v; try econstructor.
    apply flatinj_I.
      destruct (CONT b) as [ContVal ContInval].
      apply (valid_split _ _ _ _  (ACCESS b)); intros.
      (*case valid*)
          clear ContInval.
          destruct (ContVal H0 ofs) as [ContPerm ContNoperm]; clear ContVal.
          specialize (H1 Cur ofs).
          apply (perm_split _ _ _ _ _ H1); clear H1; intros.
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
            clear ContNoperm.
            specialize (ContPerm H1).
            remember (j b) as jb.
            destruct jb.
               destruct p. rewrite ContPerm in Heqv; clear ContPerm.
                  unfold Mem.valid_block in VB'. 
                  rewrite <-  VB'. unfold mem_wd in WD1'.
                  assert (X: Mem.flat_inj (Mem.nextblock m1') b = Some (b, Z0)).
                     apply flatinj_I. apply eq_sym in Heqjb. apply Fwd1.
                     apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqjb Inj13).
                  destruct WD1'. specialize (mi_memval b ofs _ _ X R). 
                  rewrite Zplus_0_r in mi_memval. 
                  rewrite <- Heqv in mi_memval.
                  clear X Heqv. inversion mi_memval. clear H8. 
                  subst. apply flatinj_E in H4. apply H4.
            rewrite ContPerm in Heqv; clear ContPerm.
                  assert (X: Mem.flat_inj (Mem.nextblock m2) b = Some (b, Z0)).
                                   apply flatinj_I. apply H0.
                  assert (R2: Mem.perm m2 b ofs Cur Readable).
                     rewrite EP12; try apply H1.
                     destruct UnchOn1 as [U1Perm _]. 
                     rewrite U1Perm. apply R. 
                     unfold loc_unmapped. rewrite Heqjb. trivial.
                     apply (Mem.perm_valid_block _ _ _ _ _ H1).
                  destruct WD2. specialize (mi_memval b ofs _ _ X R2). 
                  rewrite Zplus_0_r in mi_memval. rewrite <- Heqv in mi_memval.
                  clear X Heqv. inversion mi_memval. clear H8. 
                  subst. apply flatinj_E in H4.
                  apply Fwd2.  apply H4.
          clear ContPerm.
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
            rewrite (ContNoperm H1) in Heqv; clear ContNoperm.
            assert (X: Mem.flat_inj (Mem.nextblock m2) b = Some (b, Z0)).
                       apply flatinj_I. apply H0.
            destruct WD2. specialize (mi_memval b ofs _ _ X R). 
            rewrite Zplus_0_r in mi_memval. rewrite <- Heqv in mi_memval.
            clear X Heqv. inversion mi_memval. clear H8. subst. 
            apply flatinj_E in H4.
            apply Fwd2. apply H4.
      clear ContVal.
        destruct (ContInval H0 ofs) as [ContPerm ContNoperm]; clear ContInval.
        specialize (H1 Cur ofs).
        apply (perm_split _ _ _ _ _ H1); clear H1; intros.
           rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
           clear ContNoperm.
           rewrite (ContPerm H1) in Heqv; clear ContPerm.
           assert (X: Mem.flat_inj (Mem.nextblock m1') b = Some (b, Z0)).
                  apply flatinj_I. apply (Mem.perm_valid_block _ _ _ _ _ H1).
           destruct WD1'. specialize (mi_memval b ofs _ _ X R). 
           rewrite Zplus_0_r in mi_memval. rewrite <- Heqv in mi_memval.
           clear X Heqv. inversion mi_memval. clear H8. subst. 
           apply flatinj_E in H4. 
           unfold Mem.valid_block in VB'. rewrite <- VB'. apply H4.
           unfold Mem.perm in R. rewrite H2 in R. inv R.
    rewrite Int.add_zero. trivial.
Qed.

Parameter mkAccessMap_EI_exists:  forall  (m1 m1' m2:Mem.mem), 
          ZMap.t (Z -> perm_kind -> option permission).
Axiom mkAccessMap_EI_ok: forall  (m1 m1' m2:Mem.mem), 
      AccessMap_EI_Property m1 m1' m2 (mkAccessMap_EI_exists m1 m1' m2).

Parameter mkContentsMap_EI_exists: 
           forall (j :meminj) (m1 m1' m2:Mem.mem), ZMap.t (ZMap.t memval).
Axiom mkContentsMap_EI_ok: forall j m1 m1' m2, 
      Content_EI_Property j m1 m1' m2 (mkContentsMap_EI_exists j m1 m1' m2).

Definition mkEI (j j': meminj) (m1 m2 m1':mem)
                (Ext12: Mem.extends m1 m2) (EP12: extends_perm_nonempty m1 m2)
                (Fwd1: mem_forward m1 m1') m3 
                (Inj23: Mem.inject j m2 m3) (IP23: inject_perm_nonempty j m2 m3)
                m3' (Fwd3: mem_forward m3 m3') 
                (Inj13': Mem.inject j' m1' m3')
                (IP13': inject_perm_nonempty j' m1' m3')
                (UnchOn3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                (UnchOn1: my_mem_unchanged_on (loc_unmapped j) m1 m1')
                (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3': mem_wd m3')
             : Mem.mem'.
eapply Mem.mkmem with (nextblock:=m1'.(Mem.nextblock))
                      (mem_access:=mkAccessMap_EI_exists m1 m1' m2).
  apply (mkContentsMap_EI_exists j m1 m1' m2).
  apply m1'.
  (*access_max*)
     intros. specialize (mkAccessMap_EI_ok m1 m1' m2 b). intros.
     apply (valid_split _ _ _ _  H); clear H; intros.
     (*valid_block m2 b*)
         destruct (H0 Max ofs) as [MaxPerm MaxNoPerm].
         apply (perm_split _ _ _ _ _ (H0 Cur ofs)); clear H0; intros.
              clear MaxNoPerm.
                 rewrite H1 in *; clear H1.
                 rewrite (MaxPerm H0). apply m1'.
          clear MaxPerm. 
                 rewrite H1 in *; clear H1.
                 rewrite (MaxNoPerm H0). apply m2.
     (*~ valid_block m2 b*)
         destruct (H0 Max ofs) as [MaxPerm MaxNoPerm].
         apply (perm_split _ _ _ _ _ (H0 Cur ofs)); clear H0; intros.
              clear MaxNoPerm.
                 rewrite H1 in *; clear H1.
                 rewrite (MaxPerm H0). apply m1'.
          clear MaxPerm. 
                 rewrite H1 in *; clear H1.
                 rewrite (MaxNoPerm H0). constructor.
  (*nextblock_noaccess*)
    intros. 
    assert (NV1' : ~ Mem.valid_block m1' b). apply H.
    assert (NV1 : ~ Mem.valid_block m1 b). intros N. destruct (Fwd1 _ N). apply (NV1' H0).
    destruct (mkAccessMap_EI_ok m1 m1' m2 b) as [_ Inval].
     assert (NVB2: ~ Mem.valid_block m2 b). 
        intros N. apply NV1. 
        apply (Mem.valid_block_extends _ _ b Ext12). apply N.
     specialize (Inval NVB2 k ofs).
     apply (perm_split _ _ _ _ _ Inval); clear Inval; intros.
          rewrite H1. apply m1'.  apply H.
          rewrite H1. trivial.
Defined.

Lemma my_interpolate_EI: forall (j j': meminj) (m1 m2 m1':mem)
                (Ext12: Mem.extends m1 m2) (EP12: extends_perm_nonempty m1 m2)
                (Fwd1: mem_forward m1 m1') m3 
                (Inj23: Mem.inject j m2 m3) (IP23: inject_perm_nonempty j m2 m3)
                m3' (Fwd3: mem_forward m3 m3') 
                (Inj13': Mem.inject j' m1' m3') 
                (IP13': inject_perm_nonempty j' m1' m3')
                (UnchOn3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                (UnchOn1: my_mem_unchanged_on (loc_unmapped j) m1 m1')
                (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3': mem_wd m3'),
    exists m2', mem_forward m2 m2' /\
                Mem.extends m1' m2' /\  extends_perm_nonempty m1' m2' /\
                Mem.inject j' m2' m3' /\  inject_perm_nonempty j' m2' m3' /\
                my_mem_unchanged_on (my_loc_out_of_bounds m1) m2 m2' /\
                my_mem_unchanged_on (loc_unmapped j) m2 m2' /\
                (mem_wd m2 -> mem_wd m2').
Proof. intros. 
  exists (mkEI j j' m1 m2 m1' Ext12 EP12 Fwd1 _ Inj23 IP23 _ Fwd3 Inj13' IP13'
              UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3'). 
  apply (EI_ok m1 m2 m1' Ext12 EP12 Fwd1 _ _ Inj23 IP23 _ Fwd3 _ Inj13' IP13'
            UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3' 
            (mkEI j j' m1 m2 m1' Ext12 EP12 Fwd1 m3 Inj23 IP23 m3' Fwd3 
                  Inj13' IP13' UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3')
            (eq_refl _)).
   apply mkContentsMap_EI_ok.  apply mkAccessMap_EI_ok.
Qed.

Lemma interpolate_EI: forall (m1 m2 m1':mem) 
                   (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
                   m3 j (Inj23: Mem.inject j m2 m3) m3' 
                   (Fwd3: mem_forward m3 m3') j'
                   (Inj13': Mem.inject j' m1' m3')
                   (UnchOn3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                   (InjInc: inject_incr j j')
                   (injSep: inject_separated j j' m1 m3)
                   (UnchOn1: mem_unchanged_on (loc_unmapped j) m1 m1')
                   (WD1':mem_wd m1') (WD2: mem_wd m2) (WD3': mem_wd m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ 
                   Mem.inject j' m2' m3' /\ 
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   mem_unchanged_on (loc_unmapped j) m2 m2' /\
                   (mem_wd m2 -> mem_wd m2').
Proof. intros. rewrite <- unchAx in UnchOn3.  rewrite <- unchAx in UnchOn1. 
  assert (EP12 := ext_implies_extends_perm_nonenempty _ _ Ext12).
  assert (IP23 := inj_implies_inject_perm_nonenempty _ _ _ Inj23).
  assert (IP13' := inj_implies_inject_perm_nonenempty _ _ _ Inj13').
  destruct (my_interpolate_EI _ _ _ _ _ Ext12 EP12 Fwd1 _ Inj23 IP23 _ 
              Fwd3 Inj13' IP13' UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3')
    as [m2' [Fwd2 [Ext12' [_ [Inj23' [_ [UnchLoob22 [UnchLU22 WD2']]]]]]]].
  rewrite unchAx in *. rewrite loobAx in *.
  exists m2'. repeat (split; trivial).
Qed.