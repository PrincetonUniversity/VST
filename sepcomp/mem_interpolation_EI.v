Load loadpath.

Require Import Events. (*is needed for some definitions (loc_unmapped etc, and
  also at the very end of this file, in order to convert between the 
  tweaked and the standard definitions of mem_unchanged_on etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolation_defs.

Definition AccessMap_EI_Property (j:meminj) (m1 m1' m2 : mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> forall k ofs2,
       match j b2 with 
         None => ZMap.get b2 AM ofs2 k  = 
                        ZMap.get b2 m2.(Mem.mem_access) ofs2 k
       | Some (b3,d3) =>
          (Mem.perm m1 b2 ofs2 Max Nonempty -> 
           ZMap.get b2 AM ofs2 k = ZMap.get b2 m1'.(Mem.mem_access) ofs2 k) 
       /\ (~Mem.perm m1 b2 ofs2 Max Nonempty -> 
           ZMap.get b2 AM ofs2 k  = ZMap.get b2 m2.(Mem.mem_access) ofs2 k)
     end)
  /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
         (Mem.perm m1' b2 ofs2 Max Nonempty ->
           ZMap.get b2 AM ofs2 k = ZMap.get b2 m1'.(Mem.mem_access) ofs2 k)
       /\ (~Mem.perm m1' b2 ofs2 Max Nonempty -> ZMap.get b2 AM ofs2 k = None)).

Definition Content_EI_Property (j:meminj) (m1 m1' m2:Mem.mem) 
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2, 
      (Mem.valid_block m2 b2 -> forall ofs2,
             match j b2 with
               None =>  ZMap.get ofs2 (ZMap.get b2 CM) =
                           ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents))
             | Some (b3,delta3) => 
                     (Mem.perm m1 b2 ofs2 Max Nonempty ->
                            ZMap.get ofs2 (ZMap.get b2 CM) =
                           ZMap.get ofs2 (ZMap.get b2 m1'.(Mem.mem_contents)))
                 /\ (~Mem.perm m1 b2 ofs2 Max Nonempty -> 
                          ZMap.get ofs2 (ZMap.get b2 CM) = 
                         ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents)))
            end)
  /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
           (Mem.perm m1' b2 ofs2 Cur Readable ->
                ZMap.get ofs2 (ZMap.get b2 CM) =
                ZMap.get ofs2 (ZMap.get b2 m1'.(Mem.mem_contents)))
        /\ (~Mem.perm m1' b2 ofs2 Cur Readable -> 
                ZMap.get ofs2 (ZMap.get b2 CM) =Undef)).

Lemma EI_ok: forall (m1 m2 m1':mem)
               (Ext12: Mem.extends m1 m2)
               (Fwd1: mem_forward m1 m1') m3 j
               (Inj23: Mem.inject j m2 m3)
               m3' (Fwd3: mem_forward m3 m3') j'
               (Inj13': Mem.inject j' m1' m3')
               (UnchOn3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
               (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
               (UnchOn1: my_mem_unchanged_on (loc_unmapped j) m1 m1')
               (WD1': mem_wd m1') 
               (WD2: mem_wd m2) (WD3': mem_wd m3') m2'
               (NB: m2'.(Mem.nextblock)=m1'.(Mem.nextblock))
               (CONT: Content_EI_Property j m1 m1' m2 (m2'.(Mem.mem_contents)))
               (ACCESS: AccessMap_EI_Property j m1 m1' m2 (m2'.(Mem.mem_access))),
        mem_forward m2 m2' /\ 
               Mem.extends m1' m2' /\ 
               Mem.inject j' m2' m3' /\ 
               my_mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
               my_mem_unchanged_on (loc_unmapped j) m2 m2' /\
               (mem_wd m2 -> mem_wd m2').
Proof. intros.
assert (VB' : forall b : block, Mem.valid_block m1' b = Mem.valid_block m2' b).
  intros; unfold Mem.valid_block. rewrite NB. trivial.
assert (Inj13:= extends_inject_compose _ _ _ _ Ext12 Inj23).
assert (MMU_LU: my_mem_unchanged_on (loc_unmapped j) m2 m2' ).
   split. intros. 
       destruct (ACCESS b) as [Val _].
        specialize (Val H k ofs). rewrite HP in Val.
        rewrite (perm_subst _ _ _ _ _ _ _ Val). trivial.
    intros. assert (Val2:= Mem.perm_valid_block _ _ _ _ _ HMeperm).
        destruct (CONT b) as [ContVal _]. rewrite HP in ContVal.
        rewrite (ContVal Val2 ofs). apply H. 
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
assert (MMU_LOOB: my_mem_unchanged_on (loc_out_of_bounds m1) m2 m2'). 
   split; intros.
      apply (valid_split _ _ _ _  (ACCESS b)); clear ACCESS; intros.
         specialize (H1 k ofs).
         remember (j b) as jb.
         destruct jb; apply eq_sym in Heqjb.
              destruct p.
              destruct H1 as [_ NoMax].
              rewrite (perm_subst _ _ _ _ _ _ _ (NoMax HP)). trivial.
         rewrite (perm_subst _ _ _ _ _ _ _ H1) in *. trivial.
      exfalso. apply (H0 H).
  destruct (CONT b) as [ValC _].
       destruct (ACCESS b) as [ValA _].
       specialize (ValC (Mem.perm_valid_block _ _ _ _ _ HMeperm) ofs).
       specialize (ValA (Mem.perm_valid_block _ _ _ _ _ HMeperm) Cur ofs).
       unfold loc_out_of_bounds in HP.
       remember (j b) as jb.
       destruct jb; apply eq_sym in Heqjb.
          destruct p.
          eapply (perm_split _ _ _ _ _ _ _ ValC); clear ValC; intros.
             exfalso. apply HP. apply H0.
         rewrite H1. assumption.
      rewrite ValC. assumption.
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
                 rewrite (UP _ _ _ Heqjb Val1). apply H. 
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
                         rewrite <- (UP _ _ _ Heqjb2 H) in H0.
                         rewrite (UV _ _ Heqjb2 H0 _ (eq_refl _)).
                         specialize (Mem.mi_memval _ _ _ (Mem.mext_inj _ _ 
                                      Ext12) b2 ofs _ _ (eq_refl _) H0).
                         rewrite Zplus_0_r; trivial.  
                destruct (ContInval H ofs) as [Cont _]. 
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
              rewrite <- (U3Perm _ _ _ H3 Val3).
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
            rewrite (U3Val _ _ H3 Perm3 _ (eq_refl _)).
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
              destruct (ContInval H1 ofs) as [ContPerm ContNoPerm]; 
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
admit.  (* weak_valid_pointer...
             specialize (H2 k (Int.unsigned ofs)).
             rewrite J in H2.
             apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                   rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                   eapply Inj13'. apply H. apply H0.
             rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                       eapply Inj23. apply J. apply H0. *)
           (*case invalid*)
             assert (J: j b = None).
               remember (j b) as d. destruct d; apply eq_sym in Heqd; trivial. 
                  destruct p. exfalso. apply H1.
                  apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqd Inj23).
admit.  (* weak_valid_pointer...
             specialize (H2 k (Int.unsigned ofs)).
             apply (perm_split _ _ _ _ _ _ _ H2); clear H2; intros.
                 rewrite (perm_subst _ _ _ _ _ _ _ H3) in *; clear H3.
                     eapply Inj13'. apply H. apply H0.
             unfold Mem.perm in H0. rewrite H3 in H0. inv H0. *)
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
          specialize (ContVal H0 ofs).
          specialize (H1 Cur ofs).
          remember (j b) as jb.
          destruct jb; apply eq_sym in Heqjb.
              destruct p. 
              destruct ContVal as [ContPerm ContNoperm].
              apply (perm_split _ _ _ _ _ _ _ H1); clear H1; intros.
                rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
                clear ContNoperm.
                rewrite (ContPerm H1) in Heqv; clear ContPerm.
                  unfold Mem.valid_block in VB'. 
                  rewrite <-  VB'. unfold mem_wd in WD1'.
                  assert (X: Mem.flat_inj (Mem.nextblock m1') b = Some (b, Z0)).
                     apply flatinj_I. apply Fwd1.
                     apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqjb Inj13).
                  destruct WD1'. specialize (mi_memval b ofs _ _ X R). 
                  rewrite Zplus_0_r in mi_memval. 
                  rewrite <- Heqv in mi_memval.
                  clear X Heqv. inversion mi_memval. clear H8. 
                  subst. apply flatinj_E in H4. apply H4.
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
         (*j b = None*)
           rewrite ContVal in Heqv. clear ContVal.
           rewrite (perm_subst _ _ _ _ _ _ _ H1) in R; clear H1.
           assert (X: Mem.flat_inj (Mem.nextblock m2) b = Some (b, Z0)).
                                   apply flatinj_I. apply H0.
             destruct WD2. specialize (mi_memval b ofs _ _ X R). 
                  rewrite Zplus_0_r in mi_memval. rewrite <- Heqv in mi_memval.
                  clear X Heqv. inversion mi_memval. clear H7. 
                  subst. apply flatinj_E in H3.
                  apply Fwd2.  apply H3.
      (*case invalid*)
        clear ContVal.
        destruct (ContInval H0 ofs) as [ContPerm ContNoperm]; clear ContInval.
        specialize (H1 Cur ofs).
        apply (perm_split _ _ _ _ _ _ _ H1); clear H1; intros.
           rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
           clear ContNoperm.
           rewrite (ContPerm R) in Heqv; clear ContPerm.
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

Parameter mkAccessMap_EI_exists:  forall (j:meminj) (m1 m1' m2:Mem.mem), 
          ZMap.t (Z -> perm_kind -> option permission).
Axiom mkAccessMap_EI_ok: forall j (m1 m1' m2:Mem.mem), 
      AccessMap_EI_Property j m1 m1' m2 (mkAccessMap_EI_exists j m1 m1' m2).

Parameter mkContentsMap_EI_exists: 
           forall (j :meminj) (m1 m1' m2:Mem.mem), ZMap.t (ZMap.t memval).
Axiom mkContentsMap_EI_ok: forall j m1 m1' m2, 
      Content_EI_Property j m1 m1' m2 (mkContentsMap_EI_exists j m1 m1' m2).

Definition mkEI (j j': meminj) (m1 m2 m1':mem)
                (Ext12: Mem.extends m1 m2) 
                (Fwd1: mem_forward m1 m1') m3 
                (Inj23: Mem.inject j m2 m3)
                m3' (Fwd3: mem_forward m3 m3') 
                (Inj13': Mem.inject j' m1' m3')
                (UnchOn3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                (UnchOn1: my_mem_unchanged_on (loc_unmapped j) m1 m1')
                (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3': mem_wd m3')
             : Mem.mem'.
eapply Mem.mkmem with (nextblock:=m1'.(Mem.nextblock))
                      (mem_access:=mkAccessMap_EI_exists j m1 m1' m2).
  apply (mkContentsMap_EI_exists j m1 m1' m2).
  apply m1'.
  (*access_max*)
     intros. specialize (mkAccessMap_EI_ok j m1 m1' m2 b). intros.
     apply (valid_split _ _ _ _  H); clear H; intros.
     (*valid_block m2 b*)
         assert (MAX:= H0 Max ofs). 
         specialize (H0 Cur ofs).
         remember (j b) as jb.
         destruct jb; apply eq_sym in Heqjb.
            destruct p.
            destruct MAX as [MaxPerm MaxNoperm].
            apply (perm_split _ _ _ _ _ _ _ H0); clear H0; intros.
              clear MaxNoperm.
                 rewrite H1 in *; clear H1.
                 rewrite (MaxPerm H0). apply m1'.
            clear MaxPerm. 
                 rewrite H1 in *; clear H1.
                 rewrite (MaxNoperm H0). apply m2.
          rewrite H0 in *; clear H0.
                 rewrite MAX; clear MAX. apply m2.
     (*~ valid_block m2 b*)
         destruct (H0 Max ofs) as [MaxPerm MaxNoPerm].
         apply (perm_split _ _ _ _ _ _ _ (H0 Cur ofs)); clear H0; intros.
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
    destruct (mkAccessMap_EI_ok j m1 m1' m2 b) as [_ Inval].
     assert (NVB2: ~ Mem.valid_block m2 b). 
        intros N. apply NV1. 
        apply (Mem.valid_block_extends _ _ b Ext12). apply N.
     specialize (Inval NVB2 k ofs).
     apply (perm_split _ _ _ _ _ _ _ Inval); clear Inval; intros.
          rewrite H1. apply m1'.  apply H.
          rewrite H1. trivial.
Defined.

Lemma my_interpolate_EI: forall (j j': meminj) (m1 m2 m1':mem)
                (Ext12: Mem.extends m1 m2) 
                (Fwd1: mem_forward m1 m1') m3 
                (Inj23: Mem.inject j m2 m3)
                m3' (Fwd3: mem_forward m3 m3') 
                (Inj13': Mem.inject j' m1' m3') 
                (UnchOn3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                (UnchOn1: my_mem_unchanged_on (loc_unmapped j) m1 m1')
                (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3': mem_wd m3'),
    exists m2', mem_forward m2 m2' /\
                Mem.extends m1' m2' /\ 
                Mem.inject j' m2' m3' /\ 
                my_mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                my_mem_unchanged_on (loc_unmapped j) m2 m2' /\
                (mem_wd m2 -> mem_wd m2').
Proof. intros. 
  exists (mkEI j j' m1 m2 m1' Ext12 Fwd1 _ Inj23 _ Fwd3 Inj13' 
              UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3'). 
  apply (EI_ok m1 m2 m1' Ext12 Fwd1 _ _ Inj23 _ Fwd3 _ Inj13'
            UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3' 
            (mkEI j j' m1 m2 m1' Ext12 Fwd1 m3 Inj23 m3' Fwd3 
                  Inj13' UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3')
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
  destruct (my_interpolate_EI _ _ _ _ _ Ext12 Fwd1 _ Inj23 _ 
              Fwd3 Inj13' UnchOn3 InjInc injSep UnchOn1 WD1' WD2 WD3')
    as [m2' [Fwd2 [Ext12' [Inj23' [UnchLoob22 [UnchLU22 WD2']]]]]].
  rewrite unchAx in *. 
  exists m2'. repeat (split; trivial).
Qed.