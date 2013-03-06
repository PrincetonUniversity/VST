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
Require Import sepcomp.i_defs.

Definition AccessMap_IE_Property  j12 j12' m1 m1' m2 m3' 
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> forall k ofs2,
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) =>  ZMap.get b2 AM ofs2 k =
                               ZMap.get b1 m1'.(Mem.mem_access) ofs1 k
           | None => ZMap.get b2 AM ofs2 k = 
                     ZMap.get b2 m2.(Mem.mem_access) ofs2 k
           end)
     /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
           match source j12' m1' b2 ofs2 with 
              Some(b1,ofs1) => ZMap.get b2 AM ofs2 k =
                               ZMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None => ZMap.get b2 AM ofs2 k =
                      ZMap.get b2 m3'.(Mem.mem_access) ofs2 k
          end).

Definition Content_IE_Property j12 (m1 m1' m2 m3':Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2, 
    (Mem.valid_block m2 b2 -> forall ofs2,
       match source j12 m1 b2 ofs2 with
            Some(b1,ofs1) => ZMap.get ofs2 (ZMap.get b2 CM) = 
                             ZMap.get ofs2 (ZMap.get b2 m3'.(Mem.mem_contents))
          | None => ZMap.get ofs2 (ZMap.get b2 CM) =
                    ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents))
       end)
 /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
          ZMap.get ofs2 (ZMap.get b2 CM) = 
          ZMap.get ofs2 (ZMap.get b2 m3'.(Mem.mem_contents))).

Lemma IE_ok: forall (m1 m1' m2 m3 m3':Mem.mem) j 
           (Minj12 : Mem.inject j m1 m2) 
           (Fwd1: mem_forward m1 m1') j'
           (InjInc: inject_incr j j')  (Sep12 : inject_separated j j' m1 m2) 
           (UnchLUj: my_mem_unchanged_on (loc_unmapped j) m1 m1')
           (Ext23 : Mem.extends m2 m3) 
           (Fwd3: mem_forward m3 m3') 
           (UnchLOORj1_3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
           (Inj13' : Mem.inject j' m1' m3')
           (UnchLOOB23_3': my_mem_unchanged_on (loc_out_of_bounds m2) m3 m3')
           (WD2: mem_wd m2) (WD1' : mem_wd m1') (WD3': mem_wd m3')
           m2'
           (NB: m2'.(Mem.nextblock)=m3'.(Mem.nextblock))
           (CONT:  Content_IE_Property j m1 m1' m2 m3' (m2'.(Mem.mem_contents)))
           (ACCESS: AccessMap_IE_Property j j' m1 m1' m2 m3'
                    (m2'.(Mem.mem_access))),
       mem_forward m2 m2' /\  
          Mem.extends m2' m3' /\ 
          Mem.inject j' m1' m2' /\ 
          my_mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
          (mem_wd m2 -> mem_wd m2').    
Proof. intros.
assert (Fwd2: mem_forward m2 m2').
  split; intros; rename b into b2.
  (*valid_block*) apply (Mem.valid_block_extends _ _ b2 Ext23) in H.
     apply Fwd3 in H. destruct H as[H _]. 
     unfold Mem.valid_block. rewrite  NB. apply H.
  (*max*)
     destruct (ACCESS b2) as [Val2 _].
     specialize (Val2 H Max ofs). 
     remember (source j m1 b2 ofs) as src.
     destruct src.
       apply source_SomeE in Heqsrc.
       destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]]; 
                subst.
       unfold Mem.perm in *.
       rewrite Val2 in H0. clear Val2.
       rewrite po_oo in *.
       eapply po_trans. apply (inject_permorder _ _ _ Minj12 _ _ _ J1).
       eapply po_trans. apply (fwd_maxpermorder _ _ Fwd1).
            eapply (Mem.valid_block_inject_1 _ _ _ _ _ _ J1 Minj12).
       assumption.
  (*perm*) unfold Mem.perm in *. rewrite Val2 in H0. apply H0.
split; trivial.
assert (Ext23': Mem.extends m2' m3').
    split. 
    (*nextblock*)
        apply NB. 
    (*mem_inj*)
       split; intros. inv H. rewrite Zplus_0_r.
         (*mi_perm*)
            destruct (ACCESS b2) as [Val2 Inval2].
            remember (zlt b2 (Mem.nextblock m2)) as z.
            destruct z; clear Heqz. clear Inval2. specialize (Val2 z k ofs).
              remember (source j m1 b2 ofs) as src.
              destruct src.
                 apply source_SomeE in Heqsrc.
                 destruct Heqsrc as [b1 [delta [ofs1 [PBO 
                                    [Bounds [J1 [P1 Off2]]]]]]]; subst.
                 unfold Mem.perm in *.
                 rewrite Val2 in H0. clear Val2. rewrite po_oo in *.
                 assert (J1' := InjInc _ _ _  J1).
                 eapply po_trans. 
                   apply (inject_permorder _ _ _ Inj13' _ _ _ J1').
                   assumption. 
              unfold Mem.perm in H0. rewrite Val2 in H0. clear Val2.
                 destruct UnchLOORj1_3 as [U _].
                    rewrite <- U.
                      unfold Mem.perm; rewrite po_oo in*. 
                        eapply po_trans. eapply (extends_permorder _ _ Ext23).
                                         apply H0.
                      eapply sourceNone_LOOR. apply Heqsrc. eassumption.
                      rewrite <- (Mem.valid_block_extends _ _ _ Ext23). apply z.                      
            clear Val2. specialize (Inval2 z k ofs).
               remember (source j' m1' b2 ofs) as src.
               destruct src.
                  apply source_SomeE in Heqsrc.
                  destruct Heqsrc as [b1 [delta [ofs1
                                     [PBO [Bounds [J1' [P1 Off2]]]]]]]; subst.
                  unfold Mem.perm in *.
                  rewrite Inval2 in H0. clear Inval2. rewrite po_oo in *.
                  eapply po_trans.
                     apply (inject_permorder _ _ _ Inj13' _ _ _ J1').
                     assumption. 
               unfold Mem.perm in *. rewrite Inval2 in H0; clear Inval2.
               apply H0.
         (*mi_access*) unfold Mem.valid_access in *. 
            destruct H0. inv H. rewrite Zplus_0_r.
            split; trivial. 
               intros off; intros. specialize (H0 _ H). clear H.
               destruct (ACCESS b2) as [Val2 Inval2].
               remember (zlt b2 (Mem.nextblock m2)) as z.
               destruct z; clear Heqz.
                  clear Inval2. specialize (Val2 z Cur off).
                  remember (source j m1 b2 off) as src. 
                  destruct src.  
                      apply source_SomeE in Heqsrc.
                      destruct Heqsrc as [b1 [delta [ofs1
                           [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
                      unfold Mem.perm in *.
                      rewrite Val2 in H0. clear Val2. rewrite po_oo in *.
                      assert (J1' := InjInc _ _ _  J1).
                      eapply po_trans. 
                         apply (inject_permorder _ _ _ Inj13' _ _ _ J1').
                         assumption. 
                  unfold Mem.perm in H0. rewrite Val2 in H0. clear Val2.
                  destruct UnchLOORj1_3 as [U _]. 
                  rewrite <- U.
                       unfold Mem.perm. rewrite po_oo in *.
                          eapply po_trans.  eapply (extends_permorder _ _ Ext23). apply H0.
                      eapply sourceNone_LOOR. apply Heqsrc. eassumption.
                      rewrite <- (Mem.valid_block_extends _ _ _ Ext23). apply z.   
               clear Val2. specialize (Inval2 z Cur off).
                  remember (source j' m1' b2 off) as src.
                  destruct src.
                  apply source_SomeE in Heqsrc.
                  destruct Heqsrc as [b1 [delta [ofs1
                            [PBO [Bounds [J1' [P1 Off2]]]]]]]; subst.
                  unfold Mem.perm in *.
                  rewrite Inval2 in H0. clear Inval2. rewrite po_oo in *.
                  eapply po_trans.
                     apply (inject_permorder _ _ _ Inj13' _ _ _ J1').
                     assumption. 
                  unfold Mem.perm in *. rewrite Inval2 in H0; clear Inval2.
                  apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. 
            destruct (CONT b2) as [ValC InvalC].  
            destruct (ACCESS b2) as [ValA InvalA]. 
            remember (zlt b2 (Mem.nextblock m2)) as z.
            destruct z; clear Heqz.
              clear InvalC InvalA.
                 specialize (ValC z ofs). specialize (ValA z Cur ofs).
                 remember (source j m1 b2 ofs) as src.
                 destruct src.
                     apply source_SomeE in Heqsrc.
                     destruct Heqsrc as [b1 [delta [ofs1
                              [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
                     unfold Mem.perm in *. rewrite ValA in H0. 
                     rewrite ValC. clear ValA ValC.
                     apply memval_inject_id_refl.
                 unfold Mem.perm in *. rewrite ValA in H0. rewrite ValC.
                    clear ValA ValC.
                    assert (NE:= sourceNone_LOOR _ _ _ _ Heqsrc _ Minj12). 
                    destruct UnchLOORj1_3 as [UP UV]. 
                    assert (Hperm3 := Mem.perm_extends _ _ _ _ _ _ Ext23 H0).
                    destruct Ext23. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0). 
                    rewrite Zplus_0_r in mi_memval.
                    specialize (UV _ _ NE Hperm3).
                    inv mi_memval.
                        apply eq_sym in H. rewrite (UV _ H). constructor.
                        apply eq_sym in H1. rewrite (UV _ H1). econstructor. 
                            apply H2. trivial.
                        constructor. 
              clear ValA ValC. rewrite (InvalC z).
                  apply memval_inject_id_refl.
split; trivial.
assert (Inj12': Mem.inject j' m1' m2'). 
    assert (MemInj': Mem.mem_inj j' m1' m2').
       split; intros.
       (*mi_perm*)
          destruct (ACCESS b2) as [Val2 Inval2].
          remember (zlt b2 (Mem.nextblock m2)) as z.
          destruct z; clear Heqz. clear Inval2. 
            specialize  (Val2 z k (ofs + delta)).
            assert (HJ: j b1 = Some (b2, delta)).
              remember (j b1).
              destruct o; apply eq_sym in Heqo.
                 destruct p0. apply InjInc in Heqo. 
                              rewrite Heqo in H. inv H. reflexivity.
                 destruct (Sep12 _ _ _ Heqo H). exfalso. apply H2. apply z.
            assert (P1: Mem.perm m1 b1 ofs Max p). apply Fwd1.
                    eapply (Mem.valid_block_inject_1 _ _ _ _ _ _  HJ Minj12).
                                eapply Mem.perm_max. apply H0.
            rewrite (source_SomeI j m1 b2 b1 ofs delta) in Val2.
                  unfold Mem.perm in *. rewrite Val2. apply H0.
                  eapply Minj12. apply HJ. 
                  eapply Mem.perm_implies. apply P1. apply perm_any_N.
          clear Val2. specialize (Inval2 z k (ofs + delta)). 
            remember (source j' m1' b2 (ofs + delta)) as src.
            destruct src.
               rewrite (source_SomeI j' m1' b2 b1 ofs delta) in Heqsrc.
               inv Heqsrc.
               unfold Mem.perm. rewrite Inval2. apply H0.
               apply Inj13'. apply H.  eapply Mem.perm_implies. 
                    eapply Mem.perm_max. apply H0. apply perm_any_N.
            unfold Mem.perm in *. rewrite Inval2.
               rewrite po_oo in *.
               eapply po_trans. 
                  eapply (inject_permorder _ _ _ Inj13' _ _ _ H ofs k). 
                  apply H0.
       (*mi_access*) destruct H0. 
           split.
              intros off; intros. 
              destruct (ACCESS b2) as [Val2 Inval2].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z; clear Heqz. clear Inval2. 
                 specialize (Val2 z Cur off).
                 assert (HJ: j b1 = Some (b2, delta)).
                    remember (j b1).
                    destruct o; apply eq_sym in Heqo.
                          destruct p0. apply InjInc in Heqo. 
                          rewrite Heqo in H. inv H. reflexivity.
                    destruct (Sep12 _ _ _ Heqo H). exfalso. apply H4. apply z.
                 assert (PM1:  Mem.perm m1 b1 (off - delta) Max Nonempty).
                    eapply Fwd1. 
                    eapply (Mem.valid_block_inject_1 _ _ _ _ _ _ HJ Minj12). 
                    eapply Mem.perm_implies. eapply Mem.perm_max. 
                    apply H0. omega. apply perm_any_N.
                 specialize (source_SomeI j m1 b2 b1 (off-delta) delta).
                    intros.
                    assert (off - delta + delta = off). omega. 
                    rewrite H4 in H3. 
                    rewrite H3 in Val2. 
                       unfold Mem.perm. rewrite Val2. apply H0. omega.
                       apply Minj12. 
                       apply HJ. 
                       apply PM1.
              clear Val2. specialize (Inval2 z Cur off). 
                 specialize (source_SomeI j' m1' b2 b1 (off-delta) delta). 
                 intros.
                 assert (off - delta + delta = off). omega. 
                 rewrite H4 in H3. 
                 rewrite H3 in Inval2. 
                    unfold Mem.perm. rewrite Inval2. apply H0. omega.
                    apply Inj13'. 
                    apply H. 
                    eapply Mem.perm_implies. eapply Mem.perm_max. 
                      apply H0. omega. apply perm_any_N. 
         eapply Inj13'. apply H. split; eassumption.
   (*memval*)
            destruct (CONT b2) as [ValC InvalC].  
            destruct (ACCESS b2) as [ValA InvalA]. 
            remember (zlt b2 (Mem.nextblock m2)) as z.
            destruct z; clear Heqz.
              clear InvalC InvalA. 
                specialize (ValC z (ofs+delta)). 
                specialize (ValA z Cur (ofs+delta)). 
                assert (HJ: j b1 = Some (b2, delta)).
                   remember (j b1).
                   destruct o; apply eq_sym in Heqo.
                     destruct p. apply InjInc in Heqo. 
                            rewrite Heqo in H. inv H. reflexivity.
                     destruct (Sep12 _ _ _ Heqo H). exfalso. apply H2. apply z.
                assert (Hperm1:Mem.perm m1 b1 ofs Max Nonempty). 
                   apply Fwd1. 
                      eapply (Mem.valid_block_inject_1 _ _ _ _ _ _ HJ Minj12).
                      eapply Mem.perm_implies. eapply Mem.perm_max. 
                         apply H0. apply perm_any_N. 
                assert (OV1: Mem.meminj_no_overlap j m1). eapply Minj12.
                rewrite (source_SomeI j m1 b2 b1 ofs delta OV1 HJ Hperm1) in *.
                rewrite ValC.
                eapply Inj13'. apply H. apply H0. 
            clear ValC ValA. rewrite (InvalC z). clear InvalC. 
                specialize ( InvalA z Cur (ofs+delta)).
                eapply Inj13'.  apply H. apply H0.
    split. assumption.
    intros. eapply Inj13'. apply H.
    intros. apply (Mem.valid_block_extends _ _ _ Ext23'). 
             eapply Inj13'. apply H.
    apply Inj13'.
    apply Inj13'.
split; trivial.
assert (MUO: my_mem_unchanged_on (loc_out_of_reach j m1) m2 m2').
   destruct UnchLOORj1_3 as [UnchA UnchB].
   split; intros. clear UnchB.
      destruct (ACCESS b) as [Val _].
      specialize (Val H k ofs).
      unfold loc_out_of_reach in HP.
      remember (source j m1 b ofs) as src.
      destruct src. 
         apply source_SomeE in Heqsrc.
         destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
         subst.
         specialize (HP _ _ J1). 
         assert (ofs1 + delta - delta=ofs1). omega. 
         rewrite H0 in HP.
         exfalso. apply (HP P1).
      unfold Mem.perm in *. rewrite Val. trivial.
   clear UnchA.
      assert (V2:= Mem.perm_valid_block _ _ _ _ _ HMeperm).
      destruct (CONT b) as [Val _].
      specialize (Val V2 ofs).
      unfold loc_out_of_reach in HP.
      remember (source j m1 b ofs) as src.
      destruct src. 
        apply source_SomeE in Heqsrc.
        destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
        subst.
        specialize (HP _ _ J1). 
        assert (ofs1 + delta - delta=ofs1). omega. 
        rewrite H in HP.
        exfalso. apply (HP P1).
      unfold Mem.perm in *. rewrite Val. trivial.
split; trivial. 
  intros. eapply extends_memwd. apply Ext23'. assumption.
Qed.

Parameter mkAccessMap_IE_exists: 
           forall (j j':meminj) (m1 m1' m2 m3':Mem.mem), 
           ZMap.t (Z -> perm_kind -> option permission).
Axiom mkAccessMap_IE_ok: forall j j' m1 m1' m2 m3', 
      AccessMap_IE_Property j j' m1 m1' m2 m3' 
               (mkAccessMap_IE_exists j j' m1 m1' m2 m3').

Parameter mkContentsMap_IE_exists: 
           forall (j :meminj) (m1 m1' m2 m3':Mem.mem), ZMap.t (ZMap.t memval).
Axiom mkContentsMap_IE_ok: forall j m1 m1' m2 m3', 
      Content_IE_Property j m1 m1' m2 m3'
              (mkContentsMap_IE_exists j m1 m1' m2 m3').

Definition mkIE (j j': meminj) (m1 m1' m2 :Mem.mem)
                 (Minj12 : Mem.inject j m1 m2) 
                 (Fwd1: mem_forward m1 m1') 
                 (InjInc: inject_incr j j')  
                 (Sep12 : inject_separated j j' m1 m2) 
                 m3 m3' (Ext23 : Mem.extends m2 m3)
                 (Fwd3: mem_forward m3 m3') 
                 (Inj13' : Mem.inject j' m1' m3')
                 (WD2: mem_wd m2) (WD1' : mem_wd m1') (WD3': mem_wd m3')
               : Mem.mem'.
eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock))
                      (mem_access:=mkAccessMap_IE_exists j j' m1 m1' m2 m3').
  apply (mkContentsMap_IE_exists j m1 m1' m2 m3').
  apply m3'.
  (*access_max*)
  intros. destruct (mkAccessMap_IE_ok j j' m1 m1' m2 m3' b) as [Val Inval].
    remember (zlt b m2.(Mem.nextblock)) as z. 
    destruct z; clear Heqz.
    (*Case valid*) clear Inval.
      assert (MaxP := Val z Max ofs).
      assert (CurP := Val z Cur ofs).
      clear Val.
      remember (source j m1 b ofs) as src.
      destruct src.
        apply source_SomeE in Heqsrc.
        destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
        subst.
        rewrite MaxP. rewrite CurP.  apply m1'.
      rewrite MaxP. rewrite CurP.  apply m2.
    (*Case invalid*) clear Val.
      assert (MaxP := Inval z Max ofs).
      assert (CurP := Inval z Cur ofs).
      clear Inval.
      remember (source j' m1' b ofs) as src.
      destruct src.
      apply source_SomeE in Heqsrc.
      destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
      subst.
      rewrite MaxP. rewrite CurP.  apply m1'.
    rewrite MaxP. rewrite CurP.  apply m3'.
  (*nextblock_noaccess*)
    intros. 
    assert (NV3 : ~ Mem.valid_block m3 b). intros N. 
           destruct (Fwd3 _ N). unfold Mem.valid_block in H0. omega.
    assert (NV2 : ~ Mem.valid_block m2 b). intros N.
           apply NV3. eapply (Mem.valid_block_extends _ _ _ Ext23). apply N.  
    destruct (mkAccessMap_IE_ok j j' m1 m1' m2 m3' b) as [_ Inval].
    specialize (Inval NV2 k ofs).
    remember (source j' m1' b ofs) as src.
    destruct src.
    apply source_SomeE in Heqsrc.
       destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
       subst.
       specialize (Mem.valid_block_inject_2  _ _ _ _ _ _ J1 Inj13').
       intros. exfalso. unfold Mem.valid_block in H0. omega.
    rewrite Inval. apply m3'. apply H.
Defined.

Lemma my_interpolate_IE: forall m1 m1' m2 j
              (Minj12 : Mem.inject j m1 m2) 
              (Fwd1: mem_forward m1 m1') j' (InjInc: inject_incr j j')
              (Sep12 : inject_separated j j' m1 m2) 
              (UnchLUj: my_mem_unchanged_on (loc_unmapped j) m1 m1')
              m3 m3' (Ext23 : Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') 
              (UnchLOORj1_3: my_mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
              (Inj13' : Mem.inject j' m1' m3')
              (UnchLOOB23_3' : my_mem_unchanged_on 
                              (loc_out_of_bounds m2) m3 m3')
              (WD2: mem_wd m2) (WD1' : mem_wd m1') (WD3': mem_wd m3'),
         exists m2', mem_forward m2 m2' /\ 
                     Mem.extends m2' m3' /\ 
                     Mem.inject j' m1' m2' /\ 
                     my_mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                     (mem_wd m2 -> mem_wd m2').
Proof. intros. 
  exists (mkIE j j' m1 m1' m2 Minj12 Fwd1 InjInc Sep12 m3 m3' Ext23 
             Fwd3 Inj13' WD2 WD1' WD3').
eapply IE_ok with (m3:=m3); trivial.
        subst. apply mkContentsMap_IE_ok.  
        subst. apply mkAccessMap_IE_ok.  
Qed.

Lemma interpolate_IE: forall m1 m1' m2 j (Minj12 : Mem.inject j m1 m2)
                 (Fwd1: mem_forward m1 m1') j' (InjInc: inject_incr j j')
                 (Sep12 : inject_separated j j' m1 m2) 
                 (UnchLUj: mem_unchanged_on (loc_unmapped j) m1 m1')
                 m3 m3' (Ext23 : Mem.extends m2 m3)
                 (Fwd3: mem_forward m3 m3') 
                 (UnchLOORj1_3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
                 (Inj13' : Mem.inject j' m1' m3')
                 (UnchLOOB23_3': mem_unchanged_on
                                  (loc_out_of_bounds m2) m3 m3')
                 (WD2: mem_wd m2) (WD1' : mem_wd m1') (WD3': mem_wd m3'),
         exists m2',  mem_forward m2 m2' /\ Mem.extends m2' m3' /\ 
                      Mem.inject j' m1' m2' /\
                      mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                      (mem_wd m2 -> mem_wd m2').    
Proof. intros.
   rewrite <- unchAx in UnchLUj, UnchLOORj1_3, UnchLOOB23_3'.
   destruct (my_interpolate_IE _ _ _ _ Minj12  Fwd1
                             j' InjInc Sep12 
                             UnchLUj
                             m3 m3' Ext23
                             Fwd3
                             UnchLOORj1_3
                             Inj13'  UnchLOOB23_3' WD2 WD1' WD3')
   as [m2' [Fwd2 [Ext23' [Inj12' [MU WD2']]]]].
  exists m2'. rewrite unchAx in MU. repeat (split; trivial).
Qed.     