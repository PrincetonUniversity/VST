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

Definition AccessMap_IE_Property  j12 j12' m1 m1' m2 m3'
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2,
    (Mem.valid_block m2 b2 -> forall k ofs2,
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) =>  PMap.get b2 AM ofs2 k =
                               PMap.get b1 m1'.(Mem.mem_access) ofs1 k
           | None => PMap.get b2 AM ofs2 k =
                     PMap.get b2 m2.(Mem.mem_access) ofs2 k
           end)
     /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
           match source j12' m1' b2 ofs2 with
              Some(b1,ofs1) => PMap.get b2 AM ofs2 k =
                               PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None => PMap.get b2 AM ofs2 k =
                      PMap.get b2 m3'.(Mem.mem_access) ofs2 k
          end).

Definition Content_IE_Property j12 (m1 m1' m2 m3':Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2,
    (Mem.valid_block m2 b2 -> forall ofs2,
       match source j12 m1 b2 ofs2 with
            Some(b1,ofs1) => ZMap.get ofs2 (PMap.get b2 CM) =
                             ZMap.get ofs2 (PMap.get b2 m3'.(Mem.mem_contents))
          | None => ZMap.get ofs2 (PMap.get b2 CM) =
                    ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
       end)
   /\ (~ Mem.valid_block m2 b2 -> forall (HM3': Mem.valid_block m3' b2) ofs2,
          ZMap.get ofs2 (PMap.get b2 CM) =
          ZMap.get ofs2 (PMap.get b2 m3'.(Mem.mem_contents)))
   /\ fst CM !! b2 = Undef.

Lemma IE_ok: forall (m1 m1' m2 m3 m3':Mem.mem) j
           (Minj12 : Mem.inject j m1 m2)
           (Fwd1: mem_forward m1 m1') j'
           (InjInc: inject_incr j j')  (Sep12 : inject_separated j j' m1 m2)
           (UnchLUj: Mem.unchanged_on (loc_unmapped j) m1 m1')
           (Ext23 : Mem.extends m2 m3)
           (Fwd3: mem_forward m3 m3')
           (UnchLOORj1_3: Mem.unchanged_on (loc_out_of_reach j m1) m3 m3')
           (Inj13' : Mem.inject j' m1' m3')
           (UnchLOOB23_3': Mem.unchanged_on (loc_out_of_bounds m2) m3 m3')
           m2'
           (NB: m2'.(Mem.nextblock)=m3'.(Mem.nextblock))
           (CONT:  Content_IE_Property j m1 m1' m2 m3' (m2'.(Mem.mem_contents)))
           (ACCESS: AccessMap_IE_Property j j' m1 m1' m2 m3'
                    (m2'.(Mem.mem_access))),
       mem_forward m2 m2' /\
          Mem.extends m2' m3' /\
          Mem.inject j' m1' m2' /\
          Mem.unchanged_on (loc_out_of_reach j m1) m2 m2'.
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
            remember (plt b2 (Mem.nextblock m2)) as z.
            destruct z as [z|z]; clear Heqz. clear Inval2. specialize (Val2 z k ofs).
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
         (*mi_align*) inv H. apply Z.divide_0_r.
         (*mi_memval *) inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [ValC [InvalC Default]].
            destruct (ACCESS b2) as [ValA InvalA].
            remember (plt b2 (Mem.nextblock m2)) as z.
            destruct z as [z|z]; clear Heqz.
            (*validblock m2 b2*)
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
                    rewrite (UV _ _ NE Hperm3).
                    apply mi_memval.
            (*invalidblock m2 b2*)
              clear ValA ValC.
              assert (VB3: Mem.valid_block m3' b2).
                 apply Mem.perm_valid_block in H0.
                 unfold Mem.valid_block.
                 rewrite <- NB. apply H0.
              rewrite (InvalC z VB3).
                  apply memval_inject_id_refl.
split; trivial.
assert (Inj12': Mem.inject j' m1' m2').
    assert (MemInj': Mem.mem_inj j' m1' m2').
       split; intros.
       (*mi_perm*)
          destruct (ACCESS b2) as [Val2 Inval2].
          remember (plt b2 (Mem.nextblock m2)) as z.
          destruct z as [z|z]; clear Heqz. clear Inval2.
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
       (*mi_align*) eapply Inj13'. apply H. apply H0.
       (*mi_memval*)
            destruct (CONT b2) as [ValC [InvalC Default]].
            destruct (ACCESS b2) as [ValA InvalA].
            remember (plt b2 (Mem.nextblock m2)) as z.
            destruct z as [z|z]; clear Heqz.
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
            clear ValC ValA.
              assert (VB3: Mem.valid_block m3' b2).
                eapply Mem.valid_block_inject_2. apply H. apply Inj13'.
              rewrite (InvalC z VB3). clear InvalC.
              specialize ( InvalA z Cur (ofs+delta)).
              eapply Inj13'.  apply H. apply H0.
    split.
    (*mi_inj*) assumption.
    (*mi_freeblocks*) intros. eapply Inj13'. apply H.
    (*mi_mappedblocks*)  intros. apply (Mem.valid_block_extends _ _ _ Ext23').
             eapply Inj13'. apply H.
    (*mi_no_overlap*) apply Inj13'.
    (*mi_representable*) apply Inj13'.
split; trivial.
assert (MUO: Mem.unchanged_on (loc_out_of_reach j m1) m2 m2').
   destruct UnchLOORj1_3 as [UnchA UnchB].
   split; intros. clear UnchB.
      destruct (ACCESS b) as [Val _].
      specialize (Val H0 k ofs).
      unfold loc_out_of_reach in H.
      remember (source j m1 b ofs) as src.
      destruct src.
         apply source_SomeE in Heqsrc.
         destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
         subst.
         specialize (H _ _ J1).
         assert (Arith: ofs1 + delta - delta=ofs1) by omega.
         rewrite Arith in H. contradiction.
      unfold Mem.perm in *. rewrite Val. split; auto.
   clear UnchA.
      assert (V2:= Mem.perm_valid_block _ _ _ _ _ H0).
      destruct (CONT b) as [Val _].
      specialize (Val V2 ofs).
      unfold loc_out_of_reach in H.
      remember (source j m1 b ofs) as src.
      destruct src.
        apply source_SomeE in Heqsrc.
        destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
        subst.
        specialize (H _ _ J1).
        assert (Arith : ofs1 + delta - delta=ofs1) by omega.
        rewrite Arith in H. contradiction.
      apply Val.
assumption.
Qed.

Definition AccessMap_IE_FUN (j12 j12':meminj) (m1 m1' m2 m3':Mem.mem) (b2:block):
           Z -> perm_kind -> option permission :=
  if plt b2 (Mem.nextblock m2)
  then (fun ofs2 k =>
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
           | None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
         end)
  else (fun ofs2 k =>
           match source j12' m1' b2 ofs2 with
              Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None => PMap.get b2 m3'.(Mem.mem_access) ofs2 k
          end).

Lemma mkAccessMap_IE_existsT: forall j12 j12'(m1 m1' m2 m3':Mem.mem)
       (VB': forall b1 b3 delta, j12' b1 = Some (b3, delta) ->
               (Mem.valid_block m1' b1 /\ Mem.valid_block m3' b3))
       (VB : (Mem.nextblock m2 <= Mem.nextblock m3')%positive),
      { M : PMap.t (Z -> perm_kind -> option permission) |
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = AccessMap_IE_FUN j12 j12' m1 m1' m2 m3' b}.
Proof. intros.
  apply (pmap_construct_c _ (AccessMap_IE_FUN j12 j12' m1 m1' m2 m3')
              (Mem.nextblock m3') (fun ofs k => None)).
    intros. unfold AccessMap_IE_FUN.
    remember (plt n (Mem.nextblock m2)) as d.
    destruct d; clear Heqd; trivial.
       exfalso. xomega.
    extensionality ofs. extensionality k.
      remember (source j12' m1' n ofs) as src.
      destruct src.
        apply source_SomeE in Heqsrc.
        destruct Heqsrc as [b1 [delta [ofs1
          [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
        destruct (VB' _ _ _ J1).
           contradiction.
      apply m3'. apply H.
Qed.

Definition ContentMap_IE_ValidBlock_FUN (j12:meminj) m1 m2 m3'
                  b2 ofs2: memval :=
    match source j12 m1 b2 ofs2 with
      Some(b1,ofs1) => ZMap.get ofs2 (PMap.get b2 m3'.(Mem.mem_contents))
    | None => ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
    end.

Definition ContentMap_IE_InvalidBlock_FUN m3' b2 ofs2: memval :=
   ZMap.get ofs2 (PMap.get b2 m3'.(Mem.mem_contents)).

Definition ContentMap_IE_Block_FUN j12 m1 m2 m3' b ofs : memval:=
  if plt b (Mem.nextblock m2)
  then ContentMap_IE_ValidBlock_FUN j12 m1 m2 m3' b ofs
  else ContentMap_IE_InvalidBlock_FUN m3' b ofs.

Lemma CM_block_IE_existsT: forall j12 (m1 m2 m3':Mem.mem) b,
      { M : ZMap.t memval |
          fst M = Undef /\
          forall ofs, ZMap.get ofs M =
                      ContentMap_IE_Block_FUN j12 m1 m2 m3' b ofs}.
Proof. intros.
  remember (zmap_finite_c _ (PMap.get b m3'.(Mem.mem_contents))) as LH3.
  apply eq_sym in HeqLH3. destruct LH3 as [lo3 hi3].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH3).
  intros Bounds3; clear HeqLH3.
  remember (zmap_finite_c _ (PMap.get b m2.(Mem.mem_contents))) as LH2.
  apply eq_sym in HeqLH2. destruct LH2 as [lo2 hi2].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH2).
  intros Bounds2; clear HeqLH2.
   assert (Undef2: fst (Mem.mem_contents m2) !! b = Undef). apply m2.
   assert (Undef3: fst (Mem.mem_contents m3') !! b = Undef). apply m3'.
   rewrite Undef2 in *. rewrite Undef3 in *. clear Undef3 Undef2.

  destruct (zmap_construct_c _ (ContentMap_IE_Block_FUN j12 m1 m2 m3' b)
             (Z.min lo2 lo3) (Z.max hi2 hi3) Undef) as [M PM].
    intros. unfold ContentMap_IE_Block_FUN; simpl.
        unfold ContentMap_IE_ValidBlock_FUN.
        unfold ContentMap_IE_InvalidBlock_FUN.
   rewrite Bounds3.
   rewrite Bounds2.
     destruct (plt b (Mem.nextblock m2)); trivial.
       destruct (source j12 m1 b n); trivial.
         destruct p0; trivial.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi2 hi3 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi2 hi3 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
  exists M. apply PM.
Qed.

Definition ContentsMap_IE_FUN (j12:meminj) (m1 m2 m3':Mem.mem) (b:block):
            ZMap.t memval.
destruct (plt b (Mem.nextblock m3')).
  apply(CM_block_IE_existsT j12 m1 m2 m3' b).
  apply (ZMap.init Undef).
Defined.

Lemma ContentsMap_IE_existsT: forall (j12:meminj) (m1 m2 m3':Mem.mem),
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M = ContentsMap_IE_FUN j12 m1 m2 m3' b}.
Proof. intros.
  apply (pmap_construct_c _ (ContentsMap_IE_FUN j12 m1 m2 m3')
              (Mem.nextblock m3') (ZMap.init Undef)).
    intros. unfold ContentsMap_IE_FUN.
    remember (plt n (Mem.nextblock m3')) as d.
    destruct d; clear Heqd; trivial.
      exfalso. xomega.
Qed.

Definition mkIE (j j': meminj) (m1 m1' m2 m3':Mem.mem)
                (VB': forall (b1 b3 : block) (delta : Z),
                       j' b1 = Some (b3, delta) ->
                       (Mem.valid_block m1' b1 /\ Mem.valid_block m3' b3))
                (VB: (Mem.nextblock m2 <= Mem.nextblock m3')%positive)
               : Mem.mem'.
destruct (mkAccessMap_IE_existsT j j' m1 m1' m2 m3' VB' VB) as [AM [ADefault PAM]].
destruct (ContentsMap_IE_existsT j m1 m2 m3') as [CM [CDefault PCM]].

eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock))
                      (mem_access:=AM)
                      (mem_contents:=CM).
 (* apply (mkContentsMap_IE_exists j m1 m1' m2 m3').*)
(*  apply m3'.*)
  (*access_max*)
  intros. rewrite PAM. unfold AccessMap_IE_FUN.
     destruct (plt b (Mem.nextblock m2)).
     (*valid_block m2 b*)
        remember (source j m1 b ofs) as src.
        destruct src.
          destruct p0. apply m1'.
        apply m2.
     (*invalid_block m2 b*)
        remember (source j' m1' b ofs) as src.
        destruct src.
          destruct p. apply m1'.
        apply m3'.
  (*nextblock_noaccess*)
    intros. rewrite PAM.
    unfold AccessMap_IE_FUN.
    destruct (plt b (Mem.nextblock m2)).
      exfalso. apply H; clear - VB p. xomega.
    remember (source j' m1' b ofs) as src.
    destruct src.
      destruct p.
      exfalso. apply H. clear - Heqsrc VB'.
      apply source_SomeE in Heqsrc.
      destruct Heqsrc as [b1 [delta [ofs1
          [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
        apply (VB' _ _ _ J1).
      apply m3'. apply H.
  (*contents_default*)
    intros. rewrite PCM.
    unfold ContentsMap_IE_FUN.
    destruct (plt b (Mem.nextblock m3')).
     remember (CM_block_IE_existsT j m1 m2 m3' b).
     destruct s. apply a.
    reflexivity.
Defined.

Lemma interpolate_IE: forall m1 m1' m2 j (Minj12 : Mem.inject j m1 m2)
                 (Fwd1: mem_forward m1 m1') j' (InjInc: inject_incr j j')
                 (Sep12 : inject_separated j j' m1 m2)
                 (UnchLUj: Mem.unchanged_on (loc_unmapped j) m1 m1')
                 m3 m3' (Ext23 : Mem.extends m2 m3)
                 (Fwd3: mem_forward m3 m3')
                 (UnchLOORj1_3: Mem.unchanged_on (loc_out_of_reach j m1) m3 m3')
                 (Inj13' : Mem.inject j' m1' m3')
                 (UnchLOOB23_3': Mem.unchanged_on
                                  (loc_out_of_bounds m2) m3 m3'),
         exists m2',  mem_forward m2 m2' /\ Mem.extends m2' m3' /\
                      Mem.inject j' m1' m2' /\
                      Mem.unchanged_on (loc_out_of_reach j m1) m2 m2' .
Proof. intros.
  assert (VB': forall (b1 b3 : block) (delta : Z),
               j' b1 = Some (b3, delta) ->
               (Mem.valid_block m1' b1 /\ Mem.valid_block m3' b3)).
    intros.
    split.
       eapply (Mem.valid_block_inject_1 _ _ _ _ _ _ H Inj13').
       eapply (Mem.valid_block_inject_2 _ _ _ _ _ _ H Inj13').
  assert (VB: (Mem.nextblock m2 <= Mem.nextblock m3')%positive).
    apply forward_nextblock in Fwd3. inv Ext23.
    rewrite mext_next. apply Fwd3.
assert (VBB: Mem.nextblock (mkIE j j' m1 m1' m2 m3' VB' VB)
                 = Mem.nextblock m3').
  unfold mkIE.
  destruct (mkAccessMap_IE_existsT j j' m1 m1' m2 m3' VB' VB) as [AM [ADefault PAM]].
  simpl.
  destruct (ContentsMap_IE_existsT j m1 m2 m3') as [CM [CDefault PCM]].
  simpl. reflexivity.
exists (mkIE j j' m1 m1' m2 m3' VB' VB).
eapply IE_ok with (m3:=m3); trivial.
(*ContentMapOK*)
   unfold Content_IE_Property, mkIE.
  destruct (mkAccessMap_IE_existsT j j' m1 m1' m2 m3' VB' VB) as [AM [ADefault PAM]].
  simpl.
  destruct (ContentsMap_IE_existsT j m1 m2 m3') as [CM [CDefault PCM]].
  simpl.
   intros.
   split; intros.
   (*valid_block m2 b*)
     assert (PLT3: Plt b2 (Mem.nextblock m3')).
       unfold Mem.valid_block in H. clear -VB H. xomega.
     rewrite PCM. unfold ContentsMap_IE_FUN.
     destruct (plt b2 (Mem.nextblock m3')); try contradiction.
     destruct (CM_block_IE_existsT j m1 m2 m3' b2) as [CMb [CMbDef CMbP]]; simpl.
     remember (source j m1 b2 ofs2) as src.
     destruct src.
       destruct p0.
         rewrite CMbP.
         unfold ContentMap_IE_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)); try contradiction.
           unfold ContentMap_IE_ValidBlock_FUN.
           rewrite <- Heqsrc. trivial.
     rewrite CMbP.
         unfold ContentMap_IE_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)); try contradiction.
         unfold ContentMap_IE_ValidBlock_FUN.
         rewrite <- Heqsrc. trivial.
  split; intros.
     rewrite PCM. unfold ContentsMap_IE_FUN.
     destruct (CM_block_IE_existsT j m1 m2 m3' b2) as [CMb [CMbDef CMbP]]; simpl.
     destruct (plt b2 (Mem.nextblock m3')); try contradiction.
     rewrite CMbP. unfold ContentMap_IE_Block_FUN.
         destruct (plt b2 (Mem.nextblock m2)); try contradiction.
         unfold ContentMap_IE_InvalidBlock_FUN. trivial.
  (*default*)
     rewrite PCM.
     unfold ContentsMap_IE_FUN.
     destruct ( plt b2 (Mem.nextblock m3')).
       destruct (CM_block_IE_existsT j m1 m2 m3' b2) as [CMb [CMbDef CMbP]]; simpl.
       assumption.
       reflexivity.
(*AccessMapOK*)
   unfold AccessMap_IE_Property, mkIE.
   destruct (mkAccessMap_IE_existsT j j' m1 m1' m2 m3' VB' VB) as [AM [ADefault PAM]].
   simpl.
   destruct (ContentsMap_IE_existsT j m1 m2 m3') as [CM [CDefault PCM]].
   simpl.
   intros.
   split; intros.
   (*valid_block m2 b*)
     rewrite PAM. unfold AccessMap_IE_FUN.
     destruct (plt b2 (Mem.nextblock m2)); try contradiction.
     remember (source j m1 b2 ofs2) as src.
     destruct src; trivial.
       destruct p0; trivial.
  (*invalid_block m2 b*)
   rewrite PAM. unfold AccessMap_IE_FUN.
   destruct (plt b2 (Mem.nextblock m2)); try contradiction.
   remember (source j' m1' b2 ofs2) as src.
     destruct src; trivial.
       destruct p; trivial.
Qed.