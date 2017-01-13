Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Axioms.

Require Import FiniteMaps.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolation_defs.

Definition AccessMap_EE_Property  (m1 m1' m2:Mem.mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b,
    (Mem.valid_block m2 b -> forall k ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          PMap.get b AM ofs k = PMap.get b m1'.(Mem.mem_access) ofs k) /\
         (~Mem.perm m1 b ofs Max Nonempty ->
          PMap.get b AM ofs k = PMap.get b m2.(Mem.mem_access) ofs k))
     /\ (~ Mem.valid_block m2 b -> forall k ofs,
             PMap.get b AM ofs k = PMap.get b m1'.(Mem.mem_access) ofs k).

Definition Content_EE_Property
  (m1 m1' m2:Mem.mem) (CM:ZMap.t (ZMap.t memval)):=
  forall b,
    (Mem.valid_block m2 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
           ZMap.get ofs (PMap.get b CM) =
           ZMap.get ofs (PMap.get b m1'.(Mem.mem_contents))) /\
         (~Mem.perm m1 b ofs Max Nonempty ->
           ZMap.get ofs (PMap.get b CM) =
           ZMap.get ofs (PMap.get b m2.(Mem.mem_contents))))
     /\ (~ Mem.valid_block m2 b -> forall (HM1': Mem.valid_block m1' b) ofs,
              ZMap.get ofs (PMap.get b CM) =
              ZMap.get ofs (PMap.get b m1'.(Mem.mem_contents)))
    /\ fst CM !! b = Undef.

Lemma EE_ok: forall (m1 m1' m2 m3 m3':Mem.mem)
             (Ext12: Mem.extends m1 m2)
             (Fwd1: mem_forward m1 m1')
             (Ext23: Mem.extends m2 m3)
             (Fwd3: mem_forward m3 m3')
             (Ext13' : Mem.extends m1' m3')
             (UnchOn13 : Mem.unchanged_on (loc_out_of_bounds m1) m3 m3')
             m2'
             (NB: m2'.(Mem.nextblock)=m3'.(Mem.nextblock))
             (CONT: Content_EE_Property  m1 m1' m2 (m2'.(Mem.mem_contents)))
             (ACCESS: AccessMap_EE_Property m1 m1' m2 (m2'.(Mem.mem_access))),
         mem_forward m2 m2' /\
             Mem.extends m1' m2' /\
             Mem.extends m2' m3' /\
             Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof. intros.
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext23) in H.
        apply Fwd3 in H. destruct H as[H _].
        unfold Mem.valid_block. rewrite NB. apply H.
      (*max*)
        destruct (ACCESS b) as [X _].
        unfold Mem.perm in *. destruct (X H Max ofs). clear X ACCESS.
        remember (Mem.perm_order'_dec (PMap.get b (Mem.mem_access m1) ofs Max) Nonempty) as d.
        destruct d; clear Heqd.
           clear H2. rewrite (H1 p0) in H0. clear H1.
           rewrite po_oo in *.
           assert (ZZ:= fwd_maxpermorder _ _ Fwd1).
           apply (Mem.valid_block_extends _ _ b Ext12) in H.
           assert (XX:= extends_permorder _ _ Ext12 b ofs Max).
           eapply po_trans. apply XX.
           eapply po_trans. apply (ZZ _ H). apply H0.
        clear H1. rewrite (H2 n) in H0. apply H0.
split; trivial.
assert (Ext12':  Mem.extends m1' m2').
    split.
    (*nextblock*)
        rewrite NB. apply Ext13'.
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
              destruct (ACCESS b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (plt b2 (Mem.nextblock m2)) as z.
              destruct z as [z|z]. clear Inval. destruct (Val z k ofs); clear Val Heqz.
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                destruct d; clear Heqd.
                   clear H1. unfold Mem.perm. rewrite (H p0). apply H0.
                clear H. unfold Mem.perm. rewrite (H1 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z.
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies.
                                       apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *.
                 rewrite (Inval z k ofs); clear Inval Heqz. apply H0.
         (*mi_align*)
             inv H. apply Z.divide_0_r.
         (*mi_memval *) inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [Val [Inval DEFAULT]]; clear CONT.
            remember (plt b2 (Mem.nextblock m2)) as d.
            destruct d as [z|z].
              destruct (Val z ofs) as [A _]. clear Val Inval.
              rewrite A.
                  apply memval_inject_id_refl.
                  eapply Fwd1. eapply (Mem.valid_block_extends _ _ _ Ext12).
                               apply z.
                     eapply Mem.perm_implies.
                       eapply Mem.perm_max. apply H0.
                       apply perm_any_N.
            assert (VB1':= Mem.perm_valid_block _ _ _ _ _ H0).
            rewrite (Inval z VB1' ofs); clear Val Inval Heqd.
                  apply memval_inject_id_refl.
split; trivial.
assert (Ext23': Mem.extends m2' m3').
    split.
    (*nextblock*)
        apply NB.
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
              destruct (ACCESS b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (plt b2 (Mem.nextblock m2)) as z.
              destruct z as [z|z]. clear Inval.
                destruct (Val z k ofs) as [A B]; clear Val Heqz.
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                destruct d; clear Heqd.
                   clear B. unfold Mem.perm in *. rewrite po_oo in *.
                   rewrite (A p0) in H0; clear A.
                   eapply po_trans.
                          eapply (extends_permorder _ _ Ext13' b2 ofs k).
                   apply H0.
                clear A. unfold Mem.perm in H0. rewrite (B n) in H0. clear B.
                   destruct UnchOn13 as [U _].
                   rewrite <- U.
                        unfold Mem.perm. rewrite po_oo in *.
                          eapply po_trans.  eapply (extends_permorder _ _ Ext23). apply H0.
                        apply n.
                        rewrite <- (Mem.valid_block_extends _ _ _ Ext23). apply z.
              clear Val Heqz. unfold Mem.perm in H0.
                 rewrite (Inval z k ofs) in H0; clear Inval.
                       unfold Mem.perm. rewrite po_oo in *.
                      eapply po_trans.  eapply (extends_permorder _ _ Ext13'). apply H0.
         (*mi_align*) inv H. apply Z.divide_0_r.
         (*mi_memval *) inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [ValC [InvalC DefaultC]].
            destruct (ACCESS b2) as [ValA InvalA].
            remember (plt b2 (Mem.nextblock m2)) as z.
            destruct z as [z|z].
              clear InvalC InvalA.
                 destruct (ValC z ofs) as [VA VB]; clear ValC Heqz.
                 destruct (ValA z Cur ofs) as [AccA AccB]; clear ValA.
                 remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                 destruct d; clear Heqd.
                    rewrite (VA p). clear AccB VA VB.
                    unfold Mem.perm in H0. rewrite (AccA p) in H0. clear AccA.
                    destruct Ext13'. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).
                    rewrite Zplus_0_r in mi_memval. assumption.
                 rewrite (VB n). clear AccA VA VB.
                    unfold Mem.perm in *. rewrite (AccB n) in H0. clear AccB.
                      assert (Mem.perm m3 b2 ofs Cur Readable).
                         unfold Mem.perm in *.
                         rewrite po_oo in *.
                         eapply po_trans.
                            eapply (extends_permorder _ _ Ext23). apply H0.
                         eapply memvalUnchOnR. apply n. apply UnchOn13.
                            destruct Ext23. destruct mext_inj.
                            specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).
                              rewrite Zplus_0_r in mi_memval. assumption.
                            apply H.
              clear ValA ValC.
                 assert (VB1': Mem.valid_block m1' b2).
                    apply (Mem.valid_block_extends _ _ b2 Ext13').
                    unfold Mem.valid_block. rewrite <- NB.
                    apply (Mem.perm_valid_block _ _ _ _ _ H0).
                 rewrite (InvalC z VB1' ofs); clear InvalC Heqz.
                 unfold Mem.perm in H0.
                 rewrite (InvalA z Cur ofs) in H0; clear InvalA.
                    destruct Ext13'. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).
                    rewrite Zplus_0_r in mi_memval. assumption.
split; trivial.
(*unchanged_on (loc_out_of_bounds m1) m2 m2'*)
     destruct UnchOn13 as [UnchP UnchVal].
     split; intros. clear UnchVal.
        specialize (UnchP _ _ k p H).
        destruct (ACCESS b) as [Val _].
        destruct (Val H0 k ofs) as [_ B]; clear Val.
          unfold Mem.perm. rewrite (B H). split; auto.
      clear UnchP.
      assert (Hperm3 := Mem.perm_extends _ _ _ _ _ _ Ext23 H0).
      assert (BV2:= Mem.perm_valid_block _ _ _ _ _ H0).
      specialize (UnchVal b ofs H Hperm3).
      destruct (CONT b) as [Val _].
      destruct (Val BV2 ofs) as [_ B]; clear Val.
            apply (B H).
Qed.

Definition AccessMap_EE_FUN'  (m1 m1' m2:Mem.mem) (b:block):
           Z -> perm_kind -> option permission :=
if plt b (Mem.nextblock m1')
then
  if plt b (Mem.nextblock m2)
  then (fun ofs k =>
         if Mem.perm_dec m1 b ofs Max Nonempty
         then PMap.get b m1'.(Mem.mem_access) ofs k
         else PMap.get b m2.(Mem.mem_access) ofs k)
  else PMap.get b m1'.(Mem.mem_access)
else (fun ofs k => None).

Definition AccessMap_EE_FUN  (m1 m1' m2:Mem.mem) (b:block):
           Z -> perm_kind -> option permission :=
  if plt b (Mem.nextblock m2)
  then (fun ofs k =>
         if Mem.perm_dec m1 b ofs Max Nonempty
         then PMap.get b m1'.(Mem.mem_access) ofs k
         else PMap.get b m2.(Mem.mem_access) ofs k)
  else PMap.get b m1'.(Mem.mem_access).

Lemma mkAccessMap_EE_exists: forall (m1 m1' m2:Mem.mem),
       exists M : PMap.t (Z -> perm_kind -> option permission),
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = AccessMap_EE_FUN' m1 m1' m2 b.
Proof. intros.
  destruct (pmap_construct_c _ (AccessMap_EE_FUN' m1 m1' m2)
              (Mem.nextblock m1') (fun ofs k => None)).
    intros. unfold AccessMap_EE_FUN'. simpl.
    remember (plt n (Mem.nextblock m1')) as d.
    destruct d; clear Heqd; trivial.
    exfalso. xomega.
 exists x. apply a.
Qed.

Lemma mkAccessMap_EE_existsT: forall (m1 m1' m2:Mem.mem),
      { M : PMap.t (Z -> perm_kind -> option permission) |
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = AccessMap_EE_FUN' m1 m1' m2 b}.
Proof. intros.
  apply (pmap_construct_c _ (AccessMap_EE_FUN' m1 m1' m2)
              (Mem.nextblock m1') (fun ofs k => None)).
    intros. unfold AccessMap_EE_FUN'. simpl.
    remember (plt n (Mem.nextblock m1')) as d.
    destruct d; clear Heqd; trivial.
    exfalso. xomega.
Qed.

Definition ContentMap_EE_ValidBlock_FUN m1 m1' m2 b ofs: memval :=
  if Mem.perm_dec m1 b ofs Max Nonempty
  then ZMap.get ofs (PMap.get b m1'.(Mem.mem_contents))
  else ZMap.get ofs (PMap.get b m2.(Mem.mem_contents)).

Definition ContentMap_EE_InvalidBlock_FUN m1' b ofs: memval:=
   ZMap.get ofs (PMap.get b m1'.(Mem.mem_contents)).

Definition ContentMap_EE_Block_FUN m1 m1' m2 b ofs : memval:=
  if plt b (Mem.nextblock m2)
  then ContentMap_EE_ValidBlock_FUN m1 m1' m2 b ofs
  else ContentMap_EE_InvalidBlock_FUN m1' b ofs.

(*The constructive version in TYPE below is actually more useful..*)
Lemma CM_block_EE_exists: forall (m1 m1' m2:Mem.mem) b,
      exists M : ZMap.t memval,
         fst M = Undef /\
         forall ofs, ZMap.get ofs M =
                     ContentMap_EE_Block_FUN m1 m1' m2 b ofs.
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

  destruct (zmap_construct_c _ (ContentMap_EE_Block_FUN m1 m1' m2 b)
             (Z.min lo1 lo2) (Z.max hi1 hi2) Undef).
    intros. unfold ContentMap_EE_Block_FUN; simpl.
        unfold ContentMap_EE_ValidBlock_FUN.
        unfold ContentMap_EE_InvalidBlock_FUN.
   rewrite Bounds1.
   rewrite Bounds2.
     destruct (plt b (Mem.nextblock m2)); trivial.
     destruct (Mem.perm_dec m1 b n Max Nonempty); trivial.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi1 hi2 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi1 hi2 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
 exists x. apply a.
Qed.

Lemma CM_block_EE_existsT: forall (m1 m1' m2:Mem.mem) b,
      { M : ZMap.t memval |
          fst M = Undef /\
          forall ofs, ZMap.get ofs M =
                      ContentMap_EE_Block_FUN m1 m1' m2 b ofs}.
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

  destruct (zmap_construct_c _ (ContentMap_EE_Block_FUN m1 m1' m2 b)
             (Z.min lo1 lo2) (Z.max hi1 hi2) Undef) as [M PM].
    intros. unfold ContentMap_EE_Block_FUN; simpl.
        unfold ContentMap_EE_ValidBlock_FUN.
        unfold ContentMap_EE_InvalidBlock_FUN.
   rewrite Bounds1.
   rewrite Bounds2.
     destruct (plt b (Mem.nextblock m2)); trivial.
     destruct (Mem.perm_dec m1 b n Max Nonempty); trivial.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi1 hi2 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
     destruct H.  apply Z.min_glb_lt_iff in H. left. apply H.
     assert (Z.max hi1 hi2 < n) by omega.
     apply Z.max_lub_lt_iff in H0. right; omega.
  exists M. apply PM.
Qed.

Definition ContentsMap_EE_FUN  (m1 m1' m2:Mem.mem) (b:block):
            ZMap.t memval.
destruct (plt b (Mem.nextblock m1')).
  apply(CM_block_EE_existsT m1 m1' m2 b).
  apply (ZMap.init Undef).
Defined.

Lemma ContentsMap_EE_exists: forall (m1 m1' m2:Mem.mem),
       exists M : PMap.t (ZMap.t memval),
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M = ContentsMap_EE_FUN m1 m1' m2 b.
Proof. intros.
  destruct (pmap_construct_c _ (ContentsMap_EE_FUN m1 m1' m2)
              (Mem.nextblock m1') (ZMap.init Undef)).
    intros. unfold ContentsMap_EE_FUN. simpl.
    remember (plt n (Mem.nextblock m1')) as d.
    destruct d; clear Heqd; trivial.
      exfalso. xomega.
 exists x. apply a.
Qed.

Lemma ContentsMap_EE_existsT: forall (m1 m1' m2:Mem.mem),
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M = ContentsMap_EE_FUN m1 m1' m2 b}.
Proof. intros.
  apply (pmap_construct_c _ (ContentsMap_EE_FUN m1 m1' m2)
              (Mem.nextblock m1') (ZMap.init Undef)).
    intros. unfold ContentsMap_EE_FUN. simpl.
    remember (plt n (Mem.nextblock m1')) as d.
    destruct d; clear Heqd; trivial.
      exfalso. xomega.
Qed.

Definition mkEE (m1 m1' m2 m3 m3':Mem.mem) (Ext12: Mem.extends m1 m2)
                (Fwd1: mem_forward m1 m1')
                (Ext23: Mem.extends m2 m3) (Fwd3: mem_forward m3 m3')
                (Ext13' : Mem.extends m1' m3')
                (UnchOn3: Mem.unchanged_on (loc_out_of_bounds m1) m3 m3')
              : Mem.mem'.
destruct (mkAccessMap_EE_existsT m1 m1' m2) as [AM [ADefault PAM]].
destruct (ContentsMap_EE_existsT m1 m1' m2) as [CM [CDefault PCM]].
eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock))
                      (mem_access:=AM)
                      (mem_contents:=CM).
(* (NB: forall b, Mem.valid_block m2 b -> Mem.valid_block m3' b)*)
(*  apply (mkContentsMap_EE_exists m1 m1' m2).*)
(*eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock))
                        (mem_access:=(Mem.mem_access m2')).*)
(*  apply m3'.*)
  (*access_max*)
  intros. rewrite PAM. unfold AccessMap_EE_FUN'.
  destruct (plt b (Mem.nextblock m1')).
    remember (plt b m2.(Mem.nextblock)) as z.
    destruct z as [z|z]; clear Heqz.
    (*Case valid*) (*clear Inval.
        specialize (Val z).
        destruct (Val Max ofs) as [MaxA MaxB].
        destruct (Val Cur ofs) as [CurA CurB]. clear Val.*)
        remember (Mem.perm_dec m1 b ofs Max Nonempty) as zz.
        destruct zz; clear Heqzz. apply m1'. apply m2.
    (*Case invalid*) apply m1'.
   reflexivity.
  (*nextblock_noaccess*)
    intros. rewrite PAM.
    unfold AccessMap_EE_FUN'.
    destruct (plt b (Mem.nextblock m1')).
      exfalso. apply H; clear - Ext13' p.
        destruct Ext13'. rewrite <- mext_next. apply p.
    trivial.
  (*Default*)
    intros. simpl. rewrite PCM.
    unfold ContentsMap_EE_FUN.
    destruct (plt b (Mem.nextblock m1')).
     remember (CM_block_EE_existsT m1 m1' m2 b).
     destruct s. apply a.
    reflexivity.
Defined.

Lemma interpolate_EE: forall m1 m2 (Ext12: Mem.extends m1 m2) m1'
            (Fwd1: mem_forward m1 m1') m3 (Ext23: Mem.extends m2 m3) m3'
            (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
            (UnchOn3: Mem.unchanged_on (loc_out_of_bounds m1) m3 m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\
                   Mem.extends m2' m3' /\
                   Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof. intros.
   assert (NB:forall b, Mem.valid_block m2 b -> Mem.valid_block m3' b).
      intros. apply Fwd3. destruct Ext23.
              unfold Mem.valid_block. rewrite <- mext_next. apply H.
   exists (mkEE m1 m1' m2 m3 m3' Ext12 Fwd1 Ext23 Fwd3 Ext13' UnchOn3).
     eapply (EE_ok m1 m1' m2 m3 m3'); trivial.
     unfold mkEE. simpl.
        destruct (mkAccessMap_EE_existsT m1 m1' m2) as [? [? ?]]; simpl.
        destruct (ContentsMap_EE_existsT m1 m1' m2) as [? [? ?]]. simpl.
        reflexivity.
(*ContentMapOK*)
   unfold Content_EE_Property, mkEE.
   destruct (mkAccessMap_EE_existsT m1 m1' m2) as [AM [ADef AP]]; simpl.
        destruct (ContentsMap_EE_existsT m1 m1' m2) as [CM [CDef CP]]. simpl.
   intros.
   split; intros.
   (*valid_block m2 b*)
     rewrite CP. unfold ContentsMap_EE_FUN.
     destruct ( plt b (Mem.nextblock m1')).
       destruct (CM_block_EE_existsT m1 m1' m2 b) as [CMb [CMbDef CMbP]]; simpl.
       unfold ContentMap_EE_Block_FUN in CMbP.
       destruct (plt b (Mem.nextblock m2)).
          unfold ContentMap_EE_ValidBlock_FUN in CMbP.
          rewrite (CMbP ofs). clear CMbP.
          destruct (Mem.perm_dec m1 b ofs Max Nonempty).
          split; intros; try contradiction; trivial.
          split; intros; try contradiction; trivial.
       contradiction.
     exfalso. apply n; clear - H Fwd1 Ext12.
       apply forward_nextblock in Fwd1.
       destruct Ext12. rewrite mext_next in Fwd1. clear mext_inj mext_next.
        unfold Mem.valid_block in H. xomega.
   split; intros.
   (*invalid_block m2 b*)
     rewrite CP.
     unfold ContentsMap_EE_FUN.
     destruct (plt b (Mem.nextblock m1')).
       destruct (CM_block_EE_existsT m1 m1' m2 b) as [CMb [CMbDef CMbP]]; simpl.
       rewrite CMbP. clear CMbP.
       unfold ContentMap_EE_Block_FUN.
       destruct (plt b (Mem.nextblock m2)).
          contradiction.
       clear n.
       unfold ContentMap_EE_InvalidBlock_FUN. trivial.
     contradiction.
   (*default*)
     rewrite CP.
     unfold ContentsMap_EE_FUN.
     destruct ( plt b (Mem.nextblock m1')).
       destruct (CM_block_EE_existsT m1 m1' m2 b) as [CMb [CMbDef CMbP]]; simpl.
       assumption.
       reflexivity.

(*AccessMapOK*)
   unfold AccessMap_EE_Property, mkEE.
   destruct (mkAccessMap_EE_existsT m1 m1' m2) as [AM [ADef AP]]; simpl.
        destruct (ContentsMap_EE_existsT m1 m1' m2) as [CM [CDef CP]]. simpl.
   intros.
   split; intros.
   (*valid_block m2 b*)
     rewrite AP. unfold AccessMap_EE_FUN'.
     destruct (plt b (Mem.nextblock m2)).
       destruct (plt b (Mem.nextblock m1')).
          destruct (Mem.perm_dec m1 b ofs Max Nonempty).
          split; intros; try contradiction; trivial.
          split; intros; try contradiction; trivial.
     exfalso. apply n; clear - H Fwd1 Ext12.
       apply forward_nextblock in Fwd1.
       destruct Ext12. rewrite mext_next in Fwd1. clear mext_inj mext_next.
        unfold Mem.valid_block in H. xomega.
    contradiction.

  (*invalid_block m2 b*)
   rewrite AP. unfold AccessMap_EE_FUN'.
     destruct (plt b (Mem.nextblock m1')).
       destruct (plt b (Mem.nextblock m2)).
        contradiction.
        trivial.
     rewrite (Mem.nextblock_noaccess m1'); trivial.
Qed.

(****** THE REST OF THIS FILE IS AN ATTEMPT TO PROVE THE
CONTRUCTION WITHOUT THE EXTRA CLAUSE
(HM1': Mem.valid_block m1' b)
IN THE DEFINITION OF THE CONTENT MAP -- BUT THIS WOULD REQUIRE
US TO HAVE m1'!!b = ZMap.init Undef for all b >= nextblock m1' --
an invariant that is not currently satisfied by the memory model*)

Definition Content_EE_Property'
  (m1 m1' m2:Mem.mem) (CM:ZMap.t (ZMap.t memval)):=
  forall b,
    (Mem.valid_block m2 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
           ZMap.get ofs (PMap.get b CM) =
           ZMap.get ofs (PMap.get b m1'.(Mem.mem_contents))) /\
         (~Mem.perm m1 b ofs Max Nonempty ->
           ZMap.get ofs (PMap.get b CM) =
           ZMap.get ofs (PMap.get b m2.(Mem.mem_contents))))
     /\ (~ Mem.valid_block m2 b -> forall ofs,
              ZMap.get ofs (PMap.get b CM) =
              ZMap.get ofs (PMap.get b m1'.(Mem.mem_contents)))
    /\ fst CM !! b = Undef.

Lemma EE_ok': forall (m1 m1' m2 m3 m3':Mem.mem)
             (Ext12: Mem.extends m1 m2)
             (Fwd1: mem_forward m1 m1')
             (Ext23: Mem.extends m2 m3)
             (Fwd3: mem_forward m3 m3')
             (Ext13' : Mem.extends m1' m3')
             (UnchOn13 : Mem.unchanged_on (loc_out_of_bounds m1) m3 m3')
             m2'
             (NB: m2'.(Mem.nextblock)=m3'.(Mem.nextblock))
             (CONT: Content_EE_Property' m1 m1' m2 (m2'.(Mem.mem_contents)))
             (ACCESS: AccessMap_EE_Property m1 m1' m2 (m2'.(Mem.mem_access))),
         mem_forward m2 m2' /\
             Mem.extends m1' m2' /\
             Mem.extends m2' m3' /\
             Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof. intros.
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext23) in H.
        apply Fwd3 in H. destruct H as[H _].
        unfold Mem.valid_block. rewrite NB. apply H.
      (*max*)
        destruct (ACCESS b) as [X _].
        unfold Mem.perm in *. destruct (X H Max ofs). clear X ACCESS.
        remember (Mem.perm_order'_dec (PMap.get b (Mem.mem_access m1) ofs Max) Nonempty) as d.
        destruct d; clear Heqd.
           clear H2. rewrite (H1 p0) in H0. clear H1.
           rewrite po_oo in *.
           assert (ZZ:= fwd_maxpermorder _ _ Fwd1).
           apply (Mem.valid_block_extends _ _ b Ext12) in H.
           assert (XX:= extends_permorder _ _ Ext12 b ofs Max).
           eapply po_trans. apply XX.
           eapply po_trans. apply (ZZ _ H). apply H0.
        clear H1. rewrite (H2 n) in H0. apply H0.
split; trivial.
assert (Ext12':  Mem.extends m1' m2').
    split.
    (*nextblock*)
        rewrite NB. apply Ext13'.
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
              destruct (ACCESS b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (plt b2 (Mem.nextblock m2)) as z.
              destruct z as [z|z]. clear Inval. destruct (Val z k ofs); clear Val Heqz.
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                destruct d; clear Heqd.
                   clear H1. unfold Mem.perm. rewrite (H p0). apply H0.
                clear H. unfold Mem.perm. rewrite (H1 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z.
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies.
                                       apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *.
                 rewrite (Inval z k ofs); clear Inval Heqz. apply H0.
         (*mi_align*) inv H. apply Z.divide_0_r.
         (*mi_memval *) inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [Val [Inval DEFAULT]]; clear CONT.
            remember (plt b2 (Mem.nextblock m2)) as d.
            destruct d as [z|z].
              destruct (Val z ofs) as [A _]. clear Val Inval.
              rewrite A.
                  apply memval_inject_id_refl.
                  eapply Fwd1. eapply (Mem.valid_block_extends _ _ _ Ext12).
                               apply z.
                     eapply Mem.perm_implies.
                       eapply Mem.perm_max. apply H0.
                       apply perm_any_N.
(*            assert (VB1':= Mem.perm_valid_block _ _ _ _ _ H0).*)
            rewrite (Inval z ofs); clear Val Inval Heqd.
                  apply memval_inject_id_refl.
split; trivial.
assert (Ext23': Mem.extends m2' m3').
    split.
    (*nextblock*)
        apply NB.
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
              destruct (ACCESS b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (plt b2 (Mem.nextblock m2)) as z.
              destruct z as [z|z]. clear Inval.
                destruct (Val z k ofs) as [A B]; clear Val Heqz.
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                destruct d; clear Heqd.
                   clear B. unfold Mem.perm in *. rewrite po_oo in *.
                   rewrite (A p0) in H0; clear A.
                   eapply po_trans.
                          eapply (extends_permorder _ _ Ext13' b2 ofs k).
                   apply H0.
                clear A. unfold Mem.perm in H0. rewrite (B n) in H0. clear B.
                   destruct UnchOn13 as [U _].
                   rewrite <- U.
                        unfold Mem.perm. rewrite po_oo in *.
                          eapply po_trans.  eapply (extends_permorder _ _ Ext23). apply H0.
                        apply n.
                        rewrite <- (Mem.valid_block_extends _ _ _ Ext23). apply z.
              clear Val Heqz. unfold Mem.perm in H0.
                 rewrite (Inval z k ofs) in H0; clear Inval.
                       unfold Mem.perm. rewrite po_oo in *.
                      eapply po_trans.  eapply (extends_permorder _ _ Ext13'). apply H0.
         (*mi_align*) inv H. apply Z.divide_0_r.
         (*mi_memval *) inv H. rewrite Zplus_0_r.
            destruct (CONT b2) as [ValC [InvalC DefaultC]].
            destruct (ACCESS b2) as [ValA InvalA].
            remember (plt b2 (Mem.nextblock m2)) as z.
            destruct z as [z|z].
              clear InvalC InvalA.
                 destruct (ValC z ofs) as [VA VB]; clear ValC Heqz.
                 destruct (ValA z Cur ofs) as [AccA AccB]; clear ValA.
                 remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                 destruct d; clear Heqd.
                    rewrite (VA p). clear AccB VA VB.
                    unfold Mem.perm in H0. rewrite (AccA p) in H0. clear AccA.
                    destruct Ext13'. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).
                    rewrite Zplus_0_r in mi_memval. assumption.
                 rewrite (VB n). clear AccA VA VB.
                    unfold Mem.perm in *. rewrite (AccB n) in H0. clear AccB.
                      assert (Mem.perm m3 b2 ofs Cur Readable).
                         unfold Mem.perm in *.
                         rewrite po_oo in *.
                         eapply po_trans.
                            eapply (extends_permorder _ _ Ext23). apply H0.
                         eapply memvalUnchOnR. apply n. apply UnchOn13.
                            destruct Ext23. destruct mext_inj.
                            specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).
                              rewrite Zplus_0_r in mi_memval. assumption.
                            apply H.
              clear ValA ValC.
(*                 assert (VB1': Mem.valid_block m1' b2).
                    apply (Mem.valid_block_extends _ _ b2 Ext13').
                    unfold Mem.valid_block. rewrite <- NB.
                    apply (Mem.perm_valid_block _ _ _ _ _ H0).
*)
                 rewrite (InvalC z (*VB1'*) ofs); clear InvalC Heqz.
                 unfold Mem.perm in H0.
                 rewrite (InvalA z Cur ofs) in H0; clear InvalA.
                    destruct Ext13'. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).
                    rewrite Zplus_0_r in mi_memval. assumption.
split; trivial.
(*unchanged_on (loc_out_of_bounds m1) m2 m2'*)
     destruct UnchOn13 as [UnchP UnchVal].
     split; intros. clear UnchVal.
        specialize (UnchP _ _ k p H).
        destruct (ACCESS b) as [Val _].
        destruct (Val H0 k ofs) as [_ B]; clear Val.
          unfold Mem.perm. rewrite (B H). split; auto.
      clear UnchP.
      assert (Hperm3 := Mem.perm_extends _ _ _ _ _ _ Ext23 H0).
      assert (BV2:= Mem.perm_valid_block _ _ _ _ _ H0).
      specialize (UnchVal b ofs H Hperm3).
      destruct (CONT b) as [Val _].
      destruct (Val BV2 ofs) as [_ B]; clear Val.
            apply (B H).
Qed.

