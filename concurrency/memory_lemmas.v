Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.common.Values. (*for val*)
Require Import VST.concurrency.common.permissions.
Require Import Coq.ZArith.ZArith.
Require Import compcert.lib.Coqlib.

(** ** Various results about CompCert's memory model*)
Module MemoryLemmas.

  Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).
  Transparent Mem.store.
  (*TODO: see if we can reuse that for gsoMem_obs_eq.*)
  (*TODO: maybe we don't need to open up the interface here*)
  Lemma store_contents_other:
    forall m m' b b' ofs ofs' v chunk
      (Hstore: Mem.store chunk m b ofs v = Some m')
      (Hstable: ~ Mem.perm m b' ofs' Cur Writable),
      Maps.ZMap.get ofs' (Mem.mem_contents m') # b' =
      Maps.ZMap.get ofs' (Mem.mem_contents m) # b'.
  Proof.
    intros.
    erewrite Mem.store_mem_contents; eauto.
    simpl.
    destruct (Pos.eq_dec b b') as [Heq | Hneq];
      [| erewrite Maps.PMap.gso by auto; reflexivity ].
    subst b'.
    rewrite Maps.PMap.gss.
    destruct (Z_lt_le_dec ofs' ofs) as [Hlt | Hge].
    erewrite Mem.setN_outside by (left; auto);
      reflexivity.
    destruct (Z_lt_ge_dec
                ofs' (ofs + (size_chunk chunk)))
      as [Hlt | Hge'].
    (* case the two addresses coincide - contradiction*)
    apply Mem.store_valid_access_3 in Hstore.
    unfold Mem.valid_access in Hstore. simpl in Hstore.
    destruct Hstore as [Hcontra _].
    unfold Mem.range_perm in Hcontra.
    specialize (Hcontra ofs' (conj Hge Hlt));
      exfalso; intuition.
    erewrite Mem.setN_outside; auto.
    right; rewrite size_chunk_conv in Hge';
      rewrite encode_val_length; auto.
  Qed.

  Transparent Mem.alloc.

  Lemma val_at_alloc_1:
    forall m m' lo hi nb b ofs
      (Halloc: Mem.alloc m lo hi  = (m', nb))
      (Hvalid: Mem.valid_block m b),
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
  Proof.
    intros.
    unfold Mem.alloc in Halloc.
    inv Halloc.
    simpl.
    rewrite Maps.PMap.gso; auto.
    intro; subst. unfold Mem.valid_block in *.
    eapply Plt_strict; eauto.
  Qed.

  Lemma val_at_alloc_2:
    forall m m' lo hi nb ofs
      (Halloc: Mem.alloc m lo hi = (m', nb)),
      Maps.ZMap.get ofs (Maps.PMap.get nb (Mem.mem_contents m')) = Undef.
  Proof.
    intros.
    unfold Mem.alloc in Halloc.
    inv Halloc.
    simpl.
    rewrite PMap.gss, ZMap.gi.
    reflexivity.
  Qed.

  (*stronger version of val_at_alloc_1*)
  Lemma val_at_alloc_3:
    forall m m' lo hi  nb b ofs
      (Halloc: Mem.alloc m lo hi = (m', nb))
      (Hvalid: b <> nb),
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
  Proof.
    intros.
    unfold Mem.alloc in Halloc.
    inv Halloc.
    simpl.
    rewrite Maps.PMap.gso; auto.
  Qed.

  Lemma permission_at_alloc_1:
    forall m m' lo hi nb b ofs
      (Halloc: Mem.alloc m lo hi = (m', nb))
      (Hvalid: Mem.valid_block m b),
    forall k, permissions.permission_at m b ofs k =
         permissions.permission_at m' b ofs k.
  Proof.
    intros.
    unfold Mem.alloc in Halloc.
    inv Halloc.
    unfold permissions.permission_at. simpl.
    rewrite Maps.PMap.gso; auto.
    intro; subst. unfold Mem.valid_block in *.
    eapply Plt_strict; eauto.
  Qed.

  Lemma permission_at_alloc_2:
    forall m m' lo sz nb ofs
      (Halloc: Mem.alloc m lo sz = (m', nb))
      (Hofs: (lo <= ofs < sz)%Z),
      forall k, permissions.permission_at m' nb ofs k = Some Freeable.
  Proof.
    intros.
    eapply Memory.alloc_access_same in Halloc; eauto.
  Qed.

  Lemma permission_at_alloc_3:
    forall m m' lo sz nb ofs
      (Halloc: Mem.alloc m lo sz = (m', nb))
      (Hofs: (ofs < lo \/ ofs >= sz)%Z),
      forall k, permissions.permission_at m' nb ofs k = None.
  Proof.
    intros.
    pose proof (Mem.fresh_block_alloc _ _ _ _ _ Halloc) as Hinvalid.
    apply Mem.nextblock_noaccess with (ofs := ofs) (k := k) in Hinvalid.
    unfold permission_at.
    eapply Memory.alloc_access_other with (b' := nb) (k := k) in Halloc;
      unfold Memory.access_at, permission_at in *; simpl in *; eauto.
    rewrite <- Halloc;
      now auto.
  Qed.

  Lemma permission_at_alloc_4:
    forall m m' lo hi nb b ofs
      (Halloc: Mem.alloc m lo hi = (m', nb))
      (Hb: b <> nb),
    forall k, permissions.permission_at m b ofs k =
         permissions.permission_at m' b ofs k.
  Proof.
    intros.
    unfold Mem.alloc in Halloc.
    inv Halloc.
    unfold permissions.permission_at. simpl.
    rewrite Maps.PMap.gso; auto.
  Qed.

  Lemma permission_at_free_1 :
    forall m m' (lo hi : Z) b b' ofs'
      (Hfree: Mem.free m b lo hi = Some m')
      (Hnon_freeable: ~ Mem.perm m b' ofs' Cur Freeable),
    forall k : perm_kind,
      permission_at m b' ofs' k = permission_at m' b' ofs' k.
  Proof.
    intros.
    pose proof (Mem.free_result _ _ _ _ _ Hfree) as Hfree'.
    subst.
    unfold Mem.unchecked_free. unfold permission_at. simpl.
    destruct (Pos.eq_dec b' b); subst.
    - destruct (zle lo ofs' && zlt ofs' hi) eqn:Hintv.
      + exfalso.
        apply andb_true_iff in Hintv.
        destruct Hintv as [Hle Hlt].
        destruct (zle lo ofs'); simpl in *; auto.
        destruct (zlt ofs' hi); simpl in *; auto.
        apply Mem.free_range_perm in Hfree.
        unfold Mem.range_perm in Hfree.
        specialize (Hfree ofs' (conj l l0)).
        auto.
      + rewrite Maps.PMap.gss.
        rewrite Hintv.
        reflexivity.
    - rewrite Maps.PMap.gso;
      auto.
  Qed.

  Lemma permission_at_free_2 :
    forall m m' (lo hi : Z) b b' ofs'
      (Hfree: Mem.free m b lo hi = Some m')
      (Hb: b <> b'),
    forall k : perm_kind,
      permission_at m b' ofs' k = permission_at m' b' ofs' k.
  Proof.
    intros.
    pose proof (Mem.free_result _ _ _ _ _ Hfree) as Hfree'.
    subst.
    unfold Mem.unchecked_free. unfold permission_at. simpl.
    destruct (Pos.eq_dec b' b); subst.
    - exfalso; now auto.
    - rewrite Maps.PMap.gso;
        auto.
  Qed.

  Lemma permission_at_free_list_1:
    forall m m' l b ofs
      (Hfree: Mem.free_list m l = Some m')
      (Hnon_freeable: ~ Mem.perm m b ofs Cur Freeable),
    forall k : perm_kind,
      permission_at m b ofs k = permission_at m' b ofs k.
  Proof.
    intros m m' l.
    generalize dependent m.
    induction l; intros.
    - simpl in Hfree; inv Hfree; reflexivity.
    - simpl in Hfree. destruct a, p.
      destruct (Mem.free m b0 z0 z) eqn:Hfree'; try discriminate.
      pose proof Hfree' as Hfree''.
      eapply permission_at_free_1 with (k := k) in Hfree'; eauto.
      eapply permission_at_free_1 with (k := Cur) in Hfree''; eauto.
      rewrite Hfree'. eapply IHl; eauto.
      unfold Mem.perm in *. unfold permission_at in *.
      rewrite <- Hfree''. assumption.
  Qed.

  Lemma mem_free_contents:
    forall m m2 lo hi b
      (Hfree: Mem.free m b lo hi = Some m2),
    forall b' ofs,
      Maps.ZMap.get ofs (Maps.PMap.get b' (Mem.mem_contents m)) =
      Maps.ZMap.get ofs (Maps.PMap.get b' (Mem.mem_contents m2)).
  Proof.
    intros.
    apply Mem.free_result in Hfree.
    subst; unfold Mem.unchecked_free.
    reflexivity.
  Qed.

  Lemma mem_store_max:
    forall chunk b ofs v m m',
      Mem.store chunk m b ofs v = Some m' ->
      forall b' ofs',
        (getMaxPerm m) # b' ofs' = (getMaxPerm m') # b' ofs'.
  Proof.
    intros.
    unfold Mem.store in *.
    destruct (Mem.valid_access_dec m chunk b ofs Writable); try discriminate.
    inversion H; subst.
    do 2 rewrite getMaxPerm_correct.
    reflexivity.
  Qed.

  Lemma mem_storebytes_cur :
    forall b (ofs : Z) bytes (m m' : mem),
      Mem.storebytes m b ofs bytes = Some m' ->
      forall (b' : positive) (ofs' : Z),
        (getCurPerm m) !! b' ofs' = (getCurPerm m') !! b' ofs'.
  Proof.
    intros.
    Transparent Mem.storebytes.
    unfold Mem.storebytes in *.
    destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur
                                 Writable); try discriminate.
    inversion H; subst.
    do 2 rewrite getCurPerm_correct.
    reflexivity.
  Qed.

  Lemma mem_store_cur:
    forall chunk b ofs v m m',
      Mem.store chunk m b ofs v = Some m' ->
      forall b' ofs',
        (getCurPerm m) # b' ofs' = (getCurPerm m') # b' ofs'.
  Proof.
    intros.
    apply Mem.store_storebytes in H.
    eapply mem_storebytes_cur; eauto.
  Qed.

  Lemma mem_storev_store:
    forall chunk ptr v m m',
      Mem.storev chunk m ptr v = Some m' ->
      exists b ofs, ptr = Vptr b ofs /\
               Mem.store chunk m b (Integers.Ptrofs.intval ofs) v = Some m'.
  Proof.
    intros.
    destruct ptr; try discriminate.
    simpl in H.
    do 2 eexists; split; eauto.
  Qed.

  Lemma load_valid_block:
    forall (m : mem) b ofs chunk v,
      Mem.load chunk m b ofs = Some v ->
      Mem.valid_block m b.
  Proof.
    intros m b ofs chunk v Hload.
    apply Mem.load_valid_access in Hload.
    apply Mem.valid_access_valid_block with (chunk:=chunk) (ofs:= ofs).
    eapply Mem.valid_access_implies; eauto.
    constructor.
  Qed.

  Definition max_inv mf := forall b ofs, Mem.valid_block mf b ->
                                    permission_at mf b ofs Max = Some Freeable.

  Lemma max_inv_store:
    forall m m' chunk b ofs v pmap
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hmax: max_inv m)
      (Hstore: Mem.store chunk (restrPermMap Hlt) b ofs v = Some m'),
      max_inv m'.
  Proof.
    intros.
    intros b0 ofs0 Hvalid0.
    unfold permission_at.
    erewrite Mem.store_access; eauto.
    assert (H := restrPermMap_Max Hlt b0 ofs0).
    eapply Mem.store_valid_block_2 in Hvalid0; eauto.
    erewrite restrPermMap_valid in Hvalid0.
    specialize (Hmax b0 ofs0 Hvalid0).
    unfold permission_at in H.
    rewrite H.
    rewrite getMaxPerm_correct;
      assumption.
  Qed.

   Lemma sim_valid_access:
    forall (mf m1f : mem)
      (b1 b2 : block) (ofs : Z)
      (Hm1f: m1f = makeCurMax mf)
      (HmaxF: max_inv mf)
      (Hvalidb2: Mem.valid_block mf b2)
      (Halign: (4 | ofs)%Z),
      Mem.valid_access m1f Mint32 b2 ofs Freeable.
  Proof.
    unfold Mem.valid_access. simpl. split; try assumption.
    unfold Mem.range_perm. intros ofs0 Hbounds. subst m1f.
    specialize (HmaxF _ ofs0 Hvalidb2).
    unfold Mem.perm.
    assert (Hperm := makeCurMax_correct mf b2 ofs0 Cur).
    rewrite HmaxF in Hperm.
    unfold permission_at in Hperm.
    unfold Mem.perm.
    rewrite <- Hperm.
    simpl;
      constructor.
  Qed.

  Lemma setPermBlock_lt:
    forall pmap m b ofs sz p
      (Hinv: max_inv m)
      (Hvalid: Mem.valid_block m b)
      (Hlt: permMapLt pmap (getMaxPerm m)),
      permMapLt (setPermBlock p b ofs pmap sz) (getMaxPerm m).
  Proof.
    intros.
    intros b' ofs'.
    specialize (Hlt b' ofs').
    destruct (Pos.eq_dec b b').
    - subst.
      destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat sz)%Z).
      + erewrite setPermBlock_same; [|eauto].
        specialize (Hinv _ ofs' Hvalid).
        erewrite getMaxPerm_correct in *.
        erewrite Hinv in *.
        simpl; destruct p; eauto using perm_order.
      + destruct sz. simpl.
        assumption.
        erewrite setPermBlock_other_1.
        assumption.
        eapply Intv.range_notin in n; eauto.
        simpl. zify; omega.
    - erewrite setPermBlock_other_2; [| eauto].
      assumption.
  Qed.

  Lemma setN_inside: forall (vl : list memval) (c : ZMap.t memval) (ofs0 ofs: Z),
      Intv.In ofs0 (ofs, (ofs + Z.of_nat (length vl))%Z) ->
      ZMap.get ofs0 (Mem.setN vl ofs c) = List.nth (Z.to_nat (ofs0 - ofs)%Z) vl Undef.
  Proof.
    intros vl.
    induction vl using rev_ind; intros.
    - unfold Intv.In in H.
      simpl in H. exfalso.
      now omega.
    - simpl in *.
      unfold Intv.In in H. simpl in H.
      rewrite Mem.setN_concat.
      simpl.
      rewrite ZMap.gsspec.
      destruct (ZIndexed.eq ofs0 (ofs + Z.of_nat (length vl))). subst.
      + assert ((Z.to_nat (ofs + Z.of_nat (length vl) - ofs)) = length vl)
          by (rewrite <- Z.add_sub_assoc;
              rewrite Zplus_minus, Nat2Z.id; reflexivity).
        rewrite H0.
        rewrite List.app_nth2.
        rewrite NPeano.Nat.sub_diag. reflexivity.
        omega.
      + rewrite List.app_length in H.
        simpl in H.
        rewrite NPeano.Nat.add_1_r in H.
        simpl in H.
        rewrite Zpos_P_of_succ_nat in H.
        apply threads_lemmas.lt_succ_neq in H; eauto.
        rewrite List.app_nth1.
        eapply IHvl. auto.
        destruct H.
        clear - H0 H.
        zify.
        erewrite Z2Nat.id in * by omega.
        omega.
  Qed.

End MemoryLemmas.
