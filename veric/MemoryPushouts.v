Load loadpath.
Require Import veric.base.
Require Import compcert.Events.

Lemma mem_inj_id_trans: forall m1 m2 (Inj12: Mem.mem_inj inject_id m1 m2) m3 
          (Inj23: Mem.mem_inj inject_id m2 m3),Mem.mem_inj inject_id m1 m3.
Proof. intros.
  destruct Inj12. rename mi_perm into perm12. rename mi_access into access12. rename mi_memval into memval12.
  destruct Inj23. rename mi_perm into perm23. rename mi_access into access23. rename mi_memval into memval23.
  split; intros.
  (*mi_perm*)
    apply (perm12 _ _ _ _  _ _ H) in H0. 
    assert (inject_id b2 = Some (b2, delta)).
        unfold inject_id in *. inv H. trivial.
    apply (perm23 _ _ _ _  _ _ H1) in H0.  inv H. inv H1. rewrite Zplus_0_r in H0. assumption.
  (*mi_access*)
    apply (access12 _ _ _ _  _ _ H) in H0. 
    assert (inject_id b2 = Some (b2, delta)).
        unfold inject_id in *. inv H. trivial.
    apply (access23 _ _ _ _  _ _ H1) in H0.  inv H. inv H1. rewrite Zplus_0_r in H0. assumption.
  (*mi_memval*)
    assert (MV1:= memval12 _ _ _ _  H H0). 
    assert (inject_id b2 = Some (b2, delta)).
        unfold inject_id in *. inv H. trivial.
    assert (R2: Mem.perm m2 b2 ofs Cur Readable).
        apply (perm12 _ _ _ _  _ _ H) in H0. inv H. rewrite Zplus_0_r in H0. assumption.
    assert (MV2:= memval23 _ _ _ _  H1 R2).
    inv H. inv H1.  rewrite Zplus_0_r in *.
    remember  (ZMap.get ofs (ZMap.get b2 (Mem.mem_contents m2))) as v.
    destruct v. inv MV1. apply MV2.
      inv MV1. apply MV2.
      inv MV2. constructor.
     inv MV1. inv MV2. inv H3. inv H4. rewrite Int.add_zero. rewrite Int.add_zero.  econstructor. reflexivity. rewrite Int.add_zero.   trivial.
      inv MV2. inv H3.  rewrite Int.add_zero.   rewrite Int.add_zero in H5. econstructor.
Qed.

Lemma extends_trans: forall m1 m2 (Ext12: Mem.extends m1 m2) m3 (Ext23: Mem.extends m2 m3), Mem.extends m1 m3.
Proof. intros. inv Ext12. inv Ext23.
  split. rewrite mext_next. assumption. eapply mem_inj_id_trans; eauto. 
Qed.  

Lemma memval_inject_id_refl: forall v, memval_inject inject_id v v. 
Proof.  destruct v. constructor. constructor. econstructor. reflexivity. rewrite Int.add_zero. trivial. Qed.

Lemma extends_refl: forall m, Mem.extends m m.
Proof. intros.
  split. trivial.
  split; intros. 
     inv H.  rewrite Zplus_0_r. assumption.
     inv H.  rewrite Zplus_0_r. assumption.
     inv H.  rewrite Zplus_0_r. apply memval_inject_id_refl.
Qed.

Lemma meminj_split_idR: forall j, j = compose_meminj j inject_id.
Proof. intros. unfold  compose_meminj, inject_id. 
   apply extensionality. intro b. 
   remember (j b). 
   destruct o; trivial. destruct p. rewrite Zplus_0_r. trivial.
Qed.

Lemma meminj_split_idL: forall j, j = compose_meminj inject_id j.
Proof. intros. unfold  compose_meminj, inject_id.
   apply extensionality. intro b.
   remember (j b). 
   destruct o; trivial. destruct p. rewrite Zplus_0_l. trivial.  
Qed.

Goal (*inject_id_refl:*) forall m, Mem.inject inject_id m m.
Proof.
  intros. unfold inject_id; split; intros.
        split; intros; inv H; rewrite Zplus_0_r; trivial.
        apply memval_inject_id_refl.
Admitted. (*FAILs*)

Lemma compose_idL: forall f, compose_meminj inject_id f = f.
Proof. intros. apply extensionality. intros b.
   unfold compose_meminj.
   remember (inject_id b).
   destruct o; inv Heqo. remember (f b). destruct o. destruct  p. rewrite Zplus_0_l. trivial.
  trivial.
Qed.
 
Lemma compose_idR: forall f, compose_meminj f inject_id = f.
Proof. intros. apply extensionality. intros b.
   unfold compose_meminj.
   remember (f b).
   destruct o; trivial. destruct  p.
   remember (inject_id b0).
   destruct o; inv Heqo0. rewrite Zplus_0_r. trivial.
Qed.

Lemma extends_inject_compose:
  forall f m1 m2 m3,
  Mem.extends m1 m2 -> Mem.inject f m2 m3 -> Mem.inject f m1 m3.
Proof. intros.
    inv H. inv mext_inj. inv H0. inv mi_inj.
    split; intros. 
         split; intros. 
             apply (mi_perm _ _ _ _ _ _ (eq_refl _)) in H0. rewrite Zplus_0_r in H0.
                 apply (mi_perm0 _ _ _ _ _ _ H H0).
             apply (mi_access _ _ _ _ _ _ (eq_refl _)) in H0. rewrite Zplus_0_r in H0.
                 apply (mi_access0 _ _ _ _ _ _ H H0).
             assert (K1:= mi_memval _ _ _ _ (eq_refl _) H0).
                  apply  (mi_perm _ _ _ _ _ _ (eq_refl _)) in H0. rewrite Zplus_0_r in H0.
                  assert (K2:= mi_memval0 _ _ _ _ H H0). rewrite Zplus_0_r in K1.
                  assert (K:= memval_inject_compose _ _ _ _ _ K1 K2).
                  rewrite compose_idL in K. apply K.
       apply mi_freeblocks. unfold Mem.valid_block. rewrite <- mext_next. apply H.
       eapply mi_mappedblocks. apply H.
        intros b; intros.  apply (mi_perm _ _ _ _ _ _ (eq_refl _)) in H2. rewrite Zplus_0_r in H2. apply (mi_perm _ _ _ _ _ _ (eq_refl _)) in H3. rewrite Zplus_0_r in H3.
               apply (mi_no_overlap _ _ _ _ _ _ _ _ H H0 H1 H2 H3).
       apply (mi_perm _ _ _ _ _ _ (eq_refl _)) in H0. rewrite Zplus_0_r in H0.
                eapply mi_representable. apply H. apply H0.
Qed.

Lemma inject_extends_compose:
  forall f m1 m2 m3,
  Mem.inject f m1 m2 -> Mem.extends m2 m3 -> Mem.inject f m1 m3.
Proof. intros.
    inv H. inv mi_inj. inv H0. inv mext_inj.
    split; intros. 
         split; intros. 
             apply (mi_perm _ _ _ _ _ _ H) in H0.
                 apply (mi_perm0 _ _ _ _ _ _  (eq_refl _)) in H0.  rewrite Zplus_0_r in H0. assumption.
             apply (mi_access _ _ _ _ _ _ H) in H0.
                 apply (mi_access0 _ _ _ _ _ _  (eq_refl _)) in H0. rewrite Zplus_0_r in H0. assumption.
             assert (K1:= mi_memval _ _ _ _ H H0).
                  apply  (mi_perm _ _ _ _ _ _ H) in H0. 
                  assert (K2:= mi_memval0 _ _ _ _ (eq_refl _) H0). rewrite Zplus_0_r in K2.
                  assert (K:= memval_inject_compose _ _ _ _ _ K1 K2).
                  rewrite compose_idR in K. apply K.
       apply mi_freeblocks. apply H.
       unfold Mem.valid_block. rewrite <- mext_next. eapply mi_mappedblocks. apply H.
        intros b; intros. apply (mi_no_overlap _ _ _ _ _ _ _ _ H H0 H1 H2 H3).
        eapply mi_representable. apply H. apply H0.
Qed.

Lemma extends_extends_compose:
  forall m1 m2 m3,
  Mem.extends m1 m2 -> Mem.extends m2 m3 -> Mem.extends m1 m3.
Proof. intros.
    inv H. inv mext_inj. inv H0. inv mext_inj.
    split; intros. rewrite mext_next; assumption. 
    split; intros.
             apply (mi_perm _ _ _ _ _ _ H) in H0. 
                 apply (mi_perm0 _ _ _ _ _ _  (eq_refl _)) in H0.  rewrite Zplus_0_r in H0. assumption.
             apply (mi_access _ _ _ _ _ _ H) in H0.
                 apply (mi_access0 _ _ _ _ _ _  (eq_refl _)) in H0. rewrite Zplus_0_r in H0. assumption.
             assert (K1:= mi_memval _ _ _ _ H H0).
                  apply  (mi_perm _ _ _ _ _ _ H) in H0. 
                  assert (K2:= mi_memval0 _ _ _ _ (eq_refl _) H0). rewrite Zplus_0_r in K2.
                  assert (K:= memval_inject_compose _ _ _ _ _ K1 K2).
                  rewrite compose_idR in K. apply K.
Qed.

Lemma flatinj_E: forall b b1 b2 delta (H:Mem.flat_inj b b1 = Some (b2, delta)), b2=b1 /\ delta=0 /\ b2 < b.
Proof. unfold Mem.flat_inj. intros.
  remember (zlt b1 b).
  destruct s; inv H. repeat split; trivial.
Qed.

Lemma flatinj_I: forall bb b, b < bb ->
               Mem.flat_inj bb b = Some (b, 0).
Proof. intros. unfold Mem.flat_inj.
           remember (zlt b bb). destruct s; trivial. exfalso. omega. 
Qed.

Lemma flatinj_mono: forall b b1 b2 b' delta (F: Mem.flat_inj b1 b = Some (b', delta)),
 Zlt b1 b2 -> Mem.flat_inj b2 b = Some (b', delta).
Proof. intros.
   apply flatinj_E in F. destruct F as [? [? ?]]; subst.
   apply flatinj_I. omega.
Qed.

Lemma forall_lessdef_refl: forall vals,  Forall2 Val.lessdef vals vals.
Proof. induction vals; econstructor; trivial. Qed.

Lemma lessdef_hastype: forall v v' (V:Val.lessdef v v') T, Val.has_type v' T -> Val.has_type v T.
Proof. intros. inv V; simpl; trivial. Qed.

Lemma forall_lessdef_hastype: forall vals vals' (V:Forall2 Val.lessdef vals vals') Ts 
          (HTs: Forall2 Val.has_type vals' Ts), Forall2 Val.has_type vals Ts.
Proof.
  intros vals vals' V.
  induction V; simpl in *; intros.
       trivial.
  inv HTs. constructor. eapply  lessdef_hastype; eassumption. apply (IHV _ H4).
Qed.

Lemma valinject_hastype:  forall j v v' (V: (val_inject j) v v') T, Val.has_type v' T -> Val.has_type v T.
Proof. intros. inv V; simpl; trivial. Qed.

Lemma forall_valinject_hastype:  forall j vals vals' (V:  Forall2 (val_inject j) vals vals') 
                Ts (HTs: Forall2 Val.has_type vals' Ts), Forall2 Val.has_type vals Ts.
Proof.
  intros j vals vals' V.
  induction V; simpl in *; intros.
       trivial.
  inv HTs. constructor. eapply  valinject_hastype; eassumption. apply (IHV _ H4).
Qed.


Lemma forall_lessdef_trans: forall vals1 vals2 (V12: Forall2 Val.lessdef vals1 vals2) 
                                                               vals3  (V23: Forall2 Val.lessdef vals2 vals3) ,  Forall2 Val.lessdef vals1 vals3.
Proof. intros vals1 vals2 V12. 
   induction V12; intros; inv V23; econstructor.
   eapply Val.lessdef_trans; eauto.
          eapply IHV12; trivial.
Qed.

Lemma extends_loc_out_of_bounds: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs,
                loc_out_of_bounds m2 b ofs -> loc_out_of_bounds m1 b ofs.
Proof. intros.
  inv Ext. inv mext_inj.
  intros N.  eapply H. apply (mi_perm _ b 0) in N. rewrite Zplus_0_r in N. assumption. reflexivity.
Qed.

Lemma extends_loc_out_of_reach: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs j
               (Hj: loc_out_of_reach j m2 b ofs), loc_out_of_reach j m1 b ofs.
Proof. intros. unfold loc_out_of_reach in *. intros.
           intros N. eapply (Hj _ _ H). clear Hj H. inv Ext. inv mext_inj.
           specialize (mi_perm b0 _ 0 (ofs - delta) Max Nonempty (eq_refl _)). rewrite Zplus_0_r in mi_perm. apply (mi_perm N).
Qed.

Lemma valinject_lessdef: forall v1 v2 v3 j (V12:val_inject j v1 v2) (V23 : Val.lessdef v2 v3),val_inject j v1 v3.
Proof. intros. 
   inv V12; inv V23; try constructor.
    econstructor. eassumption. trivial.
Qed.

Lemma forall_valinject_lessdef: forall vals1 vals2 j (VInj12 : Forall2 (val_inject j) vals1 vals2) vals3 
                  (LD23 : Forall2 Val.lessdef vals2 vals3), Forall2 (val_inject j) vals1 vals3.
Proof. intros vals1 vals2 j VInj12.
   induction VInj12; intros; inv LD23. constructor.
     econstructor. eapply valinject_lessdef; eassumption.
          eapply (IHVInj12 _ H4).
Qed.

Lemma val_lessdef_inject_compose: forall v1 v2 (LD12 : Val.lessdef v1 v2) j v3
              (InjV23 : val_inject j v2 v3), val_inject j v1 v3.
Proof. intros. 
  apply val_inject_id in LD12.
  apply (val_inject_compose _ _ _ _ _ LD12) in InjV23.
  rewrite compose_idL in InjV23. assumption.
Qed. 

Lemma forall_val_lessdef_inject_compose: forall v1 v2 (LD12 : Forall2 Val.lessdef v1 v2) j v3
              (InjV23 : Forall2 (val_inject j) v2 v3), Forall2 (val_inject j) v1 v3.
Proof. intros v1 v2 H.
  induction H; intros; inv InjV23; econstructor.
       eapply val_lessdef_inject_compose; eassumption.
       apply (IHForall2 _ _ H5). 
Qed. 

Lemma inject_LOOR_LOOB: forall m1 m2 j (Minj12 : Mem.inject j m1 m2) m3 m3', 
  mem_unchanged_on (loc_out_of_reach j m1) m3 m3' -> mem_unchanged_on (loc_out_of_bounds m2) m3 m3'.
Proof. intros.
     split; intros; eapply H; trivial.
         intros b2; intros. unfold loc_out_of_bounds in H0. intros N. apply H0.
                          inv Minj12. inv mi_inj. apply (mi_perm _ _ _ _ _ _ H2) in N.
                         rewrite <- Zplus_comm in N. rewrite Zplus_minus in N.  apply N.
    intros. apply H0 in H2.
         intros b2; intros. unfold loc_out_of_bounds in H2. intros N. apply H2.
                          inv Minj12. inv mi_inj. apply (mi_perm _ _ _ _ _ _ H3) in N.
                         rewrite <- Zplus_comm in N. rewrite Zplus_minus in N.  apply N.
Qed.

Lemma forall_val_inject_compose: forall vals1 vals2 j1 (ValsInj12 : Forall2 (val_inject j1) vals1 vals2)
                vals3 j2 (ValsInj23 : Forall2 (val_inject j2) vals2 vals3),
              Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3.
Proof.
  intros vals1 vals2 j1 ValsInj12.
  induction ValsInj12; intros; inv ValsInj23; econstructor.
     eapply val_inject_compose; eassumption.
  apply (IHValsInj12 _ _ H4).
Qed.

Lemma val_inject_flat: forall m1 m2 j (Inj: Mem.inject j m1 m2) v1 v2 (V: val_inject j v1 v2),
                val_inject  (Mem.flat_inj (Mem.nextblock m1)) v1 v1.
Proof. intros.
  inv V; try constructor.
    apply val_inject_ptr with (delta:=0).
            unfold Mem.flat_inj. inv Inj.
            remember (zlt b1 (Mem.nextblock m1)).
            destruct s. trivial. assert (j b1 = None). apply mi_freeblocks. apply z. rewrite H in H0. inv H0.
            rewrite Int.add_zero. trivial.
Qed.

Lemma forall_val_inject_flat: forall m1 m2 j (Inj: Mem.inject j m1 m2) vals1 vals2
                (V: Forall2 (val_inject j) vals1 vals2),
                Forall2 (val_inject  (Mem.flat_inj (Mem.nextblock m1))) vals1 vals1.
Proof. intros.
  induction V; intros; try econstructor.
       eapply val_inject_flat; eassumption.
  apply IHV.
Qed.

Module PUSHOUTS.
Require Import veric.Address.
Require Import veric.sim.
Definition contents_at (m: mem) (loc: address) : memval := 
  ZMap.get (snd loc) (ZMap.get (fst loc) (Mem.mem_contents m)).

Definition access_at (m: mem) (loc: address) : option permission :=
   ZMap.get (fst loc) (Mem.mem_access m) (snd loc) Cur.  

Definition max_access_at (m: mem) (loc: address) : option permission :=
   ZMap.get (fst loc) (Mem.mem_access m) (snd loc) Max.  

Section PO_EE.
Variable m1 m2 m1':mem.
(*Program Definition PO_EEmem:mem :=
  Mem.mkmem 
        (*content*) 
            (ZMap.init (ZMap.init Undef)) (*Todo: change this*)
        (*permissions*)
           (ZMap.init (fun ofs k => None))
        (*nextblock*)
           (Mem.nextblock m1')
        (*proof obligations*)  _ _ _ .
(*Definition PO_EE_cont: ZMap.t (ZMap.t memval).
    Proof. apply (@ZMap.map (Z -> memval)).
                    intros cont. Check ZMap.map. apply ZMap.map apply (ZMap.get b m1'.(Mem.mem_contents)).
                    eapply  ZMap.init. (fun b => None)).
Check (fun ofs => @ZMap.get memval ofs (ZMap.get b m1'.(Mem.mem_contents))).
                   intros b.*)
*)
Lemma pushout_EE: forall (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                          forall m3 (Ext23: Mem.extends m2 m3) m3' (Fwd1: mem_forward m3 m3') 
                                          (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3'),
                                          Mem.extends m2' m3'.
Proof. intros. inv Ext12. unfold mem_forward in Fwd1. inv mext_inj.
  (*exists PO_EEmem.*)
Admitted. (*We expect we can iteratively contruct m2' ie walk the blocks (and in the blocks, walk the ofs) to combine
  m1' with m2 pointwise using store operations of the memory model.
  The claim about m3 then (hopefully) follows by an induction on the construction, or is carried around in theproof of the first part*)
End PO_EE.

Section PO_EI.
Variable m1 m2 m1':mem. 
Lemma pushout_EI: forall (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                         forall j (UnchgdOn1: mem_unchanged_on (loc_unmapped j) m1 m1'),
                                       mem_unchanged_on (loc_unmapped j) m2 m2' /\
                                      forall m3 (Ext23: Mem.inject j m2 m3) m3' (Fwd1: mem_forward m3 m3') 
                                            (UnchOn3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3') j' 
                                             (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3) (Inj13': Mem.inject j' m1' m3'),
                                            Mem.inject j' m2' m3'.
Admitted. 
End PO_EI.

Section PO_IE.
Variable m1 m2 m1':mem. 
Lemma pushout_IE: forall j (Minj12 : Mem.inject j m1 m2) (Fwd1: mem_forward m1 m1') 
                          j' (InjInc: inject_incr j j')  (Sep12 : inject_separated j j' m1 m2) 
                          (UnchLUj: mem_unchanged_on (loc_unmapped j) m1 m1'),
exists m2',  Mem.inject j' m1' m2' /\ mem_forward m2 m2' /\
                    mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                    forall m3 m3' (Ext23 : Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') 
                                             (UnchLOORj1_3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3'),
                                             Mem.extends m2' m3'.
Admitted.
End PO_IE.
End PUSHOUTS.

Module MEM_WD.
(*memories that do not contain "dangling pointers"*)
Definition mem_wd m := Mem.inject_neutral (Mem.nextblock m) m.

Lemma mem_wdI: forall m,
    (forall b ofs  (R:Mem.perm m b ofs Cur Readable),
                memval_inject  (Mem.flat_inj (Mem.nextblock m)) 
                                             (ZMap.get ofs (ZMap.get b (Mem.mem_contents m)))
                                            (ZMap.get ofs (ZMap.get b (Mem.mem_contents m)))) -> mem_wd m.
Proof. intros.
  split; intros.
     apply flatinj_E in  H0. destruct H0 as [? [? ?]]; subst. rewrite Zplus_0_r. trivial. 
     apply flatinj_E in  H0. destruct H0 as [? [? ?]]; subst. rewrite Zplus_0_r. trivial. 
     apply flatinj_E in  H0. destruct H0 as [? [? ?]]; subst. rewrite Zplus_0_r.
        apply H. apply H1.
Qed.
        
Lemma mem_wd_E: forall m, mem_wd m ->  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
Proof. intros. apply Mem.neutral_inject. apply H. Qed.

Lemma meminj_split_flatinjR: forall j m m' (J:Mem.inject j m' m), mem_wd m -> 
     j = compose_meminj j (Mem.flat_inj (Mem.nextblock m)).
Proof. intros. apply mem_wd_E in H.
   unfold  compose_meminj.
   apply extensionality. intro b. 
   remember (j b). 
   destruct o; trivial. destruct p. unfold Mem.flat_inj in *.
   remember (zlt b0 (Mem.nextblock m)).
  destruct s.  rewrite Zplus_0_r. trivial.
  inv J. apply eq_sym in Heqo. specialize (mi_mappedblocks _ _ _ Heqo).
               exfalso. unfold Mem.valid_block in mi_mappedblocks. omega.
Qed.

Lemma meminj_split_flatinjL: forall j m m' (J:Mem.inject j m m'), mem_wd m -> 
     j = compose_meminj (Mem.flat_inj (Mem.nextblock m)) j.
Proof. intros. apply mem_wd_E in H.
   unfold  compose_meminj.
   apply extensionality. intro b. 
   unfold Mem.flat_inj in *.
   remember (zlt b (Mem.nextblock m)).
  destruct s. remember (j b). destruct o. destruct p.  rewrite Zplus_0_l. trivial. trivial.
  inv J. apply mi_freeblocks. apply z.
Qed.

(*Preservation of mem_wd by memory operations*)
Lemma mem_wd_empty: mem_wd Mem.empty.
Proof.  apply Mem.empty_inject_neutral. Qed.

Lemma  mem_wd_alloc: forall m b lo hi m' (ALL: Mem.alloc m lo hi = (m',b))
     (WDm: mem_wd m), mem_wd m'.
Proof. intros. unfold mem_wd in *.
  rewrite (Mem.nextblock_alloc _ _ _ _ _ ALL).
  eapply (Mem.alloc_inject_neutral _ _ _ _ _ _ ALL); try omega.
  inv WDm. 
         split; intros. 
             apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r. assumption.
             apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r. assumption.
             apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r.
                 assert (X: Mem.flat_inj (Mem.nextblock m) b1 = Some (b1, 0)).
                     apply flatinj_I. apply (Mem.perm_valid_block _ _ _ _ _ H0).
                  specialize (mi_memval _ _ _ _ X H0). rewrite Zplus_0_r in mi_memval.
                  eapply memval_inject_incr; try eassumption.
                       intros bb; intros. eapply flatinj_mono; try eassumption. omega.
Qed. 

Lemma  mem_wd_drop: forall m b lo hi p m' (DROP: Mem.drop_perm m b lo hi p = Some m')
     (WDm: mem_wd m), Mem.valid_block m b -> mem_wd m'.
Proof. intros. unfold mem_wd in *.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP).
  eapply (Mem.drop_inject_neutral _ _ _ _ _ _ _ DROP); trivial.
Qed.
  
Lemma free_neutral: forall (thr : block) (m : mem) (lo hi : Z) (b : block) (m' : Mem.mem')
  (FREE: Mem.free m b lo hi = Some m'),
  Mem.inject_neutral thr m -> Mem.inject_neutral thr m'.
Proof. intros. inv H. 
  split; intros.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r. assumption.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r. assumption.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r.
        assert (X: Mem.flat_inj thr b1 = Some (b1,0)). apply flatinj_I. assumption.
        assert (Y:= Mem.perm_free_3 _ _ _ _ _ FREE _ _ _ _ H0).
         specialize (mi_memval _ _ _ _ X Y). rewrite Zplus_0_r in *.
  admit. (*prove that content of m' at that loc is same as in m*)
Qed.

Lemma mem_wd_free: forall m b lo hi m' (WDm: mem_wd m)
  (FREE: Mem.free m b lo hi = Some m'), mem_wd m'.
Proof. intros. unfold mem_wd in *.
  eapply free_neutral. apply FREE.
   rewrite (Mem.nextblock_free _ _ _ _ _ FREE). assumption.
Qed.

(*A value that is (if its a pointer) not dangling wrt m - a condition like this will probably be need to imposed
on after-external return values (and thus also on the values returned by safely-halted)*)
Definition val_valid (v:val) (m:mem):Prop := match v with Vptr b ofs => Mem.valid_block m b | _ => True end.

(*In fact valid vals is a slight relaxtion of valid pointers*)
Lemma valid_ptr_val_valid: forall b ofs m, Mem.valid_pointer m b ofs = true -> val_valid (Vptr b (Int.repr ofs)) m.
Proof. intros.
  apply Mem.valid_pointer_nonempty_perm in H. eapply Mem.perm_valid_block. apply H.
Qed.

Lemma mem_wd_store: forall m b ofs v m' chunk (WDm: mem_wd m)
  (ST: Mem.store chunk m b ofs v = Some m')
  (V: val_valid v m), mem_wd m'.
Proof. intros. unfold mem_wd in *.
  eapply Mem.store_inject_neutral. apply ST.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ ST). assumption.
      assert (X:= Mem.store_valid_access_3 _ _ _ _ _ _ ST).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ ST). 
           apply (Mem.valid_access_implies _ _ _ _ _  Nonempty) in X.
                apply Mem.valid_access_valid_block in X. apply X.
            constructor.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ ST). 
          destruct v. constructor. constructor. constructor.  econstructor. eapply flatinj_I. apply V. rewrite Int.add_zero. trivial.
Qed.


End MEM_WD.