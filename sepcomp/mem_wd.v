(*CompCert imports*)
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.
Require Import common.Globalenvs.

Require Import sepcomp.mem_lemmas.


(*A value that is (if its a pointer) not dangling wrt m - a condition
 like this will probably be need to imposed on after-external return
 values (and thus also on the values returned by halted)*)
Definition val_valid (v:val) (m:mem):Prop := 
     match v with Vptr b ofs => Mem.valid_block m b | _ => True 
     end.

(*In fact val_valid is a slight relaxtion of valid_pointer*)
Lemma valid_ptr_val_valid: forall b ofs m, 
    Mem.valid_pointer m b ofs = true -> val_valid (Vptr b (Int.repr ofs)) m.
Proof. intros.
  apply Mem.valid_pointer_nonempty_perm in H. eapply Mem.perm_valid_block. apply H.
Qed.

Lemma extends_valvalid: forall m1 m2 (Ext: Mem.extends m1 m2) v,
        val_valid v m1 <-> val_valid v m2.
Proof. intros.
  split; intros. destruct v; simpl in *; try econstructor.
     eapply (Mem.valid_block_extends _ _ _ Ext). apply H. 
  destruct v; simpl in *; try econstructor.
     eapply (Mem.valid_block_extends _ _ _ Ext). apply H.
Qed.

Lemma inject_valvalid: forall j m1 m2 (Inj: Mem.inject j m1 m2) v2 (V:val_valid v2 m2) v1,
             val_inject j v1 v2 -> val_valid v1 m1.
Proof. intros.
  inv H. constructor. constructor. constructor.
     simpl in *. eapply Mem.valid_block_inject_1; eassumption. 
     constructor. 
Qed.

(*Preservation of val_valid along an injection only holds 
  if the LHS value is defined*) 
Lemma inject_valvalid_1:
  forall (j : meminj) (m1 m2 : mem),
  Mem.inject j m1 m2 ->
  forall v1 : val,
  val_valid v1 m1 -> forall v2 : val, val_inject j v1 v2 -> 
  match v1 with Vundef => True
      | _ => val_valid v2 m2
  end.
Proof. intros.
  destruct v1; trivial.
  inv H1; trivial.
  inv H1; trivial.
  inv H1; trivial.
  inv H1. simpl in *.
  eapply Mem.valid_block_inject_2; eassumption.
Qed.

(*memories that do not contain "dangling pointers"*)
Definition mem_wd m := Mem.inject_neutral (Mem.nextblock m) m.

Lemma align_chunk_0: forall chunk, (align_chunk chunk | 0).
Proof.
  intros chunk. destruct chunk; simpl; apply Z.divide_0_r.
Qed.

Lemma mem_wdI: forall m,
  (forall (b:block) ofs  (R:Mem.perm m b ofs Cur Readable),
    memval_inject  (Mem.flat_inj (Mem.nextblock m)) 
    (ZMap.get ofs (PMap.get b (Mem.mem_contents m)))
    (ZMap.get ofs (PMap.get b (Mem.mem_contents m)))) -> mem_wd m.
Proof. intros.
  split; intros.
     apply flatinj_E in  H0. destruct H0 as [? [? ?]]; subst. rewrite Zplus_0_r. trivial. 
     apply flatinj_E in  H0. destruct H0 as [? [? ?]]; subst. apply align_chunk_0.
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
   destruct (plt b0 (Mem.nextblock m)).
     rewrite Zplus_0_r. trivial.
   inv J. apply eq_sym in Heqo. specialize (mi_mappedblocks _ _ _ Heqo).
               exfalso. unfold Mem.valid_block in mi_mappedblocks. xomega.
Qed.

Lemma meminj_split_flatinjL: forall j m m' (J:Mem.inject j m m'), mem_wd m -> 
     j = compose_meminj (Mem.flat_inj (Mem.nextblock m)) j.
Proof. intros. apply mem_wd_E in H.
   unfold  compose_meminj.
   apply extensionality. intro b. 
   unfold Mem.flat_inj in *.
   destruct (plt b (Mem.nextblock m)).
     remember (j b). destruct o. destruct p0.  rewrite Zplus_0_l. trivial. trivial.
  inv J. apply mi_freeblocks. assumption.
Qed.

Lemma mem_wd_inject_splitL: forall j m1 m2
              (J:Mem.inject j m1 m2)  (WD: mem_wd m1),
     Mem.inject (Mem.flat_inj (Mem.nextblock m1)) m1 m1 
     /\ j = compose_meminj (Mem.flat_inj (Mem.nextblock m1)) j.
Proof. intros.
    split. apply mem_wd_E. apply WD.  
    eapply (meminj_split_flatinjL _ _ _ J WD).
Qed.

Lemma mem_wd_inject_splitR: forall j m1 m2
              (J:Mem.inject j m1 m2)  (WD: mem_wd m2),
     Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 
     /\ j = compose_meminj j (Mem.flat_inj (Mem.nextblock m2)).
Proof. intros.
    split. apply mem_wd_E. apply WD.  
    eapply (meminj_split_flatinjR _ _ _ J WD).
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
             apply flatinj_E in H. destruct H as [? [? ?]]; subst. apply align_chunk_0.
             apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r.
                 assert (X: Mem.flat_inj (Mem.nextblock m) b1 = Some (b1, 0)).
                     apply flatinj_I. apply (Mem.perm_valid_block _ _ _ _ _ H0).
                  specialize (mi_memval _ _ _ _ X H0). rewrite Zplus_0_r in mi_memval.
                  eapply memval_inject_incr; try eassumption.
                       intros bb; intros.
                        eapply flatinj_mono; try eassumption; xomega.
       xomega.
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
     apply flatinj_E in H. destruct H as [? [? ?]]; subst. apply align_chunk_0.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r.
        assert (X: Mem.flat_inj thr b1 = Some (b1,0)). apply flatinj_I. assumption.
        assert (Y:= Mem.perm_free_3 _ _ _ _ _ FREE _ _ _ _ H0).
         specialize (mi_memval _ _ _ _ X Y). rewrite Zplus_0_r in *.    
         rewrite (Mem.free_result _ _ _ _ _ FREE) in *. simpl in *. apply mi_memval.
Qed.

Lemma mem_wd_free: forall m b lo hi m' (WDm: mem_wd m)
  (FREE: Mem.free m b lo hi = Some m'), mem_wd m'.
Proof. intros. unfold mem_wd in *.
  eapply free_neutral. apply FREE.
   rewrite (Mem.nextblock_free _ _ _ _ _ FREE). assumption.
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
          destruct v; try solve [constructor].
            econstructor. eapply flatinj_I. apply V. 
                          rewrite Int.add_zero. trivial.
Qed.

Lemma extends_memwd: 
forall m1 m2 (Ext: Mem.extends m1 m2), mem_wd m2 -> mem_wd m1.
Proof.
  intros. eapply mem_wdI. intros.
  assert (Mem.perm m2 b ofs Cur Readable).
    eapply (Mem.perm_extends _ _ _ _ _ _ Ext R).
  assert (Mem.valid_block m2 b).
     apply (Mem.perm_valid_block _ _ _ _ _ H0). 
  destruct Ext. rewrite mext_next.
  assert (Mem.flat_inj (Mem.nextblock m2) b = Some (b,0)).
    apply flatinj_I. apply H1.
  destruct mext_inj. specialize (mi_memval b ofs b 0 (eq_refl _) R). 
  rewrite Zplus_0_r in mi_memval.
  destruct H. specialize (mi_memval0 b ofs b 0 H2 H0). 
  rewrite Zplus_0_r in mi_memval0. 
  remember (ZMap.get ofs (PMap.get b (Mem.mem_contents m1))) as v.
  destruct v. constructor. constructor.
  econstructor.
    eapply flatinj_I. inv mi_memval. inv H4. rewrite Int.add_zero in H6. 
      rewrite <- H6 in mi_memval0. simpl in mi_memval0. inversion mi_memval0.
      apply flatinj_E in H4. apply H4. 
   rewrite Int.add_zero. reflexivity.
Qed. 

Definition valid_genv {F V:Type} (ge:Genv.t F V) (m:mem) :=
   (forall i b, Genv.find_symbol ge i = Some b -> val_valid (Vptr b Int.zero) m) 
/\ (forall gv b, Genv.find_var_info ge b = Some gv -> val_valid (Vptr b Int.zero) m).

Lemma valid_genv_alloc: forall {F V:Type} (ge:Genv.t F V) (m m1:mem) lo hi b
    (ALLOC: Mem.alloc m lo hi = (m1,b)) (G: valid_genv ge m), valid_genv ge m1.
Proof. intros. split. intros x; intros.
  apply (Mem.valid_block_alloc _ _ _ _ _ ALLOC).
  destruct G as [G G0].
  apply (G _ _ H).
  destruct G as [G G0].
  intros gv b0 H. 
  apply (Mem.valid_block_alloc _ _ _ _ _ ALLOC).
  apply (G0 _ _ H).
Qed.

Lemma valid_genv_store: forall {F V:Type} (ge:Genv.t F V) m m1 b ofs v chunk
    (STORE: Mem.store chunk m b ofs v = Some m1) 
     (G: valid_genv ge m), valid_genv ge m1.
Proof. intros. split. intros x; intros.
  apply (Mem.store_valid_block_1 _ _ _ _ _ _ STORE).
  destruct G as [G G0]. apply (G _ _ H).
  intros.   apply (Mem.store_valid_block_1 _ _ _ _ _ _ STORE).
  destruct G as [G G0]. apply (G0 _ _ H).
Qed.

Lemma valid_genv_store_zeros: forall {F V:Type} (ge:Genv.t F V) m m1 b y z 
    (STORE_ZERO: store_zeros m b y z = Some m1)
    (G: valid_genv ge m), valid_genv ge m1.
Proof. intros. split. intros x; intros.
  apply Genv.store_zeros_nextblock in STORE_ZERO.
  destruct G as [G G0]. specialize (G _ _ H); simpl in *. 
  unfold Mem.valid_block in *. 
  rewrite STORE_ZERO. apply G.
  intros. destruct G as [G G0]. specialize (G0 _ _ H); simpl in *. 
  unfold Mem.valid_block in *. 
  apply Genv.store_zeros_nextblock in STORE_ZERO.
  rewrite STORE_ZERO. apply G0.
Qed.

Lemma mem_wd_store_zeros: forall m b p n m1
    (STORE_ZERO: store_zeros m b p n = Some m1) (WD: mem_wd m), mem_wd m1.
Proof. intros until n. functional induction (store_zeros m b p n); intros.
  inv STORE_ZERO; tauto.
  apply (IHo _ STORE_ZERO); clear IHo.
      eapply (mem_wd_store m). apply WD. apply e0. simpl; trivial.
  inv STORE_ZERO.
Qed.

Lemma valid_genv_drop: forall {F V:Type} (ge:Genv.t F V) (m m1:mem) b lo hi p
    (DROP: Mem.drop_perm m b lo hi p = Some m1) (G: valid_genv ge m), 
    valid_genv ge m1.
Proof. intros. split. intros x; intros.
  apply (Mem.drop_perm_valid_block_1 _ _ _ _ _ _ DROP).
  destruct G as [G G0]; apply (G _ _ H).
  intros. apply (Mem.drop_perm_valid_block_1 _ _ _ _ _ _ DROP).
  destruct G as [G G0]; apply (G0 _ _ H).
Qed.

Lemma mem_wd_store_init_data: forall {F V} (ge: Genv.t F V) a (b:block) (z:Z) 
  m1 m2 (SID:Genv.store_init_data ge m1 b z a = Some m2),
  valid_genv ge m1 -> mem_wd m1 -> mem_wd m2.
Proof. intros F V ge a.
  destruct a; simpl; intros;
      try apply (mem_wd_store _ _ _ _ _ _ H0 SID); simpl; trivial.
   inv SID; trivial.
   remember (Genv.find_symbol ge i) as d.
     destruct d; inv SID.
     eapply (mem_wd_store _ _ _ _ _ _ H0 H2).
    apply eq_sym in Heqd. 
    destruct H as [H _]; apply (H _ _ Heqd). 
Qed.

Lemma valid_genv_store_init_data: 
  forall {F V}  (ge: Genv.t F V) a (b:block) (z:Z) m1 m2
  (SID: Genv.store_init_data ge m1 b z a = Some m2),
  valid_genv ge m1 -> valid_genv ge m2.
Proof. intros F V ge a.
  destruct a; simpl; intros;
  try solve [
    split; intros x bb; intros; simpl;
      destruct H as [A B]; 
      try apply (Mem.store_valid_block_1 _ _ _ _ _ _ SID _ (A _ _ H0));
      try apply (Mem.store_valid_block_1 _ _ _ _ _ _ SID _ (B _ _ H0))].
    inv SID; trivial.
    remember (Genv.find_symbol ge i) as d.
      destruct d; inv SID. 
      apply eq_sym in Heqd.
      destruct H as [A B].
      split. intros bb; intros; simpl. 
      apply (Mem.store_valid_block_1 _ _ _ _ _ _ H1 _ (A _ _ H)).
      intros; apply (Mem.store_valid_block_1 _ _ _ _ _ _ H1 _ (B _ _ H)).
Qed.

Lemma mem_wd_store_init_datalist: forall {F V} (ge: Genv.t F V) l (b:block) 
  (z:Z) m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
  valid_genv ge m1 -> mem_wd m1 -> mem_wd m2.
Proof. intros F V ge l.
  induction l; simpl; intros. 
    inv SID. trivial.
  remember (Genv.store_init_data ge m1 b z a) as d.
  destruct d; inv SID; apply eq_sym in Heqd.
  apply (IHl _ _ _ _ H2); clear IHl H2.
     eapply valid_genv_store_init_data. apply Heqd. apply H. 
  eapply mem_wd_store_init_data. apply Heqd. apply H. apply H0.
Qed. 

Lemma valid_genv_store_init_datalist: forall {F V} (ge: Genv.t F V) l (b:block)
  (z:Z) m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
   valid_genv ge m1 -> valid_genv ge m2.
Proof. intros F V ge l.
  induction l; simpl; intros. 
    inv SID. trivial.
  remember (Genv.store_init_data ge m1 b z a) as d.
  destruct d; inv SID; apply eq_sym in Heqd.
  apply (IHl _ _ _ _ H1); clear IHl H1.
     eapply valid_genv_store_init_data. apply Heqd. apply H. 
Qed. 

Lemma mem_wd_alloc_global: forall  {F V} (ge: Genv.t F V) a m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   mem_wd m0 -> valid_genv ge m0 -> mem_wd m1.
Proof. intros F V ge a.
destruct a; simpl. intros.
destruct g.
  remember (Mem.alloc m0 0 1) as mm. destruct mm. 
    apply eq_sym in Heqmm. 
    specialize (mem_wd_alloc _ _ _ _ _ Heqmm). intros. 
     eapply (mem_wd_drop _ _ _ _ _  _ GA).
    apply (H1 H). 
    apply (Mem.valid_new_block _ _ _ _ _ Heqmm).
remember (Mem.alloc m0 0 (Genv.init_data_list_size (AST.gvar_init v)) ) as mm.
  destruct mm. apply eq_sym in Heqmm.
  remember (store_zeros m b 0 (Genv.init_data_list_size (AST.gvar_init v)))
           as d. 
  destruct d; inv GA; apply eq_sym in Heqd.
  remember (Genv.store_init_data_list ge m2 b 0 (AST.gvar_init v)) as dd.
  destruct dd; inv H2; apply eq_sym in Heqdd.
  eapply (mem_wd_drop _ _ _ _ _ _ H3); clear H3.
    eapply (mem_wd_store_init_datalist _ _ _ _ _ _ Heqdd).
    apply (valid_genv_store_zeros _ _ _ _ _ _ Heqd).
    apply (valid_genv_alloc ge _ _ _ _ _ Heqmm H0).
  apply (mem_wd_store_zeros _ _ _ _ _ Heqd).
    apply (mem_wd_alloc _ _ _ _ _ Heqmm H).
  unfold Mem.valid_block.
     apply Genv.store_init_data_list_nextblock in Heqdd.
           rewrite Heqdd. clear Heqdd.
      apply Genv.store_zeros_nextblock in Heqd. rewrite Heqd; clear Heqd.
      apply (Mem.valid_new_block _ _ _ _ _  Heqmm).
Qed.

Lemma valid_genv_alloc_global: forall  {F V} (ge: Genv.t F V) a m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   valid_genv ge m0 -> valid_genv ge m1.
Proof. intros F V ge a.
destruct a; simpl. intros.
destruct g.
  remember (Mem.alloc m0 0 1) as d. destruct d. 
    apply eq_sym in Heqd.
    apply (valid_genv_drop _ _ _ _ _ _ _ GA).
    apply (valid_genv_alloc _ _ _ _ _ _ Heqd H).
remember (Mem.alloc m0 0 (Genv.init_data_list_size (AST.gvar_init v)) )
         as Alloc.
  destruct Alloc. apply eq_sym in HeqAlloc.
  remember (store_zeros m b 0 
           (Genv.init_data_list_size (AST.gvar_init v))) as SZ. 
  destruct SZ; inv GA; apply eq_sym in HeqSZ.
  remember (Genv.store_init_data_list ge m2 b 0 (AST.gvar_init v)) as Drop.
  destruct Drop; inv H1; apply eq_sym in HeqDrop.
  eapply (valid_genv_drop _ _ _ _ _ _ _ H2); clear H2.
  eapply (valid_genv_store_init_datalist _ _ _ _ _ _ HeqDrop). clear HeqDrop.
  apply (valid_genv_store_zeros _ _ _ _ _ _ HeqSZ).
    apply (valid_genv_alloc _ _ _ _ _ _ HeqAlloc H).
Qed.

Lemma valid_genv_alloc_globals:
   forall F V (ge: Genv.t F V) init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
   valid_genv ge m0 -> valid_genv ge m.
Proof. intros F V ge l.
induction l; intros; simpl in *.
  inv GA. assumption.
remember (Genv.alloc_global ge m0 a) as d.
  destruct d; inv GA. apply eq_sym in Heqd.
  eapply (IHl  _ _  H1). clear H1.
    apply (valid_genv_alloc_global _ _ _ _ Heqd H).
Qed.

Lemma mem_wd_alloc_globals:
   forall F V (ge: Genv.t F V) init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
   mem_wd m0 -> valid_genv ge m0 -> mem_wd m.
Proof. intros F V ge l.
induction l; intros; simpl in *.
  inv GA. assumption.
remember (Genv.alloc_global ge m0 a) as d.
  destruct d; inv GA. apply eq_sym in Heqd.
eapply (IHl  _ _  H2).
    apply (mem_wd_alloc_global ge _ _ _ Heqd H H0).
    apply (valid_genv_alloc_global _ _ _ _ Heqd H0).
Qed.

Lemma mem_wd_load: forall m ch b ofs v
  (LD: Mem.load ch m b ofs = Some v)
  (WD : mem_wd m), val_valid v m.
Proof. intros.
  destruct v; simpl; trivial.
  destruct (Mem.load_valid_access _ _ _ _ _ LD) as [Perms Align].
  apply Mem.load_result in LD.
  apply eq_sym in LD. apply decode_val_pointer_inv in LD.
  destruct LD.
  destruct ch; inv H; simpl in *.
  unfold mem_wd in WD. unfold Mem.inject_neutral in WD.
  destruct WD.
  assert (Arith: ofs <= ofs < ofs + 4). omega.
  specialize (Perms _ Arith).
  assert (VB:= Mem.perm_valid_block _ _ _ _ _ Perms).
  assert (Z:= flatinj_I (Mem.nextblock m) b VB).
  specialize (mi_memval _ _ _ _ Z Perms).
  inv H0. rewrite Zplus_0_r in mi_memval. rewrite H1 in mi_memval.
  inversion mi_memval. clear H9. subst.
  apply flatinj_E in H5. apply H5.
Qed.

Lemma mem_wd_storebytes: forall m b ofs bytes m' (WDm: mem_wd m)
  (ST: Mem.storebytes m b ofs bytes = Some m')
  (BytesValid: forall v, In v bytes ->
               memval_inject (Mem.flat_inj (Mem.nextblock m)) v v), 
   mem_wd m'.
Proof. intros. apply mem_wdI. intros.
  assert (F: Mem.flat_inj (Mem.nextblock m) b0 = Some (b0, 0)).
        apply flatinj_I. 
        apply (Mem.storebytes_valid_block_2 _ _ _ _ _ ST).
        eapply Mem.perm_valid_block; eassumption.
  apply mem_wd_E in WDm.
  assert (P:= Mem.perm_storebytes_2 _ _ _ _ _ ST _ _ _ _ R).
  specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ WDm) _ _ _ _ F P).
  rewrite Zplus_0_r.
  intros MVI.
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ ST).
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST).
  remember (eq_block b0 b).
  destruct s; subst; clear Heqs.
  (*case b0=b*) 
    rewrite PMap.gss.
    remember (zlt ofs0 ofs) as d.
    destruct d; clear Heqd.
    (*case ofs0 < ofs*) 
      rewrite Mem.setN_outside; try (left; assumption).
      assumption.
    (*case ofs0 >= ofs*)
      remember (zlt ofs0 (ofs + (Z.of_nat (length bytes)))) as d.
      destruct d; clear Heqd.
      (*case <*) 
        eapply Mem.setN_property. 
          apply BytesValid.
          split. omega. apply l. 
      (*case >= *)
         rewrite Mem.setN_outside; try (right; assumption).
      assumption.
  (*case b0 <> b*)
    rewrite PMap.gso; trivial.
Qed.

Lemma getN_aux: forall n p c B1 v B2, Mem.getN n p c = B1 ++ v::B2 ->
    v = ZMap.get (p + Z.of_nat (length B1)) c.
Proof. intros n.
  induction n; simpl; intros. 
    destruct B1; simpl in *. inv H. inv H.
    destruct B1; simpl in *. 
      inv H. rewrite Zplus_0_r. trivial.
      inv H. specialize (IHn _ _ _ _ _ H2). subst.
        rewrite Zpos_P_of_succ_nat. 
        remember (Z.of_nat (length B1)) as m. clear Heqm H2. rewrite <- Z.add_1_l.
         rewrite Zplus_assoc. trivial. 
Qed. 

Lemma getN_range: forall n ofs M bytes1 v bytes2,
  Mem.getN n ofs M = bytes1 ++ v::bytes2 ->
  (length bytes1 < n)%nat.
Proof. intros n.
  induction n; simpl; intros.
    destruct bytes1; inv H. 
    destruct bytes1; simpl in *; inv H.
      omega.
    specialize (IHn _ _ _ _ _ H2). omega.
Qed.

Lemma loadbytes_D: forall m b ofs n bytes
      (LD: Mem.loadbytes m b ofs n = Some bytes),
      Mem.range_perm m b ofs (ofs + n) Cur Readable /\
      bytes = Mem.getN (nat_of_Z n) ofs (PMap.get b (Mem.mem_contents m)).
Proof. intros.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in LD.
  Opaque Mem.loadbytes.
  remember (Mem.range_perm_dec m b ofs (ofs + n) Cur Readable) as d.
  destruct d; inv LD. auto.
Qed.

Lemma loadbytes_valid: forall m (WD: mem_wd m) b ofs' n bytes
      (LD: Mem.loadbytes m b (Int.unsigned ofs') n = Some bytes)
      v (B: In v bytes),
      memval_inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof. intros.
  destruct (loadbytes_D _ _ _ _ _ LD) as [Range BB]; subst. 
  assert (L:= Mem.loadbytes_length _ _ _ _ _ LD).
  apply In_split in B. destruct B as [bytes1 [bytes2 B]]. subst.
  assert (I: Int.unsigned ofs' <= (Int.unsigned ofs') + Z.of_nat (length bytes1) < 
                  Int.unsigned ofs' + n).
    assert (II:= getN_range _ _ _ _ _ _ B).
    clear Range LD B L.
    split. omega.
    assert (Z.of_nat (length bytes1) < Z.of_nat (nat_of_Z n)).
        omega.
    rewrite nat_of_Z_eq in H. omega. clear H.
     unfold nat_of_Z in II.
        destruct n. omega. specialize (Pos2Z.is_pos p); omega.
        rewrite Z2Nat.inj_neg in II. destruct bytes1; simpl in II; inv II.
  specialize (Range _ I). 
  assert (F: Mem.flat_inj (Mem.nextblock m) b = Some (b, 0)).
    apply flatinj_I. apply Mem.perm_valid_block in Range. apply Range.
    specialize (Mem.mi_memval _ _ _ WD _ _ _ _ F Range).
    intros. rewrite Zplus_0_r in H.
   apply getN_aux in B. subst. apply H.
Qed.

Lemma freelist_mem_wd: forall l m m'
      (M: Mem.free_list m l = Some m')
      (WD: mem_wd m), mem_wd m'.
Proof. intros l.
  induction l; simpl; intros.
    inv M; trivial.
  destruct a. destruct p.
  remember (Mem.free m b z0 z) as d.
  destruct d; inv M; apply eq_sym in Heqd.
  apply (IHl _ _ H0).
  eapply mem_wd_free; eassumption. 
Qed.
