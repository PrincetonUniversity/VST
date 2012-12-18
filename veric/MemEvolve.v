Load loadpath.
Require Import veric.base.

Theorem drop_extends:
  forall m1 m2 lo hi b p m1',
  Mem.extends m1 m2 ->
  Mem.drop_perm m1 b lo hi p = Some m1'  ->
  exists m2',
     Mem.drop_perm m2 b lo hi p = Some m2'
  /\ Mem.extends m1' m2'.
Proof.
  intros. inv H.
  destruct (Mem.drop_mapped_inj  _ _ _ b b 0 _ _ _ _ mext_inj H0) as [m2' [D Inj]].
        intros b'; intros. inv H1. inv H2. left. assumption.
         reflexivity.
  repeat rewrite Zplus_0_r in D. exists m2'. split; trivial.
  split; trivial.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ H0). 
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ D). assumption.
Qed.  

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
Admitted. (*FAILs, but is only a goal, not a lemma*)

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

(* A minimal preservation property we sometimes require.*)
Definition mem_forward (m1 m2:mem) :=
  (forall b, Mem.valid_block m1 b ->
      Mem.valid_block m2 b /\ 
       forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p).
       (*was: forall ofs, Mem.perm m1 b ofs Max = Mem.perm m2 b ofs Max*)

Lemma mem_forward_refl: forall m, mem_forward m m.
  Proof. intros m b H. split; eauto. Qed. 

Lemma mem_forward_trans: forall m1 m2 m3, 
  mem_forward m1 m2 -> mem_forward m2 m3 -> mem_forward m1 m3.
  Proof. intros. intros  b Hb.
    destruct (H _ Hb). 
    destruct (H0 _ H1).
    split; eauto. 
Qed. 

(*A value that is (if its a pointer) not dangling wrt m - a condition like this will probably be need to imposed
on after-external return values (and thus also on the values returned by safely-halted)*)
Definition val_valid (v:val) (m:mem):Prop := 
     match v with Vptr b ofs => Mem.valid_block m b | _ => True 
     end.

(*In fact valid vals is a slight relaxtion of valid pointers*)
Lemma valid_ptr_val_valid: forall b ofs m, 
    Mem.valid_pointer m b ofs = true -> val_valid (Vptr b (Int.repr ofs)) m.
Proof. intros.
  apply Mem.valid_pointer_nonempty_perm in H. eapply Mem.perm_valid_block. apply H.
Qed.
(*
Inductive EvolutionStep:Type :=
  EAlloc: forall m m' lo hi b,  Mem.alloc m lo hi = (m',b) -> EvolutionStep
| EStore: forall m m' ch b ofs u, Mem.store ch m b ofs u = Some m' -> EvolutionStep
| EFree: forall m m' b lo hi, Mem.free m b lo hi = Some m' -> EvolutionStep
| EDrop: forall m m' b lo hi p, Mem.drop_perm m b lo hi p = Some m' -> EvolutionStep.

Inductive Evolve: Mem.mem -> Mem.mem -> val -> Type :=
  EvolveVal: forall v m, val_valid v m -> Evolve m m v
| EvolveAlloc: forall m m' m'' v lo hi b,  Mem.alloc m lo hi = (m',b) -> 
                           Evolve m' m'' v -> Evolve m m'' v
| EvolveStore: forall m m' m'' v ch b ofs u, Mem.store ch m b ofs u = Some m' ->
                           Evolve m' m'' v -> Evolve m m'' v
| EvolveFree: forall m m' m'' v b lo hi, Mem.free m b lo hi = Some m' ->
                           Evolve m' m'' v -> Evolve m m'' v
| EvolveDrop: forall m m' m'' v b lo hi p, Mem.drop_perm m b lo hi p = Some m' ->
                           Evolve m' m'' v -> Evolve m m'' v.

Lemma Evolve_nextblock: forall m m'' v (E:Evolve m m'' v), Mem.nextblock m <= Mem.nextblock m''.
Proof. intros.
  induction E; intros. omega.
  apply Mem.nextblock_alloc in e. rewrite e in IHE. omega.
  apply Mem.nextblock_store in e. rewrite e in IHE. omega.
  apply Mem.nextblock_free in e. rewrite e in IHE. omega.
  apply Mem.nextblock_drop in e. rewrite e in IHE. omega.
Qed. 

Fixpoint PurgeEE m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) : option (prod Mem.mem val) :=
match E3 with
  EvolveVal v m V => 
        match v with Vundef => Some (m2,Vundef)
                              | Vint i => Some (m2, Vint i)
                              | Vfloat f => Some (m2, Vfloat f)
                              | Vptr b i => if Mem.valid_pointer m2 b (Int.unsigned i) 
                                                    then Some (m2, Vptr b i) else Some (m2, Vundef)
        end
| EvolveAlloc m m' m'' v lo hi b A E => 
        match Mem.alloc m2 lo hi with (m2',b2) => PurgeEE m' m'' v E m2' end (*have b2=b whenever Match23 indeed is a memory extension*)
| EvolveStore m m' m'' v ch b ofs u St E => 
        match Mem.store ch m2 b ofs u with Some m2' => PurgeEE m' m'' v E m2' | None => None end
| EvolveFree m m' m'' v b lo hi F E => 
        match Mem.free m2 b lo hi with Some m2' => PurgeEE m' m'' v E m2' | None => None end
| EvolveDrop  m m' m'' v b lo hi p D E => 
        match Mem.drop_perm m2 b lo hi p with Some m2' => PurgeEE m' m'' v E m2' | None => None end
end.

Fixpoint PurgeEE1 m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) : prod Mem.mem val :=
match E3 with
  EvolveVal v m V => 
        match v with Vundef => (m2,Vundef)
                              | Vint i => (m2, Vint i)
                              | Vfloat f => (m2, Vfloat f)
                              | Vptr b i => if Mem.valid_pointer m2 b (Int.unsigned i) 
                                                    then (m2, Vptr b i) else (m2, Vundef)
        end
| EvolveAlloc m m' m'' v lo hi b A E => 
        match Mem.alloc m2 lo hi with (m2',b2) => PurgeEE1 m' m'' v E m2' end (*have b2=b whenever Match23 indeed is a memory extension*)
| EvolveStore m m' m'' v ch b ofs u St E => 
        match Mem.store ch m2 b ofs u with 
                     Some m2' => PurgeEE1 m' m'' v E m2' 
                   | None => PurgeEE1 m' m'' v E m2
        end
| EvolveFree m m' m'' v b lo hi F E => 
        match Mem.free m2 b lo hi with 
                     Some m2' => PurgeEE1 m' m'' v E m2'
                   | None => PurgeEE1 m' m'' v E m2 end
| EvolveDrop  m m' m'' v b lo hi p D E => 
        match Mem.drop_perm m2 b lo hi p with
                     Some m2' => PurgeEE1 m' m'' v E m2'
                   | None => PurgeEE1 m' m'' v E m2 end
end.

Lemma PurgeEE1_extends: forall m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) (Ext: Mem.extends m2 m3),
    match PurgeEE1 m3 m3' v3 E3 m2 with (m2',v2) => Mem.extends m2' m3' /\ Val.lessdef v2 v3 end.
Proof. intros m3 m3' v3  E. 
  induction E; simpl; intros.
   (*Val*)
      destruct v.
           split. assumption. apply Val.lessdef_refl.
           split. assumption. apply Val.lessdef_refl.
           split. assumption. apply Val.lessdef_refl.
          remember (Mem.valid_pointer m2 b (Int.unsigned i)) as z.
              destruct z.
                      split. assumption. apply Val.lessdef_refl.
                      split. assumption. constructor.
  (*Alloc*) rename m into m3.
       remember (Mem.alloc m2 lo hi) as z.
       destruct z as [m2' b2]; apply eq_sym in Heqz.
           destruct (Mem.alloc_extends _ _ lo hi _ _ lo hi Ext Heqz) as [m3'' [A EE]].
                omega. omega.
            rewrite A in e. inv e.
            apply (IHE _ EE). 
  (*Store*) rename m into m3. rename m' into m3'.
       remember (Mem.store ch m2 b ofs u) as z.
       destruct z; apply eq_sym in Heqz.
           destruct (Mem.store_within_extends _ _ _ _ _ _ _ _ Ext Heqz (Val.lessdef_refl _)) as [m3'' [St EE]].
            rewrite St in e. inv e.
            apply (IHE _ EE). 
      (*None*) 
           assert (QQ: Mem.extends m2 m3').
                clear IHE. split.
                     apply Mem.nextblock_store in e. rewrite e. eapply Ext.
                     split; intros. inv H. eapply (Mem.perm_store_1 _ _ _ _ _ _ e). 
                                eapply Ext. reflexivity. assumption.
                        inv H. eapply (Mem.store_valid_access_1 _ _ _ _ _ _ e).
                                eapply Ext. reflexivity. assumption.
                 inv H. rewrite (Mem.store_mem_contents _ _ _ _ _ _ e).
(*           assert (ZZ:= Mem.store_valid_access_3 _ _ _ _ _ _ e).
            remember (Mem.valid_access_dec m2 ch b ofs Writable) as q.
            destruct q; clear Heqq. apply (Mem.valid_access_store _ _ _ _ u) in v0.
                      destruct v0. rewrite e0 in Heqz. inv Heqz.*)
                             destruct Ext. destruct mext_inj.
                                specialize (mi_memval b2 _ _ _ (eq_refl _) H0). clear mi_perm mi_access.
                                destruct (eq_block b2 b). subst. rewrite ZMap.gss. rewrite Zplus_0_r in *. 
                                     admit. (*may not hold*)
                                rewrite (ZMap.gso _ _ n). assumption.
            specialize ( IHE _ QQ). apply IHE.
  (*Free*) rename m into m3.
       remember (Mem.free m2 b lo hi ) as z.
       destruct z; apply eq_sym in Heqz.
           destruct (Mem.free_parallel_extends _ _ _ _ _ _  Ext Heqz) as [m3'' [Fr EE]].
            rewrite Fr in e. inv e.
            apply (IHE _ EE). 
         admit. (*ToDo - may not hold*)
  (*Drop*) rename m into m3.
       remember ( Mem.drop_perm m2 b lo hi p) as z.
       destruct z; apply eq_sym in Heqz.
       destruct (drop_extends _ _ _ _ _ _ _ Ext Heqz) as [m3'' [DR EE]].
            rewrite DR in e. inv e.
            apply (IHE _ EE). 
         admit. (*ToDo - may not hold*)
Qed.

Lemma PurgeEE1_Evolve: forall m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) (Ext: Mem.extends m2 m3),
    match PurgeEE1 m3 m3' v3 E3 m2 with (m2',v2) => Evolve m2 m2' v2 end.
Proof. intros m3 m3' v3 E.
  induction E; intros; simpl in *.
  (*Val*)
     destruct v; try apply EvolveVal. auto. auto. auto.
       simpl in v0. 
       remember (Mem.valid_pointer m2 b (Int.unsigned i)) as z.
       destruct z. econstructor. simpl. apply (Mem.valid_block_extends _ _ b) in Ext.
                            apply Ext. assumption.
           econstructor. simpl. trivial.
  (*Alloc*)
      remember (Mem.alloc m2 lo hi) as z. destruct z. apply eq_sym in Heqz.
      (*destruct (Mem.alloc_extends _ _ lo hi _ _ lo hi Ext Heqz). as [m3'' [A EE]].
                omega. omega.
            rewrite A in e. inv e.
            apply (IHE _ EE). 
      *)
Admitted.
(*
Lemma PurgeEE' m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) : option (prod Mem.mem val).
Proof. generalize dependent m2.
  induction E3; intros m2.
  (*Val*) rename m into m3. rename v0 into V.
      destruct v.
      apply (Some (m2,Vundef)).
      apply (Some (m2, Vint i)).
      apply (Some (m2, Vfloat f)).
      apply (if Mem.valid_pointer m2 b (Int.unsigned i) then Some (m2, Vptr b i) else Some (m2, Vundef)).
  (*Alloc*)  rename m into m3. 
       destruct (Mem.alloc m2 lo hi) as [m2' b2]. (*have b2=b whenever Match23 indeed is a memory extension*)
       apply (IHE3 m2').
  (*Store*) rename m into m3. 
       destruct (Mem.store ch m2 b ofs u). 
       (*Some *) rename m into m2'. apply (IHE3 m2').
       (*None*) apply None.
  (*Free*) rename m into m3. 
       destruct (Mem.free m2 b lo hi). 
       (*Some *) rename m into m2'. apply (IHE3 m2').
       (*None*) apply None.
  (*Free*) rename m into m3. 
       destruct (Mem.drop_perm m2 b lo hi p). 
       (*Some *) rename m into m2'. apply (IHE3 m2').
       (*None*) apply None.
Defined.

Goal forall m3 m3' v3  (E3: Evolve m3 m3' v3) m2, PurgeEE m3 m3' v3 E3 m2 = PurgeEE' m3 m3' v3 E3 m2.
Proof. intros m3 m3' v3  E.
  induction E; simpl; intros.
      destruct v; trivial.
       remember (Mem.alloc m2 lo hi) as z. destruct z; trivial.
       remember (Mem.store ch m2 b ofs u) as z. destruct z; trivial.
       remember (Mem.free m2 b lo hi) as z. destruct z; trivial.
       remember (Mem.drop_perm m b lo hi p) as z. destruct z; trivial.
Qed.
*)

Lemma PurgeEE_Evaolve: forall m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) (Ext: Mem.extends m2 m3),
    match PurgeEE m3 m3' v3 E3 m2 with Some(m2',v2) => Evolve m2 m2' v2 | None => True end.
Admitted.

Lemma PurgeEE_extends: forall m3 m3' v3 (E3: Evolve m3 m3' v3) (m2:Mem.mem) (Ext: Mem.extends m2 m3),
    exists m2', exists v2, PurgeEE m3 m3' v3 E3 m2 = Some(m2',v2) /\ Mem.extends m2' m3' /\ Val.lessdef v2 v3.
Proof. intros m3 m3' v3  E. 
  induction E; simpl; intros.
   (*Val*)
      destruct v.
          eexists; eexists; split; try reflexivity.
           split. assumption. apply Val.lessdef_refl.
          eexists; eexists; split; try reflexivity.
           split. assumption. apply Val.lessdef_refl.
          eexists; eexists; split; try reflexivity.
           split. assumption. apply Val.lessdef_refl.
          remember (Mem.valid_pointer m2 b (Int.unsigned i)) as z.
              destruct z. 
                eexists; eexists; split; try reflexivity.
                      split. assumption. apply Val.lessdef_refl.
                eexists; eexists; split; try reflexivity.
                      split. assumption. constructor.
  (*Alloc*) rename m into m3.
       remember (Mem.alloc m2 lo hi) as z.
       destruct z as [m2' b2]; apply eq_sym in Heqz.
           destruct (Mem.alloc_extends _ _ lo hi _ _ lo hi Ext Heqz) as [m3'' [A EE]].
                omega. omega.
            rewrite A in e. inv e.
            apply (IHE _ EE). 
  (*Store*) rename m into m3.
       remember (Mem.store ch m2 b ofs u) as z.
       destruct z; apply eq_sym in Heqz.
           destruct (Mem.store_within_extends _ _ _ _ _ _ _ _ Ext Heqz (Val.lessdef_refl _)) as [m3'' [St EE]].
            rewrite St in e. inv e.
            apply (IHE _ EE). 
      (*None*) clear IHE E.
           assert (ZZ:= Mem.store_valid_access_3 _ _ _ _ _ _ e).
            remember (Mem.valid_access_dec m2 ch b ofs Writable) as q.
            destruct q; clear Heqq. apply (Mem.valid_access_store _ _ _ _ u) in v0.
                      destruct v0. rewrite e0 in Heqz. inv Heqz.
            destruct Ext. destruct mext_inj.
         admit. (*ToDo - may not hold*)
  (*Free*) rename m into m3.
       remember (Mem.free m2 b lo hi ) as z.
       destruct z; apply eq_sym in Heqz.
           destruct (Mem.free_parallel_extends _ _ _ _ _ _  Ext Heqz) as [m3'' [Fr EE]].
            rewrite Fr in e. inv e.
            apply (IHE _ EE). 
         admit. (*ToDo - may not hold*)
  (*Drop*) rename m into m3.
       remember ( Mem.drop_perm m2 b lo hi p) as z.
       destruct z; apply eq_sym in Heqz.
       destruct (drop_extends _ _ _ _ _ _ _ Ext Heqz) as [m3'' [DR EE]].
            rewrite DR in e. inv e.
            apply (IHE _ EE). 
         admit. (*ToDo - may not hold*)
Qed.

Lemma pushout_EE1: forall   m3 m3' v3 (Fwd3: Evolve m3 m3' v3 )
                 m1 m1' v1 (Fwd1: Evolve m1 m1' v1) m2 (Ext12: Mem.extends m1 m2)
                 (Ext23: Mem.extends m2 m3) (LD : Val.lessdef v1 v3) 
                                          (Ext13' : Mem.extends m1' m3')
                                          (UnchOn3: Events.mem_unchanged_on (Events.loc_out_of_bounds m1) m3 m3'),
       exists m2',  (*Evolve m2 m2' v1 /\*)
              Mem.extends m1' m2' /\ Events.mem_unchanged_on (Events.loc_out_of_bounds m1) m2 m2' /\
                                          Mem.extends m2' m3'.
Proof. intros.
   destruct (PurgeEE_extends _ _ _ Fwd3 _ Ext23) as [m2' [v2 [Prg [Ext23' LD23]]]].
   exists m2'. 
   split. 
Admitted.

(*
Lemma getSteps m3 m3' v3 (E:Evolve m3 m3' v3) : list EvolutionStep.
Proof.
  intros. induction E.
  (*Val*) apply nil.
  (*Alloc*) apply ((EAlloc _ _ _ _ _ e) :: IHE).
  (*Store*) apply ((EStore _ _ _ _ _ _ e) :: IHE).
  (*Free*) apply ((EFree _ _ _ _ _ e) :: IHE).
  (*Drop*) apply ((EDrop _ _ _ _ _ _ e) :: IHE).
Defined.

(*purge the Sem3-evolution list for cases where match12 and match23 are extensions.
  Allocations are erase, and so are stores and drop_perms for which m2 odes not have appropriate permission*)
Fixpoint purge_ext_ext (l: list EvolutionStep)(m2:mem) : list EvolutionStep :=
  match l with nil => nil
    | (step::steps) => match step with
                                      EAlloc m1 m1'  lo hi b e => purge_ext steps m2
                                    | EStore m m' ch b ofs u e
                                  end
  end.
*)

Lemma Evolve_forward: forall m m'' v (E:Evolve m m'' v),  mem_forward m m''.
Proof. intros. induction E; intros b1; intros.
   split; trivial.
   split. apply IHE. eapply Mem.valid_block_alloc; eassumption.
             intros. apply IHE in H0.
                            eapply Mem.perm_alloc_4; try eassumption.
                                intros N; subst. eapply Mem.fresh_block_alloc. apply e. apply H.
                           eapply Mem.valid_block_alloc; eassumption.
  split. apply IHEvolve. eapply Mem.store_valid_block_1; eassumption.
             intros. apply IHEvolve in H2.
                            eapply Mem.perm_store_2; try eassumption.
                           eapply Mem.store_valid_block_1; eassumption.
  split. apply IHEvolve. eapply Mem.valid_block_free_1; eassumption.
             intros. apply IHEvolve in H2.
                            eapply Mem.perm_free_3; try eassumption.
                           eapply Mem.valid_block_free_1; eassumption.
  split. apply IHEvolve. eapply Mem.drop_perm_valid_block_1; eassumption.
             intros. apply IHEvolve in H2.
                            eapply Mem.perm_drop_4; try eassumption.
                           eapply Mem.drop_perm_valid_block_1; eassumption.
Qed.
*)

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
  admit. (*ToDo: prove that content of m' at that loc is same as in m*)
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
          destruct v. constructor. constructor. constructor.  econstructor. eapply flatinj_I. apply V. rewrite Int.add_zero. trivial.
Qed.
(*
Inductive StrongEvolve: Mem.mem -> Mem.mem -> val -> Prop :=
  SEvolveVal: forall v m, mem_wd m -> 
                           val_valid v m -> StrongEvolve m m v
| SEvolveAlloc: forall m m' m'' v lo hi b,  mem_wd m -> 
                           Mem.alloc m lo hi = (m',b) -> 
                           StrongEvolve m' m'' v -> StrongEvolve m m'' v
| SEvolveStore: forall m m' m'' v ch b ofs u, mem_wd m ->
                           val_valid u m ->
                           Mem.store ch m b ofs u = Some m' ->
                           StrongEvolve m' m'' v -> StrongEvolve m m'' v
| SEvolveFree: forall m m' m'' v b lo hi, mem_wd m ->
                           Mem.free m b lo hi = Some m' ->
                           StrongEvolve m' m'' v -> StrongEvolve m m'' v
| SEvolveDrop: forall m m' m'' v b lo hi p, mem_wd m ->
                           Mem.drop_perm m b lo hi p = Some m' ->
                           Mem.valid_block m b ->
                           StrongEvolve m' m'' v -> StrongEvolve m m'' v.

Lemma StrongEvolve_Evolve: forall m m'' v, StrongEvolve m m'' v -> Evolve m m'' v.
Proof. intros. induction H; intros. 
   eapply EvolveVal; try eassumption.
   eapply EvolveAlloc; try eassumption.
   eapply EvolveStore; try eassumption.
   eapply EvolveFree; try eassumption.
   eapply EvolveDrop; try eassumption.
Qed.

Lemma StrongEvolve_forward: forall m m'' v, StrongEvolve m m'' v -> 
                            mem_forward m m''.
Proof. intros. apply StrongEvolve_Evolve in H. apply (Evolve_forward _ _ _ H). Qed.

Lemma StrongEvolve_wd: forall m m'' v, StrongEvolve m m'' v -> 
   mem_wd m /\  mem_wd m'' /\  val_valid v m''.
Proof. intros. induction H; intros.
   split; auto.
   destruct IHStrongEvolve as [WD' [WD'' VV'']].
        split; auto.
   destruct IHStrongEvolve as [WD' [WD'' VV'']].
        split; auto.
   destruct IHStrongEvolve as [WD' [WD'' VV'']].
        split; auto.
   destruct IHStrongEvolve as [WD' [WD'' VV'']].
        split; auto.
Qed.

Lemma StrongEvolve_wd1: forall m m'' v, StrongEvolve m m'' v -> 
   mem_wd m ->  mem_wd m'' /\  val_valid v m''.
Proof. intros. induction H; intros.
   split; auto.
   apply IHStrongEvolve. eapply mem_wd_alloc; eassumption.
   apply IHStrongEvolve. eapply mem_wd_store; eassumption.
   apply IHStrongEvolve. eapply mem_wd_free; eassumption.
   apply IHStrongEvolve. eapply mem_wd_drop; eassumption.
Qed.
*)