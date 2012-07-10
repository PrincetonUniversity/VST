Require Import Wellfounded.

Require Import veric.base.

Require Import compcert.Events.

Require Import veric.forward_simulations.


Module Simulations : SIMULATIONS.


Lemma mem_forward_refl : forall m,
  mem_forward m m.
Proof.
  repeat intro; auto.
Qed.

Lemma mem_forward_trans : forall m1 m2 m3,
  mem_forward m1 m2 ->
  mem_forward m2 m3 ->
  mem_forward m1 m3.
Proof.
  repeat intro; auto.
  apply H in H1. destruct H1.
  apply H0 in H1. destruct H1.
  split; auto. congruence.
Qed.

Lemma free_mem_forward :  forall m1 b lo hi m2,
  Mem.free m1 b lo hi = Some m2 ->
  mem_forward m1 m2.
Proof.
  repeat intro.
  split.
  eapply Mem.valid_block_free_1; eauto.
  symmetry.
Admitted.  (* Likely not true *)

Lemma store_mem_forward : forall chunk m1 b ofs v m2,
  Mem.store chunk m1 b ofs v = Some m2 ->
  mem_forward m1 m2.
Proof.
  repeat intro. split.
  eapply Mem.store_valid_block_1; eauto.
  symmetry.
  admit.  (* likely true *)
Qed.

Lemma alloc_mem_forward : forall m1 b lo hi m2,
  Mem.alloc m1 lo hi = (m2,b) ->
  mem_forward m1 m2.
Proof.
  repeat intro. split.
  eapply Mem.valid_block_alloc; eauto.
  symmetry.
  admit.  (* likely true *)
Qed.


Lemma allowed_core_modification_refl : forall m,
  allowed_core_modification m m.
Proof.
  clear. intros.
  hnf. split; auto.
  apply mem_forward_refl.
Qed.

Lemma allowed_core_modification_trans : forall m1 m2 m3,
  allowed_core_modification m1 m2 ->
  allowed_core_modification m2 m3 ->
  allowed_core_modification m1 m3.
Proof.
  intros. destruct H. destruct H0.
  split.
  eapply mem_forward_trans; eauto.
  destruct H1; destruct H2.
  split; intros.
  specialize (H1 b ofs p H5).
  destruct H1.
  specialize (H2 b ofs p H1).
  destruct H2; auto.
  right. destruct H2; split; auto.
  destruct H3. apply H3; auto.
  apply Mem.perm_valid_block in H5. auto.
  destruct H1.
  right. split; auto.
  repeat intro.
  eapply H6.
  destruct H4. eapply H4; eauto.
  apply Mem.perm_valid_block in H5. 
  apply H in H5. destruct H5; auto.
  
  split; intros.
  destruct H3. destruct H4.
  apply H3; auto.
  apply H4; auto.
  apply H in H5. destruct H5; auto.
  destruct H3; destruct H4.
  generalize H5; intros.
  apply H6 in H5. destruct H5.
  generalize H5; intros.
  apply H7 in H5. destruct H5. auto.
  destruct H5 as [ofs [? ?]].
  right. exists ofs. split; auto.
  apply H3; auto.
  admit.  (* whatever *)
  admit.  (* whatever *)
Qed.

Require Import Zwf.

(*
Lemma getN_clearN : forall n ofs' m1 b lo hi,
  ofs' + n <= lo \/ hi <= ofs' ->
  Mem.getN (nat_of_Z n) ofs' (Mem.clearN (Mem.mem_contents m1) b lo hi b) =
  Mem.getN (nat_of_Z n) ofs' (Mem.mem_contents m1 b).
Proof.
  intro n.
  induction n using (well_founded_induction (Zwf_well_founded 0)).
  intros.
  assert (n <= 0 \/ n > 0) by omega.
  destruct H1.
  replace (nat_of_Z n) with O. simpl. auto.
  symmetry. apply nat_of_Z_neg. auto.
  replace n with (1 + (n - 1)) by omega.
  rewrite nat_of_Z_plus. 2: omega. 2: omega.
  simpl. f_equal.
  unfold Mem.clearN.
  destruct (zeq b b).
  destruct (zle lo ofs').
  destruct (zlt ofs' hi).
  elimtype False. omega.
  simpl; auto. simpl; auto.
  elim n0; auto.
  apply H.
  red. omega.
  omega.
Qed.
*)

Lemma free_allowed_core_mod : forall m1 b lo hi m2,
  Mem.free m1 b lo hi = Some m2 ->
  allowed_core_modification m1 m2.
Proof.
  intros. split.
  eapply free_mem_forward; eauto.
  split; intros.
  unfold block in *.
  assert 
    ((b0 <> b \/ ofs < lo \/ hi <= ofs) \/
     (b = b0 /\ lo <= ofs /\ ofs < hi)) by omega.
  destruct H1.
  left. eapply Mem.perm_free_1; eauto.
  destruct H1; subst.
  right. split.
  apply Mem.free_range_perm in H.
  apply H. auto.
  intro. eapply Mem.perm_free_2; eauto.
  split; intros.
  eapply Mem.perm_free_3; eauto.
  admit. 
Qed.


Lemma alloc_allowed_core_mod : forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2,b) ->
  allowed_core_modification m1 m2.
Proof.
  intros. split.
  eapply alloc_mem_forward; eauto.

  split; intros.
  left. eapply Mem.perm_alloc_1; eauto.
  split; intros.
  eapply Mem.perm_alloc_inv in H1; eauto.
  destruct (zeq b0 b); subst; auto.
  elimtype False. revert H0.
  eapply Mem.fresh_block_alloc; eauto.
  
  left.
  admit.
Qed.


Lemma store_allowed_core_mod : forall m1 chunk v b ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 ->
  allowed_core_modification m1 m2.
Proof.
  intros. split.
  eapply store_mem_forward; eauto.

  split; intros.
  left. eapply Mem.perm_store_1; eauto.
  split; intros.
  eapply Mem.perm_store_2; eauto.
  rename b0 into b'.
  unfold block in *.
  assert
    ((b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs') \/
     (b' = b /\ 0 < n /\ ofs < ofs' + n /\ ofs' < ofs + size_chunk chunk)) by omega.
  destruct H1.
  left. erewrite Mem.loadbytes_store_other; eauto.
  destruct H1; subst.
  right.
  apply Mem.store_valid_access_3 in H.
  assert (ofs' <= ofs \/ ofs < ofs') by omega.
  destruct H1.
  exists ofs. split. omega.
  apply H. destruct chunk; simpl; omega.
  assert (ofs + size_chunk chunk < ofs' +  n \/ ofs' + n  <= ofs + size_chunk chunk) by omega.
  destruct H3.
  exists (ofs + size_chunk chunk - 1).
  split. omega.
  apply H.
  destruct chunk; simpl in *; omega.
  exists ofs'. split. omega.
  apply H.
  omega.
Qed.





Definition heap_data := block -> bool.

Definition heap_data_extends (hd1 hd2:heap_data) := 
  forall x, hd1 x = true -> hd2 x = true.

Definition heap_data_matches (hd:heap_data) (m:mem) :=
  forall b, hd b = true -> Mem.valid_block m b.

Definition heap_data_inj_matches (hd:heap_data) (j:meminj) (m:mem) :=
  forall b, hd b = true ->
    exists b',
      j b = Some (b',0) /\
      Mem.valid_block m b'.

(* A forward simulation structure which uses a memory injection *)
Section ForwardSimStruct_inject.
  Variable core_data:Type.

  Definition heap_injection_invariant (j:meminj) (hd:heap_data) :=
    forall b, hd b = true ->
    forall b' b2 delta delta',
      j b  = Some (b2,delta) ->
      j b' = Some (b2,delta') ->
      b = b' /\ delta = 0 /\ delta' = 0.

  Record inject_sim_data :=
  { isd_core_data : option core_data
  ; isd_meminj    : meminj
  ; isd_heap_data : heap_data
  ; isd_invariant : heap_injection_invariant isd_meminj isd_heap_data
  }.

  Definition inj_data_extends (d1 d2:inject_sim_data) :=
    inject_incr (isd_meminj d1) (isd_meminj d2) /\
    heap_data_extends (isd_heap_data d1) (isd_heap_data d2).

  Definition inj_match_external_mem (d1 d2:inject_sim_data) (m1 m2 m1' m2':mem) :=
    inj_data_extends d1 d2 /\
    Mem.inject (isd_meminj d1) m1 m2 /\
    Mem.inject (isd_meminj d2) m1' m2' /\
    mem_unchanged_on (loc_unmapped (isd_meminj d1)) m1 m1' /\
    mem_unchanged_on (loc_out_of_reach (isd_meminj d1) m1) m2 m2' /\
    inject_separated (isd_meminj d1) (isd_meminj d2) m1 m2 /\
    heap_data_matches (isd_heap_data d1) m1 /\
    heap_data_inj_matches (isd_heap_data d1) (isd_meminj d1) m2 /\
    heap_data_matches (isd_heap_data d2) m1' /\
    heap_data_inj_matches (isd_heap_data d2) (isd_meminj d2) m2' /\
    mem_forward m1 m1' /\
    mem_forward m2 m2'.

  Definition inj_match_block (d:inject_sim_data) (b1:block) (b2:block) :=
    isd_meminj d b1 = Some (b2,0) /\ isd_heap_data d b1 = true.

  Definition inj_match_addr (d:inject_sim_data) (b1:block) (ofs1:Z) (b2:block) (ofs2:Z) :=
    match isd_meminj d b1 with
    | Some (b2',delta) => b2 = b2' /\ ofs2 = ofs1 + delta
    | None => False
    end.
  

Lemma range_chunk: forall i ch,   i <= i < i + size_chunk ch.
Proof. destruct ch; simpl; omega. Qed.

Lemma range_chunk': forall i ch,   i <= i + size_chunk ch - 1 < i + size_chunk ch.
Proof. destruct ch; simpl; omega. Qed.

  Obligation Tactic := intuition.
  Program Definition ForwardSimStruct_inj : ForwardSimulationStructure inject_sim_data :=
    @Build_ForwardSimulationStructure _
      inj_data_extends
      inj_match_addr
      (fun d t v1 v2 => val_inject (isd_meminj d) v1 v2 /\ Val.has_type v2 t)
      inj_match_block
      inj_match_external_mem
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ .
  Next Obligation.
    split; hnf; auto.
  Qed.
  Next Obligation.
    hnf in H, H0. hnf; intuition.
    hnf; intros; intuition.
    hnf; intros; intuition.
  Qed.
  Next Obligation.
    hnf in H0. hnf.
    hnf in H.
    revert H0. case_eq ((isd_meminj d) b1); intros.
    destruct p.
    destruct H1; subst.
    destruct H. apply H in H0.
    rewrite H0. split; auto.
    inv H1.
  Qed.
  Next Obligation.
    hnf in H0. hnf. intuition.
    destruct H; simpl in *. auto.
    destruct H; simpl in *. auto.
  Qed.
  Next Obligation.
    inv H1; econstructor; eauto.
    destruct H. apply H. auto.
  Qed.
  Next Obligation.
    inv H0; destruct t; simpl; auto.
  Qed.
  Next Obligation.
    hnf. auto.
  Qed.
  Next Obligation.
    hnf. auto.
  Qed.
  Next Obligation.
    inv H0. auto.
  Qed.
  Next Obligation.
    hnf. auto.
  Qed.
  Next Obligation.
    inv H0. auto.
  Qed.
  Next Obligation.
    hnf in H.
    revert H. case_eq (isd_meminj d b); intros.
    destruct p. intuition; subst.
    econstructor; eauto.
    unfold Int.add.
    apply Int.eqm_samerepr.
    apply Int.eqm_add.
    apply Int.eqm_unsigned_repr.
    apply Int.eqm_unsigned_repr.
    elim H0.
    simpl; auto.
  Qed.
  Next Obligation.
    inv H0.
    exists b2. exists (Int.add ofs (Int.repr delta)).
    split; auto.
  Qed.
  Next Obligation.
    inv H2. hnf. rewrite H6. split; auto.
    hnf in H0.
    decompose [and] H0.
    erewrite Mem.address_inject; eauto.
   (*  rewrite <- Mem.valid_pointer_nonempty_perm. auto. *)
    admit.
  Qed.
  Next Obligation.
    hnf in H; destruct H.
    hnf. rewrite H.
    split; auto.
    inv H1. simpl.
    rewrite H in H6. inv H6.
    rewrite Zmod_0_l. rewrite Zplus_0_r.
   rewrite Zmod_small; auto.
   apply Int.unsigned_range.
  Qed.
  Next Obligation.
    destruct H.
    hnf. rewrite H.
    split; auto. omega.
  Qed.
Obligation Tactic := idtac.
  Next Obligation.
    intros.
    hnf in H. destruct H.
    hnf in H0.
    rewrite H in H0.
    intuition.
  Qed.
  Next Obligation.
    intros.
    hnf in H. destruct H.
    hnf in H0.
    case_eq (isd_meminj d b2); intros; rewrite H2 in H0.
    destruct p. decompose [and] H0. clear H0. subst.
    generalize (isd_invariant d b H1); intros.
    specialize (H0 b2 b0 0 z).
    intuition.
    elim H0.
  Qed.
  Next Obligation.
    intros. destruct H0.
    hnf in H. destruct H.
    inv H0.
    rewrite H in H6. inv H6.
    split; auto.
    rewrite Int.add_zero; auto.
  Qed.
  Next Obligation.
    intros. destruct H0.
    inv  H0. destruct H.
    generalize (isd_invariant d b H0); intros.
    specialize (H2 b2 b' 0 delta).
    intuition; subst.
    rewrite Int.add_zero; auto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    hnf in H. hnf.
    revert H.
    case_eq (isd_meminj d b); intros; auto.
    destruct p. intuition.
  Qed.
  Next Obligation.
   inv H0.
   econstructor; eauto.
   do 2 rewrite Int.add_assoc.
   rewrite (Int.add_commut delta). auto.
  Qed.
  Next Obligation.
    set (hd := fun x => if zlt x (Mem.nextblock m) then true else false).
    assert (heap_injection_invariant (Mem.flat_inj (Mem.nextblock m)) hd).
      repeat intro.
      unfold hd in *.
      unfold Mem.flat_inj in *.
      destruct (zlt b (Mem.nextblock m)); inv H1.
      destruct (zlt b' (Mem.nextblock m)); inv H2.
      auto.
    assert (True) by auto.
    exists (Build_inject_sim_data None _ _ H0).

    split.
    hnf; simpl. intuition.
    split; simpl; hnf; auto.
    hnf; split; intros; auto.
    hnf; split; intros; auto.
    hnf; intros. rewrite H2 in H3. inv H3.
    hnf; intros. unfold hd in *.
    destruct (zlt b (Mem.nextblock m)).
    red. auto.
    discriminate.
    hnf; intros. unfold hd in *.
    destruct (zlt b (Mem.nextblock m)).
    exists b. split.
    unfold Mem.flat_inj.
    destruct (zlt b (Mem.nextblock m)); auto.
    elimtype False; omega.
    red; auto.
    discriminate.
    hnf; intros.
    unfold hd in *.
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)); auto.
    discriminate.
    hnf; intros.
    unfold hd in *.
    unfold Mem.valid_block.
    unfold Mem.flat_inj.
    destruct (zlt b (Mem.nextblock m)); auto.
    exists b. split; auto.
    discriminate.
    hnf; auto.
    hnf; auto.
    
    intros. split; simpl. unfold Mem.flat_inj.
    red in H2.
    destruct (zlt b (Mem.nextblock m)); auto.
    elimtype False. omega.
    unfold hd.
    destruct (zlt b (Mem.nextblock m)); auto.
  Qed.
  Next Obligation.
    hnf in H. intuition.
  Qed.
  Next Obligation.
    hnf in H0. revert H0.
    case_eq (isd_meminj d b1); intros. destruct p.
    destruct H2; subst.
    hnf in H. intuition.
    eapply Mem.valid_block_inject_2; eauto.
    elim H2.
    hnf in H0. revert H0.
    case_eq (isd_meminj d b1); intros. destruct p.
    destruct H2; subst.
    hnf in H. intuition.
    eapply Mem.valid_block_inject_1; eauto.
    elim H2.
  Qed.
  Next Obligation.
    hnf in H. intuition.
    hnf in H0.
    revert H0. case_eq (isd_meminj d b1); intros.
    destruct p0. intuition; subst.
    eapply Mem.perm_inject; eauto.
    elim H12.
  Qed.
  Next Obligation.
    hnf in H. intuition.
    hnf in H0. revert H0. case_eq (isd_meminj d b1); intros.
    destruct p. intuition; subst.
    generalize H1; intro.
    eapply Mem.load_inject in H1; eauto.
    destruct H1. destruct H1. exists x; intuition.
    eapply Mem.load_type; eauto.
    elim H12.
  Qed.
  Next Obligation.
    hnf in H; intuition.
    generalize H0; intro.
    eapply Mem.alloc_parallel_inject with (lo2:=lo) (hi2:=hi) in H11; eauto; try omega.
    destruct H11 as [? [? [? [? [? [? [? ?]]]]]]].
    exists x0. exists x1.
    assert (heap_injection_invariant x
      (fun b' => if Z_eq_dec b' b1 then true else isd_heap_data d b')).
      hnf. simpl. intros.
      destruct (Z_eq_dec b b1); subst.
      inv H17.
      rewrite H15 in H18. inv H18.
      hnf in H12.
      generalize (isd_invariant d). intro.
      hnf in H17.
      destruct (Z_eq_dec b' b1). subst. intuition.
      congruence.
      rewrite H16 in H19; auto.
      assert (Mem.valid_block m2 b2).
      eapply Mem.valid_block_inject_2 with (f:=isd_meminj d); eauto.
      eapply Mem.fresh_block_alloc in H18; eauto. elim H18.
      destruct (Z_eq_dec b' b1). subst.
      rewrite H15 in H19. inv H19.
      rewrite H16 in H18; auto.
      assert (Mem.valid_block m2 b2).
      eapply Mem.valid_block_inject_2 with (f:=isd_meminj d); eauto.
      eapply Mem.fresh_block_alloc in H19; eauto. elim H19.
      rewrite H16 in H18; auto.
      rewrite H16 in H19; auto.
      eapply (isd_invariant d); eauto.
    assert (True) by auto.
    exists (Build_inject_sim_data (isd_core_data d)  _ _ H17).
    split.
    hnf. simpl. split; auto.
    destruct (Z_eq_dec b1 b1); auto. 
    hnf; intuition.
    hnf. simpl. intuition.
    destruct H1. 
    repeat intro. 
    destruct (Z_eq_dec x2 b1); subst; auto.
    hnf; simpl. unfold inj_data_extends. simpl. clear H18.
    intuition.

    hnf; intros.
    destruct H1. apply H1 in H18.
    destruct (Z_eq_dec b b1). subst.
    eapply Mem.valid_block_inject_1 in H2; eauto.
    rewrite  H16; auto.
    hnf; simpl; intros.
    destruct (Z_eq_dec x2 b1); auto.
    destruct H1. eapply H19; auto.

    split; repeat intro.
    eapply Mem.perm_alloc_1; eauto.
    destruct H3. eapply H3; auto.
    replace (Mem.load chunk m1' b ofs) with (Mem.load chunk m1 b ofs).
    destruct H3. eapply H20; auto.
    symmetry.
    eapply Mem.load_alloc_unchanged; eauto.
    eapply H10.
    apply Mem.load_valid_access in H19.
    destruct H19.
    hnf in H19.
    specialize (H19 ofs).
    eapply Mem.perm_valid_block.
    apply H19.
    split. omega. destruct chunk; simpl; omega.
    
    split; repeat intro.
    eapply Mem.perm_alloc_1; eauto.
    destruct H4. eapply H4; eauto.
    replace (Mem.load chunk x0 b ofs) with
      (Mem.load chunk m2 b ofs).
    destruct H4. eapply H20; eauto.
    symmetry.
    eapply Mem.load_alloc_unchanged; eauto.
    hnf in H12. destruct (H12 b); auto.
    apply Mem.load_valid_access in H19.
    destruct H19.
    hnf in H19.
    eapply Mem.perm_valid_block; apply (H19 ofs).
    split. omega. destruct chunk; simpl; omega.
    
    simpl; repeat intro.
    destruct (Z_eq_dec b0 b1). subst.
    rewrite H15 in H19. inv H19.
    split.
    intro.
    apply H10 in H19. destruct H19.
    revert H19.
    eapply Mem.fresh_block_alloc; eauto.
    intro. apply H12 in H19. destruct H19.
    revert H19.
    eapply Mem.fresh_block_alloc; eauto.
    rewrite H16 in H19; auto.
    eapply H5; eauto.

    simpl; repeat intro. destruct (Z_eq_dec b b1). inv H18.
    eapply Mem.valid_new_block; eauto.
    eapply Mem.valid_block_alloc; eauto.

    hnf; simpl; intros.
    destruct (Z_eq_dec b b1). subst. inv H18.
    exists x1. split; auto.
    eapply Mem.valid_new_block; eauto.
    apply H9 in H18.
    destruct H18 as [? [? ?]].
    rewrite H16; auto.
    exists x2. split; auto.
    eapply Mem.valid_block_alloc; eauto.

    eapply mem_forward_trans. eauto.
    eapply alloc_mem_forward; eauto.
    eapply mem_forward_trans. eauto.
    eapply alloc_mem_forward; eauto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    rename H4 into Htyp.
    hnf in H. intuition.
    generalize H0; intro.
    hnf in H1. revert H1.
    case_eq (isd_meminj d b1); intros. destruct p.
    destruct H15 as [? ?]; subst.
    eapply Mem.store_mapped_inject in H0; eauto.
    destruct H0 as [? [? ?]].
    exists x. exists d.
    split; auto.
    split.
    split; hnf; auto.

    hnf; intuition.
    split; repeat intro.
    destruct H5.
    eapply Mem.perm_store_1; eauto.
    replace (Mem.load chunk0 m1' b0 ofs)
      with (Mem.load chunk0 m1 b0 ofs).
    destruct H5. eapply H18; auto.
    unfold loc_unmapped in H16.
    hnf in H7.
    destruct (Z_eq_dec b0 b1); auto.
    subst.
    destruct (H7 b1 b z); auto.
    apply (H16 ofs).
    split. omega. destruct chunk0; simpl; omega.
    eapply Mem.load_valid_access in H17.
    destruct H17.
    specialize (H17 ofs).
    apply Mem.perm_valid_block in H17. contradiction.
    split. omega. destruct chunk0; simpl; omega.
    symmetry; eapply Mem.load_store_other; eauto.

    split; intros.
    eapply Mem.perm_store_1; eauto.
    destruct H6; auto.
    replace (Mem.load chunk0 x b0 ofs) with
      (Mem.load chunk0 m2 b0 ofs).
    destruct H6; auto.
    symmetry.
    eapply Mem.load_store_other; eauto.
    destruct (Z_eq_dec b0 b); auto.
    subst b0.
    right.
    case_eq (isd_meminj dx b1); intros.
    destruct p.
    generalize H18; intros.
    apply H2 in H18.
    rewrite H1 in H18. inv H18.
    eapply Mem.store_valid_access_3 in H13; eauto.
    destruct H13 as [? _].
    admit.

    eapply H7 in H1; eauto.
    apply Mem.load_valid_access in H17.
    destruct H17. specialize (H17 ofs).
    apply Mem.perm_valid_block in H17.
    intuition.
    split. omega. destruct chunk0; simpl; omega.

    hnf. intros. apply H10 in H16.
    eapply Mem.store_valid_block_1; eauto.
    
    hnf. intros. apply H11 in H16.
    destruct H16 as [? [? ?]].
    exists x0. split; auto.
    eapply Mem.store_valid_block_1; eauto.

    eapply mem_forward_trans. eauto.
    eapply store_mem_forward; eauto.
    eapply mem_forward_trans. eauto.
    eapply store_mem_forward; eauto.

    elim H15.
  Qed.
  Next Obligation.
    hnf in H. intuition.
    hnf in H0. 
    case_eq (isd_meminj d b1); intros; rewrite H12 in H0. 2: elim H0.
    destruct p. destruct H0 as [? ?]; subst.
    destruct (Mem.range_perm_free m2 b (lo + z) (lo + sz + z)).
    hnf; intros.
    apply Mem.free_range_perm in H1. hnf in H1.
    generalize H1; intros.
    specialize (H1 (ofs - z)).
    replace ofs with ((ofs-z) + z) by omega.
    eapply Mem.perm_inject; eauto.
    apply H14; omega.
    
    exists x. exists d. split; auto.
    replace (lo + z + sz) with (lo + sz + z) by omega. auto.
    split. split; hnf; simpl; auto.
    hnf; intuition.
    eapply Mem.free_inject with (l:=((b1,lo,lo+sz)::nil)); eauto.
    simpl. rewrite H1. auto.
    simpl; intros.
    destruct (Z_eq_dec b1 b0). subst.
    rewrite H0 in H12. inv H12.
    do 2 econstructor; split; simpl; auto.
    omega.
    cut (forall x, lo <= x < lo+sz -> x + z <> ofs + delta).
    intros. elimtype False.
    specialize (H16 (ofs + delta - z)).
    apply H16. omega. omega.
    intros.
    eapply Mem.inject_no_overlap in H3; eauto.
    destruct H3. elim H3; auto. apply H3.
    apply Mem.free_range_perm in H1.
    apply Mem.perm_implies with Freeable.
    clear - H1.   admit.
    constructor.
    apply Mem.perm_implies with p.
    clear - H14. admit.
    constructor.

    split; intros.
    destruct (Z_eq_dec b1 b0). subst b0.
    hnf in H0.
    eapply H6 in H12; eauto.
    destruct H12.
    apply Mem.perm_valid_block in H14. contradiction.
    eapply Mem.perm_free_1; eauto.
    destruct H4. eapply H4; eauto.
    destruct (Z_eq_dec b1 b0). subst b1.
    specialize (H0 ofs (range_chunk _ _)).
    hnf in H0.
    apply H6 in H12; eauto.
    destruct H12.
    eapply Mem.load_valid_access in H14.
    destruct H14.
    specialize (H14 ofs (range_chunk _ _)).
    apply Mem.perm_valid_block in H14. contradiction.
    specialize (H0 ofs (range_chunk _ _)).
    hnf in H0.
    replace (Mem.load chunk m1' b0 ofs) with
      (Mem.load chunk m1 b0 ofs).
    destruct H4. eapply H15; eauto.
    symmetry.
    eapply Mem.load_free; eauto.
    
    split; intros.
    eapply Mem.perm_free_1; eauto.
    case_eq (isd_meminj dx b1); intros. destruct p0.
    destruct H2. generalize H15; intros.
    apply H2 in H15. rewrite H12 in H15. inv H15.
    destruct (Z_eq_dec b0 b2); auto. subst b0. right.
    assert (lo < lo+sz \/ (ofs < lo + z0 \/ lo + sz + z0 <= ofs)) by omega.
    destruct H15; auto.
    assert (Mem.valid_block m1x b1).
    eapply Mem.valid_block_inject_1. apply H17. eauto.
    eapply H11 in H18.
    generalize e; intros.
    eapply Mem.free_range_perm in e.
    generalize (H0 b1 z0 H17); intros.
    replace (Mem.perm m1x b1 ofs Max) with (Mem.perm m1 b1 ofs Max) in *.
    2: destruct H18; auto.
    admit.
    
    eapply H6 in H12; eauto.
    destruct (Z_eq_dec b0 b); auto. subst.
    apply Mem.perm_valid_block in H14.
    intuition.
    destruct H5. eapply H5; auto.
    replace (Mem.load chunk x b0 ofs) with (Mem.load chunk m2 b0 ofs).
    destruct H5. eapply H15; eauto.
    symmetry.
    eapply Mem.load_free; eauto.
    destruct (Z_eq_dec b b0); auto. subst b0. right.
    assert (lo < lo+sz \/ lo >= lo+sz) by omega. destruct H15. 2: left; omega. right.
    assert (lo+sz + z <= ofs \/ ofs < lo+sz + z) by omega. destruct H16; auto. left.
    case_eq (isd_meminj dx b1); intros. destruct p.
    generalize H17; intros.
    destruct H2. apply H2 in H17.
    rewrite H12 in H17. inv H17.
    generalize (H0 (ofs + size_chunk chunk - 1)). intros.
    specialize (H17 (range_chunk' _ _)).
    hnf in H17. specialize (H17 b1 z0 H18).
    generalize (H0 ofs). intros.
    specialize (H20 (range_chunk _ _)).
    hnf in H20. specialize (H20 b1 z0 H18).
    admit.
    eapply H6 in H12.
    eapply Mem.load_valid_access in H14.
    destruct H14.
    specialize (H14 ofs (range_chunk _ _)).
    apply Mem.perm_valid_block in H14. intuition.
    auto.

    repeat intro.
    apply H9 in H0.
    eapply Mem.valid_block_free_1; eauto.

    repeat intro.
    apply H10 in H0.
    destruct H0 as [? [? ?]]. exists x0; split; auto.
    eapply Mem.valid_block_free_1; eauto.

    eapply mem_forward_trans. eauto.
    eapply free_mem_forward; eauto.
    eapply mem_forward_trans. eauto.
    eapply free_mem_forward; eauto.
  Qed.
End ForwardSimStruct_inject.

Section ForwardSim_inject.
  Context {G1 C1 E1 G2 C2 E2:Type}.
  Variable Sem1 : CompcertCoreSem G1 C1 E1.
  Variable Sem2 : CompcertCoreSem G2 C2 E2.

  Variables (ge1:G1)
            (ge2:G2).
  Variable (entry_points:list (val*val * signature)).

  Variable (match_ext : signature -> E1 -> E2 -> Prop).

  Variable core_data : Type.

  Variable match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop.
  Variable core_ord : C1 -> C1 -> Prop.
  Hypothesis core_ord_wf : well_founded core_ord.

  Hypothesis core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord st1' st1).

  Hypothesis core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall j vals vals' m1 m2,
          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd j c1 m1 c2 m2.

  Hypothesis core_halted : forall cd j c1 m1 c2 m2 v1,
      match_state cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 m1 = Some v1 ->
      exists v2,
        safely_halted Sem2 ge2 c2 m2 = Some v2 /\
        val_inject j v1 v2 /\
        Val.has_type v2 AST.Tint /\
        Mem.inject j m1 m2.

  Hypothesis core_at_external : 
      forall cd j st1 m1 st2 m2 e1 vals sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        exists e2, exists vals',
          Mem.inject j m1 m2 /\
          Forall2 (val_inject j) vals vals' /\
          Forall2 (Val.has_type) vals' (sig_args sig) /\
          match_ext sig e1 e2 /\
          at_external Sem2 st2 = Some (e2,sig,vals').

  Hypothesis core_after_external :
    forall cd j j' st1 st2 m1 m2 e1 e2 vals vals' ret ret' m1' m2' sig,
        match_state cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        at_external Sem2 st2 = Some (e2,sig,vals') ->
        match_ext sig e1 e2 ->
        Forall2 (val_inject j) vals vals' ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret ret' ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals' (sig_args sig) ->
        Val.has_type ret' (proj_sig_res sig) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret'::nil) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'.

  Program Definition forward_simulation_inject : ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points match_ext :=
    @Build_ForwardSimulation _ _ _ _ _ _ _ _ ge1 ge2 entry_points match_ext
      (inject_sim_data core_data)
      (ForwardSimStruct_inj core_data)
      (fun d c1 m1 c2 m2 => 
        match (isd_core_data _ d) with
        | Some cd =>
          match_state cd (isd_meminj _ d) c1 m1 c2 m2 /\
          heap_data_matches (isd_heap_data _ d)  m1 /\
          heap_data_inj_matches (isd_heap_data _ d) (isd_meminj _ d) m2
        | None => False end)
      (fun x y => core_ord (snd x) (snd y))
      _ _ _ _ _ _.
  Next Obligation.
    intros [? ?]. revert i.
    induction c using (well_founded_induction core_ord_wf).
    constructor; intros.
    destruct y; simpl in *.
    eapply H; eauto.
  Qed.
  Next Obligation.
    specialize (core_diagram st1 m1 st1' m1' H).
    case_eq (isd_core_data _ d). intros cd Hcd. rewrite Hcd in H0.
    intuition.
    specialize (core_diagram cd st2 (isd_meminj _ d) m2).
    destruct core_diagram as [? [? [? [? [? [? [? ?]]]]]]]; auto.
    exists x. exists x0.
    assert (heap_injection_invariant x2 (isd_heap_data _ d)).
      repeat intro.
      generalize (isd_invariant _ d); intros.
      case_eq (isd_meminj _ d b); intros. destruct p.
      case_eq (isd_meminj _ d b'); intros. destruct p.
      generalize H11. generalize H12; intros.
      apply H2 in H11. apply H2 in H12.
      rewrite H8 in H11. rewrite H9 in H12.
      inv H11. inv H12.
      eapply H10 in H14; eauto.
      eapply H4 in H9; auto.
      destruct H9.
      generalize H11; intros.
      apply H2 in H11.
      rewrite H8 in H11.
      inv H11.
      specialize (H3 b H7). destruct H3 as [? [? ?]].
      rewrite H14 in H3. inv H3.
      intuition.
      apply H0 in H7.
      apply H4 in H8. destruct H8.
      intuition.
      auto.
    assert (True) by auto.
    exists (Build_inject_sim_data _ (Some x1) _ _ H7).
    simpl. split.
    split. simpl; auto.
    simpl. hnf; auto.
    split; auto.
    split; auto.
    split.
    
    hnf; intros.
    apply H0 in H9.
    cut (allowed_core_modification m1 m1'). intros [? ?].
    apply H10 in H9. destruct H9; auto.
    eapply csem_allowed_modifications; eauto.
    hnf; intros.
    eapply H3 in H9.
    destruct H9 as [? [? ?]].
    exists x3; split; auto.
    cut (allowed_core_modification m2 x0). intros [? ?].
    apply H11 in H10. destruct H10; auto.
    assert (exists n, corestepN Sem2 ge2 n st2 m2 x x0).
    destruct H6. destruct H6; eauto.
    destruct H6. destruct H6; eauto.
    destruct H11 as [n ?]. clear -H11.
    revert st2 m2 x x0 H11. induction n; simpl; intros.
    inv H11. apply allowed_core_modification_refl.
    destruct H11 as [? [? [? ?]]].
    eapply allowed_core_modification_trans.
    eapply csem_allowed_modifications; eauto.
    eapply IHn; eauto.

    intros Hcd; rewrite Hcd in H0. elim H0.
  Qed.
  Next Obligation. rename H1 into H3. rename H0 into H2.
    generalize (core_initial _ _ _ H); clear H; intro H1.
    specialize ( H1 (isd_meminj _ d) vals vals' m1 m2).
    pose proof I. pose proof I.
    spec H1.
    clear -H2.
    induction H2; constructor; auto.
    hnf in H. destruct H; auto.
    spec H1.
    clear -H2.
    revert H2. generalize (sig_args sig). intros.
    induction H2; constructor; auto.
    destruct H; auto.
    spec H1.
    hnf in H3; intuition.
    destruct H1 as [cd [c1 [c2 [? [? ?]]]]].
    exists (Build_inject_sim_data _ (Some cd) _ _ (isd_invariant _ d)).
    exists c1; exists c2. simpl.
    hnf in H3; intuition.
    split; simpl. hnf; auto. hnf; auto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    destruct (isd_core_data _ d); simpl in *; intuition.
    eapply core_halted in H0; eauto.
    destruct H0 as [v2 [? [? ?]]].
    exists v2; split; auto. split; auto.
    hnf; intuition.
    hnf. intuition.
    split; hnf; auto.
    hnf. split; auto.
    hnf. split; auto.
    hnf; intros. rewrite H4 in H7. discriminate.
    apply mem_forward_refl.
    apply mem_forward_refl.
  Qed.
  Next Obligation.
    intros.
    case_eq (isd_core_data _ d). intros cd Hcd. rewrite Hcd in H.
    intuition.
    eapply core_at_external in H0; eauto.
    destruct H0 as [e2 [vals' [? ?]]].
    exists e2. exists vals'; intuition.
    clear -H4 H2.
    revert vals' H2 H4.
    generalize (sig_args sig).
    induction vals; intros.
    inv H4. inv H2. constructor.
    inv H4. inv H2. constructor; auto.
    split; auto.

    hnf; intuition.
    hnf; auto.
    split; hnf; auto.
    hnf; auto.
    hnf; auto.
    hnf; intros.
    rewrite H6 in H8; discriminate.
    hnf; auto.
    hnf; auto.

    intro Hcd; rewrite Hcd in H. elim H.
  Qed.
  Next Obligation.
    case_eq (isd_core_data _ d). intros cd Hcd. rewrite Hcd in H.
    simpl in *; intuition.
    generalize H5; intros.
    hnf in H4; intuition.
    eapply core_after_external with (j':=isd_meminj _ d') in H6; eauto.
    destruct H6 as [? [? [? ?]]].
    exists x0. exists x1. exists (Build_inject_sim_data _ (Some x) _ _ (isd_invariant _ d')).
    simpl. intuition.
    split; simpl.
    hnf; auto.
    hnf; auto.

    clear -H3.
    induction H3. constructor.
    constructor; auto.
    destruct H; auto.

    destruct H10; auto.
    auto.
    clear -H3. revert H3. generalize (sig_args sig).
    intros. induction H3. constructor.
    constructor; auto. eapply match_val_type2; eauto.

    intros Hcd; rewrite Hcd in H; intuition.
  Qed.

End ForwardSim_inject.

(* A forward simulation structure which uses the "extends" relation  *)
Section ForwardSimStruct_extend.
  Variable core_data:Type.

  Let data := (option core_data * heap_data)%type.

  Definition ex_data_extends (d1 d2:data) :=
    heap_data_extends (snd d1) (snd d2).

  Definition ex_match_external_mem (d1 d2:data) (m1 m2 m1' m2':mem) :=
    ex_data_extends d1 d2 /\
    Mem.extends m1 m2 /\
    Mem.extends m1' m2' /\
    mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
    mem_forward m1 m1' /\
    mem_forward m2 m2' /\
    heap_data_matches (snd d1) m1 /\
    heap_data_matches (snd d1) m2 /\
    heap_data_matches (snd d2) m1' /\
    heap_data_matches (snd d2) m2'.

  Definition ex_match_heap_block (d:data) (b1:block) (b2:block) :=
    b1 = b2 /\ snd d b1 = true.

  Definition ex_match_addr (d:data) (b1:block) (ofs1:Z) (b2:block) (ofs2:Z) :=
    b1 = b2 /\ ofs1 = ofs2.

  Obligation Tactic := intuition.
  Program Definition ForwardSimStruct_ex : ForwardSimulationStructure data :=
    Build_ForwardSimulationStructure data
      ex_data_extends
      ex_match_addr
      (fun _ t v1 v2 => Val.lessdef v1 v2 /\ Val.has_type v2 t)
      ex_match_heap_block
      ex_match_external_mem
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    hnf; intuition.
  Qed.
  Next Obligation.
    hnf; intuition.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. hnf.
    intuition.
  Qed.
  Next Obligation.
    inv H0; auto. simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    inv H0; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    inv H0; auto.
  Qed.
  Next Obligation.
    destruct H; subst.
    constructor.
    simpl; auto.
  Qed.
  Next Obligation.
    inv H0. do 2 econstructor. eauto.
  Qed.
  Next Obligation.
    inv H2. split; auto.
  Qed.
  Next Obligation.
    inv H1. destruct H.
    subst.
    split; auto.
  Qed.
  Next Obligation.
    destruct H; subst; hnf; auto.
  Qed.
  Next Obligation.
    destruct H0. destruct H. subst; auto.
    destruct H0. destruct H. subst; auto.
  Qed.
  Next Obligation.
    destruct H0. destruct H. subst; auto.
    destruct H0. destruct H. subst; auto.
  Qed.
  Next Obligation.
    destruct H. inv H1. auto.
    destruct H. inv H1. auto.
  Qed.
  Next Obligation.
    destruct H. inv H1. auto.
    destruct H. inv H1. auto.
  Qed.
  Next Obligation.
    destruct H; subst.
    hnf; auto.
  Qed.
  Next Obligation.
    inv H0.
    inv H1.
    auto.
  Qed.
  Next Obligation.
    set (hd := fun x=> if zlt x (Mem.nextblock m) then true else false).
    exists (None, hd).
    split.
    hnf; intuition.
    hnf. auto. 
    apply Mem.extends_refl.
    apply Mem.extends_refl.
    split; intros; auto.
    hnf; intros; auto.
    hnf; intros; auto.
    hnf; simpl; unfold hd; intros. 
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)). auto. 
    discriminate.
    hnf; simpl; unfold hd; intros.
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)). auto.
    discriminate.
    hnf; simpl; unfold hd; intros.
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)). auto.
    discriminate.
    hnf; simpl; unfold hd; intros.
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)). auto.
    discriminate.
  
    intros. split; auto.
    simpl. unfold hd.
    red in H0.
    destruct (zlt b (Mem.nextblock m)). auto.
    elimtype False. omega.
  Qed.
  Next Obligation.
    hnf in H; intuition; subst.
  Qed.
  Next Obligation.
    destruct H0; subst. hnf in H; intuition.
    rewrite <- Mem.valid_block_extends; eauto.
    destruct H0; subst. hnf in H; intuition.
    rewrite Mem.valid_block_extends; eauto.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. intuition subst.
    eapply Mem.perm_extends; eauto.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. intuition subst.
    eapply Mem.load_extends in H1; eauto.
    destruct H1 as [? ?].
    exists x; intuition.
    eapply Mem.load_type; eauto.
  Qed.
  Next Obligation.
    hnf in H. intuition.
    simpl in *.
    generalize H0; intros.
    eapply Mem.alloc_extends with (lo2:=lo) (hi2:=hi) in H0; eauto.
    destruct H0 as [? [? ?]].
    exists x. exists b1.
    exists (fst d,fun b' => if Z_eq_dec b' b1 then true else snd d b').
    intuition.
    hnf. split; auto. simpl.
    destruct (Z_eq_dec b1 b1). auto.
    elim n; auto.
    hnf; intuition.
    hnf. simpl; intros.
    destruct (Z_eq_dec x0 b1); subst; auto.
    hnf; intuition.
    hnf; intros.
    simpl. destruct (Z_eq_dec x0 b1); subst; auto.
 
    split; simpl; intros.
    eapply Mem.perm_alloc_1; eauto.
    destruct H3. eapply H3 in H12; eauto.
    eapply Mem.load_alloc_other; eauto.
    destruct H3. eapply H14 in H12; eauto.
    
    eapply mem_forward_trans. eauto.
    eapply alloc_mem_forward; eauto.
    eapply mem_forward_trans. eauto.
    eapply alloc_mem_forward; eauto.

    hnf. simpl. intros.
    destruct (Z_eq_dec b b1). inv H12.
    erewrite Mem.valid_block_extends; eauto.
    eapply Mem.valid_new_block; eauto.
    apply H8 in H12.
    eapply Mem.valid_block_alloc; eauto.
    hnf. simpl. intros.
    destruct (Z_eq_dec b b1). inv H12.
    eapply Mem.valid_new_block; eauto.
    apply H10 in H12.
    eapply Mem.valid_block_alloc; eauto.
    omega. omega.
  Qed.
  Next Obligation.
    destruct H1; subst.
    rename H4 into Htyp.
    hnf in H. intuition. simpl in *.
    generalize H0; intros.
    eapply Mem.store_within_extends in H0; eauto.
    destruct H0. destruct H0.
    exists x. exists d.
    split; auto. hnf; intuition.
    hnf; intros; auto.

    split; intros. auto.
    intuition.

    split; intros.
    eapply Mem.perm_store_1; eauto.
    destruct H4. eapply H4 in H13; eauto.
    replace (Mem.load chunk0 x b ofs) with
      (Mem.load chunk0 m2 b ofs).
    destruct H4. eapply H15; eauto.
    symmetry.
    erewrite Mem.load_store_other; eauto.
    destruct (Z_eq_dec b b2); auto. subst b2. right.
    generalize (H13 ofs). intros.
    spec H15. split. omega. destruct chunk0; simpl; omega.
    generalize (H13 (ofs + size_chunk chunk0 - 1)).
    intros. spec H16.
    destruct chunk0; simpl; omega.
    hnf in H15, H16.
    admit.

    eapply mem_forward_trans. eauto.
    eapply store_mem_forward; eauto.
    eapply mem_forward_trans. eauto.
    eapply store_mem_forward; eauto.

    hnf; simpl; intros.
    apply H9 in H13.
    eapply Mem.store_valid_block_1; eauto.
    hnf; simpl; intros.
    apply H11 in H13. 
    eapply Mem.store_valid_block_1; eauto.
  Qed.
  Next Obligation.
    hnf in H. intuition.
    generalize H1; intro.
    eapply Mem.free_parallel_extends in H1; eauto.
    destruct H1 as [? [? ?]].
    destruct H0. subst.
    exists x. exists d. split; auto.
    split. hnf; auto.
    hnf; intuition.

    split; intros.
    eapply Mem.perm_free_1; eauto.
    destruct (Z_eq_dec b b2); auto. subst b2.
    right.
    generalize H10; intros.
    apply Mem.free_range_perm in H10.
    assert (lo' >= lo' +sz \/ lo' < lo'+sz) by omega.
    destruct H15; auto.
    omega.
    admit.
    destruct H4. eapply H4; eauto.
    replace (Mem.load chunk x b ofs) with (Mem.load chunk m2 b ofs); auto.
    destruct H4. eapply H14; eauto.
    symmetry. eapply Mem.load_free; eauto.
    destruct (Z_eq_dec b b2); auto. subst b2.
    right.
    unfold loc_out_of_bounds in H0.
    assert (lo' >= lo'+sz \/ lo' < lo' + sz) by omega. destruct H14; auto.
    right.
    generalize (H0 ofs). intros.
    spec H15. destruct chunk; simpl; omega.
    generalize (H0 (ofs + size_chunk chunk - 1)).
    intros. spec H16. destruct chunk; simpl; omega.
    admit.

    eapply mem_forward_trans. eauto.
    eapply free_mem_forward; eauto.
    eapply mem_forward_trans. eauto.
    eapply free_mem_forward; eauto.

    simpl. hnf; intros.
    apply H9 in H0.
    eapply Mem.valid_block_free_1; eauto.
    simpl. hnf; intros.
    apply H11 in H0.
    eapply Mem.valid_block_free_1; eauto.
  Qed.
End ForwardSimStruct_extend.

Section ForwardSim_extend.
  Context {G1 C1 E1 G2 C2 E2:Type}.
  Variable Sem1 : CompcertCoreSem G1 C1 E1.
  Variable Sem2 : CompcertCoreSem G2 C2 E2.

  Variables (ge1:G1)
            (ge2:G2).
  Variable (entry_points : list (val*val * signature)).
  Variable (match_ext: signature -> E1 -> E2 -> Prop).

  Variable core_data : Type.

  Variable match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop.
  Variable core_ord : C1 -> C1 -> Prop.
  Hypothesis core_ord_wf : well_founded core_ord.

  Hypothesis core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord st1' st1).

  Hypothesis core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 Val.has_type vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2.

  Hypothesis core_halted : 
      forall cd st1 m1 st2 m2 v1,
        match_state cd st1 m1 st2 m2 ->
        safely_halted Sem1 ge1 st1 m1 = Some v1 ->
        exists v2,
          safely_halted Sem2 ge2 st2 m2 = Some v2 /\
          Val.lessdef v1 v2 /\
          Val.has_type v2 AST.Tint /\
          Mem.extends m1 m2.

  Hypothesis core_at_external : 
      forall cd st1 m1 st2 m2 e1 sig vals,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        exists e2, exists vals',
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals vals' /\
          Forall2 (Val.has_type) vals' (sig_args sig) /\
          match_ext sig e1 e2 /\
          at_external Sem2 st2 = Some (e2,sig,vals').

  Hypothesis core_after_external :
      forall cd st1 st2 m1 m2 e1 e2 vals vals' sig ret ret' m1' m2',
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        at_external Sem2 st2 = Some (e2,sig,vals') ->
        match_ext sig e1 e2 ->

        Forall2 Val.lessdef vals vals' ->
        Forall2 (Val.has_type) vals' (sig_args sig) ->
      
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->
        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' ->
        Val.lessdef ret ret' ->
        Mem.extends m1' m2' ->

        Val.has_type ret' (proj_sig_res sig) ->

        exists st1', exists st2', exists cd',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret'::nil) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'.

  Program Definition forward_simulation_extends : ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points match_ext :=
    @Build_ForwardSimulation _ _ _ _ _ _ _ _ ge1 ge2 entry_points match_ext
      (option core_data * heap_data)
      (ForwardSimStruct_ex core_data)
      (fun d c1 m1 c2 m2 => 
        match fst d with
        | Some cd => 
          match_state cd c1 m1 c2 m2 /\
          heap_data_matches (snd d) m1 /\
          heap_data_matches (snd d) m2
        | None => False end)
      (fun x y => core_ord (snd x) (snd y))
      _ _ _ _ _ _.
  Next Obligation.
    intros (d,c1).
    revert d. induction c1 using (well_founded_induction core_ord_wf).
    intros. constructor; intros.
    destruct y. apply H. auto.
  Qed.
  Next Obligation.
    simpl in *.
    destruct o; intuition.
    generalize H; intro H'.
    eapply core_diagram in H; eauto.
    destruct H as [? [? [? [? ?]]]].
    exists x. exists x0. exists (Some x1,h).
    split. hnf; simpl. auto.
    simpl.
    split; auto.
    split; auto.
    split; auto.
    simpl; intuition.
    hnf; intros.
    apply H0 in H2.
    cut (allowed_core_modification m1 m1').
    intros [? ?].
    eapply H5 in H2. destruct H2; auto.
    eapply csem_allowed_modifications; eauto.

    hnf; intros.
    apply H0 in H4.
    cut (allowed_core_modification m1 m1').
    intros [? ?].
    eapply H6 in H4. destruct H4; auto.
    eapply csem_allowed_modifications; eauto.

    hnf; intros.
    apply H3 in H4.
    cut (allowed_core_modification m2 x0).
    intros [? ?]. eapply H5 in H4. destruct H4; auto.
    assert (exists n, corestepN Sem2 ge2 n st2 m2 x x0).
    destruct H2. destruct H2; eauto.
    destruct H2. destruct H2; eauto.
    destruct H5 as [n ?]. clear -H5.
    revert st2 m2 x x0 H5.
    induction n; simpl; intros.
    inv H5. apply allowed_core_modification_refl.
    destruct H5 as [? [? [? ?]]].
    eapply allowed_core_modification_trans.
    eapply csem_allowed_modifications; eauto.
    eapply IHn; eauto.
  Qed.
  Next Obligation.
    rename H0 into H2; rename H1 into H3.
    generalize (core_initial _ _ _ H); clear H; intro H1.
    pose proof I. pose proof I.
    specialize (H1 vals vals' m1 m2).
    spec H1.
    clear -H2. induction H2. constructor.
    constructor; auto. destruct H; auto.
    spec H1.
    clear -H2. revert H2.
    generalize (sig_args sig). revert vals'.
    induction vals; intros. inv H2. constructor.
    inv  H2. constructor. destruct H3; auto. auto.
    spec H1.
    hnf in H3; intuition.
    destruct H1 as [cd [c1 [c2 [? [? ?]]]]].
    exists (Some cd,h). exists c1; exists c2.
    simpl.
    hnf in H3; intuition.
    hnf. auto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    destruct a; simpl in *; intuition.
    eapply core_halted in H0; eauto.
    destruct H0 as [v2 [? ?]].
    exists v2; intuition.
    hnf; intuition.
    hnf. auto.
    hnf; auto.
    hnf; auto.
    hnf; auto.
  Qed.
  Next Obligation.
    destruct a; simpl in *; intuition.
    eapply core_at_external in H0; eauto.
    destruct H0 as [? [? ?]].
    exists x; exists x0; intuition.
    clear -H0 H4. revert H0 H4.
    generalize (sig_args sig).
    revert x0. induction vals; intros.
    inv H4. inv H0. constructor.
    inv H0. inv H0. inv H4. constructor; auto.
    split; auto.
    hnf. intuition.
    hnf. intros; auto.
    hnf; auto.
    hnf; auto.
    hnf; auto.
  Qed.
  Next Obligation.
    destruct a; simpl in *; intuition.
    hnf in H4. intuition.
    eapply core_after_external in H6; eauto.
    destruct H6 as [? [? [? ?]]].
    exists x. exists x0. exists (Some x1,b0).
    simpl; intuition.
    hnf; auto.
    eapply core_at_external in H0; eauto.
    destruct H0 as [e2' [vals'' [? [? [? [? ?]]]]]].
    replace vals' with vals'' by congruence; auto.
    
    eapply core_at_external in H0; eauto.
    destruct H0 as [e2' [vals'' [? [? [? [? ?]]]]]].
    replace vals' with vals'' by congruence; auto.
  Qed.
End ForwardSim_extend.

(* A forward simulation structure which assumes
   the memory images are identical *)
Section ForwardSimStruct_equal.
  Variable core_data:Type.

  Let data := (option core_data * heap_data)%type.

  Definition equal_data_extends (d1 d2:data) :=
    heap_data_extends (snd d1) (snd d2).

  Definition equal_match_external_mem (d1 d2:data) (m1 m2 m1' m2':mem) :=
    equal_data_extends d1 d2 /\
    m1 = m2 /\ m1' = m2' /\
    heap_data_matches (snd d1) m1 /\
    heap_data_matches (snd d2) m1'.

  Definition equal_match_block (d:data) (b1 b2:block) :=
    b1 = b2 /\ snd d b1 = true.

  Definition equal_match_addr (d:data) (b1:block) (ofs1:Z) (b2:block) (ofs2:Z) :=
    b1 = b2 /\ ofs1 = ofs2.

  Obligation Tactic := intuition.
  Program Definition ForwardSimStruct_equals : ForwardSimulationStructure (option core_data * heap_data) :=
    Build_ForwardSimulationStructure (option core_data * heap_data)
      equal_data_extends
      equal_match_addr
      (fun _ t v1 v2  => v1 = v2 /\ Val.has_type v1 t)
      equal_match_block
      equal_match_external_mem
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    hnf; intros; auto.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. hnf. intuition.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. hnf. intuition.
  Qed.
  Next Obligation.
    subst; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    inv H; subst; auto.
    simpl; auto.
  Qed.
  Next Obligation.
    subst x. do 2 econstructor; split; eauto.
  Qed.
  Next Obligation.
    inv H2. hnf; auto.
  Qed.
  Next Obligation.
    inv H1.
    hnf; auto.
  Qed.
  Next Obligation.
    destruct H. hnf. intuition.
  Qed.
Obligation Tactic := idtac.
  Next Obligation.
    intros.
    destruct H. destruct H0. subst; auto.
  Qed.
  Next Obligation.
    intros.
    destruct H. destruct H0. subst; auto.
  Qed.
  Next Obligation.
    intros.
    destruct H. destruct H0. inv H0. subst; auto.
  Qed.
  Next Obligation.
    intros.
    destruct H. destruct H0. inv H0. subst; auto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    destruct H. hnf; subst; auto.
  Qed.
  Next Obligation.
    inv  H0. auto.
  Qed.
  Next Obligation.
    set (hd := fun x=> if zlt x (Mem.nextblock m) then true else false).
    exists (None, hd).
    split.
    hnf; intuition.
    hnf. auto. hnf.
    simpl; unfold hd; intros.
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)).
    auto. 
    discriminate.
    hnf.
    simpl; unfold hd; intros.
    unfold Mem.valid_block.
    destruct (zlt b (Mem.nextblock m)).
    auto.
    discriminate.

    intros. hnf. split; simpl; auto.
    unfold hd.
    unfold Mem.valid_block in H0.
    destruct (zlt b (Mem.nextblock m)).
    auto.
    elimtype False; omega.
  Qed. 
  Next Obligation.
    hnf in H; intuition; subst.  
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. intuition; subst. auto.
    hnf in H. hnf in H0. intuition; subst. auto.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. intuition subst. auto.
  Qed.
  Next Obligation.
    hnf in H. hnf in H0. intuition subst.
    exists v1. split; auto.
    split; auto.
    eapply Mem.load_type; eauto.
  Qed.
  Next Obligation.
    hnf in H. intuition; subst.
    rename a into cd. rename b into hd.
    set (hd' := fun b => if (Z_eq_dec b b1) then true else b0 b).
    exists m1'. exists b1.
    exists (cd,hd').
    split. hnf. simpl.
    split; auto.
    unfold hd'.
    destruct (Z_eq_dec b1 b1); auto.
    split; auto.
    split.
    hnf; intros.
    unfold hd'; simpl.
    destruct (Z_eq_dec x b1); auto.
    hnf; intuition.
    
    hnf; intros.
    unfold hd'; simpl.
    destruct (Z_eq_dec x b1); auto.
    hnf; intuition.
        
    simpl in H.
    unfold hd' in H.
    destruct (Z_eq_dec b b1).  subst.
    eapply Mem.valid_new_block; eauto.
    eapply Mem.valid_block_alloc; eauto.
  Qed.
  Next Obligation.
    hnf in H. intuition; subst.
    hnf in H1. intuition; subst.
    exists m1'. exists (a0,b0). split; auto.
    split. hnf; auto.
    hnf. intuition.
    simpl.
    hnf; intros; auto.
    specialize ( H8 b1). spec H8; simpl; auto.
    eapply Mem.store_valid_block_1; eauto.
  Qed.
  Next Obligation.
    hnf in H. intuition subst.
    hnf in H0. intuition subst.
    exists m1'. exists (a0,b0).
    split; auto.
    split. hnf; auto.
    hnf. intuition.
    simpl in *.
    hnf; intros.
    specialize (H6 b1). spec H6; auto.
    eapply Mem.valid_block_free_1; eauto.
  Qed.
End ForwardSimStruct_equal.

Section ForwardSim_equal.
  Context {G1 C1 E1 G2 C2 E2:Type}.
  Variable Sem1 : CompcertCoreSem G1 C1 E1.
  Variable Sem2 : CompcertCoreSem G2 C2 E2.

  Variables (ge1:G1)
            (ge2:G2).
  Variable entry_points : list (val*val * signature).
  Variable match_ext : signature -> E1 -> E2 -> Prop.
  
  Variable core_data : Type.

  Variable match_core : core_data -> C1 -> C2 -> Prop.
  Variable core_ord : C1 -> C1 -> Prop.
  Hypothesis core_wf : well_founded core_ord.

  Hypothesis core_diagram : 
      forall st1 m st1' m', corestep Sem1 ge1 st1 m st1' m' ->
      forall d st2, match_core d st1 st2 ->
        exists st2', exists d',
          match_core d' st1' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord st1' st1).

  Hypothesis core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals,
          Forall2 Val.has_type vals (sig_args sig) ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_core cd c1 c2.

  Hypothesis core_halted :  forall cd c1 c2 m v,
      match_core cd c1 c2 ->
      safely_halted Sem1 ge1 c1 m = Some v ->
      safely_halted Sem2 ge2 c2 m = Some v /\
      Val.has_type v AST.Tint.

  Hypothesis core_at_external : 
      forall d st1 st2 e1 sig args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e1,sig,args) ->
        exists e2,
          match_ext sig e1 e2 /\
          at_external Sem2 st2 = Some (e2,sig,args) /\
          Forall2 Val.has_type args (sig_args sig).

  Hypothesis core_after_external :
      forall d st1 st2 ret e1 e2 sig args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e1,sig,args) ->
        at_external Sem2 st2 = Some (e2,sig,args) ->
        match_ext sig e1 e2 ->
        Forall2 Val.has_type args (sig_args sig) ->
        Val.has_type ret (proj_sig_res sig) ->
        exists st1', exists st2', exists d',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret::nil) st2 = Some st2' /\
          match_core d' st1' st2'.

  Program Definition forward_simulation_equals : ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points match_ext :=
    @Build_ForwardSimulation _ _ _ _ _ _ _ _ ge1 ge2 entry_points match_ext
      (option core_data * heap_data)
      (ForwardSimStruct_equals core_data)
      (fun d c1 m1 c2 m2 => 
         match fst d with
         | Some cd =>
          match_core cd c1 c2 /\ m1 = m2 /\
           heap_data_matches (snd d) m1
         | None => False end)
      (fun x y => core_ord (snd x) (snd y))
      _ _ _ _ _ _.
  Next Obligation.
    intros [d c1].
    revert d. induction c1 using (well_founded_induction core_wf).
    intros. constructor; intros.
    destruct y as [? ?].
    simpl in *. apply H. auto.
  Qed.
  Next Obligation.
    destruct o; simpl in *; intuition; subst.
    destruct (core_diagram st1 m2 st1' m1' H c st2 H1)
      as [c2' [d' [? ?]]].
    exists c2'. exists m1'. exists (Some d',h).
    simpl.
    split. hnf; auto.
    split; auto. split; auto.
    split; auto.
    hnf; simpl; intros.
    apply H3 in H4.
    cut (allowed_core_modification m2 m1'). intros [? ?].
    apply H5 in H4. destruct H4; auto.
    eapply csem_allowed_modifications; eauto.
  Qed.
  Next Obligation.
    rename H0 into H2; rename H1 into H3.
    generalize (core_initial _ _ _ H); clear H; intro H1.
    pose proof I. pose proof I.
    cut (vals = vals'); intros. subst vals'.
    specialize (H1 vals).
    spec H1.
    clear -H2. revert H2. generalize (sig_args sig).
    induction vals; intros. inv H2. constructor.
    inv H2. constructor; auto. destruct H4; auto.
    destruct H1 as [cd [c1 [c2 [? [? ?]]]]].
    exists (Some cd,h). exists c1. exists c2.
    simpl.
    hnf in H3; intuition.
    hnf. auto.
    clear -H2. induction H2; f_equal; auto.
    destruct H; auto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    destruct a; simpl in *; intuition; subst.
    eapply core_halted in H0; eauto.
    exists v1; intuition.
    hnf. intuition.
    hnf. intros; auto.
  Qed.
  Next Obligation.
    destruct a; simpl in *; intuition; subst.
    eapply core_at_external in H0; eauto.
    destruct H0 as [e2 [? [? ?]]].
    exists e2. exists vals. intuition.
    clear -H2.
    revert H2. generalize (sig_args sig).
    induction vals; intros. inv H2. constructor.
    inv H2. constructor; auto.
    split; auto.
    hnf. intuition. hnf; auto.
  Qed.
  Next Obligation.
    destruct a; simpl in *; intuition; subst.
    destruct (core_after_external c st1 st2 ret2 e1 e2 sig vals)
      as [st1' [st2' [d' [? ?]]]]; auto.
    eapply core_at_external in H0; eauto.
    destruct H0 as [e2' [? [? ?]]].
    replace e2' with e2 in * by congruence.
    auto.
    clear -H3. revert H3.
    generalize (sig_args sig).
    revert vals'.
    induction vals; intros.
    inv H3. constructor.
    inv H3. constructor; auto.
    destruct H2. auto.
    eapply IHvals; eauto.

    exists st1'. exists st2'. exists (Some d',b0).
    intuition. hnf; auto.
    simpl.
    hnf in H4; intuition.
  Qed.
End ForwardSim_equal.

Section ForwardSimStruct_compose.
  Variables data1 midCore data2:Type.
  Variable SS1 : ForwardSimulationStructure data1.
  Variable SS2 : ForwardSimulationStructure data2.

  Let data := (data1 * (option midCore*mem) * data2)%type.

  Inductive compose_extends_data : data -> data -> Prop :=
    intro_compose_extends_data : forall d12 d12' a b d23 d23',
      extends_data SS1 d12 d12' ->
      extends_data SS2 d23 d23' ->
      compose_extends_data (d12,a,d23) (d12',b,d23').

  Inductive compose_match_external_mem :
    data -> data -> mem -> mem -> mem -> mem -> Prop :=
    intro_compose_match_external_mem : forall d12 c2 m2 m2' c2' d23 d12' d23' m1 m3 m1' m3',
      match_external_mem SS1 d12 d12' m1 m2 m1' m2' ->
      match_external_mem SS2 d23 d23' m2 m3 m2' m3' ->
      compose_match_external_mem
         (d12,(c2,m2),d23)
         (d12',(c2',m2'),d23')
         m1 m3 m1' m3'.

  Definition compose_match_val (d:data) (t:typ) :=
      (fun v1 v3 => exists v2,
          let d12 := (fst (fst d)) in
          let d23 := snd d in
          match_val SS1 d12 t v1 v2 /\
          match_val SS2 d23 t v2 v3).

  Definition compose_match_block (d:data) :=
      (fun b1 b3 => exists b2,
          let d12 := (fst (fst d)) in
          let d23 := snd d in
          match_block SS1 d12 b1 b2 /\
          match_block SS2 d23 b2 b3).

  Definition compose_match_addr (d:data) :=
      (fun b1 ofs1 b3 ofs3 => exists b2, exists ofs2,
          let d12 := (fst (fst d)) in
          let d23 := snd d in
          match_addr SS1 d12 b1 ofs1 b2 ofs2 /\
          match_addr SS2 d23 b2 ofs2 b3 ofs3).

  Program Definition FSimStruct_compose : ForwardSimulationStructure data :=
    Build_ForwardSimulationStructure _
      compose_extends_data
      compose_match_addr
      compose_match_val
      compose_match_block
      compose_match_external_mem
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    destruct d as ((d12,x),d23).
    constructor; apply extends_refl.
  Qed.
  Next Obligation.
    inv H. inv H0.
    constructor; eapply extends_trans; eauto.
  Qed.
  Next Obligation.
    destruct H0 as [? [? [? ?]]].
    inv H.
    eapply extends_addr in H2; eauto.
    eapply extends_addr in H3; eauto.
    hnf. eauto.
  Qed.
  Next Obligation.
    destruct H0 as [? [? ?]].
    inv H.
    eapply extends_block in H1; eauto.
    eapply extends_block in H2; eauto.
    hnf; eauto.
  Qed.
  Next Obligation.
    inv H; inv H0.
    simpl in H.
    econstructor. simpl.
    destruct H.
    eapply extends_val in H; eauto.
    eapply extends_val in H0; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    eapply match_val_type1; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    eapply match_val_type2; eauto.
  Qed.
  Next Obligation.
    exists Vundef. simpl. split; apply match_val_undef.
  Qed.
  Next Obligation.
    exists (Vint i). simpl. split; apply match_val_int_i.
  Qed.
  Next Obligation.
    destruct H. destruct H.
    apply match_val_int_e in H. subst x0.
    apply match_val_int_e in H0. auto.
  Qed.
  Next Obligation.
    exists (Vfloat f). simpl.
    split; apply match_val_float_i.
  Qed.
  Next Obligation.
    destruct H. simpl in H. destruct H.
    apply match_val_float_e in H. subst x0.
    apply match_val_float_e in H0. auto.
  Qed.
  Next Obligation.
    destruct H as [b_ [ofs_ [? ?]]].
    exists (Vptr b_ (Int.repr ofs_)).
    simpl.
    split; eapply match_val_ptr_i; eauto.
  Qed.
  Next Obligation.
    destruct H. destruct H.
    apply match_val_ptr_e in H. destruct H as [? [? ?]].
    subst x0.
    apply match_val_ptr_e in H0. destruct H0 as [? [? ?]].
    subst x.
    do 2 econstructor. eauto.
  Qed.
  Next Obligation.
    inv H. simpl in *. destruct H2.
    inv H0.
    generalize H; intros. apply match_val_ptr_e in H.
    destruct H as [? [? ?]]. subst x.
    generalize H3. intro.
    eapply match_val_ptr_addr in H3; eauto.
    assert (Mem.valid_pointer m2' x0 (Int.unsigned x1) = true).
    rewrite Mem.valid_pointer_nonempty_perm.
    rewrite Mem.valid_pointer_nonempty_perm in H1.
    eapply match_mem_perm; eauto.
    eapply match_val_ptr_addr in H2; eauto.
    econstructor; simpl; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    destruct H0 as [? [? ?]].
    generalize H0; intros.
    apply match_val_ptr_e in H3.
    destruct H3 as [? [? ?]]. subst.
    generalize H0; intros.
    eapply match_block_match_val_eq1 in H0; eauto.
    destruct H0; subst.
    eapply match_block_match_val_addr in H3; auto.
    eapply match_block_match_val_addr in H2; auto.
    hnf. eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    exists x. exists ofs.
    split.
    apply match_block_match_addr; auto.
    apply match_block_match_addr; auto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    destruct H0 as [? [? ?]].
    simpl in *. destruct H0.
    eapply match_block_match_addr_eq1 in H0; eauto.
    destruct H0; subst.
    eapply match_block_match_addr_eq1 in H2; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    destruct H0 as [? [? ?]].
    simpl in *. destruct H0.
    eapply match_block_match_addr_eq2 in H2; eauto.
    destruct H2; subst.
    eapply match_block_match_addr_eq2 in H0; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    destruct H0 as [? [? ?]].
    generalize H0; intros.
    apply match_val_ptr_e in H0.
    destruct H0 as [? [? ?]]. subst.
    generalize H3; intros.
    eapply match_block_match_val_eq1 in H3; eauto.
    destruct H3; subst.
    eapply match_block_match_val_eq1 in H2; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    destruct H0 as [? [? ?]].
    generalize H0; intros.
    apply match_val_ptr_e in H0.
    destruct H0 as [? [? ?]]. subst.
    eapply match_block_match_val_eq2 in H2; eauto.
    destruct H2; subst.
    eapply match_block_match_val_eq2 in H3; eauto.
  Qed.
  Next Obligation.
    destruct H as [? [? [? ?]]].
    exists x. exists (x0 + delta).
    split; apply match_addr_offset; auto.
  Qed.
  Next Obligation.
    destruct H as [? [? ?]].
    generalize H; intros.
    apply match_val_ptr_e in H.
    destruct H as [? [? ?]]. subst.
    exists (Vptr x0 (Int.add x1 delta)).
    split; apply match_val_offset; auto.
  Qed.
  Next Obligation.
    destruct (match_external_mem_self SS1 m) as [? [? ?]]; auto.
    destruct (match_external_mem_self SS2 m) as [? [? ?]]; auto.
    exists (x,(None,m),x0).
    split.
    constructor; auto.
    intros.
    specialize (H1 b H4).
    specialize (H3 b H4).
    econstructor; simpl; split; eauto.
  Qed.
  Next Obligation.
    inv H. constructor.
    eapply match_external_extends; eauto.
    eapply match_external_extends; eauto.
  Qed.
  Next Obligation.
    inv H. destruct H0 as [? [? [? ?]]].
    eapply match_mem_valid_block in H; eauto.
    eapply match_mem_valid_block in H0; eauto.
    intuition.
  Qed.
  Next Obligation.
    inv H. destruct H0 as [? [? [? ?]]].
    eapply match_mem_perm; eauto.
    eapply match_mem_perm; eauto.
  Qed.
  Next Obligation.
    inv H. destruct H0 as [? [? [? ?]]].
    simpl in *.
    eapply match_mem_load in H1; eauto.
    destruct H1 as [? [? ?]].
    eapply match_mem_load in H1; eauto.
    destruct H1 as [? [? ?]]. exists x2. split; auto.
    exists x1. split; auto.
  Qed.
Obligation Tactic := intuition.
  Next Obligation.
    inv H.
    generalize H0; intros.
    eapply match_mem_alloc in H0; eauto.
    destruct H0 as [? [? [? [? [? ?]]]]].
    generalize H0; intros.
    eapply match_mem_alloc in H0; eauto.
    destruct H0 as [? [? [? [? [? ?]]]]].
    exists x2. exists x3.
    exists (x1,(c2,x),x4). intuition.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
  Qed.
  Next Obligation.
    inv H. destruct H1 as [? [? [? ?]]].
    destruct H2 as [? [? ?]].
    eapply match_mem_store in H0; eauto.
    destruct H0 as [? [? [? [? ?]]]].
    eapply match_mem_store in H0; eauto.
    destruct H0 as [? [? [? [? ?]]]].
    simpl in *.
    exists x4. exists (x3,(c2,x2),x5).
    split; auto.
    split; auto.
    constructor; auto.
    constructor; auto.
  Qed.
  Next Obligation.
    destruct H.
    destruct H0 as [? [? [? ?]]].
    eapply match_mem_free in H1; eauto.
    destruct H1 as [? [? [? [? ?]]]].
    eapply match_mem_free in H1; eauto.
    destruct H1 as [? [? [? [? ?]]]].
    simpl in *.
    exists x3.
    exists (x2,(c2,x1),x4).
    split; auto.
    split; constructor; auto.
  Qed.
End ForwardSimStruct_compose.

Section ForwardSimCompose.
  Context {G1 C1 E1 G2 C2 E2 G3 C3 E3:Type}.
  Variable Sem1 : CompcertCoreSem G1 C1 E1.
  Variable Sem2 : CompcertCoreSem G2 C2 E2.
  Variable Sem3 : CompcertCoreSem G3 C3 E3.

  Variable ge1 :G1.
  Variable ge2: G2.
  Variable ge3:G3.

  Variable entry_points12 : list (val*val*signature).
  Variable entry_points23 : list (val*val*signature).
  Variable match_ext12 : signature -> E1 -> E2 -> Prop.
  Variable match_ext23 : signature -> E2 -> E3 -> Prop.

  Variable FSim12 : ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points12 match_ext12.
  Variable FSim23 : ForwardSimulation Sem2 Sem3 ge2 ge3 entry_points23 match_ext23.


  Variable entry_points13: list (val*val*signature).
  Variable EPC: entry_points_compose entry_points12 entry_points23 entry_points13.
  Let match_ext13 sig e1 e3 := exists e2, match_ext12 sig e1 e2 /\ match_ext23 sig e2 e3.


  Let data13 := (data FSim12 * (option C2*mem) * data FSim23)%type.

  Inductive sem_compose_ord 
      : (data13*C1) -> (data13*C1) -> Prop :=

    | sem_compose_ord1 :
        forall (d12 d12':data FSim12) (c2:C2) (m:mem) (d23:data FSim23) x y,
           fsim_order FSim12 (d12,x) (d12',y) ->
           sem_compose_ord ((d12,(Some c2,m),d23),x) ((d12',(Some c2,m),d23),y)

    | sem_compose_ord2 :
        forall (d12 d12':data FSim12) (c2 c2':C2) (m m':mem) (d23 d23':data FSim23) x y,
           fsim_order FSim23 (d23,c2) (d23',c2') ->
           sem_compose_ord ((d12,(Some c2,m),d23),x) ((d12',(Some c2',m'),d23'),y).

  Lemma well_founded_sem_compose_ord : well_founded sem_compose_ord.
  Proof.
    intro. destruct a. destruct d as [[d12 [c2 m]] d23].
    revert d12 c m.
    destruct c2.
    2: constructor; intros. 2: inv H.
    set (q := (d23,c)).
    change d23 with (fst q). change c with (snd q). clearbody q.
    clear d23 c.
    induction q using (well_founded_induction (fsim_wf FSim23)).
    intros.
    set (q' := (d12,c)).
    change d12 with (fst q'). change c with (snd q').
    clearbody q'. clear d12 c.
    induction q' using (well_founded_induction (fsim_wf FSim12)).
    constructor; intros. inv H1.
    generalize (H0 (d12,x)). simpl. intros.
    apply H1. destruct q'; auto.
    generalize (H (d23,c2)).
    intros.
    spec H1. destruct q; auto.
    apply H1.
  Qed.

  Inductive compose_match_state : data13 -> C1 -> mem -> C3 -> mem -> Prop :=
    intro_compose_match_state : forall d12 c2 m2 d23 c1 m1 c3 m3,
      match_state FSim12 d12 c1 m1 c2 m2 ->
      match_state FSim23 d23 c2 m2 c3 m3 ->
      compose_match_state (d12,(Some c2,m2),d23) c1 m1 c3 m3.

  Lemma fsim_compose_diagram :
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall d st3 m3, compose_match_state d st1 m1 st3 m3 ->
        exists st3', exists m3', exists d',
          compose_extends_data _ _ _
             (fsim_struct FSim12) (fsim_struct FSim23) d d' /\
          compose_match_state d' st1' m1' st3' m3' /\
          ((corestep_plus Sem3 ge3 st3 m3 st3' m3') \/
            corestep_star Sem3 ge3 st3 m3 st3' m3' /\
            clos_trans _ sem_compose_ord (d',st1') (d,st1)).
  Proof.
    intros. inv H0.
    destruct (fsim_diagram  FSim12
      st1 m1 st1' m1' H d12 c2 m2 H1) as
    [c2' [m2' [d' [? [? ?]]]]].
    assert (
      corestep_plus Sem2 ge2 c2 m2 c2' m2' \/
      (c2,m2) = (c2',m2') /\
      fsim_order FSim12 (d', st1') (d12, st1)).
    destruct H4. auto. destruct H4.
    destruct H4. destruct x.
    right. split; auto.
    left. exists x; auto.
    clear H4. destruct H5.
    destruct H4.
    clear H1.
    revert d23 c2 m2 c2' m2' st3 m3 H2 H3 H4.
    induction x; intros. simpl in H4.
    destruct H4 as [c3' [m3' [? ?]]].
    inv H4.
    destruct (fsim_diagram FSim23
      c2 m2 c2' m2' H1 d23 st3 m3 H2) as [c3' [m3' [d'' [? [? ?]]]]].
    exists c3'. exists m3'. exists (d',(Some c2',m2'),d'').
    split. constructor; auto.

    split; auto. split; auto.
    destruct H6; auto. destruct H6.
    destruct H6.
    destruct x. right.
    split; auto. exists O; auto.
    apply t_step. constructor 2. auto.
    left. exists x; auto.
    remember (S x) as x'. simpl in H4.
    destruct H4 as [c2'' [m2'' [? ?]]]. subst x'.
    destruct (fsim_diagram FSim23
      c2 m2 c2'' m2'' H1
      d23 st3 m3 H2) as [c3' [m3' [d'' [? [? ?]]]]].
    specialize (IHx d'' c2'' m2'' c2' m2').
    specialize (IHx c3' m3'). specialize (IHx H6 H3 H4).
    destruct IHx as [c3'' [m3'' [d''' [? [? ?]]]]].
    exists c3''. exists m3''. exists d'''.
    split; auto.
    inv H8. constructor. auto.
    eapply extends_trans; eauto.
    split. auto.

    destruct H7; destruct H10.
    left. destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + S n2)%nat.
    change (S (n1 + S n2)) with (S n1 + S n2)%nat.
    rewrite corestepN_add. eauto.
    destruct H10.
    left. destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    change (S (n1 + n2)) with (S n1 + n2)%nat.
    rewrite corestepN_add. eauto.
    left. destruct H7.
    destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
    rewrite corestepN_add. eauto.
    right.
    destruct H7. destruct H10. split.
    destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    rewrite corestepN_add. eauto.
    eapply t_trans; eauto.
    apply t_step.
    constructor 2. auto.
    destruct H4.
    exists st3. exists m3. exists (d',(Some c2,m2),d23).
    split. constructor; auto.
    apply extends_refl.
    inv H4.
    split. constructor; auto.
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
  Qed.

Obligation Tactic := intuition.

  Program Definition forward_simulation_compose : ForwardSimulation Sem1 Sem3 ge1 ge3 entry_points13 match_ext13:=
    @Build_ForwardSimulation _ _ _ _ _ _ _ _  ge1 ge3 entry_points13 match_ext13
      data13
      (FSimStruct_compose _ _ _
         (fsim_struct FSim12) (fsim_struct FSim23))
      compose_match_state
      (clos_trans _ sem_compose_ord)
      (wf_clos_trans _ _ well_founded_sem_compose_ord)
      fsim_compose_diagram
      _ _ _ _.
  Next Obligation.
    rename v2 into v3.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
    pose proof EPC.
    clear - H H2.
    induction H2.
    simpl in H. destruct H. inv H.
    exists v2; split; simpl; auto.
    destruct (IHentry_points_compose H) as [v2' [? ?]].
    exists v2'; simpl; split; auto.
   inv H.
   destruct J1 as [v2 [J12 J23]].
    rename H0 into H5. rename H1 into H6.
    generalize (fsim_initial FSim12 _ _ _ J12); intro H2.
    generalize (fsim_initial FSim23 _ _ _ J23); intro H4.
    clear H; do 4 pose proof I.
    inv H6.
    assert (exists vals_,
      match_vals (fsim_struct FSim12) d12' (sig_args sig) vals vals_ /\
      match_vals (fsim_struct FSim23) d23' (sig_args sig) vals_ vals').
    clear -H5.
    revert vals' H5. generalize (sig_args sig). induction vals; simpl; intros.
    inv H5. exists nil; split; constructor.
    inv H5. eapply IHvals in H4. destruct H4 as [? [? ?]].
    destruct H2 as [? [? ?]].
    exists (x0::x). 
    split; constructor; auto.
    destruct H6 as [vals_ [? ?]].
    eapply H2 in H7; eauto.
    eapply H4 in H8; eauto.
    destruct H7 as [d12'' [c1 [c2_ [? [? [? ?]]]]]].
    destruct H8 as [d23'' [c2_' [c3 [? [? [? ?]]]]]].
    assert (c2_ = c2_') by congruence. subst c2_'.
    exists (d12'',(Some c2_,m2'),d23'').
    exists c1. exists c3.
    intuition.
    constructor; auto.
    constructor; auto.
  Qed.
  Next Obligation.
    inv H.
    eapply (fsim_halted FSim12) in H0; eauto.
    destruct H0 as [v2 [? [? ?]]].
    eapply (fsim_halted FSim23) in H; eauto.
    destruct H as [v3 [? [? ?]]].
    exists v3; intuition.
    simpl. exists v2; simpl; split; auto.
    constructor; auto.
  Qed.
  Next Obligation.
    inv H.
    eapply fsim_at_external in H0; eauto.
    destruct H0 as [e2 [vals' [? [? [??]]]]].
    eapply fsim_at_external in H0; eauto.
    destruct H0 as [e3 [vals'' [? [? [??]]]]].
    exists e3. exists vals''. intuition.
    exists e2; split; auto.

    clear -H3 H6.
    revert vals' vals'' H3 H6.
    generalize (sig_args sig).
    induction vals; intros. inv H3. inv H6.
    constructor.
    inv H3. inv H6.
    constructor.
    econstructor; simpl; split; eauto.
    eapply IHvals; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    inv H.
    inv H4. destruct H5 as [ret' [? ?]].
    generalize H0; intros.
    eapply fsim_at_external in H0; eauto.
    destruct H0 as [e2' [vals'' [? [? [??]]]]].
    generalize H8; intros.
    eapply fsim_at_external in H8; eauto.
    destruct H8 as [e3' [vals''' [? [? [??]]]]].
    rewrite H12 in H1. inv H1.
    eapply fsim_after_external with (d':=d12') in H16; eauto.
    destruct H16 as [st1' [st2' [d'' [? [? [? ?]]]]]].
    eapply fsim_after_external with (d':=d23') in H17; eauto.
    destruct H17 as [st2'' [st3' [d''' [? [? [? ?]]]]]].
    exists st1'. exists st3'. exists (d'',(Some st2'',m2'0),d''').
    intuition.
    constructor; auto.
    constructor; auto.
    replace st2'' with st2'; auto. congruence.
  Qed.

End ForwardSimCompose.

End Simulations.

Export Simulations.
