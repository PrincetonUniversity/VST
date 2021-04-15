Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.progs.conclib.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.mem_lessdef.

(* functions on byte arrays and CompCert mems *)
Lemma drop_alloc m : { m' | (let (m1, b) := Mem.alloc m 0 1 in Mem.drop_perm m1 b 0 1 Nonempty) = Some m' }.
Proof.
  destruct (Mem.alloc m 0 1) eqn: Halloc.
  apply Mem.range_perm_drop_2.
  intro; eapply Mem.perm_alloc_2; eauto.
Qed.

Definition store_byte_list m b ofs lv :=
  Mem.storebytes m b ofs (concat (map (encode_val Mint8unsigned) lv)).

Lemma access_at_readable : forall m b o sh (Hsh : readable_share sh),
  access_at m (b, o) Cur = perm_of_sh sh ->
  Mem.perm m b o Cur Readable.
Proof.
  unfold access_at, perm_of_sh, Mem.perm; intros.
  simpl in H; rewrite H.
  if_tac; if_tac; constructor || contradiction.
Qed.

Lemma access_at_writable : forall m b o sh (Hsh : writable_share sh),
  access_at m (b, o) Cur = perm_of_sh sh ->
  Mem.perm m b o Cur Writable.
Proof.
  unfold access_at, perm_of_sh, Mem.perm; intros.
  simpl in H; rewrite H.
  apply writable_writable0 in Hsh.
  if_tac; if_tac; constructor || contradiction.
Qed.

Lemma has_ext_eq' : forall {Z} (z : Z) phi, app_pred (has_ext z) phi ->
  ghost_of phi = [Some (ext_ghost z, NoneP)] /\ forall l, identity (phi @ l).
Proof.
  intros ??? (? & Hno & ->); simpl; split; auto.
  unfold ext_ghost; simpl; repeat f_equal.
Qed.

Corollary has_ext_eq : forall {Z} (z : Z) phi, app_pred (has_ext z) phi ->
  ghost_of phi = [Some (ext_ghost z, NoneP)].
Proof.
  intros; apply has_ext_eq'; auto.
Qed.

Lemma nth_nil : forall {A} n (d : A), nth n nil d = d.
Proof.
  destruct n; auto.
Qed.

Lemma ghost_join_nth : forall (a b c : ghost) n, join a b c ->
  join (nth n a None) (nth n b None) (nth n c None).
Proof.
  intros; revert n; induction H; intro; rewrite ?nth_nil; try constructor.
  destruct n; eauto.
Qed.

Lemma has_ext_join : forall {Z} phi1 phi2 phi3 (z1 z2 : Z) (Hext : nth O (ghost_of phi1) None = Some (ext_ghost z1, NoneP))
  (Hj : join phi1 phi2 phi3) (Hrest : joins (ghost_of phi3) [Some (ext_ref z2, NoneP)]),
  z1 = z2 /\ nth O (ghost_of phi3) None = Some (ext_ghost z1, NoneP).
Proof.
  simpl; intros.
  apply ghost_of_join, ghost_join_nth with (n := O) in Hj.
  rewrite Hext in Hj.
  destruct Hrest as [? Hrest].
  apply ghost_join_nth with (n := O) in Hrest.
  inv Hj.
  - split; auto.
    rewrite <- H2 in Hrest; inv Hrest.
    destruct a3; inv H4; simpl in *.
    inv H; repeat inj_pair_tac.
    destruct c0; inv H8; simpl in *.
    inv H4.
    destruct g as [[]|]; try contradiction.
    inv H.
    destruct vc as (? & [[]|] & vc); hnf in vc; try congruence.
    clear - vc; destruct vc as (? & ? & ?%join_Tsh & ?); tauto.
  - rewrite <- H1 in Hrest; inv Hrest.
    destruct a3, a4; inv H5; simpl in *.
    inv H3.
    destruct a2; inv H2; simpl in *.
    inv H3; inj_pair_tac.
    inv H; repeat inj_pair_tac.
    destruct b0, c0; inv H9; simpl in *.
    destruct c1; inv H8; simpl in *.
    destruct g as [[]|], g0 as [[]|]; try contradiction.
    { destruct H as (? & ? & ?%join_Tsh & ?); tauto. }
    inv H.
    inv H6; [|inv H8].
    assert (o = None) by (inv H2; auto); subst.
    destruct o1 as [[]|]; inv H3.
    split.
    + destruct vc0 as (? & [[]|] & vc0); hnf in vc0; try congruence.
      clear - vc0; destruct vc0 as (? & ? & ?%join_Tsh & ?); tauto.
    + unfold ext_ghost; simpl; repeat f_equal; apply proof_irr.
Qed.

Lemma change_ext : forall {Z} (a a' z : Z) (b c : ghost),
  join [Some (ext_ghost a, NoneP)] b c ->
  joins c [Some (ext_ref z, NoneP)] ->
  join [Some (ext_ghost a', NoneP)] b (Some (ext_ghost a', NoneP) :: tl c).
Proof.
  intros.
  inv H; [constructor|].
  constructor; [|inv H6; constructor].
  inv H3; [constructor|].
  inv H1.
  destruct a0, a4; simpl in *.
  inv H.
  inj_pair_tac.
  inv H7.
  constructor.
  destruct H0 as [? J]; inv J.
  inv H8.
  inv H4; simpl in *.
  destruct a4; simpl in *.
  inv H3.
  inv H2.
  constructor; constructor; auto.
  destruct b0, c0; simpl in *; inv H0; repeat constructor; simpl.
  - repeat inj_pair_tac.
    destruct o as [[]|]; auto.
    destruct o1 as [[]|]; [|contradiction].
    destruct H as (? & ? & ? & ?).
    apply join_Tsh in H2 as []; contradiction.
  - repeat inj_pair_tac.
    inv H1; [|constructor].
    inv H8; simpl in *.
    inv H1; [constructor|].
    inv H7.
Qed.

Lemma change_has_ext : forall {Z} (a a' : Z) r H, app_pred (has_ext a) r ->
  app_pred (has_ext a') (set_ghost r [Some (ext_ghost a', NoneP)] H).
Proof.
  intros; simpl in *.
  destruct H0 as (p & ? & ?); exists p.
  unfold set_ghost; rewrite resource_at_make_rmap, ghost_of_make_rmap.
  split; auto.
  unfold ext_ghost; repeat f_equal.
Qed.

Lemma ext_ref_join : forall {Z} (z : Z), join (ext_ghost z) (ext_ref z) (ext_both z).
Proof.
  intros; repeat constructor.
Qed.

Lemma set_ghost_join : forall a w1 w2 w (J : join w1 w2 w) (Hw2 : res_predicates.noghost w2) H1 H,
  join (set_ghost w1 a H1) w2 (set_ghost w a H).
Proof.
  intros.
  destruct (join_level _ _ _ J).
  apply resource_at_join2; unfold set_ghost; intros; rewrite ?level_make_rmap, ?resource_at_make_rmap, ?ghost_of_make_rmap; auto.
  - apply resource_at_join; auto.
  - rewrite (identity_core Hw2), ghost_core; constructor.
Qed.

Lemma age_rejoin : forall {Z} w1 w2 w w' (a a' z : Z) H (J : join w1 w2 w)
  (Hc : joins (ghost_of w) [Some (ext_ref z, NoneP)])
  (Hg1 : ghost_of w1 = [Some (ext_ghost a, NoneP)])
  (Hl' : (level w' <= level w)%nat)
  (Hr' : forall l, w' @ l = resource_fmap (approx (level w')) (approx (level w')) (w @ l))
  (Hg' : ghost_of w' = Some (ext_ghost a', NoneP) :: own.ghost_approx (level w') (tl (ghost_of w))),
  join (age_to.age_to (level w') (set_ghost w1 [Some (ext_ghost a', NoneP)] H)) (age_to.age_to (level w') w2) w'.
Proof.
  intros.
  destruct (join_level _ _ _ J).
  apply resource_at_join2.
  - rewrite age_to.level_age_to; auto.
    unfold set_ghost; rewrite level_make_rmap; lia.
  - rewrite age_to.level_age_to; auto; lia.
  - eapply age_to.age_to_join_eq in J; eauto.
    intro loc; apply (resource_at_join _ _ _ loc) in J.
    rewrite !age_to_resource_at.age_to_resource_at in *.
    unfold set_ghost; rewrite resource_at_make_rmap.
    rewrite Hr'; auto.
  - rewrite !age_to_resource_at.age_to_ghost_of.
    unfold set_ghost; rewrite ghost_of_make_rmap, Hg'.
    apply ghost_of_join in J; rewrite Hg1 in J.
    eapply change_ext in J; eauto.
    apply ghost_fmap_join with (f := approx (level w'))(g := approx (level w')) in J.
    apply J.
Qed.

Lemma memory_block_writable_perm : forall sh n b ofs r jm, writable_share sh ->
  (0 <= ofs)%Z -> (Z.of_nat n + ofs < Ptrofs.modulus)%Z ->
  app_pred (mapsto_memory_block.memory_block' sh n b ofs) r -> sepalg.join_sub r (m_phi jm) ->
  Mem.range_perm (m_dry jm) b ofs (ofs + Z.of_nat n) Memtype.Cur Memtype.Writable.
Proof.
  intros.
  rewrite mapsto_memory_block.memory_block'_eq in H2 by auto.
  unfold mapsto_memory_block.memory_block'_alt in H2.
  destruct (readable_share_dec sh).
  intros ??.
  apply VALspec_range_e with (loc := (b, ofs0)) in H2 as [? Hb]; simpl; auto.
  destruct H3 as [? J]; apply resource_at_join with (loc := (b, ofs0)) in J.
  pose proof (juicy_mem_access jm (b, ofs0)) as Hperm.
  rewrite Hb in J; inversion J; subst; simpl in *.
  - rewrite <- H8 in Hperm; simpl in Hperm.
    eapply access_at_writable, Hperm.
    apply join_writable1 in RJ; auto.
  - rewrite <- H8 in Hperm; simpl in Hperm.
    eapply access_at_writable, Hperm.
    apply join_writable1 in RJ; auto.
  - apply shares.writable_readable in H; contradiction.
Qed.

Lemma data_at__writable_perm : forall {cs : compspecs} sh t p r jm, writable_share sh ->
  app_pred (@data_at_ cs sh t p) r -> sepalg.join_sub r (m_phi jm) ->
  exists b ofs, p = Vptr b ofs /\
    Mem.range_perm (m_dry jm) b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof t) Memtype.Cur Memtype.Writable.
Proof.
  intros.
  rewrite data_at__memory_block in H0; destruct H0 as [[Hptr Hcompat] Hdata].
  destruct p; try contradiction.
  do 3 eexists; eauto.
  destruct Hdata as [? Hblock].
  eapply memory_block_writable_perm in Hblock; eauto;
    rewrite ?Z2Nat.id, ?nat_of_Z_max, ?Z.max_l in * by (pose proof sizeof_pos t; lia); auto.
  { apply Ptrofs.unsigned_range. }
  { rewrite Z.add_comm; auto. }
Qed.

Lemma rebuild_same : forall jm,
  juicy_mem_lemmas.rebuild_juicy_mem_fmap jm (m_dry jm) = resource_at (m_phi jm).
Proof.
  intros; extensionality l.
  unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap.
  destruct (m_phi jm @ l) eqn: Hl; auto.
  - if_tac; auto.
    destruct jm; simpl in *.
    rewrite (JMaccess l) in H.
    rewrite Hl in H; simpl in H.
    if_tac in H; inv H.
  - destruct k; auto.
    destruct jm; simpl in *.
    if_tac.
    + apply JMcontents in Hl as [-> ?]; subst; auto.
    + contradiction H.
      rewrite (JMaccess l), Hl; simpl.
      unfold perm_of_sh.
      if_tac; if_tac; try contradiction; constructor.
Qed.

Lemma data_at__VALspec_range: forall {cs : compspecs} sh z b o (Hsh: readable_share sh),
  @data_at_ cs sh (tarray tuchar z) (Vptr b o) |--
  res_predicates.VALspec_range z sh (b, Ptrofs.unsigned o).
Proof.
  intros.
  change (predicates_hered.derives (data_at_ sh (tarray tuchar z) (Vptr b o))
    (res_predicates.VALspec_range z sh (b, Ptrofs.unsigned o))).
  intros ? [(_ & _ & Hsize & _) H]; simpl in *.
  rewrite data_at_rec_eq in H; simpl in H.
  unfold default_val, unfold_reptype in H; simpl in H.
  unfold at_offset in H; rewrite offset_val_zero_Vptr in H.
  destruct H as [_ H].
  rewrite Z.sub_0_r, Z2Nat_max0 in H.
  remember 0 as lo in H at 1.
  remember (Z.to_nat z) as hi in H at 1.
  remember (Z.to_nat z) as n in H.
  assert (Z.to_nat lo + hi <= n)%nat by rep_lia.
  assert (0 <= lo <= Ptrofs.max_unsigned) by rep_lia.
  assert (Ptrofs.unsigned o + Z.of_nat n <= Ptrofs.max_unsigned).
  { subst n; rewrite Z2Nat_id'; rep_lia. }
  replace (Ptrofs.unsigned o) with (Ptrofs.unsigned o + lo) by lia.
  clear Heqlo Heqn.
  generalize dependent lo; generalize dependent z; revert a; induction hi; simpl in *.
  - split; [|apply ghost_of_identity; auto].
    intros (?, ?); if_tac; [|apply resource_at_identity; auto].
    unfold adr_range in *. destruct (zlt 0 z); try lia.
  - intros.
    destruct H as (? & ? & J & Hr1 & Hr2).
    assert (lo < Z.of_nat n) by lia.
    assert (z >= 1) by lia.
    apply IHhi with (z := z - 1) in Hr2 as [Hr2 Hg2].
    rewrite data_at_rec_eq in Hr1; simpl in Hr1.
    unfold unfold_reptype in Hr1; simpl in Hr1.
    rewrite <- (Nat2Z.id n) in Hr1.
    rewrite Znth_repeat_inrange in Hr1.
    unfold mapsto in Hr1; simpl in Hr1.
    rewrite if_true in Hr1 by auto.
    destruct Hr1 as [[] | (_ & ? & ? & [? Hr1] & Hg1)]; [contradiction|].
    rewrite Z.mul_1_l in *.
    unfold Ptrofs.add in Hr1; rewrite !Ptrofs.unsigned_repr in Hr1; auto.
    split.
    + intro l.
        specialize (Hr1 l); specialize (Hr2 l); simpl in *.
        apply (resource_at_join _ _ _ l) in J.
        destruct l as (b', o'); if_tac in Hr1; [|if_tac in Hr2].
        * destruct H5; subst.
          rewrite if_true.
          destruct Hr1 as (? & Hr1); rewrite Hr1 in J.
          rewrite if_false in Hr2.
          apply join_comm, Hr2 in J; rewrite <- J; eauto.
          { intros []; lia. }
          { repeat split; auto; lia. }
      * rewrite if_true.
        apply Hr1 in J; rewrite <- J.
        destruct Hr2 as (? & ? & ->); eauto.
        { destruct H6; subst.
          repeat split; auto; lia. }
      * apply Hr1 in J as <-.
        rewrite if_false; auto.
        { fold (adr_range (b, Ptrofs.unsigned o + lo) z (b', o')).
          replace z with (1 + (z - 1)) by lia.
          intros X%adr_range_divide; try lia.
          destruct X; try contradiction.
          unfold Z.succ in *; rewrite Z.add_assoc in *; contradiction. }
    + apply ghost_of_join in J.
        apply Hg1 in J; rewrite <- J; auto.
    + rewrite Ptrofs.unsigned_repr; auto; rep_lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rep_lia.
Qed.

Lemma data_at_bytes : forall {CS : compspecs} sh z (bytes : list val) buf jm phi
  (Hreadable : readable_share sh) (Hlen : z = Zlength bytes) (J : join_sub phi (m_phi jm))
  (Hbuf : app_pred (data_at sh (tarray tuchar z) bytes buf) phi)
  (Hdef : Forall (fun x => x <> Vundef) bytes),
  match buf with
  | Vptr b ofs =>
      Mem.loadbytes (m_dry jm) b (Ptrofs.unsigned ofs) z =
        Some (concat (map (encode_val Mint8unsigned) bytes))
  | _ => False
 end.
Proof.
  intros.
  destruct Hbuf as [(Hptr & _ & Hlim & _) Hbuf].
  unfold at_offset in Hbuf.
  destruct buf; try contradiction; simpl in Hbuf.
  rewrite ptrofs_add_repr_0_r, data_at_rec_eq in Hbuf; simpl in Hbuf.
  unfold unfold_reptype in *; simpl in *.
  destruct Hbuf as [_ Hbuf].
  rewrite Z.sub_0_r, Z.max_r in Hbuf by rep_lia.
  clear Hptr.
  erewrite <- (sublist_same _ _ bytes) by eauto.
  rewrite <- (Z.add_0_r (Ptrofs.unsigned i)).
  rewrite <- (Z.add_0_r z) at 2.
  remember 0 as lo in |- *.
  assert (0 <= lo) by lia.
  rewrite <- Heqlo in Hbuf at 1.
  remember (Z.to_nat z) as n.
  rewrite <- (Z2Nat.id z), <- Heqn by rep_lia.
  assert (lo + Z.of_nat n = Zlength bytes) by (subst; rewrite Z2Nat.id; rep_lia).
  assert (Ptrofs.unsigned i + Zlength bytes < Ptrofs.modulus).
  { rewrite Z.max_r in Hlim by rep_lia; lia. }
  clear Heqlo Hlen.
  clear dependent z.
  revert dependent phi; revert dependent lo.
  induction n; intros; subst.
  - unfold sublist; simpl.
    rewrite skipn_firstn,  Z.add_0_l, minus_diag.
    apply Mem.loadbytes_empty; reflexivity.
  - simpl in Hbuf.
    destruct Hbuf as (phi0 & ? & J' & Hbyte & Hbytes).
    rewrite Nat2Z.inj_succ in *.
    apply IHn in Hbytes; try lia.
    rewrite sublist_next by lia; simpl.
    unfold Z.succ in *; rewrite (Z.add_comm _ 1) in *.
    apply Mem.loadbytes_concat; try lia.
    clear Hbytes.
    unfold at_offset in Hbyte; simpl in Hbyte.
    rewrite data_at_rec_eq in Hbyte; simpl in Hbyte.
    unfold unfold_reptype, mapsto in Hbyte; simpl in Hbyte.
    rewrite if_true in Hbyte by auto.
    destruct Hbyte as [[? Hbyte] | [? Hbyte]].
    destruct Hbyte as (mv & ((? & Hdecode & _) & Hbyte) & _); subst.
    specialize (Hbyte (b, Ptrofs.unsigned i + lo)); simpl in Hbyte.
    replace (Ptrofs.unsigned (Ptrofs.add _ _)) with (Ptrofs.unsigned i +lo) in Hbyte.
    rewrite if_true in Hbyte by (split; auto; lia).
    destruct Hbyte as [? Hval].
    rewrite Zminus_diag in Hval.
    destruct mv; try discriminate.
    unfold decode_val in Hdecode; simpl in *.
    rewrite Z.sub_0_r in *.
    apply Forall_Znth with (i0 := lo) in Hdef; try lia.
    setoid_rewrite <- Hdecode in Hdef.
    destruct m; try contradiction; clear Hdef.
    destruct mv; try discriminate; simpl in *.
    setoid_rewrite <- Hdecode; simpl.
    assert (join_sub phi0 (m_phi jm)) as [? J0].
    { eapply join_sub_trans; [eexists|]; eauto. }
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes.
    Opaque Mem.loadbytes.
    destruct jm; simpl in *.
    assert (exists sh1 rsh1, phi1 @ (b, Ptrofs.unsigned i + lo) = YES sh1 rsh1 (VAL (Byte i0)) NoneP) as (? & ? & Hr).
    { apply (resource_at_join _ _ _ (b, Ptrofs.unsigned i + lo)) in J0.
      rewrite Hval in J0; inv J0; eauto. }
    specialize (JMaccess (b, Ptrofs.unsigned i + lo)); rewrite Hr in JMaccess; simpl in JMaccess.
    apply JMcontents in Hr as [Hr _].
    rewrite if_true.
    unfold contents_at in Hr; simpl in Hr.
    rewrite Hr.
    unfold decode_int; simpl.
    rewrite rev_if_be_singleton; simpl.
    assert (0 <= Byte.unsigned i0 <= Int.max_unsigned) by rep_lia.
    rewrite Z.add_0_r, zero_ext_inrange, Int.unsigned_repr; auto.
    unfold encode_int; simpl.
    rewrite rev_if_be_singleton; simpl.
    rewrite Byte.repr_unsigned; auto.
    * rewrite Int.unsigned_repr by auto.
      destruct (Byte.unsigned_range i0) as [_ Hmax].
      unfold Byte.modulus in Hmax.
      unfold Byte.wordsize, Wordsize_8.wordsize in Hmax.
      rewrite two_power_nat_two_p in Hmax; simpl Z.of_nat in Hmax; lia.
    * unfold Mem.range_perm; intros.
      unfold Mem.perm.
      assert (ofs = Ptrofs.unsigned i + lo) by lia; subst.
      unfold access_at in JMaccess; simpl in JMaccess; rewrite JMaccess.
      unfold perm_of_sh.
      if_tac; if_tac; try constructor; contradiction.
    * unfold Ptrofs.add.
      setoid_rewrite Ptrofs.unsigned_repr at 2; [|rep_lia].
      rewrite Ptrofs.unsigned_repr; rep_lia.
    * apply Forall_Znth with (i0 := lo - 0) in Hdef; try lia; contradiction.
    * rewrite Z.add_assoc in *.
      replace (1 + Z.of_nat n + lo) with (Z.of_nat n + (lo + 1)) by lia; auto.
    * eapply join_sub_trans; [eexists|]; eauto.
Qed.

(* up *)
Lemma perm_order_antisym : forall p p', perm_order p p' -> perm_order p' p -> p = p'.
Proof.
  inversion 1; auto; inversion 1; auto.
Qed.

Lemma mem_equiv_access : forall m m', mem_equiv m m' -> access_at m = access_at m'.
Proof.
  intros ?? (_ & Hperm & _).
  unfold Mem.perm in Hperm.
  extensionality l.
  destruct l as (b, o).
  extensionality k.
  apply equal_f with b, equal_f with o, equal_f with k in Hperm.
  unfold access_at; simpl.
  destruct (_ !! _).
  - pose proof (equal_f Hperm p) as Hp; simpl in *.
    pose proof (perm_refl p) as Hrefl; rewrite Hp in Hrefl.
    destruct (_ !! _); [simpl in * | contradiction].
    f_equal; apply perm_order_antisym; auto.
    apply equal_f with p0 in Hperm.
    rewrite Hperm; apply perm_refl.
  - destruct (_ !! _); auto.
    apply equal_f with p in Hperm; simpl in Hperm.
    pose proof (perm_refl p) as Hrefl; rewrite <- Hperm in Hrefl; contradiction.
Qed.

Lemma mem_equiv_contents : forall m m' b o (Heq : mem_equiv m m')
  (Hreadable : Mem.perm m b o Cur Readable),
  contents_at m (b, o) = contents_at m' (b, o).
Proof.
  intros ???? (Hload & Hperm & _) ?.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in Hload.
  Opaque Mem.loadbytes.
  apply equal_f with b, equal_f with o, equal_f with 1 in Hload.
  unfold contents_at; simpl.
  rewrite 2if_true  in Hload.
  inv Hload; auto.
  { unfold Mem.range_perm.
    intros; assert (ofs = o) by lia; subst.
    rewrite <- Hperm; auto. }
  { unfold Mem.range_perm.
    intros; assert (ofs = o) by lia; subst; auto. }
Qed.

Lemma mem_evolve_access : forall m1 m2, access_at m1 = access_at m2 -> mem_evolve m1 m2.
Proof.
  intros; unfold mem_evolve.
  intro; rewrite H.
  destruct (access_at _ _ _); auto.
  destruct p; auto.
Qed.

Lemma mem_evolve_equiv1 : forall m1 m2 m1', mem_evolve m1 m2 -> mem_equiv m1 m1' -> mem_evolve m1' m2.
Proof.
  unfold mem_evolve; intros.
  rewrite <- (mem_equiv_access _ _ H0); apply H.
Qed.

Lemma mem_evolve_equiv2 : forall m1 m2 m2', mem_evolve m1 m2 -> mem_equiv m2 m2' -> mem_evolve m1 m2'.
Proof.
  unfold mem_evolve; intros.
  rewrite <- (mem_equiv_access _ _ H0); apply H.
Qed.

Definition mem_equiv_jm jm m (Heq : mem_equiv (m_dry jm) m) :
  {jm' | level jm' = level jm /\ m_dry jm' = m /\ m_phi jm' = m_phi jm}.
Proof.
  destruct jm; simpl in *.
  unshelve eexists (mkJuicyMem m phi _ _ _ _); simpl; auto.
  - unfold contents_cohere in *; intros.
    destruct (JMcontents _ _ _ _ _ H) as []; subst; split; auto.
    symmetry; apply mem_equiv_contents; auto.
    specialize (JMaccess loc).
    rewrite H in JMaccess; simpl in JMaccess.
    apply access_at_readable in JMaccess; auto.
  - unfold access_cohere in *; intros.
    erewrite <- JMaccess, <- mem_equiv_access; eauto.
  - unfold max_access_cohere in *; intros.
    unfold max_access_at in *.
    erewrite <- mem_equiv_access; eauto.
  - unfold alloc_cohere in *.
    destruct Heq as (_ & _ & <-); auto.
Defined.

(* up *)
Lemma has_ext_noat : forall {Z} (z : Z), has_ext z |-- ALL x : _, res_predicates.noat x.
Proof.
  intros; unfold has_ext, own.own.
change (@predicates_hered.exp rmap ag_rmap) with (@exp mpred _).
  apply exp_left; intro.
 unfold own.Own.
 change (@predicates_hered.andp rmap ag_rmap) with (@andp mpred _).
  apply andp_left1.
  apply derives_refl.
Qed.

Lemma inflate_store_join1 : forall phi1 phi2 phi3 m (J : join phi1 phi2 phi3)
  (Hno : app_pred (ALL x : _, res_predicates.noat x) phi1),
  join phi1 (inflate_store m phi2) (inflate_store m phi3).
Proof.
  intros.
  destruct (join_level _ _ _ J).
  apply resource_at_join2; intros; unfold inflate_store;
    rewrite ?level_make_rmap, ?resource_at_make_rmap, ?ghost_of_make_rmap; try apply ghost_of_join; auto.
  apply (resource_at_join _ _ _ loc) in J.
  specialize (Hno loc).
  apply empty_NO in Hno as [Hno | (? & ? & Hno)]; rewrite Hno in *; inv J; try constructor; auto.
  rewrite H0.
  destruct k; constructor; auto.
Qed.

Lemma inflate_store_join : forall phi1 phi2 phi3 m (J : join phi1 phi2 phi3),
  join (inflate_store m phi1) (inflate_store m phi2) (inflate_store m phi3).
Proof.
  intros.
  destruct (join_level _ _ _ J) as [H1 H2].
  apply resource_at_join2; intros; unfold inflate_store;
    rewrite ?level_make_rmap, ?resource_at_make_rmap, ?ghost_of_make_rmap; try apply ghost_of_join; auto.
  apply (resource_at_join _ _ _ loc) in J.
  rewrite H1, H2.
  inv J; try constructor; auto; destruct k; constructor; auto.
Qed.

Lemma rebuild_store : forall jm0 phi m m' b o lv phi0 phi1 loc
  (Hlevel : (level phi <= level (m_phi jm0))%nat)
  (Hrebuild : compcert_rmaps.R.resource_at phi =
     compcert_rmaps.R.resource_fmap (compcert_rmaps.R.approx (level phi))
       (compcert_rmaps.R.approx (level phi))
     oo juicy_mem_lemmas.rebuild_juicy_mem_fmap jm0 m)
  (Hstore : Mem.storebytes (m_dry jm0) b o lv = Some m') (Heq : mem_equiv m m')
  (J : join phi0 phi1 (m_phi jm0))
  (Hout1 : forall l sh rsh k p, phi1 @ l = YES sh rsh k p -> ~ adr_range (b, o) (Zlength lv) l),
  join (age_to.age_to (level phi) (inflate_store m' phi0) @ loc)
         (age_to.age_to (level phi) phi1 @ loc) (phi @ loc).
Proof.
  intros.
  destruct (join_level _ _ _ J).
  rewrite Hrebuild, !age_to_resource_at.age_to_resource_at.
  unfold compose, inflate_store, juicy_mem_lemmas.rebuild_juicy_mem_fmap; rewrite !resource_at_make_rmap.
  apply (resource_at_join _ _ _ loc) in J.
  simpl.
  inv J; try constructor.
  - rewrite if_false; [constructor; auto|].
    erewrite mem_equiv_access by eauto.
    erewrite <- storebytes_access by eauto.
    destruct jm0; simpl in *.
    rewrite (JMaccess loc), <- H4; simpl.
    if_tac; auto.
    intro X; inv X.
  - destruct k; try (rewrite resource_fmap_fmap, approx_oo_approx', approx'_oo_approx by lia; constructor; auto).
    destruct jm0; simpl in *.
    pose proof (JMaccess loc) as Haccess.
    rewrite <- H4 in Haccess; simpl in Haccess.
    erewrite storebytes_access, <- mem_equiv_access in Haccess by eauto.
    destruct loc as (b', o').
    erewrite <- mem_equiv_contents; eauto.
    rewrite Haccess, if_true.
    constructor; auto.
    { unfold perm_of_sh.
      if_tac; if_tac; constructor || contradiction. }
    { eapply access_at_readable; eauto. }
  - destruct k; try (constructor; auto).
    pose proof (juicy_mem_access jm0 loc) as Haccess.
    rewrite <- H4 in Haccess; simpl in Haccess.
    erewrite storebytes_access, <- mem_equiv_access in Haccess by eauto.
    rewrite Haccess, if_true.
    destruct loc as (b', o').
    erewrite mem_equiv_contents; eauto.
    exploit (juicy_mem_contents jm0); eauto; intros []; subst.
    erewrite (storebytes_phi_elsewhere_eq _ _ _ _ _ Hstore); eauto.
    constructor; auto.
    { eapply access_at_readable; eauto. }
    { unfold perm_of_sh.
      if_tac; if_tac; constructor || contradiction. }
  - destruct k; try (rewrite resource_fmap_fmap, approx_oo_approx', approx'_oo_approx by lia; constructor; auto).
    pose proof (juicy_mem_access jm0 loc) as Haccess.
    rewrite <- H4 in Haccess; simpl in Haccess.
    erewrite storebytes_access, <- mem_equiv_access in Haccess by eauto.
    rewrite Haccess, if_true.
    destruct loc as (b', o').
    erewrite (mem_equiv_contents m); eauto.
    exploit (juicy_mem_contents jm0); eauto; intros []; subst.
    erewrite (storebytes_phi_elsewhere_eq _ _ _ _ _ Hstore); eauto.
    constructor; auto.
    { eapply access_at_readable; eauto. }
    { unfold perm_of_sh.
      if_tac; if_tac; constructor || contradiction. }
Qed.

Lemma rebuild_alloc : forall jm0 phi m len phi0 phi1 loc
  (Hlevel : (level phi <= level (m_phi jm0))%nat)
  (Hrebuild : compcert_rmaps.R.resource_at phi =
     compcert_rmaps.R.resource_fmap (compcert_rmaps.R.approx (level phi))
       (compcert_rmaps.R.approx (level phi))
     oo juicy_mem_lemmas.rebuild_juicy_mem_fmap jm0 m)
  (Hno : forall ofs : Z,
      phi0 @ (Mem.nextblock (m_dry jm0), ofs) = NO Share.bot bot_unreadable)
  (Heq : mem_equiv m (fst (Mem.alloc (m_dry jm0) 0 len)))
  (J : join phi0 phi1 (m_phi jm0)),
  join (age_to.age_to (level phi) (after_alloc 0 len (Mem.nextblock (m_dry jm0)) phi0 Hno) @ loc)
         (age_to.age_to (level phi) phi1 @ loc) (phi @ loc).
Proof.
  intros.
  destruct (join_level _ _ _ J).
  rewrite Hrebuild, !age_to_resource_at.age_to_resource_at.
  unfold compose, after_alloc, juicy_mem_lemmas.rebuild_juicy_mem_fmap; rewrite !resource_at_make_rmap.
  unfold after_alloc'.
  apply (resource_at_join _ _ _ loc) in J.
  assert (Mem.alloc (m_dry jm0) 0 len = (fst (Mem.alloc (m_dry jm0) 0 len), Mem.nextblock (m_dry jm0))) as Halloc.
  { destruct (Mem.alloc (m_dry jm0) 0 len) eqn: Halloc; simpl; f_equal.
      eapply Mem.alloc_result; eauto. }
  if_tac.
  - (* allocated block *)
    edestruct alloc_dry_updated_on as [Haccess Hcontents]; eauto.
    destruct loc, H1; subst.
    destruct jm0; simpl in *.
    rewrite JMalloc in * by (simpl; Lia.lia).
    inv J.
    rewrite if_true.
    erewrite mem_equiv_contents, Hcontents; try apply Heq.
    apply join_Bot in RJ as []; subst.
    constructor; auto.
    { destruct Heq as (_ & -> & _).
      eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto; lia | constructor]. }
    { erewrite mem_equiv_access, Haccess by apply Heq; constructor. }
  - edestruct alloc_dry_unchanged_on as [Haccess Hcontents]; eauto.
    simpl.
    inv J; try constructor.
    + rewrite if_false; [constructor; auto|].
      erewrite mem_equiv_access by eauto.
      rewrite <- Haccess.
      destruct jm0; simpl in *.
      rewrite (JMaccess loc), <- H5; simpl.
      if_tac; auto.
      intro X; inv X.
    + destruct k; try (constructor; auto).
      destruct jm0; simpl in *.
      pose proof (JMaccess loc) as Haccess'.
      rewrite <- H5 in Haccess'; simpl in Haccess'.
      erewrite Haccess, <- mem_equiv_access in Haccess' by eauto.
      destruct loc as (b', o').
      assert (Mem.perm_order'' (perm_of_sh sh3) (Some Readable)).
      { unfold perm_of_sh.
        if_tac; if_tac; constructor || contradiction. }
      erewrite mem_equiv_contents; eauto.
      rewrite Haccess', <- Hcontents, if_true; auto.
      symmetry in H5; apply JMcontents in H5 as []; subst.
      constructor; auto.
      { rewrite JMaccess, <- H5; simpl.
        unfold perm_of_sh.
        if_tac; if_tac; auto; discriminate. }
      { rewrite perm_access, Haccess'; auto. }
    + destruct k; try (constructor; auto).
      pose proof (juicy_mem_access jm0 loc) as Haccess'.
      rewrite <- H5 in Haccess'; simpl in Haccess'.
      erewrite Haccess, <- mem_equiv_access in Haccess' by eauto.
      assert (Mem.perm_order'' (perm_of_sh sh3) (Some Readable)).
      { unfold perm_of_sh.
        if_tac; if_tac; constructor || contradiction. }
      rewrite Haccess', if_true; auto.
      destruct loc as (b', o').
      destruct jm0; simpl in *.
      erewrite mem_equiv_contents; eauto.
      rewrite <- Hcontents.
      symmetry in H5; apply JMcontents in H5 as []; subst.
      constructor; auto.
      { rewrite JMaccess, <- H5; simpl.
        unfold perm_of_sh.
        if_tac; if_tac; auto; discriminate. }
      { rewrite perm_access, Haccess'; auto. }
  + destruct k; try (constructor; auto).
      pose proof (juicy_mem_access jm0 loc) as Haccess'.
      rewrite <- H5 in Haccess'; simpl in Haccess'.
      erewrite Haccess, <- mem_equiv_access in Haccess' by eauto.
      assert (Mem.perm_order'' (perm_of_sh sh3) (Some Readable)).
      { unfold perm_of_sh.
        if_tac; if_tac; constructor || contradiction. }
      rewrite Haccess', if_true; auto.
      destruct loc as (b', o').
      destruct jm0; simpl in *.
      erewrite mem_equiv_contents; eauto.
      rewrite <- Hcontents.
      symmetry in H5; apply JMcontents in H5 as []; subst.
      constructor; auto.
      { rewrite JMaccess, <- H5; simpl.
        unfold perm_of_sh.
        if_tac; if_tac; auto; discriminate. }
      { rewrite perm_access, Haccess'; auto. }
Qed.

Lemma inflate_emp : forall m phi, app_pred emp phi -> app_pred emp (inflate_store m phi).
Proof.
  simpl; intros.
  apply all_resource_at_identity.
  - intros; unfold inflate_store; rewrite resource_at_make_rmap.
    apply (resource_at_identity _ l) in H.
    destruct (phi @ l); auto.
    apply YES_not_identity in H; contradiction.
  - unfold inflate_store; rewrite ghost_of_make_rmap.
    apply ghost_of_identity; auto.
Qed.

Lemma encode_vals_length : forall lv,
  length (concat (map (encode_val Mint8unsigned) lv)) = length lv.
Proof.
  induction lv; auto; simpl.
  rewrite app_length, IHlv.
  unfold encode_val; simpl.
  destruct a; auto.
Qed.

Lemma store_bytes_data_at : forall {CS : compspecs} phi m0 m sh lv b o
  (Hsh : readable_share sh) (Hvals : Forall (fun v => exists i, v = Vint i /\ Int.unsigned i <= Byte.max_unsigned) lv)
  (Hdata : app_pred (res_predicates.VALspec_range (Zlength lv) sh (b, Ptrofs.unsigned o)) phi)
  (Hstore : Mem.storebytes m0 b (Ptrofs.unsigned o) (concat (map (encode_val Mint8unsigned) lv)) = Some m)
  (Hbounds : Ptrofs.unsigned o + Zlength lv <= Ptrofs.max_unsigned),
  app_pred (data_at sh (tarray tuchar (Zlength lv)) lv (Vptr b o)) (inflate_store m phi).
Proof.
  split.
  { split; simpl; auto.
    split; auto.
    split; [rewrite Z.max_r by rep_lia; unfold Ptrofs.max_unsigned in Hbounds; lia|].
    split; auto.
    constructor.
    intros; econstructor; simpl; eauto.
    apply Z.divide_1_l. }
  unfold at_offset; rewrite data_at_rec_eq; simpl.
  rewrite Z.max_r by rep_lia.
  rewrite ptrofs_add_repr_0_r.
  unfold unfold_reptype; simpl.
  split.
  { rewrite Z.sub_0_r; reflexivity. }
  rewrite Z.sub_0_r.
  rewrite <- (Z.add_0_r (Ptrofs.unsigned o)) in Hdata.
  remember 0 as lo.
  assert (0 <= lo) by lia.
  rewrite Heqlo; rewrite <- Heqlo at 1.
  remember (Z.to_nat (Zlength lv)) as n.
  replace (Zlength lv) with (Z.of_nat n) in Hdata by (subst; rewrite Z2Nat.id; rep_lia).
  assert (lo + Z.of_nat n = Zlength lv) as Hlen.
  { subst; rewrite Z2Nat.id; rep_lia. }
  clear Heqlo Heqn.
  revert dependent lo; revert dependent phi; induction n; intros.
  - rewrite res_predicates.VALspec_range_0 in Hdata; simpl.
    apply inflate_emp; auto.
  - rewrite Nat2Z.inj_succ, res_predicates.VALspec_range_split2 with (n := 1)(m := Z.of_nat n) in Hdata by lia.
    destruct Hdata as (phi1 & phi2 & J & Hval1 & Hval2).
    rewrite Nat2Z.inj_succ in Hlen.
    rewrite <- Z.add_assoc in Hval2; apply IHn in Hval2; try lia.
    eexists _, _; split; [apply inflate_store_join; eauto|].
    split; auto.
    unfold at_offset.
    rewrite data_at_rec_eq; simpl.
    unfold unfold_reptype; simpl.
    rewrite Z.sub_0_r.
    unfold mapsto; simpl.
    rewrite if_true by auto.
    left.
    apply Forall_Znth with (i := lo) in Hvals as (i & Hi & ?); try lia.
    split.
    { setoid_rewrite Hi; auto. }
    unfold res_predicates.address_mapsto.
    exists [Byte (Byte.repr (Int.unsigned i))].
    destruct Hval1 as [Hval1 Hg].
    split; [|simpl; unfold inflate_store; rewrite ghost_of_make_rmap; auto].
    split.
    { split; auto.
      setoid_rewrite Hi.
      split; [|apply Z.divide_1_l].
      unfold decode_val; simpl.
      unfold decode_int; simpl.
      rewrite rev_if_be_singleton; simpl.
      rewrite Byte.unsigned_repr by rep_lia.
      rewrite Z.add_0_r, Int.repr_unsigned.
      rewrite zero_ext_inrange; auto. }
    intro l; simpl.
    unfold inflate_store; rewrite resource_at_make_rmap.
    specialize (Hval1 l); simpl in Hval1.
    unfold Ptrofs.add.
    replace (Ptrofs.unsigned (Ptrofs.repr (1 * lo))) with lo
      by (rewrite Ptrofs.unsigned_repr; rep_lia).
    rewrite Ptrofs.unsigned_repr by rep_lia.
    if_tac.
    + destruct Hval1 as (mv & rsh & ->); exists rsh.
      destruct l as (b', o'); destruct H1; subst.
      assert (o' = Ptrofs.unsigned o + lo) by lia; subst; simpl.
      rewrite Zminus_diag; simpl; f_equal; f_equal.
      Transparent Mem.storebytes.
      unfold Mem.storebytes in Hstore.
      Opaque Mem.storebytes.
      if_tac in Hstore; inv Hstore; unfold contents_at; simpl.
      rewrite PMap.gss.
      replace lv with (sublist 0 lo lv ++ Znth lo lv :: sublist (lo + 1) (Zlength lv) lv).
      rewrite map_app, concat_app; simpl.
      rewrite Mem.setN_concat.
      rewrite Hi; simpl.
      unfold encode_int; simpl.
      rewrite rev_if_be_singleton; simpl.
      rewrite encode_vals_length, <- Zlength_correct.
      rewrite Zlength_sublist, Mem.setN_outside by lia.
      rewrite Z.sub_0_r, ZMap.gss; auto.
      { rewrite <- sublist_next, sublist_rejoin, sublist_same by lia; auto. }
  + destruct (phi1 @ l); auto.
    apply YES_not_identity in Hval1; contradiction.
Qed.

Definition main_pre_dry {Z} (m : mem) (prog : Clight.program) (ora : Z)
  (ts : list Type) (gv : globals) (z : Z) :=
  Genv.globals_initialized (Genv.globalenv prog) (Genv.globalenv prog) m /\ z = ora.

Definition main_post_dry {Z} (m0 m : mem) (prog : Clight.program) (ora : Z)
  (ts : list Type) (gv : globals) (z : Z) := True. (* the desired postcondition might vary by program *)

(* simulate funspec2pre/post *)

Search genv genviron.
Definition main_pre_juicy {Z} prog (ora : Z) gv (x' : rmap * {ts : list Type & unit})
  (ge_s: extspec.injective_PTree block) args (z : Z) (m : juicy_mem) :=
    Val.has_type_list args [] /\
(*    (exists phi0 phi1 : rmap,
       join phi0 phi1 (m_phi m) /\*)
       (app_pred (main_pre prog ora gv
          (filter_genv (semax_ext.symb2genv ge_s), nil))
         (m_phi m) (*phi0 /\
       necR (fst x') phi1*) /\ joins (ghost_of (m_phi m)) [Some (ext_ref z, NoneP)]).

Definition rettype_of_option_typ (t: option typ) : rettype :=
match t with Some t => AST.Tret t | None => AST.Tvoid end.

Definition main_post_juicy {Z} prog (ora : Z) gv (x' : rmap * {ts : list Type & unit})
  (ge_s: extspec.injective_PTree block) (tret : option typ) ret (z : Z) (m : juicy_mem) :=
  (*exists phi0 phi1 : rmap,
       join phi0 phi1 (m_phi m) /\*)
       (app_pred (main_post prog gv
          (semax.make_ext_rval (filter_genv (semax_ext.symb2genv ge_s)) (rettype_of_option_typ tret) ret))
         (m_phi m)(*phi0 /\
       necR (fst x') phi1*) /\ joins (ghost_of (m_phi m)) [Some (ext_ref z, NoneP)]).

Lemma main_dry : forall {Z} prog (ora : Z) ts gv,
  (forall t b vl x jm,
  Genv.init_mem (program_of_program prog) = Some (m_dry jm) ->
  main_pre_juicy prog ora gv t b vl x jm ->
  main_pre_dry (m_dry jm) prog ora ts gv x) /\
  (forall t b ot v x jm0 jm,
    (exists vl x0, main_pre_juicy prog ora gv t b vl x0 jm0) ->
    (level jm <= level jm0)%nat ->
    resource_at (m_phi jm) = resource_fmap (approx (level jm)) (approx (level jm)) oo juicy_mem_lemmas.rebuild_juicy_mem_fmap jm0 (m_dry jm) ->
    ghost_of (m_phi jm) = Some (ghost_PCM.ext_ghost x, compcert_rmaps.RML.R.NoneP) :: ghost_fmap (approx (level jm)) (approx (level jm)) (tl (ghost_of (m_phi jm0))) ->
    (main_post_dry (m_dry jm0) (m_dry jm) prog ora ts gv x ->
     main_post_juicy prog ora gv t b ot v x jm)).
Proof.
  split; intros.
  - unfold main_pre_juicy, main_pre_dry in *.
    destruct H0 as (? & Hpre & Hext).
    unfold main_pre in Hpre.
    destruct Hpre as (? & ? & J & Hglobals & Htrace).
    apply has_ext_eq in Htrace.
    split.
    + apply Genv.init_mem_characterization_gen; auto.
    + eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join, join_comm; eauto].
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
  - unfold main_post_juicy.
    split; [apply I|].
    rewrite H2.
    eexists; constructor; constructor.
    instantiate (1 := (_, _)); constructor; simpl; [|constructor; auto].
    apply ext_ref_join.
Qed.
