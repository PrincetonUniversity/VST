Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.progs.conclib.

(* functions on byte arrays and CompCert mems *)
Fixpoint store_byte_list m b ofs lv :=
  match lv with
  | [] => Some m
  | v :: lv => match Mem.store Mint8unsigned m b ofs v with
               | Some m' => store_byte_list m' b (ofs + 1)%Z lv
               | None => None
               end
  end.

Lemma store_byte_list_access : forall m b ofs v m',
  store_byte_list m b ofs v = Some m' ->
  Memory.access_at m = Memory.access_at m'.
Proof.
  intros until v; revert m ofs; induction v; simpl; intros.
  - inv H; auto.
  - destruct (Mem.store _ _ _ _ _) eqn: Hstore; [|discriminate].
    rewrite (Memory.store_access _ _ _ _ _ _ Hstore); eauto.
Qed.

Lemma store_byte_list_nextblock : forall m b ofs v m',
  store_byte_list m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros until v; revert m ofs; induction v; simpl; intros.
  - inv H; auto.
  - destruct (Mem.store _ _ _ _ _) eqn: Hstore; [|discriminate].
    etransitivity; [|eapply Mem.nextblock_store; eauto]; eauto.
Qed.

Lemma store_byte_list_contents : forall m b ofs v m',
  store_byte_list m b ofs v = Some m' ->
  forall b' ofs',
    (b=b' /\ ofs <= ofs' < ofs + Zlength v) \/
     contents_at m (b', ofs') = contents_at m' (b', ofs').
Proof.
  intros until v; revert m ofs; induction v; simpl; intros.
  - inv H; auto.
  - destruct (Mem.store _ _ _ _ _) eqn: Hstore; [|discriminate].
    rewrite Zlength_cons.
    destruct (IHv _ _ _ H b' ofs') as [(? & ? & ?) | <-];
      [left; split; auto; split; auto; omega|].
    destruct (eq_block b b').
    subst b'.
    assert (ofs <= ofs' < ofs + Z.succ (Zlength v) \/
      (ofs' < ofs \/ ofs' >= ofs + Z.succ (Zlength v))) as [? | ?] by omega; auto.
    right.
    unfold contents_at; rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore); simpl.
    rewrite PMap.gss.
    rewrite Mem.setN_other; auto.
    intro; rewrite encode_val_length; simpl.
    pose proof Zlength_nonneg v; omega.
    { right.
      unfold contents_at; rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore); simpl.
      rewrite PMap.gso by auto. auto. }
Qed.

Lemma store_byte_list_contents' : forall jm b ofs v m' loc' rsh sh mv,
  store_byte_list (m_dry jm) b ofs v = Some m' ->
  ~ adr_range (b, ofs) (Zlength v) loc'
  -> (m_phi jm) @ loc' = YES rsh sh (VAL mv) NoneP -> contents_at m' loc' = mv.
Proof.
destruct jm. simpl.
intros.
destruct loc' as (b', ofs').
destruct (store_byte_list_contents _ _ _ _ _ H b' ofs') as [|<-]; [contradiction|].
eapply JMcontents; eauto.
Qed.

Definition store_byte_list_juicy_mem jm m' b ofs v
  (Hstore : store_byte_list (m_dry jm) b ofs v = Some m') : juicy_mem.
Proof.
 refine (mkJuicyMem m' (inflate_store m' (m_phi jm)) _ _ _ _).
(* contents_cohere *)
intros rsh sh' v' loc' pp H2.
unfold inflate_store in H2; rewrite resource_at_make_rmap in H2.
destruct (m_phi jm @ loc'); try destruct k; try solve [inversion H2].
inversion H2; auto.
(* access_cohere *)
intro loc; generalize (juicy_mem_access jm loc); intro H0.
unfold inflate_store; rewrite resource_at_make_rmap.
rewrite <- (store_byte_list_access _ _ _ _ _ Hstore).
destruct (m_phi jm @ loc); try destruct k; auto.
(* max_access_cohere *)
intro loc; generalize (juicy_mem_max_access jm loc); intro H1.
unfold inflate_store; rewrite resource_at_make_rmap.
unfold max_access_at in *.
rewrite <- (store_byte_list_access _ _ _ _ _ Hstore).
apply store_byte_list_nextblock in Hstore.
destruct (m_phi jm @ loc); auto.
destruct k; simpl; try assumption.
(* alloc_cohere *)
hnf; intros.
unfold inflate_store. rewrite resource_at_make_rmap.
generalize (juicy_mem_alloc_cohere jm loc); intro.
rewrite (store_byte_list_nextblock _ _ _ _ _ Hstore) in H.
rewrite (H0 H). auto.
Defined.

Lemma has_ext_eq : forall {Z} (z : Z) phi, app_pred (has_ext z) phi ->
  ghost_of phi = [Some (ext_ghost z, NoneP)].
Proof.
  intros ??? (? & _ & ->); simpl.
  unfold ext_ghost; simpl; repeat f_equal.
  apply proof_irr.
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

Lemma change_has_ext : forall {Z} (a a' : Z) r H, has_ext a r ->
  has_ext a' (set_ghost r [Some (ext_ghost a', NoneP)] H).
Proof.
  intros; simpl in *.
  destruct H0 as (p & ? & ?); exists p.
  unfold set_ghost; rewrite resource_at_make_rmap, ghost_of_make_rmap.
  split; auto.
  unfold ext_ghost; repeat f_equal.
  apply proof_irr.
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
    unfold set_ghost; rewrite level_make_rmap; omega.
  - rewrite age_to.level_age_to; auto; omega.
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
    unfold perm_of_sh in Hperm.
    apply join_writable1 in RJ; auto.
    destruct (writable0_share_dec _); [|destruct RJ; contradiction].
    destruct (eq_dec _ _); [|apply Memory.access_perm; auto].
    eapply Mem.perm_implies; [apply Memory.access_perm; eauto | constructor].
  - rewrite <- H8 in Hperm; simpl in Hperm.
    unfold perm_of_sh in Hperm.
    apply join_writable1 in RJ; auto.
    destruct (writable0_share_dec _); [|destruct RJ; contradiction].
    destruct (eq_dec _ _); [|apply Memory.access_perm; auto].
    eapply Mem.perm_implies; [apply Memory.access_perm; eauto | constructor].
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
    rewrite ?nat_of_Z_max, ?Z.max_l in * by (pose proof sizeof_pos t; omega); auto.
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
  assert (Z.to_nat lo + hi <= n)%nat by rep_omega.
  assert (0 <= lo <= Ptrofs.max_unsigned) by rep_omega.
  assert (Ptrofs.unsigned o + Z.of_nat n <= Ptrofs.max_unsigned).
  { subst n; rewrite Z2Nat_id'; rep_omega. }
  replace (Ptrofs.unsigned o) with (Ptrofs.unsigned o + lo) by omega.
  clear Heqlo Heqn.
  generalize dependent lo; generalize dependent z; revert a; induction hi; simpl in *.
  - split; [|apply ghost_of_identity; auto].
    intros (?, ?); if_tac; [|apply resource_at_identity; auto].
    unfold adr_range in *. destruct (zlt 0 z); try omega.
    apply Z2Nat.inj_lt in l; omega.
  - intros.
    destruct H as (? & ? & J & Hr1 & Hr2).
    assert (lo < Z.of_nat n).
    { apply Z2Nat.inj_lt; try omega.
      rewrite Nat2Z.id; omega. }
    assert (z >= 1).
    { destruct (zlt z 0). apply Z2Nat_neg in l; omega.
      apply Z.le_ge, Z2Nat.inj_le; simpl; omega. }
    apply IHhi with (z := z - 1) in Hr2 as [Hr2 Hg2].
    rewrite data_at_rec_eq in Hr1; simpl in Hr1.
    unfold unfold_reptype in Hr1; simpl in Hr1.
    rewrite <- (Nat2Z.id n) in Hr1.
    rewrite Znth_list_repeat_inrange in Hr1.
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
          { intros []; omega. }
          { repeat split; auto; omega. }
      * rewrite if_true.
        apply Hr1 in J; rewrite <- J.
        destruct Hr2 as (? & ? & ->); eauto.
        { destruct H6; subst.
          repeat split; auto; omega. }
      * apply Hr1 in J as <-.
        rewrite if_false; auto.
        { fold (adr_range (b, Ptrofs.unsigned o + lo) z (b', o')).
          replace z with (1 + (z - 1)) by omega.
          intros X%adr_range_divide; try omega.
          destruct X; try contradiction.
          unfold Z.succ in *; rewrite Z.add_assoc in *; contradiction. }
    + apply ghost_of_join in J.
        apply Hg1 in J; rewrite <- J; auto.
    + rewrite Ptrofs.unsigned_repr; auto; rep_omega.
    + omega.
    + eapply Z.le_lt_trans; eauto.
        apply Zplus_le_compat_l, Zmult_le_compat_l; try omega.
        apply Z.max_le_compat_l; omega.
    + rewrite Z2Nat.inj_sub; try omega; simpl.
        destruct (Z.to_nat z); [discriminate | omega].
    + rewrite Z2Nat.inj_succ; omega.
    + rep_omega.
Qed.
