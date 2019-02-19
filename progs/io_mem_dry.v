Require Import VST.progs.io_specs_mem.
Require Import VST.progs.io_mem.
Require Import VST.floyd.proofauto.
Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Eq.Utt.
Import MonadNotations.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.SequentialClight.
Require Import VST.progs.conclib.
Require Import VST.veric.mem_lessdef.

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


(* dry specs for I/O *)
Definition getchars_pre (m : mem) (sh : share) (buf : val) (len : Z) (k : list int -> IO_itree)
  (z : IO_itree) := (z = (r <- read_list (Z.to_nat len);; k r))%eq_utt /\
    match buf with Vptr b ofs =>
      Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + Z.max 0 len) Memtype.Cur Memtype.Writable
      | _ => False end.

Definition getchars_post (m0 m : mem) r (sh : share) (buf : val) (len : Z) (k : list int -> IO_itree) (z : IO_itree) :=
  m0 = m /\ r = Int.repr len /\ exists msg, z = k msg /\
    match buf with Vptr b ofs => exists m', store_byte_list m0 b (Ptrofs.unsigned ofs) (map Vint msg) = Some m' /\
        mem_equiv m m'
    | _ => False end.

Definition putchars_pre (m : mem) (sh : share) (buf : val) (msg : list int) (k : IO_itree) (z : IO_itree) :=
  (z = (write_list msg;; k))%eq_utt /\
  exists m0, match buf with Vptr b ofs =>
    store_byte_list m0 b (Ptrofs.unsigned ofs) (map Vint msg) = Some m
    | _ => False end.

Definition putchars_post (m0 m : mem) r (sh : share) (buf : val) (msg : list int) (k : IO_itree) (z : IO_itree) :=
  m0 = m /\ r = Int.repr (Zlength msg) /\ z = k.

Program Definition io_dry_spec : external_specification mem external_function IO_itree.
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type IO_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|exact False]];
      match goal with T := (_ * ?A)%type |- _ => exact (mem * A)%type end.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & (((sh, buf), len), k)).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ getchars_pre X3 sh buf len k X2).
    + destruct X as (m0 & _ & (((sh, buf), msg), k)).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ putchars_pre X3 sh buf msg k X2).
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & (((sh, buf), len), k)).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (getchars_post m0 X3 i sh buf len k X2).
    + destruct X as (m0 & _ & (((sh, buf), msg), k)).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (putchars_post m0 X3 i sh buf msg k X2).
  - intros; exact False.
Defined.

Definition dessicate : forall ef (jm : juicy_mem), ext_spec_type IO_ext_spec ef -> ext_spec_type io_dry_spec ef.
Proof.
  simpl; intros.
  destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|assumption]].
  - destruct X as [_ X]; exact (m_dry jm, X).
  - destruct X as [_ X]; exact (m_dry jm, X).
Defined.

(* up *)
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

(* up *)
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

(* up *)
Lemma ext_ref_join : forall {Z} (z : Z), join (ext_ghost z) (ext_ref z) (ext_both z).
Proof.
  intros; repeat constructor.
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

Theorem juicy_dry_specs : juicy_dry_ext_spec _ IO_ext_spec io_dry_spec dessicate.
Proof.
  split; [|split]; try reflexivity; simpl.
  - unfold funspec2pre, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct t as (? & ? & (((sh, buf), len), k)); simpl in *.
      destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold getchars_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & J1 & (? & ? & Htrace) & Hbuf).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      symmetry.
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
    + unfold funspec2pre; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct t as (? & ? & c & k); simpl in *.
      destruct H2 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold putchar_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      symmetry.
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & k); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (Hmem & ? & ?); subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost (k i), NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      split; [|split3].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists i.
        split3; simpl.
        -- split; auto.
        -- split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate.
        -- unfold SEPx; simpl.
             rewrite seplog.sepcon_emp.
             unfold ITREE; exists (k i); split; [apply Reflexive_eq_utt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H3; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join.
    + unfold funspec2pre, funspec2post, dessicate; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct H1 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & c & k); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H5 as (Hmem & ? & ?); subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H3.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost k, NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      split; [|split3].
      * eapply age_rejoin; eauto.
        intro; rewrite H3; auto.
      * split3; simpl.
        -- split; auto.
        -- split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate.
        -- unfold SEPx; simpl.
             rewrite seplog.sepcon_emp.
             unfold ITREE; exists k; split; [apply Reflexive_eq_utt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H4; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join.
Qed.

Instance mem_evolve_refl : Reflexive mem_evolve.
Proof.
  repeat intro.
  destruct (access_at x loc Cur); auto.
  destruct p; auto.
Qed.

Lemma dry_spec_mem : ext_spec_mem_evolve _ io_dry_spec.
Proof.
  intros ??????????? Hpre Hpost.
  simpl in Hpre, Hpost.
  simpl in *.
  if_tac in Hpre.
  - destruct w as (m0 & _ & k).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    reflexivity.
  - if_tac in Hpre; [|contradiction].
    destruct w as (m0 & _ & c & k).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    reflexivity.
Qed.
