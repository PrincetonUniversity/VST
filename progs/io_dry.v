Require Import VST.progs.io_specs.
Require Import VST.progs.io.
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

Definition io_specs :=
  [(_getchar, getchar_spec); (_putchar, putchar_spec)].

Definition ext_link := ext_link_prog prog.

(* Should we really need a concrete user program in order to build enough of an external_specification for the juicy_dry proof? *)
Definition io_ext_spec
  :=
  add_funspecs_rec
    ext_link
    (ok_void_spec IO_itree).(@OK_ty)
    (ok_void_spec IO_itree).(@OK_spec)
    io_specs.

Definition getchar_pre (m : mem) (k : int -> IO_itree) (z : IO_itree) :=
  (z = (r <- read;; k r))%eq_utt.

Definition getchar_post (m0 m : mem) r (k : int -> IO_itree) (z : IO_itree) :=
  m0 = m /\ - two_p 7 <= Int.signed r <= two_p 7 - 1 /\ z = k r.

Definition putchar_pre (m : mem) c (k : IO_itree) (z : IO_itree) :=
  (z = (write c;; k))%eq_utt.

Definition putchar_post (m0 m : mem) r (c : int) (k : IO_itree) (z : IO_itree) :=
  m0 = m /\ r = c /\ z = k.

Program Definition io_dry_spec : external_specification mem external_function IO_itree.
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type io_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|exact False]].
    + exact (mem * {_ : list Type & int -> IO_itree})%type.
    + exact (mem * {_ : list Type & int * IO_itree})%type.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & k).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ getchar_pre X3 k X2).
    + destruct X as (m0 & _ & c & k).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ putchar_pre X3 c k X2).
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & k).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (getchar_post m0 X3 i k X2).
    + destruct X as (m0 & _ & c & k).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (putchar_post m0 X3 i c k X2).
  - intros; exact False.
Defined.

Definition dessicate : forall ef (jm : juicy_mem), ext_spec_type io_ext_spec ef -> ext_spec_type io_dry_spec ef.
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

Theorem juicy_dry_specs : juicy_dry_ext_spec _ io_ext_spec io_dry_spec dessicate.
Proof.
  split; [|split]; try reflexivity; simpl.
  - unfold funspec2pre, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct t as (? & ? & k); simpl in *.
      destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold getchar_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
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
