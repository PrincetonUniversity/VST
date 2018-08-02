Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import VST.progs.invariants.
Import Ensembles.

(* Where should this sit? *)

Section Timeless.

Definition except0 P := P || |>FF.

Definition timeless P := |>P |-- except0 P.

Definition timeless' (P : mpred) := forall (a a' : rmap),
  predicates_hered.app_pred P a' -> age a a' ->
  predicates_hered.app_pred P a.

Lemma timeless'_timeless : forall P, timeless' P -> timeless P.
Proof.
  unfold timeless; intros.
  change (_ |-- _) with (predicates_hered.derives (|>P) (P || |>FF)); intros ? HP.
  destruct (level a) eqn: Ha.
  - right; intros ? ?%laterR_level; omega.
  - left.
    destruct (levelS_age a n) as [b [Hb]]; auto.
    specialize (HP _ (semax_lemmas.age_laterR Hb)).
    eapply H; eauto.
Qed.

Lemma except0_mono : forall P Q, P |-- Q -> except0 P |-- except0 Q.
Proof.
  intros; unfold except0.
  apply orp_left; [apply orp_right1 | apply orp_right2]; auto.
Qed.

Lemma except0_intro : forall P, P |-- except0 P.
Proof.
  intros; unfold except0.
  apply orp_right1; auto.
Qed.

Lemma except0_trans : forall P, except0 (except0 P) |-- except0 P.
Proof.
  intros; unfold except0.
  apply orp_left; [|apply orp_right2]; auto.
Qed.

Lemma except0_timeless : forall P Q, P |-- except0 Q -> timeless P -> |> P |-- except0 Q.
Proof.
  intros.
  eapply derives_trans; eauto.
  eapply derives_trans, except0_trans.
  apply except0_mono; auto.
Qed.

Lemma except0_frame_r : forall P Q, except0 P * Q |-- except0 (P * Q).
Proof.
  intros; unfold except0.
  rewrite distrib_orp_sepcon.
  apply orp_left; [apply orp_right1 | apply orp_right2]; auto.
  eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
  rewrite <- later_sepcon; apply later_derives.
  rewrite FF_sepcon; auto.
Qed.

Lemma except0_frame_l : forall P Q, P * except0 Q |-- except0 (P * Q).
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm _ Q); apply except0_frame_r.
Qed.

Lemma except0_bupd_elim : forall P, except0 (|==> except0 P) |-- |==> except0 P.
Proof.
  intros; unfold except0.
  apply orp_left; auto.
  eapply derives_trans, bupd_intro.
  apply orp_right2; auto.
Qed.

Lemma except0_bupd : forall P, except0 (|==> P) = |==> (except0 P).
Proof.
  intro; apply pred_ext.
  - eapply derives_trans, except0_bupd_elim.
    apply except0_mono, bupd_mono, except0_intro.
  - change (predicates_hered.derives (own.bupd (except0 P)) (except0 (own.bupd P))).
    intros ??; simpl in H.
    destruct (level a) eqn: Hl.
    + right.
      change ((|> FF)%pred a).
      intros ??%laterR_level; omega.
    + left.
      rewrite <- Hl in *.
      intros ? J; specialize (H _ J) as (? & ? & a' & ? & ? & ? & HP); subst.
      do 2 eexists; eauto; do 2 eexists; eauto; repeat split; auto.
      destruct HP as [|Hfalse]; auto.
      destruct (levelS_age a' n) as (a'' & Hage & ?); [omega|].
      exfalso; apply (Hfalse a'').
      constructor; auto.
Qed.

Lemma except0_sepcon : forall P Q, except0 (P * Q) = except0 P * except0 Q.
Proof.
  intros; unfold except0.
  rewrite distrib_orp_sepcon, !distrib_orp_sepcon2.
  apply pred_ext.
  - apply orp_left.
    + apply orp_right1, orp_right1; auto.
    + apply orp_right2, orp_right2.
      rewrite <- later_sepcon, FF_sepcon; auto.
  - apply orp_left; apply orp_left.
    + apply orp_right1; auto.
    + apply orp_right2.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply now_later|].
      rewrite <- later_sepcon; apply later_derives; rewrite sepcon_FF; auto.
    + apply orp_right2.
      eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
      rewrite <- later_sepcon; apply later_derives; rewrite FF_sepcon; auto.
    + apply orp_right2.
      rewrite <- later_sepcon, FF_sepcon; auto.
Qed.

Lemma except0_andp : forall P Q, except0 (P && Q) = except0 P && except0 Q.
Proof.
  intros; unfold except0.
  rewrite distrib_orp_andp.
  rewrite 2(andp_comm _ (_ || _)), !distrib_orp_andp.
  apply pred_ext.
  - apply orp_left.
    + apply orp_right1, orp_right1.
      rewrite andp_comm; auto.
    + apply orp_right2, orp_right2.
      rewrite <- later_andp, FF_andp; auto.
  - apply orp_left; apply orp_left.
    + apply orp_right1.
      rewrite andp_comm; auto.
    + apply orp_right2.
      rewrite andp_comm.
      eapply derives_trans; [apply andp_derives, derives_refl; apply now_later|].
      rewrite <- later_andp; apply later_derives; rewrite andp_FF; auto.
    + apply orp_right2.
      rewrite andp_comm.
      eapply derives_trans; [apply andp_derives, now_later; apply derives_refl|].
      rewrite <- later_andp; apply later_derives; rewrite FF_andp; auto.
    + apply orp_right2.
      rewrite <- later_andp, FF_andp; auto.
Qed.

Lemma except0_exp : forall {A} (x : A) P, except0 (EX x : A, P x) = EX x : A, except0 (P x).
Proof.
  intros; unfold except0; apply pred_ext.
  - apply orp_left.
    + Intro y; Exists y; apply orp_right1; auto.
    + Exists x; apply orp_right2; auto.
  - Intro y; apply orp_left; [apply orp_right1; Exists y | apply orp_right2]; auto.
Qed.

Lemma timeless_sepcon : forall P Q, timeless P -> timeless Q -> timeless (P * Q).
Proof.
  unfold timeless; intros.
  rewrite later_sepcon, except0_sepcon.
  apply sepcon_derives; auto.
Qed.

Lemma timeless_andp : forall P Q, timeless P -> timeless Q -> timeless (P && Q).
Proof.
  unfold timeless; intros.
  rewrite later_andp, except0_andp.
  apply andp_derives; auto.
Qed.

Lemma own_timeless : forall {P : Ghost} g (a : G), timeless (own g a NoneP).
Proof.
  intros; apply timeless'_timeless.
  intros ?? (v & ? & Hg) ?.
  exists v; simpl in *.
  split.
  + intros; eapply age1_resource_at_identity; eauto.
  + erewrite age1_ghost_of in Hg by eauto.
    rewrite own.ghost_fmap_singleton in *.
    apply own.ghost_fmap_singleton_inv in Hg as ([] & -> & Heq).
    inv Heq.
    destruct p; inv H3.
    simpl; repeat f_equal.
    extensionality l.
    destruct (_f l); auto.
Qed.

Lemma timeless_exp : forall {A} (x : A) P, (forall x, timeless (P x)) -> timeless (EX x : A, P x).
Proof.
  unfold timeless; intros.
  rewrite later_exp' by auto.
  Intro y.
  eapply derives_trans; eauto.
  apply except0_mono.
  Exists y; auto.
Qed.

Lemma timeless_prop : forall P, timeless (!! P).
Proof.
  intro; apply timeless'_timeless.
  intro; auto.
Qed.

Lemma address_mapsto_timeless : forall m v sh p, timeless (res_predicates.address_mapsto m v sh p).
Proof.
  intros; apply timeless'_timeless.
  repeat intro.
  simpl in *.
  destruct H as (b & [? HYES] & ?); exists b; split; [split|]; auto.
  intro b'; specialize (HYES b').
  if_tac.
  - destruct HYES as (rsh & Ha'); exists rsh.
    erewrite age_to_resource_at.age_resource_at in Ha' by eauto.
    destruct (a @ b'); try discriminate; inv Ha'.
    destruct p0; inv H6; simpl.
    f_equal.
    apply proof_irr.
  - rewrite age1_resource_at_identity; eauto.
  - rewrite age1_ghost_of_identity; eauto.
Qed.

Lemma timeless_FF : timeless FF.
Proof.
  unfold timeless, except0.
  apply orp_right2; auto.
Qed.

Lemma timeless_emp : timeless emp.
Proof.
  apply timeless'_timeless; intros ????.
  apply all_resource_at_identity.
  - intro.
    eapply age1_resource_at_identity; eauto.
    eapply resource_at_identity; eauto.
  - eapply age1_ghost_of_identity; eauto.
    eapply ghost_of_identity; eauto.
Qed.

Lemma nonlock_permission_bytes_timeless : forall sh l z,
  timeless (res_predicates.nonlock_permission_bytes sh l z).
Proof.
  intros; apply timeless'_timeless.
  repeat intro.
  simpl in *.
  destruct H; split.
  intro b'; specialize (H b').
  if_tac.
  - erewrite age1_resource_at in H by (rewrite ?resource_at_approx; eauto).
    destruct (a @ b'); auto.
  - rewrite age1_resource_at_identity; eauto.
  - rewrite age1_ghost_of_identity; eauto.
Qed.

Lemma timeless_orp : forall P Q, timeless P -> timeless Q -> timeless (P || Q).
Proof.
  unfold timeless, except0; intros.
  rewrite later_orp.
  apply orp_left; eapply derives_trans; try eassumption; apply orp_left.
  - apply orp_right1, orp_right1; auto.
  - apply orp_right2; auto.
  - apply orp_right1, orp_right2; auto.
  - apply orp_right2; auto.
Qed.

Lemma mapsto_timeless : forall sh t v p, timeless (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply timeless_FF.
  destruct (type_is_volatile); try apply timeless_FF.
  destruct p; try apply timeless_FF.
  if_tac.
  - apply timeless_orp.
    + apply timeless_andp; [apply timeless_prop | apply address_mapsto_timeless].
    + apply timeless_andp; [apply timeless_prop|].
      apply (timeless_exp Vundef); intro; apply address_mapsto_timeless.
  - apply timeless_andp; [apply timeless_prop | apply nonlock_permission_bytes_timeless].
Qed.

Lemma memory_block'_timeless : forall sh n b z,
  timeless (mapsto_memory_block.memory_block' sh n b z).
Proof.
  induction n; simpl; intros.
  - apply timeless_emp.
  - apply timeless_sepcon, IHn.
    apply mapsto_timeless.
Qed.

Lemma memory_block_timeless : forall sh n p,
  timeless (memory_block sh n p).
Proof.
  intros.
  destruct p; try apply timeless_FF.
  apply timeless_andp; [apply timeless_prop | apply memory_block'_timeless].
Qed.

Lemma struct_pred_timeless : forall {CS : compspecs} sh m f t off
  (IH : Forall (fun it : ident * type =>
        forall (v : reptype (t it)) (p : val),
        timeless (data_at_rec sh (t it) v p)) m) v p,
  timeless (struct_pred m (fun (it : ident * type) v =>
      withspacer sh (f it + sizeof (t it)) (off it)
        (at_offset (data_at_rec sh (t it) v) (f it))) v p).
Proof.
  induction m; intros.
  - apply timeless_emp.
  - destruct a; inv IH.
    destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply timeless_sepcon; auto.
      unfold spacer.
      if_tac.
      * apply timeless_emp.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite struct_pred_cons2.
      apply timeless_sepcon; auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply timeless_sepcon; auto.
      unfold spacer.
      if_tac.
      * apply timeless_emp.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma union_pred_timeless : forall {CS : compspecs} sh m t off
  (IH : Forall (fun it : ident * type =>
        forall (v : reptype (t it)) (p : val),
        timeless (data_at_rec sh (t it) v p)) m) v p,
  timeless (union_pred m (fun (it : ident * type) v =>
      withspacer sh (sizeof (t it)) (off it)
        (data_at_rec sh (t it) v)) v p).
Proof.
  induction m; intros.
  - apply timeless_emp.
  - destruct a; inv IH.
    destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply timeless_sepcon; auto.
      unfold spacer.
      if_tac.
      * apply timeless_emp.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite union_pred_cons2.
      destruct v; auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply timeless_sepcon; auto.
      unfold spacer.
      if_tac.
      * apply timeless_emp.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma data_at_rec_timeless : forall {CS : compspecs} sh t v p,
  timeless (data_at_rec sh t v p).
Proof.
  intros ???.
  type_induction.type_induction t; intros; rewrite data_at_rec_eq; try apply timeless_FF.
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - apply timeless_andp; [apply timeless_prop|].
    rewrite Z.sub_0_r.
    forget (Z.to_nat (Z.max 0 z)) as n.
    set (lo := 0) at 1.
    clearbody lo.
    revert lo; induction n; simpl; intros.
    + apply timeless_emp.
    + apply timeless_sepcon, IHn.
      unfold at_offset; apply IH.
  - apply struct_pred_timeless; auto.
  - apply union_pred_timeless; auto.
Qed.

Lemma data_at_timeless : forall {CS : compspecs} sh t v p, timeless (data_at sh t v p).
Proof.
  intros; apply timeless_andp; [apply timeless_prop | apply data_at_rec_timeless].
Qed.

End Timeless.

Section FancyUpdates.

Context {inv_names : invG}.

Definition fupd (E1 E2 : Ensemble iname) P :=
  (wsat * ghost_set g_en E1) -* |==> except0 (wsat * ghost_set g_en E2 * P).

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 62): logic.
Notation "|={ E }=> P" := (fupd E E P) (at level 62): logic.

Lemma fupd_mono : forall E1 E2 P Q, P |-- Q -> |={E1, E2}=> P |-- |={E1, E2}=> Q.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_comm; eapply derives_trans; [apply modus_ponens_wand|].
  apply bupd_mono, except0_mono; cancel.
Qed.

Lemma bupd_fupd : forall E P, |==> P |-- |={E}=> P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [apply bupd_frame_r|].
  rewrite sepcon_comm; apply bupd_mono, except0_intro.
Qed.

Lemma fupd_frame_r : forall E1 E2 P Q, (|={E1,E2}=> P) * Q |-- |={E1,E2}=> (P * Q).
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
  eapply derives_trans; [apply bupd_frame_r|].
  apply bupd_mono.
  rewrite <- sepcon_assoc.
  apply except0_frame_r.
Qed.

Lemma fupd_intro_mask : forall E1 E2 P (Hdec : forall a, In E2 a \/ ~In E2 a),
  Included E2 E1 -> P |-- |={E1,E2}=> |={E2,E1}=> P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_intro.
  eapply derives_trans, except0_intro.
  rewrite ghost_set_subset with (s' := E2) by auto.
  cancel.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_intro.
  eapply derives_trans, except0_intro; cancel.
Qed.

Lemma fupd_trans : forall E1 E2 E3 P, (|={E1,E2}=> |={E2,E3}=> P) |-- |={E1,E3}=> P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_comm.
  eapply derives_trans; [apply modus_ponens_wand|].
  eapply derives_trans; [apply bupd_mono, except0_mono, modus_ponens_wand|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  apply except0_bupd_elim.
Qed.

Lemma fupd_timeless : forall E P, timeless P -> |> P |-- |={E}=> P.
Proof.
  intros; unfold fupd.
  eapply derives_trans; [apply except0_timeless; auto; apply except0_intro|].
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [apply except0_frame_r|].
  rewrite sepcon_comm.
  apply bupd_intro.
Qed.

Lemma fupd_frame_l : forall E1 E2 P Q, P * (|={E1,E2}=> Q) |-- |={E1,E2}=> (P * Q).
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply fupd_frame_r.
Qed.

(* This is a generally useful pattern. *)
Lemma fupd_mono' : forall E1 E2 P Q (a : rmap) (Himp : (P >=> Q) (level a)),
  app_pred (fupd E1 E2 P) a -> app_pred (fupd E1 E2 Q) a.
Proof.
  intros.
  assert (app_pred ((|={E1,E2}=> P * approx (S (level a)) emp)) a) as HP'.
  { apply (fupd_frame_r _ _ _ _ a).
    do 3 eexists; [apply join_comm, core_unit | split; auto].
    split; [|apply core_identity].
    rewrite level_core; auto. }
  eapply fupd_mono in HP'; eauto.
  change (predicates_hered.derives (P * approx (S (level a)) emp) Q).
  intros a0 (? & ? & J & HP & [? Hemp]).
  destruct (join_level _ _ _ J).
  apply join_comm, Hemp in J; subst.
  eapply Himp in HP; try apply necR_refl; auto; omega.
Qed.

Lemma fupd_bupd : forall E1 E2 P Q, P |-- |==> (|={E1,E2}=> Q) -> P |-- |={E1,E2}=> Q.
Proof.
  intros; eapply derives_trans, fupd_trans; eapply derives_trans, bupd_fupd; auto.
Qed.

Lemma fupd_bupd_elim : forall E1 E2 P Q, P |-- |={E1,E2}=> Q -> |==> P |-- |={E1,E2}=> Q.
Proof.
  intros; apply fupd_bupd, bupd_mono; auto.
Qed.

Lemma fupd_intro : forall E P, P |-- |={E}=> P.
Proof.
  intros; eapply derives_trans, bupd_fupd; apply bupd_intro.
Qed.

Lemma fupd_timeless' : forall E1 E2 P Q, timeless P -> P |-- |={E1,E2}=> Q ->
  |> P |-- |={E1,E2}=> Q.
Proof.
  intros.
  eapply derives_trans; [apply fupd_timeless; auto|].
  eapply derives_trans, fupd_trans.
  apply fupd_mono; eauto.
Qed.

Lemma fupd_except0_elim : forall E1 E2 P Q, P |-- |={E1,E2}=> Q -> except0 P |-- |={E1,E2}=> Q.
Proof.
  intros.
  unfold except0.
  apply orp_left; auto.
  unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_intro.
  unfold except0.
  apply orp_right2.
  eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
  rewrite <- later_sepcon; apply later_derives.
  rewrite FF_sepcon; auto.
Qed.

Lemma wsat_fupd_elim : forall P, wsat * (|={Empty_set _,Empty_set _}=> P) |-- |==> except0 (wsat * P).
Proof.
  intros; unfold fupd.
  rewrite <- wsat_empty_eq; apply modus_ponens_wand.
Qed.

Lemma fupd_prop' : forall E1 E2 E2' P Q, Included E1 E2 -> (forall a, In E1 a \/ ~ In E1 a) ->
  Q |-- |={E1,E2'}=> !!P ->
  |={E1, E2}=> Q |-- |={E1}=> !!P && (|={E1, E2}=> Q).
Proof.
  unfold fupd; intros ??????? HQ.
  rewrite <- wand_sepcon_adjoint in *.
  rewrite sepcon_comm; eapply derives_trans; [apply modus_ponens_wand|].
  apply bupd_mono.
  eapply derives_trans, except0_trans; apply except0_mono.
  rewrite ghost_set_subset with (s' := E1) by auto.
  rewrite (add_andp (_ * _ * Q) (except0 (!! P))) at 1.
- eapply derives_trans; [apply andp_derives, derives_refl; apply except0_intro|].
  rewrite <- except0_andp; apply except0_mono.
  Intros.
  apply andp_right; [apply prop_right; auto | cancel].
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_intro; eapply derives_trans, except0_intro; cancel.
- rewrite sepcon_comm, <- !sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; rewrite sepcon_assoc; apply HQ|].
  setoid_rewrite <- (own.bupd_prop P) at 2.
  rewrite except0_bupd.
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  eapply derives_trans; [apply except0_frame_r | apply except0_mono].
  rewrite (sepcon_comm _ (!!P)), !sepcon_assoc.
  apply derives_left_sepcon_right_corable, derives_refl.
  change (!!P)%pred with (!!P); apply corable_prop.
Qed.

Lemma fupd_prop : forall E1 E2 P Q, Included E1 E2 -> (forall a, In E1 a \/ ~ In E1 a) ->
  Q |-- !!P ->
  |={E1, E2}=> Q |-- |={E1}=> !!P && (|={E1, E2}=> Q).
Proof.
  intros; eapply fupd_prop'; auto.
  eapply derives_trans; eauto.
  apply fupd_intro.
Qed.

Lemma inv_alloc : forall E P, |> P |-- |={E}=> EX i : _, invariant i P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- sepcon_assoc, (sepcon_comm _ wsat).
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply wsat_alloc|].
  eapply derives_trans; [apply bupd_frame_r|].
  apply bupd_mono.
  rewrite sepcon_assoc, (sepcon_comm _ (ghost_set _ _)), <- sepcon_assoc.
  apply except0_intro.
Qed.

Lemma make_inv : forall E P Q, P |-- Q -> P |-- |={E}=> EX i : _, invariant i Q.
Proof.
  intros.
  eapply derives_trans, inv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

Lemma inv_close_aux : forall E (i : iname) P,
  ghost_list(P := token_PCM) g_dis (list_singleton i (Some tt)) * invariant i P * |> P *
  (wsat * ghost_set g_en (Subtract E i))
  |-- |==> except0 (wsat * (ghost_set g_en (Singleton i) * ghost_set g_en (Subtract E i))).
Proof.
  intros.
  sep_apply (wsat_close i P).
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  rewrite <- sepcon_assoc; apply except0_intro.
Qed.

Lemma inv_open : forall E i P, In E i ->
  invariant i P |-- |={E, Subtract E i}=> (|> P) * (|>P -* |={Subtract E i, E}=> emp).
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  erewrite ghost_set_remove; eauto.
  rewrite invariant_dup.
  sep_apply (wsat_open i P).
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  eapply derives_trans, except0_intro.
  cancel.
  rewrite <- !wand_sepcon_adjoint.
  apply inv_close_aux.
  { intro; omega. }
Qed.

(* these last two are probably redundant *)
Lemma inv_close : forall E i P, In E i ->
  invariant i P * |> P * ghost_list(P := exclusive_PCM _) g_dis (list_singleton i (Some tt)) |--
  |={Subtract E i, E}=> TT.
Proof.
  intros; unfold fupd.
  rewrite <- !wand_sepcon_adjoint.
  rewrite (sepcon_comm _ (ghost_list _ _)), <- 2sepcon_assoc, sepcon_assoc.
  eapply derives_trans; [apply inv_close_aux|].
  erewrite (ghost_set_remove _ _ E); eauto.
  apply bupd_mono, except0_mono; cancel.
  { intro; omega. }
Qed.

Lemma inv_access : forall E i P, In E i ->
  invariant i P |-- |={E, Subtract E i}=> |> P * (|> P -* |={Subtract E i, E}=> TT).
Proof.
  intros.
  eapply derives_trans; [apply inv_open; eauto|].
  apply fupd_mono; cancel.
  apply wand_derives; auto.
  apply fupd_mono; auto.
Qed.

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)

End FancyUpdates.

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 62): logic.
Notation "|={ E }=> P" := (fupd E E P) (at level 62): logic.
