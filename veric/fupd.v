Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.ghosts.
Require Import VST.veric.own.
Require Import VST.veric.invariants.
Import Ensembles.

Definition timeless' (P : pred rmap) := forall (a a' : rmap),
  predicates_hered.app_pred P a' -> age a a' ->
  predicates_hered.app_pred P a.

Lemma list_set_replace : forall {A} n l (a : A), (n < length l)%nat ->
  own.list_set l n a = replace_nth n l (Some a).
Proof.
  induction n; destruct l; unfold own.list_set; auto; simpl; try lia; intros.
  setoid_rewrite IHn; auto; lia.
Qed.

Lemma own_timeless : forall {P : Ghost} g (a : G), timeless' (own(RA := P) g a NoneP).
Proof.
  intros ????? (v & ? & Hg) ?.
  exists v; simpl in *.
  split.
  + intros; eapply age1_resource_at_identity; eauto.
  + erewrite age1_ghost_of in Hg by eauto.
    erewrite own.ghost_fmap_singleton in *; simpl in *.
    destruct Hg as [? Hg]; apply singleton_join_inv_gen in Hg as (J & ? & Hnth & ?).
    setoid_rewrite (map_nth _ _ None) in Hnth; setoid_rewrite (map_nth _ _ None) in J.
    destruct (nth g (ghost_of a0) None) as [(?, ?)|] eqn: Hga; [|inv J].
    rewrite <- (list_set_same _ _ _ Hga).
    assert (g < length (ghost_of a0))%nat.
    { destruct (lt_dec g (length (ghost_of a0))); auto.
      rewrite -> nth_overflow in Hga by lia; discriminate. }
    inv J.
    * erewrite list_set_replace, <- replace_nth_replace_nth, <- list_set_replace; rewrite ?replace_nth_length; auto.
      eexists; apply singleton_join_gen; rewrite -> nth_replace_nth by auto.
      destruct p; inv H7.
      replace _f with (fun _ : list Type => tt).
      apply lower_None2.
      { extensionality i; destruct (_f i); auto. }
    * destruct a2, p, H6 as (? & ? & ?); simpl in *; subst.
      inv H6.
      erewrite list_set_replace, <- replace_nth_replace_nth, <- list_set_replace; rewrite ?replace_nth_length; auto.
      eexists; apply singleton_join_gen; rewrite -> nth_replace_nth by auto.
      constructor.
      instantiate (1 := (_, _)).
      split; simpl; [|split; auto]; eauto.
      f_equal.
      extensionality i; destruct (_f i); auto.
Qed.

Lemma address_mapsto_timeless : forall m v sh p, timeless' (res_predicates.address_mapsto m v sh p).
Proof.
  repeat intro.
  simpl in *.
  destruct H as (b & [? HYES]); exists b; split; auto.
  intro b'; specialize (HYES b').
  if_tac.
  - destruct HYES as (rsh & Ha'); exists rsh.
    erewrite age_resource_at in Ha' by eauto.
    destruct (a @ b'); try discriminate; inv Ha'.
    destruct p0; inv H5; simpl.
    f_equal.
    apply proof_irr.
  - rewrite age1_resource_at_identity; eauto.
Qed.

Lemma timeless_FF : timeless' FF.
Proof.
  repeat intro.
  inv H.
Qed.

Lemma nonlock_permission_bytes_timeless : forall sh l z,
  timeless' (res_predicates.nonlock_permission_bytes sh l z).
Proof.
  repeat intro.
  simpl in *.
  specialize (H b).
  if_tac.
  - erewrite age1_resource_at in H by (erewrite ?resource_at_approx; eauto).
    destruct (a @ b); auto.
  - rewrite age1_resource_at_identity; eauto.
Qed.

Lemma emp_timeless : timeless' emp.
Proof.
  intros ????.
  setoid_rewrite res_predicates.emp_no in H.
  setoid_rewrite res_predicates.emp_no.
  intros l.
  eapply age1_resource_at_identity, H; auto.
Qed.

Lemma sepcon_timeless : forall P Q, timeless' P -> timeless' Q ->
  timeless' (P * Q)%pred.
Proof.
  intros ?????? (? & ? & J & ? & ?) ?.
  eapply unage_join2 in J as (? & ? & ? & ? & ?); eauto.
  do 3 eexists; eauto.
Qed.

Lemma exp_timeless : forall {A} (P : A -> pred rmap), (forall x, timeless' (P x)) ->
  timeless' (exp P).
Proof.
  intros ????? [? HP] Hage.
  eapply H in Hage; eauto.
  exists x; auto.
Qed.

Lemma andp_timeless : forall P Q, timeless' P -> timeless' Q ->
  timeless' (P && Q)%pred.
Proof.
  intros ?????? [] ?; split; eauto.
Qed.

Section FancyUpdates.

Context {inv_names : invG}.

Lemma join_preds : forall a b c d e, join(Join := Join_lower (Join_prod _ ghost_elem_join _ preds_join)) (Some (a, b)) c (Some (d, e)) ->
  b = e.
Proof.
  intros.
  inv H; auto.
  destruct H3 as [_ H]; simpl in H.
  inv H; auto.
Qed.

Definition fupd E1 E2 P :=
  ((wsat * ghost_set g_en E1) -* |==> |>FF || (wsat * ghost_set g_en E2 * P))%pred.

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 99, E1 at level 50, E2 at level 50, P at level 200): pred.
Notation "|={ E }=> P" := (fupd E E P) (at level 99, E at level 50, P at level 200): pred.

Lemma fupd_mono : forall E1 E2 P Q, (P |-- Q) -> (|={E1, E2}=> P) |-- (|={E1, E2}=> Q).
Proof.
  unfold fupd; intros.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [rewrite sepcon_comm; apply modus_wand|].
  apply bupd_mono, orp_derives, sepcon_derives; auto.
Qed.

Lemma bupd_fupd : forall E P, bupd P |-- |={E}=> P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_mono; [apply bupd_frame_r|].
  apply orp_right2.
  rewrite sepcon_comm; auto.
Qed.

Lemma fupd_frame_r : forall E1 E2 P Q, (|={E1,E2}=> P) * Q |-- |={E1,E2}=> (P * Q).
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint, sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_wand|].
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  rewrite distrib_orp_sepcon; apply orp_derives.
  - eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
    rewrite <- later_sepcon, FF_sepcon; auto.
  - rewrite sepcon_assoc; auto.
Qed.

Lemma fupd_or : forall E1 E2 P Q, (|={E1,E2}=> P) |-- |={E1,E2}=> P || Q.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint, sepcon_comm; eapply derives_trans; [apply modus_wand|].
  apply bupd_mono, orp_derives, sepcon_derives; auto.
  apply orp_right1; auto.
Qed.

Lemma fupd_trans : forall E1 E2 E3 P, (|={E1,E2}=> |={E2,E3}=> P) |-- |={E1,E3}=> P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint, sepcon_comm; eapply derives_trans; [apply modus_wand|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  apply orp_left.
  - eapply derives_trans, bupd_intro; apply orp_right1; auto.
  - apply modus_wand.
Qed.

Lemma fupd_frame_l : forall E1 E2 P Q, P * (|={E1,E2}=> Q) |-- |={E1,E2}=> (P * Q).
Proof.
  intros; erewrite sepcon_comm, (sepcon_comm P Q); apply fupd_frame_r.
Qed.

(*(* This is a generally useful pattern. *)
Lemma bupd_mono' : forall P Q (a : rmap) (Himp : (P >=> Q)%pred (level a)),
  app_pred (bupd P) a -> app_pred (bupd Q) a.
Proof.
  intros.
  assert (app_pred ((|==> P * approx (S (level a)) emp))%pred a) as HP'.
  { apply (bupd_frame_r _ _ a).
    do 3 eexists; [apply join_comm, core_unit | split; auto].
    split; [|apply core_identity].
    rewrite level_core; auto. }
  eapply bupd_mono in HP'; eauto.
  change (predicates_hered.derives (P * approx (S (level a)) emp) Q).
  intros a0 (? & ? & J & HP & [? Hemp]).
  destruct (join_level _ _ _ J).
  apply join_comm, Hemp in J; subst.
  eapply Himp in HP; try apply necR_refl; auto; lia.
Qed.

Lemma fupd_mono' : forall E1 E2 P Q (a : rmap) (Himp : (P >=> Q)%pred (level a)),
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
  eapply Himp in HP; try apply necR_refl; auto; lia.
Qed.*)

Lemma fupd_bupd : forall E1 E2 P Q, (P |-- (|==> (|={E1,E2}=> Q))) -> P |-- |={E1,E2}=> Q.
Proof.
  intros; eapply derives_trans, fupd_trans; eapply derives_trans, bupd_fupd; auto.
Qed.

Lemma fupd_bupd_elim : forall E1 E2 P Q, (P |-- (|={E1,E2}=> Q)) -> (|==> P) |-- |={E1,E2}=> Q.
Proof.
  intros; apply fupd_bupd, bupd_mono; auto.
Qed.

Lemma fupd_intro : forall E P, P |-- |={E}=> P.
Proof.
  intros; eapply derives_trans, bupd_fupd; apply bupd_intro.
Qed.

(*Corollary fview_shift_nonexpansive : forall E1 E2 P Q n,
  approx n (P -* |={E1,E2}=> Q)%logic = approx n (approx n P  -* |={E1,E2}=> approx n Q)%logic.
Proof.
  intros.
  rewrite wand_nonexpansive; setoid_rewrite wand_nonexpansive at 3.
  rewrite approx_idem; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.*)

Lemma fupd_except0_elim : forall E1 E2 P Q, (P |-- (|={E1,E2}=> Q)) -> (|> FF || P) |-- |={E1,E2}=> Q.
Proof.
  unfold fupd; intros.
  apply orp_left; auto.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_intro.
  apply orp_right1.
  eapply derives_trans, later_derives; [rewrite later_sepcon; apply sepcon_derives, now_later; auto|].
  rewrite FF_sepcon; auto.
Qed.

Lemma fupd_mask_union : forall E1 E2, Disjoint E1 E2 ->
    emp |-- fupd (Union E1 E2) E2 (fupd E2 (Union E1 E2) emp).
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- (prop_true_andp _ (ghost_set _ _) H) at 1.
  rewrite <- ghost_set_join.
  eapply derives_trans, bupd_intro.
  apply orp_right2.
  rewrite emp_sepcon, (sepcon_comm _ (ghost_set _ _)), <- sepcon_assoc; apply sepcon_derives; auto.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans, bupd_intro.
  apply orp_right2.
  rewrite sepcon_comm, sepcon_emp.
  rewrite sepcon_assoc, (sepcon_comm (ghost_set _ _)), ghost_set_join, prop_true_andp; auto.
Qed.

Lemma except_0_fupd : forall E1 E2 P, ((|> FF) || fupd E1 E2 P) |-- fupd E1 E2 P.
Proof.
  intros.
  apply fupd_except0_elim, derives_refl.
Qed.

Lemma timeless'_except_0 : forall P, timeless' P -> |> P |-- |> FF || P.
Proof.
  intros; intros ? HP.
  destruct (level a) eqn: Ha.
  - left; intros ? Hl%laterR_level.
    rewrite Ha in Hl; apply Nat.nlt_0_r in Hl; contradiction Hl.
  - right.
    destruct (levelS_age a n) as [b [Hb]]; auto.
    eapply H; eauto.
    apply HP; constructor; auto.
Qed.

Lemma fupd_timeless : forall E P, timeless' P -> |> P |-- |={E}=> P.
Proof.
  intros.
  eapply derives_trans, except_0_fupd.
  eapply derives_trans; [apply timeless'_except_0; auto|].
  apply orp_derives, fupd_intro; auto.
Qed.

Lemma fupd_mask_frame_r' : forall E1 E2 Ef P, Disjoint E1 Ef ->
  fupd E1 E2 (!! (Disjoint E2 Ef) --> P) |-- fupd (Union E1 Ef) (Union E2 Ef) P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- (prop_true_andp _ (ghost_set _ (Union _ _)) H).
  rewrite <- ghost_set_join.
  rewrite <- 2sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl|].
  { rewrite sepcon_assoc, sepcon_comm; apply modus_wand. }
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  rewrite distrib_orp_sepcon; apply orp_derives.
  { eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
    rewrite <- later_sepcon; apply later_derives.
    rewrite FF_sepcon; auto. }
  rewrite (sepcon_assoc _ _ (_ --> _)%pred), (sepcon_comm _ (_ --> _)%pred).
  rewrite <- sepcon_assoc, sepcon_assoc, ghost_set_join.
  rewrite sepcon_andp_prop; apply prop_andp_left; intros.
  rewrite !sepcon_assoc; apply sepcon_derives; auto.
  rewrite sepcon_comm; apply sepcon_derives; auto.
  rewrite normalize.true_eq by auto.
  intros ??; apply imp_lem0; auto.
Qed.

End FancyUpdates.

Section Invariants.

Context {inv_names : invG}.

(*Lemma fupd_timeless' : forall E1 E2 P Q, timeless' P -> ((P |-- (|={E1,E2}=> Q)) ->
  |> P |-- |={E1,E2}=> Q)%pred.
Proof.
  intros.
  eapply derives_trans; [apply fupd_timeless; auto|].
  eapply derives_trans, fupd_trans.
  apply fupd_mono; eauto.
Qed.

Lemma wsat_fupd_elim' : forall E P, (wsat * ghost_set g_en E * (|={E}=> P) |-- (|==> sbi_except_0 (wsat * ghost_set g_en E * P)))%I.
Proof.
  intros; unfold updates.fupd, bi_fupd_fupd; simpl; unfold fupd.
  apply modus_ponens_wand.
Qed.

Corollary wsat_fupd_elim : forall P, (wsat * (|={empty}=> P) |-- (|==> sbi_except_0 (wsat * P)))%I.
Proof.
  intros; rewrite wsat_empty_eq; apply wsat_fupd_elim'.
Qed.

Lemma bupd_except_0 : forall P, ((|==> sbi_except_0 P) |-- sbi_except_0 (|==> P))%I.
Proof.
  intros; change (predicates_hered.derives (own.bupd (sbi_except_0 P)) (sbi_except_0 (own.bupd P : mpred))).
  intros ??; simpl in H.
  destruct (level a) eqn: Hl.
  + left.
    change ((|> FF)%pred a).
    intros ??%laterR_level.
    rewrite Hl in H1; apply Nat.nlt_0_r in H1; contradiction H1.
  + right.
    rewrite <- Hl in *.
    intros ? J; specialize (H _ J) as (? & ? & a' & ? & ? & ? & HP); subst.
    do 2 eexists; eauto; do 2 eexists; eauto; repeat split; auto.
    destruct HP as [Hfalse|]; auto.
    destruct (levelS_age a' n) as (a'' & Hage & ?); [omega|].
    exfalso; apply (Hfalse a'').
    constructor; auto.
Qed.*)

Lemma fupd_andp_corable : forall E1 E2 P Q, corable P -> P && fupd E1 E2 Q |-- fupd E1 E2 (P && Q).
Proof.
  unfold fupd; intros.
  rewrite <- wand_sepcon_adjoint.
  rewrite corable_andp_sepcon1 by auto.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_wand]|].
  rewrite <- bupd_andp_corable by auto; apply bupd_mono.
  rewrite andp_comm, distrib_orp_andp; apply orp_derives.
  - apply andp_left1; auto.
  - rewrite corable_sepcon_andp1, andp_comm; auto.
Qed.

Lemma fupd_andp_prop : forall E1 E2 P Q, !! P && fupd E1 E2 Q |-- fupd E1 E2 (!!P && Q).
Proof.
  intros; apply fupd_andp_corable, corable_prop.
Qed.

Lemma unfash_sepcon: forall P (Q : pred rmap), !P * Q |-- !P.
Proof.
  intros ??? (? & ? & J & ? & ?); simpl in *.
  apply join_level in J as [<- _]; auto.
Qed.

Lemma bupd_unfash: forall P, bupd (! P) |-- ! P.
Proof.
  repeat intro; simpl in *.
  destruct (H (core (ghost_of a))) as (? & ? & ? & <- & ? & ? & ?); auto.
  rewrite <- ghost_of_approx at 1; eexists; apply ghost_fmap_join, join_comm, core_unit.
Qed.

Lemma bupd_andp_unfash: forall P Q, (bupd (!P && Q) = !P && bupd Q)%pred.
Proof.
  intros; apply pred_ext.
  - apply andp_right.
    + eapply derives_trans; [apply bupd_mono, andp_left1, derives_refl|].
      apply bupd_unfash.
    + apply bupd_mono, andp_left2, derives_refl.
  - intros ? [? HQ] ? J.
    destruct (HQ _ J) as (? & ? & a' & Hl & ? & ? & ?); subst.
    eexists; split; eauto.
    exists a'; repeat (split; auto).
    simpl in *.
    rewrite Hl; auto.
Qed.

Lemma fupd_andp_unfash: forall E1 E2 P Q, !P && fupd E1 E2 Q |-- fupd E1 E2 (!P && Q).
Proof.
  unfold fupd; intros.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [apply andp_right|].
  { eapply derives_trans, unfash_sepcon.
    apply sepcon_derives, derives_refl; apply andp_left1; auto. }
  { apply sepcon_derives, derives_refl; apply andp_left2, derives_refl. }
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_wand]|].
  rewrite <- bupd_andp_unfash.
  apply bupd_mono.
  rewrite andp_comm, distrib_orp_andp; apply orp_derives.
  - apply andp_left1; auto.
  - rewrite andp_comm, unfash_sepcon_distrib; apply sepcon_derives; auto.
    apply andp_left2; auto.
Qed.

Lemma subp_fupd : forall (G : pred nat) E (P P' : pred rmap),
  (G |-- P >=> P' -> G |-- (fupd E E P) >=> (fupd E E P'))%pred.
Proof.
  intros; unfold fupd.
  apply sub_wand; [apply subp_refl|].
  apply subp_bupd, subp_orp; [apply subp_refl|].
  apply subp_sepcon; auto; apply subp_refl.
Qed.


(*Lemma fupd_prop' : forall E1 E2 E2' P Q, subseteq E1 E2 ->
  (Q |-- (|={E1,E2'}=> !!P) ->
  (|={E1, E2}=> Q) |-- |={E1}=> !!P && (|={E1, E2}=> Q))%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  unfold fupd; intros ?????? HQ.
  iIntros "H Hpre".
  iMod ("H" with "Hpre") as ">(Hpre & Q)".
  erewrite ghost_set_subset with (s' := E1) by auto.
  iDestruct "Hpre" as "(wsat & en1 & en2)".
  iCombine ("wsat en1 Q") as "Q".
  erewrite (add_andp (_ ∗ _ ∗ Q)%I (sbi_except_0 (!! P))) at 1.
  rewrite sepcon_andp_prop bi.except_0_and.
  iModIntro; iSplit.
  { iDestruct "Q" as "[? ?]"; auto. }
  iDestruct "Q" as "[(? & ? & ?) _]"; iFrame; auto.
  { iIntros "(? & ? & Q)".
    setoid_rewrite <- (own.bupd_prop P).
    iApply bupd_except_0.
    iMod (HQ with "Q [$]") as ">(? & ?)"; auto. }
Qed.

Lemma fupd_prop : forall E1 E2 P Q, subseteq E1 E2 ->
  Q |-- !!P ->
  ((|={E1, E2}=> Q) |-- |={E1}=> !!P && (|={E1, E2}=> Q))%I.
Proof.
  intros; eapply fupd_prop'; auto.
  eapply derives_trans; eauto.
  apply fupd_intro.
Qed.

Lemma inv_alloc : forall E P, |> P |-- (|={E}=> EX i : _, invariant i P)%I.
Proof.
  intros; unfold fupd; iIntros "P (wsat & ?)".
  iMod (wsat_alloc with "[$]") as "(? & ?)"; iFrame; auto.
Qed.

Lemma make_inv : forall E P Q, P |-- Q -> (P |-- |={E}=> EX i : _, invariant i Q)%I.
Proof.
  intros.
  eapply derives_trans, inv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

Lemma make_inv' : forall P Q, P |-- Q -> (wsat * P |-- |==> EX i : _, |> (wsat * (invariant i Q)))%I.
Proof.
  intros.
  iIntros "[wsat P]".
  iPoseProof (make_inv empty _ _ H with "P") as "inv".
  iMod (wsat_fupd_elim with "[$wsat $inv]") as "[wsat inv]".
  iDestruct "inv" as (i) "inv"; iExists i.
  unfold sbi_except_0.
  iIntros "!> !>".
  iDestruct "wsat" as "[? | $]"; auto.
  iDestruct "inv" as "[? | ?]"; auto.
Qed.*)

Lemma inv_close_aux : forall E (i : iname) P,
  (ghost_list(P := token_PCM) g_dis (list_singleton i (Some tt)) * invariant i P * |> P *
  (wsat * ghost_set g_en (Subtract E i)))
  |-- |==> |> FF || (wsat * (ghost_set g_en (Singleton i) * ghost_set g_en (Subtract E i))).
Proof.
  intros.
  rewrite (sepcon_comm wsat), <- !sepcon_assoc, sepcon_comm.
  rewrite (sepcon_assoc (ghost_list _ _)), (sepcon_comm (ghost_list _ _)).
  rewrite <- !sepcon_assoc; eapply derives_trans; [apply sepcon_derives, derives_refl; apply wsat_close|].
  eapply derives_trans, bupd_mono; [apply bupd_frame_r|].
  apply orp_right2; auto.
Qed.

Lemma inv_open : forall E i P, In E i ->
  invariant i P |-- fupd E (Subtract E i) (|> P * (|>P -* fupd (Subtract E i) E emp)).
Proof.
  intros; unfold fupd.
  rewrite -> invariant_dup, <- wand_sepcon_adjoint.
  erewrite ghost_set_remove by eauto.
  rewrite <- !sepcon_assoc, !sepcon_assoc.
  rewrite <- (sepcon_assoc wsat), <- (sepcon_assoc _ (_ * _)%pred), sepcon_comm, sepcon_assoc.
  rewrite <- (sepcon_assoc _ wsat), (sepcon_comm _ wsat).
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply wsat_open|].
  eapply derives_trans, bupd_mono; [apply bupd_frame_r|].
  apply orp_right2.
  rewrite !sepcon_assoc; apply sepcon_derives; auto.
  rewrite (sepcon_comm _ (_ * (_ -* _))%pred), sepcon_assoc; apply sepcon_derives; auto.
  rewrite (sepcon_comm _ (invariant _ _)), <- sepcon_assoc; apply sepcon_derives; auto.
  rewrite <- !wand_sepcon_adjoint, sepcon_emp.
  apply inv_close_aux.
Qed.

End Invariants.

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 99, E1 at level 50, E2 at level 50, P at level 200): pred.
Notation "|={ E }=> P" := (fupd E E P) (at level 99, E at level 50, P at level 200): pred.
