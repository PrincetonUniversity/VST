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

Lemma own_timeless : forall {P : Ghost} g (a : G), timeless' (own(RA := P) g a NoneP).
Proof.
  intros ????? (v & ? & Hg) ?.
  exists v; simpl in *.
  split.
  + intros; eapply age1_resource_at_identity; eauto.
  + erewrite age1_ghost_of in Hg by eauto.
    erewrite own.ghost_fmap_singleton in *.
    apply own.ghost_fmap_singleton_inv in Hg as ([] & -> & Heq).
    inv Heq.
    destruct p; inv H3.
    simpl; repeat f_equal.
    extensionality l.
    destruct (_f l); auto.
Qed.

Lemma address_mapsto_timeless : forall m v sh p, timeless' (res_predicates.address_mapsto m v sh p).
Proof.
  repeat intro.
  simpl in *.
  destruct H as (b & [? HYES] & ?); exists b; split; [split|]; auto.
  intro b'; specialize (HYES b').
  if_tac.
  - destruct HYES as (rsh & Ha'); exists rsh.
    erewrite age_resource_at in Ha' by eauto.
    destruct (a @ b'); try discriminate; inv Ha'.
    destruct p0; inv H6; simpl.
    f_equal.
    apply proof_irr.
  - rewrite age1_resource_at_identity; eauto.
  - rewrite age1_ghost_of_identity; eauto.
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
  destruct H; split.
  intro b'; specialize (H b').
  if_tac.
  - erewrite age1_resource_at in H by (erewrite ?resource_at_approx; eauto).
    destruct (a @ b'); auto.
  - rewrite age1_resource_at_identity; eauto.
  - rewrite age1_ghost_of_identity; eauto.
Qed.

Lemma emp_timeless : timeless' emp.
Proof.
  intros ????.
  apply all_resource_at_identity.
  - intro.
    eapply age1_resource_at_identity; eauto.
    eapply resource_at_identity; eauto.
  - eapply age1_ghost_of_identity; eauto.
    eapply ghost_of_identity; eauto.
Qed.

Section FancyUpdates.

Context {inv_names : invG}.

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

(*Lemma fupd_intro_mask : forall E1 E2 P,
  subseteq E2 E1 -> P |-- |={E1,E2}=> |={E2,E1}=> P.
Proof.
  intros; unfold fupd; iIntros "P Hpre".
  erewrite ghost_set_subset with (s' := E2) by auto.
  iDestruct "Hpre" as "(? & ? & en)".
  iIntros "!> !>"; iSplitR "P en"; iFrame; auto.
Qed.*)

Lemma fupd_trans : forall E1 E2 E3 P, (|={E1,E2}=> |={E2,E3}=> P) |-- |={E1,E3}=> P.
Proof.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint, sepcon_comm; eapply derives_trans; [apply modus_wand|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  apply orp_left.
  - eapply derives_trans, bupd_intro; apply orp_right1; auto.
  - apply modus_wand.
Qed.

(*Lemma fupd_timeless : forall E P, Timeless P -> |> P |-- |={E}=> P.
Proof.
  intros; unfold fupd; iIntros ">P Hpre"; iFrame; auto.
Qed.*)

Lemma fupd_frame_l : forall E1 E2 P Q, P * (|={E1,E2}=> Q) |-- |={E1,E2}=> (P * Q).
Proof.
  intros; erewrite sepcon_comm, (sepcon_comm P Q); apply fupd_frame_r.
Qed.

(* This is a generally useful pattern. *)
Lemma bupd_mono' : forall P Q (a : rmap) (Himp : (P >=> Q)%pred (level a)),
  app_pred (bupd P) a -> app_pred (bupd Q) a.
Proof.
  intros.
  assert (app_pred ((|==> P * approx (S (level a)) emp)) a) as HP'.
  { apply (bupd_frame_r _ _ a).
    do 3 eexists; [apply join_comm, core_unit | split; auto].
    split; [|apply core_identity].
    rewrite level_core; auto. }
  eapply bupd_mono in HP'; eauto.
  change (predicates_hered.derives (P * approx (S (level a)) emp) Q).
  intros a0 (? & ? & J & HP & [? Hemp]).
  destruct (join_level _ _ _ J).
  apply join_comm, Hemp in J; subst.
  eapply Himp in HP; try apply necR_refl; auto; omega.
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
  eapply Himp in HP; try apply necR_refl; auto; omega.
Qed.

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

(*Lemma fupd_nonexpansive: forall E1 E2 P n, approx n (|={E1,E2}=> P) = approx n (|={E1,E2}=> approx n P).
Proof.
  intros; unfold fupd.
  rewrite wand_nonexpansive; setoid_rewrite wand_nonexpansive at 2.
  f_equal; f_equal.
  rewrite !approx_bupd; f_equal.
  unfold sbi_except_0.
  setoid_rewrite approx_orp; f_equal.
  erewrite !approx_sepcon, approx_idem; reflexivity.
Qed.

Corollary fview_shift_nonexpansive : forall E1 E2 P Q n,
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

Lemma fupd_andp_prop : forall E1 E2 P Q, !! P && fupd E1 E2 Q |-- fupd E1 E2 (!!P && Q).
Proof.
  unfold fupd; intros.
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_andp_prop1.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_wand]|].
  rewrite <- bupd_andp_prop; apply bupd_mono.
  rewrite andp_comm, distrib_orp_andp; apply orp_derives.
  - apply andp_left1; auto.
  - rewrite sepcon_andp_prop, andp_comm; auto.
Qed.

Lemma fupd_andp_unfash: forall E1 E2 P Q, !P && fupd E1 E2 Q |-- fupd E1 E2 (!P && Q).
Proof.
  unfold fupd; intros.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [apply andp_right|].
  { eapply derives_trans, seplog.unfash_sepcon.
    apply sepcon_derives, derives_refl; apply andp_left1; auto. }
  { apply sepcon_derives, derives_refl; apply andp_left2, derives_refl. }
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_wand]|].
  rewrite <- seplog.bupd_andp_unfash.
  apply bupd_mono.
  rewrite andp_comm, distrib_orp_andp; apply orp_derives.
  - apply andp_left1; auto.
  - rewrite andp_comm, unfash_sepcon_distrib; apply sepcon_derives; auto.
    apply andp_left2; auto.
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
Qed.

Lemma inv_close_aux : forall E (i : iname) P,
  (ghost_list(P := token_PCM) g_dis (list_singleton i (Some tt)) * invariant i P * |> P *
  (wsat * ghost_set g_en (difference E (base.singleton (Pos.of_nat (S i)))))
  |-- |==> sbi_except_0 (wsat * (ghost_set g_en (base.singleton (Pos.of_nat (S i))) * ghost_set g_en (difference E (base.singleton (Pos.of_nat (S i)))))))%I.
Proof.
  intros.
  sep_apply (wsat_close i P).
  eapply derives_trans; [apply updates.bupd_frame_r | apply updates.bupd_mono].
  rewrite <- sepcon_assoc; apply bi.except_0_intro.
Qed.

Definition inv i : coPset := base.singleton (Pos.of_nat (S i)).

Lemma inv_open : forall E i P, subseteq (inv i) E ->
  (invariant i P |-- |={E, difference E (inv i)}=> (|> P) * (|>P -* |={difference E (inv i), E}=> emp))%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  intros; unfold fupd.
  rewrite -> invariant_dup, <- wand_sepcon_adjoint.
  erewrite ghost_set_remove by (apply elem_of_subseteq_singleton; eauto).
  sep_apply (wsat_open i P).
  eapply derives_trans; [apply updates.bupd_frame_r | apply updates.bupd_mono].
  eapply derives_trans, bi.except_0_intro.
  unfold bi_sep; simpl; cancel.
  rewrite <- !wand_sepcon_adjoint.
  rewrite sepcon_emp.
  apply inv_close_aux.
Qed.

(* these last two are probably redundant *)
Lemma inv_close : forall E i P, subseteq (inv i) E ->
  invariant i P * |> P * ghost_list(P := exclusive_PCM _) g_dis (list_singleton i (Some tt)) |--
  (|={difference E (inv i), E}=> TT)%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  intros; unfold fupd; iIntros "((? & ?) & ?) ?".
  iMod (inv_close_aux with "[-]") as ">H"; [iFrame|].
  do 2 iModIntro.
  erewrite (ghost_set_remove _ _ E); first by iFrame; auto.
  { apply elem_of_subseteq_singleton; auto. }
Qed.

Lemma inv_access : forall E i P, subseteq (inv i) E ->
  (invariant i P |-- |={E, difference E (inv i)}=>
    |> P * (|> P -* |={difference E (inv i), E}=> TT))%I.
Proof.
  intros.
  eapply derives_trans; [apply inv_open; eauto|].
  apply fupd_mono; cancel.
  apply wand_derives; auto.
  apply fupd_mono; auto.
Qed.*)

End Invariants.

(*Lemma inv_in : forall i, elem_of (Pos.of_nat (S i)) (inv i).
Proof.
  intros; rewrite elem_of_singleton; reflexivity.
Qed.
Hint Resolve inv_in : ghost.

(* avoids some fragility in tactics *)
Definition except0 : mpred -> mpred := sbi_except_0.

Global Opaque fupd.*)

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)
