Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import VST.progs.invariants.
Require Export VST.veric.bi.
Require Import VST.msl.ghost_seplog.
Import Ensembles.

(* Where should this sit? *)

Definition timeless' (P : mpred) := forall (a a' : rmap),
  predicates_hered.app_pred P a' -> age a a' ->
  predicates_hered.app_pred P a.

Lemma timeless'_timeless : forall P, timeless' P -> Timeless P.
Proof.
  unfold Timeless; intros; simpl.
  change (_ -∗ _) with (predicates_hered.derives (|>P) (|>FF || P)); intros ? HP.
  destruct (level a) eqn: Ha.
  - left; intros ? ?%laterR_level.
    rewrite Ha in H1; apply Nat.nlt_0_r in H1; contradiction H1.
  - right.
    destruct (levelS_age a n) as [b [Hb]]; auto.
    specialize (HP _ (semax_lemmas.age_laterR Hb)).
    eapply H; eauto.
Qed.

Instance own_timeless : forall {P : Ghost} g (a : G), Timeless (own g a NoneP).
Proof.
  intros; apply timeless'_timeless.
  intros ?? (v & ? & Hg) ?.
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

Lemma address_mapsto_timeless : forall m v sh p, Timeless (res_predicates.address_mapsto m v sh p : mpred).
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

Instance timeless_FF : Timeless FF.
Proof.
  unfold Timeless; intros.
  iIntros ">?"; auto.
Qed.

Lemma nonlock_permission_bytes_timeless : forall sh l z,
  Timeless (res_predicates.nonlock_permission_bytes sh l z : mpred).
Proof.
  intros; apply timeless'_timeless.
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

Lemma mapsto_timeless : forall sh t v p, Timeless (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply timeless_FF.
  destruct (type_is_volatile); try apply timeless_FF.
  destruct p; try apply timeless_FF.
  if_tac.
  - apply (@bi.or_timeless mpredSI).
    + apply (@bi.and_timeless mpredSI); [apply (@bi.pure_timeless mpredSI) | apply address_mapsto_timeless].
    + apply (@bi.and_timeless mpredSI); [apply (@bi.pure_timeless mpredSI)|].
      apply (@bi.exist_timeless mpredSI); intro; apply address_mapsto_timeless.
  - apply (@bi.and_timeless mpredSI); [apply (@bi.pure_timeless mpredSI) | apply nonlock_permission_bytes_timeless].
Qed.

Lemma emp_timeless : Timeless seplog.emp.
Proof.
  apply timeless'_timeless; intros ????.
  apply all_resource_at_identity.
  - intro.
    eapply age1_resource_at_identity; eauto.
    eapply resource_at_identity; eauto.
  - eapply age1_ghost_of_identity; eauto.
    eapply ghost_of_identity; eauto.
Qed.

Lemma memory_block'_timeless : forall sh n b z,
  Timeless (mapsto_memory_block.memory_block' sh n b z).
Proof.
  induction n; simpl; intros.
  - apply emp_timeless.
  - apply (@bi.sep_timeless), IHn.
    apply mapsto_timeless.
Qed.

Lemma memory_block_timeless : forall sh n p,
  Timeless (memory_block sh n p).
Proof.
  intros.
  destruct p; try apply timeless_FF.
  apply (@bi.and_timeless mpredSI); [apply (@bi.pure_timeless mpredSI) | apply memory_block'_timeless].
Qed.

Lemma struct_pred_timeless : forall {CS : compspecs} sh m f t off
  (IH : Forall (fun it : _ * type =>
        forall (v : reptype (t it)) (p : val),
        Timeless (data_at_rec sh (t it) v p)) m) v p,
  Timeless (struct_pred m (fun (it : _ * type) v =>
      withspacer sh (f it + sizeof (t it)) (off it)
        (at_offset (data_at_rec sh (t it) v) (f it))) v p).
Proof.
  induction m; intros.
  - apply emp_timeless.
  - destruct a; inv IH.
    destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredSI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite struct_pred_cons2.
      apply (@bi.sep_timeless mpredSI); auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredSI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma union_pred_timeless : forall {CS : compspecs} sh m t off
  (IH : Forall (fun it : _ * type =>
        forall (v : reptype (t it)) (p : val),
        Timeless (data_at_rec sh (t it) v p)) m) v p,
  Timeless (union_pred m (fun (it : _ * type) v =>
      withspacer sh (sizeof (t it)) (off it)
        (data_at_rec sh (t it) v)) v p).
Proof.
  induction m; intros.
  - apply emp_timeless.
  - destruct a; inv IH.
    destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredSI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite union_pred_cons2.
      destruct v; auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredSI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma data_at_rec_timeless : forall {CS : compspecs} sh t v p,
  Timeless (data_at_rec sh t v p).
Proof.
  intros ???.
  type_induction.type_induction t; intros; rewrite data_at_rec_eq; try apply timeless_FF.
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - apply (@bi.and_timeless mpredSI); [apply (@bi.pure_timeless mpredSI)|].
    rewrite Z.sub_0_r.
    forget (Z.to_nat (Z.max 0 z)) as n.
    set (lo := 0) at 1.
    clearbody lo.
    revert lo; induction n; simpl; intros.
    + apply emp_timeless.
    + apply (@bi.sep_timeless mpredSI), IHn.
      unfold at_offset; apply IH.
  - apply struct_pred_timeless; auto.
  - apply union_pred_timeless; auto.
Qed.

Lemma data_at_timeless : forall {CS : compspecs} sh t v p, Timeless (data_at sh t v p).
Proof.
  intros; apply (@bi.and_timeless mpredSI); [apply (@bi.pure_timeless mpredSI) | apply data_at_rec_timeless].
Qed.

Section FancyUpdates.

Context {inv_names : invG}.

Definition fupd E1 E2 P :=
  (wsat * ghost_set g_en E1) -* (|==> sbi_except_0 (wsat * ghost_set g_en E2 * P))%I.

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 99, E1 at level 50, E2 at level 50, P at level 200): logic.
Notation "|={ E }=> P" := (fupd E E P) (at level 99, E at level 50, P at level 200): logic.

Lemma fupd_mono : forall E1 E2 P Q, P |-- Q -> (|={E1, E2}=> P) |-- (|={E1, E2}=> Q).
Proof.
  intros; unfold fupd; iIntros "H Hpre".
  iMod ("H" with "Hpre") as ">($ & P)"; do 2 iModIntro.
  iApply (H with "P").
Qed.

Lemma bupd_fupd : forall E P, (|==> P)%I |-- |={E}=> P.
Proof.
  intros; unfold fupd; iIntros ">P Hpre".
  iModIntro; iFrame; auto.
Qed.

Lemma fupd_frame_r : forall E1 E2 P Q, (|={E1,E2}=> P) * Q |-- |={E1,E2}=> (P * Q).
Proof.
  intros; unfold fupd; iIntros "[H Q] Hpre".
  iMod ("H" with "Hpre") as ">($ & $)"; auto.
Qed.

Lemma fupd_intro_mask : forall E1 E2 P,
  subseteq E2 E1 -> P |-- |={E1,E2}=> |={E2,E1}=> P.
Proof.
  intros; unfold fupd; iIntros "P Hpre".
  erewrite ghost_set_subset with (s' := E2) by auto.
  iDestruct "Hpre" as "(? & ? & en)".
  do 2 iModIntro; iSplitR "P en"; iFrame; auto.
Qed.

Lemma fupd_trans : forall E1 E2 E3 P, (|={E1,E2}=> |={E2,E3}=> P) |-- |={E1,E3}=> P.
Proof.
  intros; unfold fupd; iIntros "H Hpre".
  iMod ("H" with "Hpre") as ">(Hpre & H)".
  iMod ("H" with "Hpre") as ">H"; iFrame; auto.
Qed.

Lemma fupd_timeless : forall E P, Timeless P -> |> P |-- |={E}=> P.
Proof.
  intros; unfold fupd; iIntros ">P Hpre"; iFrame; auto.
Qed.

Lemma fupd_frame_l : forall E1 E2 P Q, P * (|={E1,E2}=> Q) |-- |={E1,E2}=> (P * Q).
Proof.
  intros; erewrite sepcon_comm, (sepcon_comm P Q); apply fupd_frame_r.
Qed.

(* This is a generally useful pattern. *)
Lemma fupd_mono' : forall E1 E2 P Q (a : rmap) (Himp : (P >=> Q) (level a)),
  app_pred (fupd E1 E2 P) a -> app_pred (fupd E1 E2 Q) a.
Proof.
  intros.
  assert (app_pred ((|={E1,E2}=> P * approx (S (level a)) seplog.emp)) a) as HP'.
  { apply (fupd_frame_r _ _ _ _ a).
    do 3 eexists; [apply join_comm, core_unit | split; auto].
    split; [|apply core_identity].
    rewrite level_core; auto. }
  eapply fupd_mono in HP'; eauto.
  change (predicates_hered.derives (P * approx (S (level a)) seplog.emp) Q).
  intros a0 (? & ? & J & HP & [? Hemp]).
  destruct (join_level _ _ _ J).
  apply join_comm, Hemp in J; subst.
  eapply Himp in HP; try apply necR_refl; auto; omega.
Qed.

Lemma fupd_bupd : forall E1 E2 P Q, P |-- (|==> (|={E1,E2}=> Q)) -> P |-- |={E1,E2}=> Q.
Proof.
  intros; eapply derives_trans, fupd_trans; eapply derives_trans, bupd_fupd; auto.
Qed.

Lemma fupd_bupd_elim : forall E1 E2 P Q, P |-- (|={E1,E2}=> Q) -> (|==> P) |-- |={E1,E2}=> Q.
Proof.
  intros; apply fupd_bupd, bupd_mono; auto.
Qed.

Lemma fupd_intro : forall E P, P |-- |={E}=> P.
Proof.
  intros; eapply derives_trans, bupd_fupd; apply updates.bupd_intro.
Qed.

Lemma fupd_nonexpansive: forall E1 E2 P n, approx n (|={E1,E2}=> P) = approx n (|={E1,E2}=> approx n P).
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
Qed.

End FancyUpdates.

Lemma mpred_fupd_mixin {inv_names : invG} : BiFUpdMixin mpredSI fupd.
Proof.
  split.
  - repeat intro; hnf in *.
    setoid_rewrite fupd_nonexpansive; congruence.
  - exact fupd_intro_mask.
  - iIntros (E1 E2 P) ">H ?".
    iApply "H"; auto.
  - exact fupd_mono.
  - exact fupd_trans.
  - intros E1 E2 Ef P HE1Ef.
    symmetry in HE1Ef.
    unfold updates.fupd, fupd.
    unfold ghost_set at 3; erewrite (own_op(RA := set_PCM) _ _ _ (union E1 Ef)) by (split; auto).
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">(($ & HE2) & HP)"; first by iFrame.
    iCombine "HE2 HEf" as "H"; setoid_rewrite ghost_set_join.
    iDestruct "H" as "[% H]"; iFrame.
    iIntros "!> !>". iPoseProof ("HP" with "[%]") as "HP"; auto.
  - exact fupd_frame_r.
Qed.
Instance mpred_bi_fupd {inv_names : invG} : BiFUpd mpredSI :=
  {| bi_fupd_mixin := mpred_fupd_mixin |}.

Instance mpred_bi_bupd_fupd {inv_names : invG} : BiBUpdFUpd mpredSI.
Proof. hnf. by iIntros (E P) ">? [$ $] !> !>". Qed.

Section Invariants.

Context {inv_names : invG}.

Lemma fupd_timeless' : forall E1 E2 P Q, Timeless P -> (P |-- (|={E1,E2}=> Q) ->
  |> P |-- |={E1,E2}=> Q)%I.
Proof.
  intros.
  eapply derives_trans; [apply fupd_timeless; auto|].
  eapply derives_trans, fupd_trans.
  apply fupd_mono; eauto.
Qed.

Lemma fupd_except0_elim : forall E1 E2 P Q, (P |-- (|={E1,E2}=> Q) -> sbi_except_0 P |-- |={E1,E2}=> Q)%I.
Proof.
  intros; iIntros ">P Hpre".
  iPoseProof (H with "P Hpre") as ">>Q"; iFrame; auto.
Qed.

Lemma wsat_fupd_elim : forall P, (wsat * (|={empty,empty}=> P) |-- (|==> sbi_except_0 (wsat * P)))%I.
Proof.
  intros; unfold updates.fupd, bi_fupd_fupd; simpl; unfold fupd.
  rewrite <- wsat_empty_eq; apply modus_ponens_wand.
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
Qed.

Lemma fupd_prop' : forall E1 E2 E2' P Q, subseteq E1 E2 ->
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

Lemma inv_open : forall E i P, elem_of (Pos.of_nat (S i)) E ->
  (invariant i P |-- |={E, difference E (inv i)}=> (|> P) * (|>P -* |={difference E (inv i), E}=> emp))%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  intros; unfold fupd.
  rewrite <- wand_sepcon_adjoint.
  erewrite ghost_set_remove; eauto.
  rewrite invariant_dup.
  sep_apply (wsat_open i P).
  eapply derives_trans; [apply updates.bupd_frame_r | apply updates.bupd_mono].
  eapply derives_trans, bi.except_0_intro.
  unfold bi_sep; simpl; cancel.
  rewrite <- !wand_sepcon_adjoint.
  rewrite sepcon_emp.
  apply inv_close_aux.
Qed.

(* these last two are probably redundant *)
Lemma inv_close : forall E i P, elem_of (Pos.of_nat (S i)) E ->
  invariant i P * |> P * ghost_list(P := exclusive_PCM _) g_dis (list_singleton i (Some tt)) |--
  (|={difference E (inv i), E}=> TT)%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  intros; unfold fupd; iIntros "((? & ?) & ?) ?".
  iMod (inv_close_aux with "[-]") as ">H"; [iFrame|].
  do 2 iModIntro.
  erewrite (ghost_set_remove _ _ E) by eauto; iFrame; auto.
Qed.

Lemma inv_access : forall E i P, elem_of (Pos.of_nat (S i)) E ->
  (invariant i P |-- |={E, difference E (inv i)}=>
    |> P * (|> P -* |={difference E (inv i), E}=> TT))%I.
Proof.
  intros.
  eapply derives_trans; [apply inv_open; eauto|].
  apply fupd_mono; cancel.
  apply wand_derives; auto.
  apply fupd_mono; auto.
Qed.

End Invariants.

Lemma inv_in : forall i, elem_of (Pos.of_nat (S i)) (inv i).
Proof.
  intros; rewrite elem_of_singleton; reflexivity.
Qed.
Hint Resolve inv_in.

Global Opaque fupd.

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)
