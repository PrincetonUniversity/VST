From stdpp Require Export coPset.
From VST.veric Require Import compcert_rmaps fupd.
Require Export VST.veric.bi.
From VST.msl Require Import ghost ghost_seplog sepalg_generators.
From VST.concurrent Require Import ghosts conclib invariants.
Import Ensembles.
Import FashNotation.

Lemma timeless'_timeless : forall P, timeless' P -> Timeless P.
Proof.
  unfold Timeless; intros; simpl.
  constructor; change (predicates_hered.derives (|>P) (|>FF || P)%pred); intros ? HP.
  destruct (level a) eqn: Ha.
  - left; intros ? Hl%laterR_level.
    rewrite Ha in Hl; apply Nat.nlt_0_r in Hl; contradiction Hl.
  - right.
    destruct (levelS_age a n) as [b [Hb]]; auto.
    specialize (HP _ (semax_lemmas.age_laterR Hb)).
    eapply H; eauto.
Qed.

#[(*export, after Coq 8.13*)global] Instance own_timeless : forall {P : Ghost} g (a : G), Timeless (own g a NoneP).
Proof.
  intros; apply timeless'_timeless, own_timeless.
Qed.

Lemma address_mapsto_timeless : forall m v sh p, Timeless (res_predicates.address_mapsto m v sh p : mpred).
Proof.
  intros; apply timeless'_timeless, address_mapsto_timeless.
Qed.

#[(*export, after Coq 8.13*)global] Instance timeless_FF : Timeless FF.
Proof.
  unfold Timeless; intros.
  iIntros ">?"; auto.
Qed.

Lemma nonlock_permission_bytes_timeless : forall sh l z,
  Timeless (res_predicates.nonlock_permission_bytes sh l z : mpred).
Proof.
  intros; apply timeless'_timeless, nonlock_permission_bytes_timeless.
Qed.

Lemma mapsto_timeless : forall sh t v p, Timeless (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply timeless_FF.
  destruct (type_is_volatile); try apply timeless_FF.
  destruct p; try apply timeless_FF.
  if_tac.
  - apply (@bi.or_timeless mpredI).
    + apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply address_mapsto_timeless].
    + apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI)|].
      apply (@bi.exist_timeless mpredI); intro; apply address_mapsto_timeless.
  - apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply nonlock_permission_bytes_timeless].
Qed.

#[(*export, after Coq 8.13*)global] Instance emp_timeless : (@Timeless mpredI) emp.
Proof.
  apply timeless'_timeless, emp_timeless.
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
  apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply memory_block'_timeless].
Qed.

Lemma struct_pred_timeless : forall {CS : compspecs} sh m f t off
  (IH : Forall (fun it : _ =>
        forall (v : reptype (t it)) (p : val),
        Timeless (data_at_rec sh (t it) v p)) m) v p,
  Timeless (struct_pred m (fun (it : _) v =>
      withspacer sh (f it + sizeof (t it)) (off it)
        (at_offset (data_at_rec sh (t it) v) (f it))) v p).
Proof.
  induction m; intros.
  - apply emp_timeless.
  - inv IH. destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite struct_pred_cons2.
      apply (@bi.sep_timeless mpredI); auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma union_pred_timeless : forall {CS : compspecs} sh m t off
  (IH : Forall (fun it : _ =>
        forall (v : reptype (t it)) (p : val),
        Timeless (data_at_rec sh (t it) v p)) m) v p,
  Timeless (union_pred m (fun (it : _) v =>
      withspacer sh (sizeof (t it)) (off it)
        (data_at_rec sh (t it) v)) v p).
Proof.
  induction m; intros.
  - apply emp_timeless.
  - inv IH. destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite union_pred_cons2.
      destruct v; auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
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
  - apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI)|].
    rewrite Z.sub_0_r.
    forget (Z.to_nat (Z.max 0 z)) as n.
    set (lo := 0) at 1.
    clearbody lo.
    revert lo; induction n; simpl; intros.
    + apply emp_timeless.
    + apply (@bi.sep_timeless mpredI), IHn.
      unfold at_offset; apply IH.
  - apply struct_pred_timeless; auto.
  - apply union_pred_timeless; auto.
Qed.

#[(*export, after Coq 8.13*)global] Instance data_at_timeless : forall {CS : compspecs} sh t v p, Timeless (data_at sh t v p).
Proof.
  intros; apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply data_at_rec_timeless].
Qed.

Section FancyUpdates.

Lemma fview_shift_nonexpansive : forall E1 E2 P Q n,
  approx n (P -* |={E1,E2}=> Q)%logic = approx n (approx n P  -* |={E1,E2}=> approx n Q)%logic.
Proof.
  intros.
  rewrite wand_nonexpansive; setoid_rewrite wand_nonexpansive at 3.
  rewrite approx_idem; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.

End FancyUpdates.

Section Invariants.

Lemma fupd_timeless' : forall E1 E2 P Q, Timeless P -> ((P |-- (|={E1,E2}=> Q)) ->
  |> P |-- |={E1,E2}=> Q)%I.
Proof.
  intros.
  eapply derives_trans; [apply fupd_timeless; auto|].
  eapply derives_trans, fupd_trans.
  apply fupd_mono; eauto.
Qed.

Lemma wsat_fupd_elim' : forall E P, (wsat * ghost_set g_en (coPset_to_Ensemble E) * (|={E}=> P) |-- (|==> bi_except_0 (wsat * ghost_set g_en (coPset_to_Ensemble E) * P)))%I.
Proof.
  intros; unfold updates.fupd, bi_fupd_fupd; simpl; unfold fupd.
  apply modus_ponens_wand.
Qed.

Corollary wsat_fupd_elim : forall P, wsat * (|={empty}=> P)%I |-- (|==> bi_except_0 (wsat * P))%I.
Proof.
  intros; rewrite wsat_empty_eq.
  replace Empty_set with (coPset_to_Ensemble empty); [apply wsat_fupd_elim'|].
  apply Extensionality_Ensembles; constructor; intros ? X; inv X.
Qed.

Lemma bupd_except_0 : forall P, ((|==> bi_except_0 P) |-- bi_except_0 (|==> P))%I.
Proof.
  intros; constructor; change (predicates_hered.derives (own.bupd (bi_except_0 P)) (bi_except_0 (own.bupd P : mpred))).
  intros ??; simpl in H.
  destruct (level a) eqn: Hl.
  + left.
    change ((|> FF)%pred a).
    intros ? Hl'%laterR_level.
    rewrite Hl in Hl'; apply Nat.nlt_0_r in Hl'; contradiction Hl'.
  + right.
    rewrite <- Hl in *.
    intros ? J; specialize (H _ J) as (? & ? & a' & ? & ? & ? & HP); subst.
    do 2 eexists; eauto; do 2 eexists; eauto; repeat split; auto.
    destruct HP as [Hfalse|]; auto.
    destruct (levelS_age a' n) as (a'' & Hage & ?); [lia|].
    exfalso; apply (Hfalse a'').
    constructor; auto.
Qed.

Lemma fupd_prop' : forall E1 E2 E2' P Q, subseteq E1 E2 ->
  ((Q |-- (|={E1,E2'}=> !!P)) ->
  (|={E1, E2}=> Q) |-- |={E1}=> !!P && (|={E1, E2}=> Q))%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  unfold fupd; intros ?????? HQ.
  iIntros "H Hpre".
  iMod ("H" with "Hpre") as ">(Hpre & Q)".
  erewrite ghost_set_subset with (s' := coPset_to_Ensemble E1).
  iDestruct "Hpre" as "(wsat & en1 & en2)".
  iCombine ("wsat en1 Q") as "Q".
  erewrite (add_andp (_ ∗ _ ∗ Q)%I (bi_except_0 (!! P))) at 1.
  rewrite sepcon_andp_prop bi.except_0_and.
  iModIntro; iSplit.
  { iDestruct "Q" as "[? ?]"; auto. }
  iDestruct "Q" as "[($ & $ & $) _]"; iFrame; auto.
  { iIntros "(? & ? & Q)".
    setoid_rewrite <- (own.bupd_prop P).
    iApply bupd_except_0.
    iMod (HQ with "Q [$]") as ">(? & ?)"; auto. }
  { intro a; destruct (coPset_elem_of_dec (Pos.of_nat (S a)) E1); auto. }
  { unfold coPset_to_Ensemble; intros ??; unfold In in *; auto. }
Qed.

Lemma fupd_prop : forall E1 E2 P Q, subseteq E1 E2 ->
  (Q |-- !!P) ->
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

Lemma make_inv : forall E P Q, (P |-- Q) -> (P |-- |={E}=> EX i : _, invariant i Q)%I.
Proof.
  intros.
  eapply derives_trans, inv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

Lemma make_inv' : forall P Q, (P |-- Q) -> (wsat * P |-- |==> EX i : _, |> (wsat * (invariant i Q)))%I.
Proof.
  intros.
  iIntros "[wsat P]".
  iPoseProof (make_inv empty _ _ H with "P") as "inv".
  iMod (wsat_fupd_elim with "[$wsat $inv]") as "[wsat inv]".
  iDestruct "inv" as (i) "inv"; iExists i.
  unfold bi_except_0.
  iIntros "!> !>".
  iDestruct "wsat" as "[? | $]"; auto.
  iDestruct "inv" as "[? | ?]"; auto.
Qed.

Lemma inv_close_aux : forall E (i : iname) P,
  (ghost_list(P := token_PCM) g_dis (list_singleton i (Some tt)) * invariant i P * |> P *
  (wsat * ghost_set g_en (Subtract E i))
  |-- |==> bi_except_0 (wsat * (ghost_set g_en (Singleton i) * ghost_set g_en (Subtract E i))))%I.
Proof.
  intros.
  iIntros "(((? & ?) & ?) & ? & en)".
  iMod (wsat_close with "[-en]") as "[$ $]"; iFrame; auto.
Qed.

Definition inv i : coPset := base.singleton (Pos.of_nat (S i)).

Lemma inv_open : forall E i P, subseteq (inv i) E ->
  (invariant i P |-- |={E, difference E (inv i)}=> (|> P) * (|>P -* |={difference E (inv i), E}=> emp))%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  intros; unfold fupd.
  rewrite -> invariant_dup.
  erewrite ghost_set_remove.
  iIntros "[I ?] (wsat & i & en)".
  iMod (wsat_open with "[$wsat $I $i]") as "([$ $] & ?)".
  assert (Subtract (coPset_to_Ensemble E) i = (coPset_to_Ensemble (E ∖ inv i))) as Heq.
  { apply Extensionality_Ensembles; constructor; intros ? X.
    * inv X; unfold In, coPset_to_Ensemble in *.
      rewrite elem_of_difference; split; auto.
      unfold inv; intros X%elem_of_singleton%Nat2Pos.inj; auto.
      inv X; contradiction.
    * unfold In, coPset_to_Ensemble in *.
      apply elem_of_difference in X as [].
      constructor; auto.
      intro X; inv X; contradiction H1.
      unfold inv; apply elem_of_singleton; auto. }
  rewrite <- Heq; iFrame "en".
  iIntros "!> !> ? [? ?]".
  rewrite sepcon_emp; iApply inv_close_aux; iFrame.
  { unfold In, coPset_to_Ensemble.
    rewrite elem_of_subseteq_singleton; auto. }
Qed.

End Invariants.

Lemma inv_in : forall i, elem_of (Pos.of_nat (S i)) (inv i).
Proof.
  intros; rewrite elem_of_singleton; reflexivity.
Qed.
#[(*export, after Coq 8.13*)global] Hint Resolve inv_in : ghost.

(* avoids some fragility in tactics *)
Definition except0 : mpred -> mpred := bi_except_0.

Global Opaque fupd.
