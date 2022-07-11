Require Import stdpp.namespaces.
Require Import VST.veric.invariants.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.conclib.
Require Export VST.concurrency.ghostsI.
Require Import VST.veric.bi.
Require Import VST.msl.sepalg.
Require Import List.
Import Ensembles.

#[export] Notation iname := iname.

Lemma coPset_to_Ensemble_minus : forall E1 E2, coPset_to_Ensemble (E1 ∖ E2) = Setminus (coPset_to_Ensemble E1) (coPset_to_Ensemble E2).
Proof.
  intros; unfold coPset_to_Ensemble.
  apply Extensionality_Ensembles; split; intros ? Hin; unfold In in *.
  - apply elem_of_difference in Hin as []; constructor; auto.
  - inv Hin. apply elem_of_difference; auto.
Qed.

Lemma coPset_to_Ensemble_single : forall x, coPset_to_Ensemble {[Pos.of_nat (S x)]} = Singleton x.
Proof.
  intros; unfold coPset_to_Ensemble.
  apply Extensionality_Ensembles; split; intros ? Hin; unfold In in *.
  - apply elem_of_singleton in Hin.
    apply (f_equal Pos.to_nat) in Hin.
    rewrite -> !Nat2Pos.id in Hin by auto; inv Hin; constructor.
  - inv Hin.
    apply elem_of_singleton; auto.
Qed.

(* recapitulating Iris "semantic invariants" so we can use custom namespaces. *)
Definition inv (N : namespace) (P : mpred) : mpred := 
  □ ∀ E, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ emp).

Definition own_inv (N : namespace) (P : mpred) :=
    ∃ i, ⌜Pos.of_nat (S i) ∈ (↑N:coPset)⌝ ∧ invariant i P.

Lemma own_inv_acc E N P :
  ↑N ⊆ E → own_inv N P |-- |={E,E∖↑N}=> ▷ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
Proof.
  intros.
  iDestruct 1 as (i) "[% HiP]".
  iPoseProof (inv_open (coPset_to_Ensemble E) with "HiP") as "H".
  { unfold Ensembles.In, coPset_to_Ensemble; set_solver. }
  iAssert (|={E,E ∖ {[Pos.of_nat (S i)]}}=> |> P * (|> P -* |={E ∖ {[Pos.of_nat (S i)]},E}=> emp)) with "[H]" as "H".
  { unfold fupd, bi_fupd_fupd; simpl.
    rewrite coPset_to_Ensemble_minus coPset_to_Ensemble_single; auto. }
  iMod "H"; iApply fupd_mask_intro; first by set_solver.
  iIntros "mask".
  iDestruct "H" as "[$ H]"; iIntros "?".
  iMod "mask"; iMod ("H" with "[$]"); auto.
Qed.

Lemma fresh_inv_name n N : ∃ i, (n <= i)%nat /\ Pos.of_nat (S i) ∈ (↑N:coPset).
Proof.
  pose proof (coPpick_elem_of (↑ N ∖ gset_to_coPset (list_to_set (map (fun i => Z.to_pos (i + 1)) (upto n))))).
  rewrite elem_of_difference in H; destruct H as [HN H].
  { apply coPset_infinite_finite, difference_infinite, gset_to_coPset_finite.
    apply coPset_infinite_finite, nclose_infinite. }
  exists (Pos.to_nat (coPpick (↑ N ∖ gset_to_coPset (list_to_set (map (fun i => Z.to_pos (i + 1)) (upto n))))) - 1)%nat; split.
  - match goal with |-(?a <= ?b)%nat => destruct (le_lt_dec a b); auto; exfalso end.
    apply H, elem_of_gset_to_coPset, elem_of_list_to_set, elem_of_list_In, in_map_iff.
    apply Nat2Z.inj_lt in l.
    setoid_rewrite In_upto; eexists; split; [|split; [|apply l]]; lia.
  - destruct (eq_dec (coPpick (↑N ∖ gset_to_coPset (list_to_set (map (λ i : Z, Z.to_pos (i + 1)) (upto n))))) 1%positive).
    + rewrite e in HN |- *; auto.
    + rewrite -> Nat2Pos.inj_succ, Nat2Pos.inj_sub, Pos2Nat.id, Positive_as_OT.sub_1_r, Pos.succ_pred; auto; lia.
Qed.

Lemma own_inv_alloc N E P : ▷ P |-- |={E}=> own_inv N P.
Proof.
  iIntros "HP".
  iPoseProof (inv_alloc_strong _ _ (fun i => Pos.of_nat (S i) ∈ (↑N : coPset)) with "HP") as "H";
    auto using fresh_inv_name.
Qed.

Global Instance agree_persistent g P : Persistent (agree g P : mpred).
Proof.
  apply core_persistent; auto.
Qed.

Lemma own_inv_to_inv M P: own_inv M P |-- inv M P.
Proof.
  iIntros "#I !>". iIntros (E H).
  iPoseProof (own_inv_acc with "I") as "H"; eauto.
Qed.

Global Instance inv_persistent N P : Persistent (inv N P).
Proof.
  apply _.
Qed.

Global Instance inv_affine N P : Affine (inv N P).
Proof.
  apply _.
Qed.

Lemma invariant_dup : forall N P, inv N P = (inv N P * inv N P)%logic.
Proof.
  intros; apply pred_ext; rewrite <- (bi.persistent_sep_dup (inv N P)); auto.
Qed.

Lemma agree_join : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P1.
Proof.
  constructor; apply agree_join.
Qed.

Lemma agree_join2 : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P2.
Proof.
  constructor; apply agree_join2.
Qed.

Lemma inv_alloc : forall N E P, |> P |-- |={E}=> inv N P.
Proof.
  intros; iIntros "?"; iApply own_inv_to_inv; iApply own_inv_alloc; auto.
Qed.

Lemma make_inv : forall N E P Q, (P |-- Q) -> P |-- |={E}=> inv N Q.
Proof.
  intros.
  eapply derives_trans, inv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

#[export] Instance into_acc_inv N P E:
  IntoAcc (X := unit) (inv N P)
          (↑N ⊆ E) emp (updates.fupd E (E ∖ ↑N)) (updates.fupd (E ∖ ↑N) E)
          (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
Proof.
  rewrite /inv /IntoAcc /accessor bi.exist_unit.
  intros; iIntros "#I _".
  iMod ("I" with "[%]"); auto.
Qed.

(* up *)
Lemma persistently_nonexpansive : nonexpansive persistently.
Proof.
  intros; unfold nonexpansive, persistently.
  intros; split; intros ?????; simpl in *; eapply (H (core a'')); eauto;
    rewrite level_core; apply necR_level in H1; apply ext_level in H2; lia.
Qed.

Lemma persistently_nonexpansive2 : forall f, nonexpansive f ->
  nonexpansive (fun a => persistently (f a)).
Proof.
  intros; unfold nonexpansive.
  intros; eapply predicates_hered.derives_trans; [apply H|].
  apply persistently_nonexpansive.
Qed.

Lemma bupd_nonexpansive : nonexpansive own.bupd.
Proof.
  unfold nonexpansive, own.bupd; split; simpl; intros;
    apply H3 in H4 as (? & ? & ? & ? & ? & ? & ?); do 2 eexists; eauto; do 2 eexists; eauto;
    repeat (split; auto); eapply (H x0); eauto; apply necR_level in H1; apply ext_level in H2; lia.
Qed.

Lemma bupd_nonexpansive2 : forall f, nonexpansive f ->
  nonexpansive (fun a => own.bupd (f a)).
Proof.
  intros; unfold nonexpansive.
  intros; eapply predicates_hered.derives_trans; [apply H|].
  apply bupd_nonexpansive.
Qed.

Lemma fupd_nonexpansive1 : forall E1 E2, nonexpansive (fupd.fupd E1 E2).
Proof.
  unfold fupd.fupd, nonexpansive; intros.
  apply (contractive.wand_nonexpansive (fun _ => wsat * ghost_set g_en E1)%pred
    (fun P => (|==> |> predicates_hered.FF || wsat * ghost_set g_en E2 * P)%pred)
    (const_nonexpansive _)).
  apply bupd_nonexpansive2, @disj_nonexpansive, sepcon_nonexpansive, identity_nonexpansive; apply const_nonexpansive.
Qed.

Lemma fupd_nonexpansive2 : forall E1 E2 f, nonexpansive f ->
  nonexpansive (fun a => fupd.fupd E1 E2 (f a)).
Proof.
  intros; unfold nonexpansive.
  intros; eapply predicates_hered.derives_trans; [apply H|].
  apply fupd_nonexpansive1.
Qed.

Lemma later_nonexpansive1 : nonexpansive (box laterM).
Proof.
  apply contractive_nonexpansive, later_contractive, identity_nonexpansive.
Qed.

Lemma inv_nonexpansive : forall N, nonexpansive (inv N).
Proof.
  intros; unfold inv.
  unfold bi_intuitionistically, bi_affinely, bi_persistently; simpl.
  apply @conj_nonexpansive, persistently_nonexpansive2, @forall_nonexpansive; intros.
  { apply const_nonexpansive. }
  apply @impl_nonexpansive, fupd_nonexpansive2, sepcon_nonexpansive, contractive.wand_nonexpansive, fupd_nonexpansive2;
    try apply later_nonexpansive1; apply const_nonexpansive.
Qed.

Lemma inv_nonexpansive2 : forall N f, nonexpansive f ->
  nonexpansive (fun a => inv N (f a)).
Proof.
  intros; unfold nonexpansive.
  intros; eapply predicates_hered.derives_trans; [apply H|].
  apply inv_nonexpansive.
Qed.

Global Opaque inv.
