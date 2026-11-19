(** Direct EXWP rules for lambda-Rust's non-atomic memory operations.

    Each rule proves both clauses of [sq_step] from the same ownership,
    using its non-separating conjunction for the step and footprint proofs. *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import tactics.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_lr_inst.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

Section footprints.
  Context `{!sq_heapGS Σ}.

  Local Lemma fp_tokens_alloc l n : ⊢ fp_tokens (lr_alloc_events l n).
  Proof.
    rewrite /lr_alloc_events. revert l.
    induction n as [|n IH]=> l /=; first apply fp_tokens_nil.
    iApply fp_tokens_cons. iSplitR; [done | iApply IH].
  Qed.

  Local Lemma fp_tokens_free l vl : l ↦∗ vl ⊢ fp_tokens (lr_free_events l (length vl)).
  Proof.
    rewrite /lr_free_events. revert l.
    induction vl as [|v vl IH]=> l /=.
    { iIntros "_". iApply fp_tokens_nil. }
    rewrite sq_pointsto_vec_cons. iIntros "[Hl Hvl]".
    iApply fp_tokens_cons. iSplitL "Hl".
    - rewrite /fp_event /=. by iExists v.
    - by iApply IH.
  Qed.
End footprints.

Global Instance not_at_external_read_na l : NotAtExternal (Read Na1Ord (Lit (LitLoc l))).
Proof.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Global Instance not_at_external_write_na l v :
    NotAtExternal (L := lr_language) (Write Na1Ord (Lit (LitLoc l)) (of_val v)).
Proof.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Global Instance not_at_external_alloc n : NotAtExternal (Alloc (Lit (LitInt n))).
Proof.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Global Instance not_at_external_free n l : NotAtExternal (Free (Lit (LitInt n)) (Lit (LitLoc l))).
Proof.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Section exwp.
  Context `{!sq_heapGS Σ, !invGS Σ,
    !ExtSpecs lr_language Σ}.

  Lemma exwp_read_na E l q v Φ :
    l ↦{q} v -∗ ▷ (l ↦{q} v -∗ Φ v) -∗
    EXWP (Read Na1Ord (Lit (LitLoc l))) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply exwp_not_at_external.
    cbn [sqlang_is_final lr_language]. iModIntro.
    rewrite /sq_step. iSplit.
    - iIntros (m) "Hm". iDestruct (sq_heap_read with "Hm Hl") as %Hl.
      iModIntro. iSplit.
      { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRReadNaS. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. simplify_map_eq. iNext.
      iModIntro. iFrame "Hm". iApply exwp_value'. by iApply "HΦ".
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro.
      rewrite fp_tokens_singleton /fp_event /=. by iExists q, v.
  Qed.

  Lemma exwp_write_na E l v v' Φ :
    l ↦ v -∗ ▷ (l ↦ v' -∗ Φ (LitV LitPoison)) -∗
    EXWP (Write Na1Ord (Lit (LitLoc l)) (of_val v')) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply exwp_not_at_external.
    cbn [sqlang_is_final lr_language]. iModIntro.
    rewrite /sq_step. iSplit.
    - iIntros (m) "Hm". iDestruct (sq_heap_read with "Hm Hl") as %Hl.
      iModIntro. iSplit.
      { iPureIntro. do 3 eexists. apply (LREctxStep []).
        econstructor; [apply to_of_val | exact Hl]. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst.
      match goal with H : to_val (of_val _) = Some _ |- _ =>
        rewrite to_of_val in H; injection H as <- end.
      iNext. iMod (sq_heap_write with "Hm Hl") as "[Hm Hl]".
      iModIntro. iFrame "Hm". iApply exwp_value'. by iApply "HΦ".
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro.
      rewrite fp_tokens_singleton /fp_event /=. by iExists v.
  Qed.

  Lemma exwp_alloc E Φ :
    ▷ (∀ l, l ↦ LitV LitPoison -∗ †l…1 -∗ Φ (LitV (LitLoc l))) -∗
    EXWP (Alloc (Lit (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply exwp_not_at_external.
    cbn [sqlang_is_final lr_language]. iModIntro.
    rewrite /sq_step. iSplit.
    - iIntros (m) "Hm". iModIntro. iSplit.
      { iPureIntro. destruct (lr_alloc_fresh m) as [l Hl].
        do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iNext.
      iMod (sq_heap_alloc _ _ 1 with "Hm") as "[Hm [Hfree Hl]]"; [lia | done | ].
      rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
      iModIntro. iFrame "Hm".
      iApply exwp_value'. iApply ("HΦ" with "Hl Hfree").
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro. iApply fp_tokens_alloc.
  Qed.

  Lemma exwp_free E (n : Z) l vl Φ :
    n = length vl ->
    l ↦∗ vl -∗ †l…(length vl) -∗ ▷ Φ (LitV LitPoison) -∗
    EXWP (Free (Lit (LitInt n)) (Lit (LitLoc l))) @ E {{ Φ }}.
  Proof.
    iIntros (Hn) "Hl Hf HΦ". iApply exwp_not_at_external.
    cbn [sqlang_is_final lr_language]. iModIntro.
    rewrite /sq_step. iSplit.
    - iIntros (m) "Hm".
      iMod (sq_heap_free _ _ _ n Hn with "Hm Hl Hf") as "(%Hpos & %Hdom & Hm)".
      iModIntro. iSplit.
      { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRFreeS. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iNext. iModIntro. iFrame "Hm".
      by iApply exwp_value'.
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro. rewrite Nat2Z.id.
      by iApply (fp_tokens_free with "Hl").
  Qed.
End exwp.
