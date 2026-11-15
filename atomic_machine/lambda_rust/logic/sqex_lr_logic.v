(** The rules of EXWP for the operations of the sequential language of
    [sq_logic.v]: the footprints of non-atomic reads, writes, allocations and
    frees, the instances of [CoreRedex] for these operations, and their
    rules for one core step ([sq_step]). Each rule is used in EXWP through
    [exwp_core_step]. *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import tactics.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** ** Footprints of the operations *)

Section footprints.
  Context `{!sq_heapGS Σ}.

  Lemma fp_tokens_read l q v : l ↦{q} v ⊢ fp_tokens [lr_read_event l].
  Proof.
    iIntros "Hl". rewrite /fp_tokens big_sepL_singleton /fp_event /=.
    by iExists q, v.
  Qed.

  Lemma fp_tokens_write l v : l ↦ v ⊢ fp_tokens [lr_write_event l].
  Proof.
    iIntros "Hl". rewrite /fp_tokens big_sepL_singleton /fp_event /=.
    by iExists v.
  Qed.

  Lemma fp_tokens_alloc l n : ⊢ fp_tokens (lr_alloc_events l n).
  Proof.
    rewrite /fp_tokens /lr_alloc_events. revert l.
    induction n as [|n IH]=> l /=; first done.
    iSplitR; [done | iApply IH].
  Qed.

  Lemma fp_tokens_free l vl : l ↦∗ vl ⊢ fp_tokens (lr_free_events l (length vl)).
  Proof.
    rewrite /fp_tokens /lr_free_events. revert l.
    induction vl as [|v vl IH]=> l /=.
    { by iIntros "_". }
    rewrite sq_pointsto_vec_cons. iIntros "[Hl Hvl]". iSplitL "Hl".
    - rewrite /fp_event /=. by iExists v.
    - by iApply IH.
  Qed.
End footprints.

(** ** The operations are core redexes *)

Global Instance core_redex_read_na l : CoreRedex (Read Na1Ord (Lit (LitLoc l))).
Proof.
  split; first done.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Global Instance core_redex_write_na l e : AsVal e -> CoreRedex (Write Na1Ord (Lit (LitLoc l)) e).
Proof.
  intros [v <-]. split; first done.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Global Instance core_redex_alloc n : CoreRedex (Alloc (Lit (LitInt n))).
Proof.
  split; first done.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

Global Instance core_redex_free n l : CoreRedex (Free (Lit (LitInt n)) (Lit (LitLoc l))).
Proof.
  split; first done.
  intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape].
Qed.

(** ** One core step of each operation *)

Section core_steps.
  Context `{!sq_heapGS Σ}.

  (** The access rules own their footprints before the step. *)
  Lemma sq_step_read_na l q v Ψ :
    l ↦{q} v -∗ ▷ (l ↦{q} v -∗ Ψ (of_val v)) -∗
    sq_step (Read Na1Ord (Lit (LitLoc l))) Ψ.
  Proof.
    rewrite /sq_step. iIntros "Hl HΨ". iSplit.
    - iIntros (m) "Hm".
      iDestruct (sq_heap_read with "Hm Hl") as %Hl.
      iModIntro. iSplit.
      { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRReadNaS. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. simplify_map_eq. iNext.
      iModIntro. iFrame "Hm". by iApply "HΨ".
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro. by iApply fp_tokens_read.
  Qed.

  Lemma sq_step_write_na l v v' Ψ :
    l ↦ v -∗ ▷ (l ↦ v' -∗ Ψ (Lit LitPoison)) -∗
    sq_step (Write Na1Ord (Lit (LitLoc l)) (of_val v')) Ψ.
  Proof.
    rewrite /sq_step. iIntros "Hl HΨ". iSplit.
    - iIntros (m) "Hm".
      iDestruct (sq_heap_read with "Hm Hl") as %Hl.
      iModIntro. iSplit.
      { iPureIntro. do 3 eexists. apply (LREctxStep []).
        econstructor; [apply to_of_val | exact Hl]. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst.
      match goal with H : to_val (of_val _) = Some _ |- _ =>
        rewrite to_of_val in H; injection H as <- end.
      iNext. iMod (sq_heap_write with "Hm Hl") as "[Hm Hl]".
      iModIntro. iFrame "Hm". by iApply "HΨ".
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro. by iApply fp_tokens_write.
  Qed.

  Lemma sq_step_alloc Ψ :
    ▷ (∀ l, l ↦ LitV LitPoison -∗ †l…1 -∗ Ψ (Lit (LitLoc l))) -∗
    sq_step (Alloc (Lit (LitInt 1))) Ψ.
  Proof.
    rewrite /sq_step. iIntros "HΨ". iSplit.
    - iIntros (m) "Hm". iModIntro. iSplit.
      { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
        do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iNext.
      iMod (sq_heap_alloc _ _ 1 with "Hm") as "[Hm [Hfree Hl]]"; [lia | done | ].
      rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
      iModIntro. iFrame "Hm". iApply ("HΨ" with "Hl Hfree").
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro. iApply fp_tokens_alloc.
  Qed.

  Lemma sq_step_free (n : Z) l vl Ψ :
    n = length vl ->
    l ↦∗ vl -∗ †l…(length vl) -∗ ▷ Ψ (Lit LitPoison) -∗
    sq_step (Free (Lit (LitInt n)) (Lit (LitLoc l))) Ψ.
  Proof.
    rewrite /sq_step. iIntros (Hn) "Hl Hf HΨ". iSplit.
    - iIntros (m) "Hm".
      iMod (sq_heap_free _ _ _ n Hn with "Hm Hl Hf") as "(%Hpos & %Hdom & Hm)".
      iModIntro. iSplit.
      { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRFreeS. }
      iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iNext. iModIntro. iFrame.
    - iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
      inversion Hs; subst. iModIntro. rewrite Nat2Z.id. by iApply fp_tokens_free.
  Qed.
End core_steps.
