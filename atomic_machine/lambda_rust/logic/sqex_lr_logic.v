(** The operations of the sequential language of [sq_logic.v] in EXWP.

    [SQWP] is a sequential weakest precondition for lambda-Rust in the style
    of Iris's, without fancy updates and later credits (and without external
    calls): its steps are exactly the step clause of EXWP. Its rules for the
    non-atomic reads, writes, allocations and frees are those of
    [sq_logic.v]. [wp_well_behaved e] states that the thread owns the
    footprint of every step of [e]. For a core redex [e] that steps to a
    value ([CoreAtomic e]), an SQWP together with [wp_well_behaved] is an
    EXWP ([exwp_sqwp]). *)

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

(** ** The operations are core redexes that step to values *)

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

(** Every step of [e] reaches a value. *)
Class CoreAtomic (e : sq_expr) : Prop :=
  core_atomic m T e2 m2 : lr_step e m T e2 m2 -> is_Some (to_val e2).

Global Instance core_atomic_read_na l : CoreAtomic (Read Na1Ord (Lit (LitLoc l))).
Proof.
  intros m T e2 m2 Hs. apply lr_step_head in Hs; last solve_redex_shape.
  inversion Hs; subst. rewrite to_of_val. by eexists.
Qed.

Global Instance core_atomic_write_na l e : AsVal e -> CoreAtomic (Write Na1Ord (Lit (LitLoc l)) e).
Proof.
  intros [v <-] m T e2 m2 Hs. apply lr_step_head in Hs; last solve_redex_shape.
  inversion Hs; subst. by eexists.
Qed.

Global Instance core_atomic_alloc n : CoreAtomic (Alloc (Lit (LitInt n))).
Proof.
  intros m T e2 m2 Hs. apply lr_step_head in Hs; last solve_redex_shape.
  inversion Hs; subst. by eexists.
Qed.

Global Instance core_atomic_free n l : CoreAtomic (Free (Lit (LitInt n)) (Lit (LitLoc l))).
Proof.
  intros m T e2 m2 Hs. apply lr_step_head in Hs; last solve_redex_shape.
  inversion Hs; subst. by eexists.
Qed.

(** ** A sequential weakest precondition without fancy updates *)

Section sqwp_pre.
  Context `{!sq_heapGS Σ}.

  Definition sqwp_pre
      (sqwp : coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ) :
      coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
    match to_val e1 with
    | Some v => |==> Φ v
    | None => ∀ m1, sq_heap m1 ==∗
        ⌜exists T e2 m2, lr_step e1 m1 T e2 m2⌝ ∗
        ∀ T e2 m2, ⌜lr_step e1 m1 T e2 m2⌝ -∗ ▷ |==> sq_heap m2 ∗ sqwp E e2 Φ
    end%I.

  Global Instance sqwp_pre_contractive : Contractive sqwp_pre.
  Proof.
    rewrite /sqwp_pre /= => n wp wp' Hwp E e1 Φ.
    repeat (f_contractive || f_equiv). apply Hwp.
  Qed.
End sqwp_pre.

Definition sqwp `{!sq_heapGS Σ} : coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ :=
  fixpoint sqwp_pre.
Global Arguments sqwp {Σ _} E e%_E Φ%_I.

Notation "'SQWP' e @ E {{ Φ } }" := (sqwp E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SQWP' e {{ Φ } }" := (sqwp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SQWP' e @ E {{ v , Q } }" := (sqwp E e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern) : bi_scope.
Notation "'SQWP' e {{ v , Q } }" := (sqwp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern) : bi_scope.

Section sqwp.
  Context `{!sq_heapGS Σ}.

  Lemma sqwp_unfold E e Φ : SQWP e @ E {{ Φ }} ⊣⊢ sqwp_pre sqwp E e Φ.
  Proof. apply (fixpoint_unfold sqwp_pre). Qed.

  Lemma sqwp_value_bupd E v Φ : SQWP of_val v @ E {{ Φ }} ⊣⊢ |==> Φ v.
  Proof. by rewrite sqwp_unfold /sqwp_pre to_of_val. Qed.

  Lemma sqwp_value E v Φ : Φ v ⊢ SQWP of_val v @ E {{ Φ }}.
  Proof. rewrite sqwp_value_bupd. apply bupd_intro. Qed.

  Lemma bupd_sqwp E e Φ : (|==> SQWP e @ E {{ Φ }}) ⊢ SQWP e @ E {{ Φ }}.
  Proof.
    rewrite sqwp_unfold /sqwp_pre. destruct (to_val e); first apply bupd_trans.
    iIntros "H" (m) "Hm". iMod "H". by iApply "H".
  Qed.

  Lemma sqwp_lift_step E e Φ :
    to_val e = None ->
    (∀ m1, sq_heap m1 ==∗
      ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
      ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==> sq_heap m2 ∗ SQWP e2 @ E {{ Φ }}) ⊢
    SQWP e @ E {{ Φ }}.
  Proof. intros Hv. by rewrite sqwp_unfold /sqwp_pre Hv. Qed.

  Lemma sqwp_bind K E e Φ :
    SQWP e @ E {{ v, SQWP fill K (of_val v) @ E {{ Φ }} }} ⊢ SQWP fill K e @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e). rewrite (sqwp_unfold E e) /sqwp_pre.
    destruct (to_val e) as [v|] eqn:Hv.
    { apply of_to_val in Hv. subst e. iApply bupd_sqwp. }
    rewrite sqwp_unfold /sqwp_pre (fill_not_val _ _ Hv).
    iIntros "H" (m) "Hm". iMod ("H" with "Hm") as "[%Hr H]". iModIntro. iSplit.
    { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
      exists T, (fill K e2), m2. destruct Hs. rewrite -!fill_app. by constructor. }
    iIntros (T e2 m2 Hs).
    destruct (lr_step_fill_inv _ _ _ _ _ _ Hv Hs) as (e2' & -> & Hs').
    iSpecialize ("H" $! T e2' m2 with "[//]"). iNext.
    iMod "H" as "[$ H]". iModIntro. by iApply "IH".
  Qed.

  Lemma sqwp_wand E e Φ Ψ :
    SQWP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ SQWP e @ E {{ Ψ }}.
  Proof.
    iLöb as "IH" forall (e). iIntros "Hwp HΦ". rewrite !(sqwp_unfold E e) /sqwp_pre.
    destruct (to_val e) as [v|].
    { iMod "Hwp". iModIntro. by iApply "HΦ". }
    iIntros (m) "Hm". iMod ("Hwp" with "Hm") as "[$ Hwp]". iModIntro.
    iIntros (T e2 m2 Hs). iSpecialize ("Hwp" $! T e2 m2 with "[//]"). iNext.
    iMod "Hwp" as "[$ Hwp]". iModIntro. iApply ("IH" with "Hwp HΦ").
  Qed.

  Lemma sqwp_pure_step E e1 e2 Φ :
    @pure_step sq_lang e1 e2 -> ▷ SQWP e2 @ E {{ Φ }} ⊢ SQWP e1 @ E {{ Φ }}.
  Proof.
    intros Hpure. have ? := pure_step_core_redex _ _ Hpure.
    destruct Hpure as [Hsafe Hdet].
    iIntros "Hwp". iApply sqwp_lift_step; first apply core_redex_not_val.
    iIntros (m) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (Hsafe m) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      eauto. }
    iIntros (T e' m' Hs).
    destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
    { by apply sq_prim_step_lr_step. }
    iNext. iModIntro. iFrame.
  Qed.

  (** The rules of [sq_logic.v] for the operations. *)
  Lemma sqwp_read_na E l q v Φ :
    l ↦{q} v -∗ ▷ (l ↦{q} v -∗ Φ v) -∗
    SQWP (Read Na1Ord (Lit (LitLoc l))) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply sqwp_lift_step; first done.
    iIntros (m) "Hm". iDestruct (sq_heap_read with "Hm Hl") as %Hl.
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRReadNaS. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. simplify_map_eq. iNext.
    iModIntro. iFrame "Hm". iApply sqwp_value. by iApply "HΦ".
  Qed.

  Lemma sqwp_write_na E l v v' Φ :
    l ↦ v -∗ ▷ (l ↦ v' -∗ Φ (LitV LitPoison)) -∗
    SQWP (Write Na1Ord (Lit (LitLoc l)) (of_val v')) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply sqwp_lift_step; first done.
    iIntros (m) "Hm". iDestruct (sq_heap_read with "Hm Hl") as %Hl.
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []).
      econstructor; [apply to_of_val | exact Hl]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst.
    match goal with H : to_val (of_val _) = Some _ |- _ =>
      rewrite to_of_val in H; injection H as <- end.
    iNext. iMod (sq_heap_write with "Hm Hl") as "[Hm Hl]".
    iModIntro. iFrame "Hm". iApply (sqwp_value _ (LitV LitPoison)). by iApply "HΦ".
  Qed.

  Lemma sqwp_alloc E Φ :
    ▷ (∀ l, l ↦ LitV LitPoison -∗ †l…1 -∗ Φ (LitV (LitLoc l))) -∗
    SQWP (Alloc (Lit (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply sqwp_lift_step; first done.
    iIntros (m) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
      do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext.
    iMod (sq_heap_alloc _ _ 1 with "Hm") as "[Hm [Hfree Hl]]"; [lia | done | ].
    rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
    iModIntro. iFrame "Hm".
    iApply (sqwp_value _ (LitV (LitLoc l))). iApply ("HΦ" with "Hl Hfree").
  Qed.

  Lemma sqwp_free E (n : Z) l vl Φ :
    n = length vl ->
    l ↦∗ vl -∗ †l…(length vl) -∗ ▷ Φ (LitV LitPoison) -∗
    SQWP (Free (Lit (LitInt n)) (Lit (LitLoc l))) @ E {{ Φ }}.
  Proof.
    iIntros (Hn) "Hl Hf HΦ". iApply sqwp_lift_step; first done.
    iIntros (m) "Hm".
    iMod (sq_heap_free _ _ _ n Hn with "Hm Hl Hf") as "(%Hpos & %Hdom & Hm)".
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRFreeS. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext. iModIntro. iFrame "Hm".
    by iApply (sqwp_value _ (LitV LitPoison)).
  Qed.
End sqwp.

(** ** Well-behaved WPs *)

Section well_behaved.
  Context `{!sq_heapGS Σ}.

  (** The thread owns the footprint of every step of [e]. *)
  Definition wp_well_behaved (e : sq_expr) : iProp Σ :=
    ∀ m T e2 m2, ⌜lr_step e m T e2 m2⌝ ==∗ fp_tokens T.

  Lemma wp_well_behaved_read_na l q v :
    l ↦{q} v ⊢ wp_well_behaved (Read Na1Ord (Lit (LitLoc l))).
  Proof.
    iIntros "Hl" (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iModIntro. by iApply fp_tokens_read.
  Qed.

  Lemma wp_well_behaved_write_na l v v' :
    l ↦ v ⊢ wp_well_behaved (Write Na1Ord (Lit (LitLoc l)) (of_val v')).
  Proof.
    iIntros "Hl" (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iModIntro. by iApply fp_tokens_write.
  Qed.

  Lemma wp_well_behaved_alloc : ⊢ wp_well_behaved (Alloc (Lit (LitInt 1))).
  Proof.
    iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iModIntro. iApply fp_tokens_alloc.
  Qed.

  Lemma wp_well_behaved_free (n : Z) l vl :
    n = length vl ->
    l ↦∗ vl ⊢ wp_well_behaved (Free (Lit (LitInt n)) (Lit (LitLoc l))).
  Proof.
    iIntros (Hn) "Hl". iIntros (m T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iModIntro. rewrite Nat2Z.id. by iApply fp_tokens_free.
  Qed.
End well_behaved.

(** ** From SQWP to EXWP *)

Section lifting.
  Context `{!lrSqGS Σ, !ExtSpecs lr_language Σ}.

  (** A well-behaved SQWP of a core redex that steps to a value is an EXWP. *)
  Lemma exwp_sqwp E e Φ `{!CoreRedex e, !CoreAtomic e} :
    SQWP e @ E {{ Φ }} ∧ wp_well_behaved e ⊢ EXWP e @ E {{ Φ }}.
  Proof.
    iIntros "H". iApply exwp_core_step. rewrite /sq_step. iSplit.
    - iDestruct "H" as "[H _]". rewrite sqwp_unfold /sqwp_pre core_redex_not_val.
      iIntros (m) "Hm". iMod ("H" with "Hm") as "[$ H]". iModIntro.
      iIntros (T e2 m2 Hs). iSpecialize ("H" $! T e2 m2 with "[//]"). iNext.
      iMod "H" as "[$ Hwp]".
      destruct (core_atomic _ _ _ _ Hs) as [v Hv]. apply of_to_val in Hv as <-.
      rewrite sqwp_value_bupd. iMod "Hwp". iModIntro. by iApply exwp_value.
    - by iDestruct "H" as "[_ H]".
  Qed.
End lifting.
