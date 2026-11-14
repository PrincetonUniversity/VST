(** * A footprint variant of EXWP whose adequacy needs no model reasoning

    [sqex_global_view.v] shows that EXWP's adequacy cannot be proved while
    treating its state interpretation abstractly: the per-thread quantifier
    over [sq_heap_gen m h] is only usable with authorities that cannot coexist
    with the other threads' fragments.

    FPWP keeps EXWP's structure (sequential steps without the reader/writer
    map, external calls through [ExtCallSpecs]) but changes the sequential
    case in two ways:
    - the state interpretation is the shared heap [sq_heap m];
    - after a step with trace [T], the thread hands over the points-to
      footprint of [T] ([fp_tokens T ds]) and receives it back at Commit.
    Footprints of reads are fractional points-to, footprints of writes are
    full points-to (also for same-value writes). Allocation needs no token:
    its reservation never conflicts with another thread's. Free needs none
    either: the freed cells leave memory, so a pending access to them would
    hold a fragment that contradicts the new state interpretation.

    The rule interfaces match EXWP's ([fpwp_read_na], [fpwp_write_na],
    [fpwp_alloc], the SC rules [fp_conc_wp_*]), and [sqfp_examples.v] replays
    the EXWP examples with the same proof scripts.

    The adequacy proof in [sqfp_adequacy.v] holds the footprints of pending
    threads, so data races become ordinary validity conflicts in the logic. *)

From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.program_logic Require Export weakestpre.
From lrust.lang Require Import tactics.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.at_logic.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_rules.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Local Existing Instance lrSqGS_invGS.

Section footprints.
  Context `{!sq_heapGS Σ}.

  (** The ownership witnessing one access. The data [d] records the fraction
      and the value, so the returned tokens are exactly the handed-over ones. *)
  Definition fp_event (ev : @mem_ev loc) (d : Qp * val) : iProp Σ :=
    match ev with
    | atomic_machine.Read l => l ↦{d.1} d.2
    | atomic_machine.Write l => l ↦ d.2
    | atomic_machine.Alloc _ | atomic_machine.Free _ => True
    end.

  Definition fp_tokens (T : list (@mem_ev loc)) (ds : list (Qp * val)) : iProp Σ :=
    [∗ list] ev; d ∈ T; ds, fp_event ev d.

  Lemma fp_tokens_nil : ⊢ fp_tokens [] [].
  Proof. by rewrite /fp_tokens. Qed.

  Lemma fp_tokens_nil_inv ds : fp_tokens [] ds -∗ ⌜ds = []⌝.
  Proof. rewrite /fp_tokens big_sepL2_nil_inv_l. by iIntros "->". Qed.

  Lemma fp_tokens_read T ds l :
    lr_read_event l ∈ T -> fp_tokens T ds ⊢ ∃ q v, l ↦{q} v ∗ True.
  Proof.
    intros (k & Hk)%list_elem_of_lookup. iIntros "Htok".
    iDestruct (big_sepL2_length with "Htok") as %Hlen.
    destruct (lookup_lt_is_Some_2 ds k) as [d Hd].
    { rewrite -Hlen. by apply lookup_lt_Some with (lr_read_event l). }
    iDestruct (big_sepL2_lookup with "Htok") as "Hl"; [exact Hk | exact Hd | ].
    iExists d.1, d.2. by iFrame.
  Qed.

  Lemma fp_tokens_write T ds l :
    lr_write_event l ∈ T -> fp_tokens T ds ⊢ ∃ v, l ↦ v ∗ True.
  Proof.
    intros (k & Hk)%list_elem_of_lookup. iIntros "Htok".
    iDestruct (big_sepL2_length with "Htok") as %Hlen.
    destruct (lookup_lt_is_Some_2 ds k) as [d Hd].
    { rewrite -Hlen. by apply lookup_lt_Some with (lr_write_event l). }
    iDestruct (big_sepL2_lookup with "Htok") as "Hl"; [exact Hk | exact Hd | ].
    iExists d.2. by iFrame.
  Qed.

  (** Conflicts between a fragment and a set of footprint tokens. *)
  Lemma fp_tokens_read_excl T ds l q v :
    fp_tokens T ds -∗ l ↦{q} v -∗ ⌜lr_write_event l ∉ T⌝.
  Proof.
    iIntros "Htok Hl %Hin".
    iDestruct (fp_tokens_write with "Htok") as (w) "[Hw _]"; first done.
    iDestruct (sq_pointsto_valid_2 with "Hw Hl") as %[Hq _].
    exfalso. exact (Qp.not_add_le_l 1 q Hq).
  Qed.

  Lemma fp_tokens_write_excl T ds l v :
    fp_tokens T ds -∗ l ↦ v -∗ ⌜lr_write_event l ∉ T ∧ lr_read_event l ∉ T⌝.
  Proof.
    iIntros "Htok Hl". iSplit.
    - iApply (fp_tokens_read_excl with "Htok Hl").
    - iIntros (Hin).
      iDestruct (fp_tokens_read with "Htok") as (q w) "[Hw _]"; first done.
      iDestruct (sq_pointsto_valid_2 with "Hl Hw") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 q Hq).
  Qed.

  Lemma fp_tokens_allocated T ds m l :
    sq_heap m -∗ fp_tokens T ds -∗
    ⌜lr_read_event l ∈ T \/ lr_write_event l ∈ T -> is_Some (m !! l)⌝.
  Proof.
    iIntros "Hm Htok" ([Hin|Hin]).
    - iDestruct (fp_tokens_read with "Htok") as (q w) "[Hw _]"; first done.
      iDestruct (sq_heap_read with "Hm Hw") as %Hw. by eauto.
    - iDestruct (fp_tokens_write with "Htok") as (w) "[Hw _]"; first done.
      iDestruct (sq_heap_read with "Hm Hw") as %Hw. by eauto.
  Qed.
End footprints.

Section fpwp_pre.
  Context `{!lrSqGS Σ} (specs : ExtCallSpecs lr_language Σ).
  Local Existing Instance specs.

  Definition fpwp_pre
      (fpwp : coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ) :
      coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
    match to_val e1 with
    | Some v => |==> Φ v
    | None => |==>
        (⌜forall op k, ~ lr_external e1 op k⌝ ∗
         ∀ m1, sq_heap m1 ==∗
          ⌜exists T e2 m2, lr_step e1 m1 T e2 m2⌝ ∗
          ∀ T e2 m2, ⌜lr_step e1 m1 T e2 m2⌝ -∗ ▷ |==>
            sq_heap m2 ∗ ∃ ds, fp_tokens T ds ∗ (fp_tokens T ds -∗ fpwp E e2 Φ)) ∨
        (∃ op k, ⌜lr_external e1 op k⌝ ∗
          |={E,∅}=> ∃ x : ext_spec_args op,
            ext_spec_pre op x (λ ef, ▷ fpwp ⊤ ef (λ _, True)) ∗
            ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> fpwp E (k ov) Φ))
    end%I.

  Global Instance fpwp_pre_contractive : Contractive fpwp_pre.
  Proof.
    rewrite /fpwp_pre /= => n wp wp' Hwp E e1 Φ.
    repeat (f_contractive || f_equiv); first [apply Hwp | intros ef; f_contractive; apply Hwp].
  Qed.
End fpwp_pre.

Definition fpwp `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} :
    coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ :=
  fixpoint (fpwp_pre _).
Global Arguments fpwp {Σ _ _} E e%_E Φ%_I.

Notation "'FPWP' e @ E {{ Φ } }" := (fpwp E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'FPWP' e {{ Φ } }" := (fpwp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'FPWP' e @ E {{ v , Q } }" := (fpwp E e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern) : bi_scope.
Notation "'FPWP' e {{ v , Q } }" := (fpwp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern) : bi_scope.

Notation "'{{{' P } } } 'FPWP' e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ FPWP e @ E {{ Φ }})%I
  (at level 20) : bi_scope.
Notation "'{{{' P } } } 'FPWP' e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, ⊢ P -∗ ▷ (Q -∗ Φ pat%V) -∗ FPWP e @ E {{ Φ }}) : stdpp_scope.

Section fpwp.
  Context `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ}.

  Lemma fpwp_unfold E e Φ :
    FPWP e @ E {{ Φ }} ⊣⊢ fpwp_pre _ fpwp E e Φ.
  Proof. apply (fixpoint_unfold (fpwp_pre _)). Qed.

  Lemma fpwp_value_bupd E v Φ : FPWP of_val v @ E {{ Φ }} ⊣⊢ |==> Φ v.
  Proof. by rewrite fpwp_unfold /fpwp_pre to_of_val. Qed.

  Lemma fpwp_value E v Φ : Φ v ⊢ FPWP of_val v @ E {{ Φ }}.
  Proof. rewrite fpwp_value_bupd. apply bupd_intro. Qed.

  Lemma bupd_fpwp E e Φ : (|==> FPWP e @ E {{ Φ }}) ⊢ FPWP e @ E {{ Φ }}.
  Proof. rewrite fpwp_unfold /fpwp_pre. destruct (to_val e); apply bupd_trans. Qed.

  Lemma fpwp_seq_unfold E e Φ :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    FPWP e @ E {{ Φ }} ⊣⊢
      (∀ m1, sq_heap m1 ==∗
        ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
        ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
          sq_heap m2 ∗ ∃ ds, fp_tokens T ds ∗ (fp_tokens T ds -∗ FPWP e2 @ E {{ Φ }})).
  Proof.
    intros Hv Hext. rewrite fpwp_unfold /fpwp_pre Hv.
    iSplit.
    - iIntros "H" (m) "Hm".
      iMod "H" as "[[_ Hseq] | (%op & %k & %Hcall & _)]".
      + by iApply "Hseq".
      + exfalso. by eapply Hext.
    - iIntros "H !>". iLeft. iFrame. done.
  Qed.

  Lemma fpwp_lift_step E e Φ :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    (∀ m1, sq_heap m1 ==∗
      ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
      ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
        sq_heap m2 ∗ ∃ ds, fp_tokens T ds ∗ (fp_tokens T ds -∗ FPWP e2 @ E {{ Φ }})) ⊢
    FPWP e @ E {{ Φ }}.
  Proof. intros Hv Hext. by rewrite (fpwp_seq_unfold _ _ _ Hv Hext). Qed.

  Lemma fpwp_lift_external E e op k Φ :
    lr_external e op k ->
    (|={E,∅}=> ∃ x : ext_spec_args op,
      ext_spec_pre op x (λ ef, ▷ FPWP ef {{ _, True }}) ∗
      ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> FPWP k ov @ E {{ Φ }})) ⊢
    FPWP e @ E {{ Φ }}.
  Proof.
    intros Hext. rewrite fpwp_unfold /fpwp_pre (lr_external_not_val _ _ _ Hext).
    iIntros "Hspec !>". iRight. iExists op, k. by iFrame.
  Qed.

  Lemma fpwp_ext_unfold E e op k Φ :
    lr_external e op k ->
    FPWP e @ E {{ Φ }} ⊣⊢
      (|={E,∅}=> ∃ x : ext_spec_args op,
        ext_spec_pre op x (λ ef, ▷ FPWP ef {{ _, True }}) ∗
        ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> FPWP k ov @ E {{ Φ }})).
  Proof.
    intros He. iSplit; last by iApply (fpwp_lift_external _ _ _ _ _ He).
    rewrite fpwp_unfold /fpwp_pre (lr_external_not_val _ _ _ He).
    iIntros ">[[%Hno _] | (%op' & %k' & %He' & Hspec)]".
    - exfalso. by eapply Hno.
    - destruct (lr_external_det _ _ _ _ _ He He') as [-> Hk].
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". rewrite -(Hk ov). by iApply "Hcont".
  Qed.

  Lemma fpwp_bind K E e Φ :
    FPWP e @ E {{ v, FPWP fill K (of_val v) @ E {{ Φ }} }} ⊢
    FPWP fill K e @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e). rewrite (fpwp_unfold E e) /fpwp_pre.
    destruct (to_val e) as [v|] eqn:Hv.
    { apply of_to_val in Hv. subst e. iApply bupd_fpwp. }
    rewrite fpwp_unfold /fpwp_pre (fill_not_val _ _ Hv).
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit.
      { iPureIntro. intros op k He.
        destruct (lr_external_fill_inv _ _ _ _ Hv He) as (k' & He' & _).
        by eapply Hno. }
      iIntros (m) "Hm". iMod ("Hseq" with "Hm") as "[%Hr Hstep]".
      iModIntro. iSplit.
      { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
        exists T, (fill K e2), m2. destruct Hs. rewrite -!fill_app. by constructor. }
      iIntros (T e2 m2 Hs).
      inversion Hs as [K' r m0 T0 r' m0' Hh Heq]; subst.
      destruct (fill_decompose K K' e r (lr_head_step_redex_shape _ _ _ _ _ Hh)
        (lr_head_step_not_val _ _ _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
      iDestruct ("Hstep" $! T (fill K'' r') m2 with "[%]") as "Hstep".
      { by constructor. }
      iNext. iMod "Hstep" as "[Hm (%ds & Htok & Hwp)]".
      iModIntro. iFrame "Hm". iExists ds. iFrame "Htok". iIntros "Htok".
      rewrite fill_app. iApply "IH". by iApply "Hwp".
    - destruct (lr_external_fill K _ _ _ He) as (k' & He' & Hk).
      iRight. iExists op, k'. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
      iModIntro. rewrite Hk. by iApply "IH".
  Qed.

  Lemma fpwp_pure_step E e1 e2 Φ :
    @pure_step sq_lang e1 e2 -> ▷ FPWP e2 @ E {{ Φ }} ⊢ FPWP e1 @ E {{ Φ }}.
  Proof.
    intros [Hsafe Hdet].
    assert (Hv : to_val e1 = None).
    { destruct (Hsafe ∅) as (e' & m' & efs & Hs). exact (language.val_stuck _ _ _ _ _ _ Hs). }
    iIntros "Hwp". iApply fpwp_lift_step; first done.
    { destruct (Hsafe ∅) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      intros op k He. by eapply lr_step_external_disjoint. }
    iIntros (m) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (Hsafe m) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      eauto. }
    iIntros (T e' m' Hs).
    destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
    { by apply sq_prim_step_lr_step. }
    iNext. iModIntro. iFrame "Hm". iExists []. iSplit; first by iApply fp_tokens_nil.
    by iIntros "_".
  Qed.

  Lemma fpwp_pure_steps E e1 e2 Φ n :
    nsteps (@pure_step sq_lang) n e1 e2 ->
    ▷^n FPWP e2 @ E {{ Φ }} ⊢ FPWP e1 @ E {{ Φ }}.
  Proof.
    induction 1 as [e | n e1 e2 e3 Hs Hsteps IH]; first done.
    simpl. iIntros "H". iApply (fpwp_pure_step _ _ _ _ Hs).
    iNext. by iApply IH.
  Qed.

  (** The access rules hand over exactly the points-to they use. *)
  Lemma fpwp_read_na E l q v :
    l ↦{q} v -∗ FPWP (Read Na1Ord (Lit (LitLoc l))) @ E
      {{ w, ⌜w = v⌝ ∗ l ↦{q} v }}.
  Proof.
    iIntros "Hl". iApply fpwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m) "Hm".
    iDestruct (sq_heap_read with "Hm Hl") as %Hl.
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRReadNaS. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. simplify_map_eq. iNext.
    iModIntro. iFrame "Hm". iExists [(q, v)]. rewrite /fp_tokens /=.
    iFrame "Hl". iIntros "[Hl _]". iApply fpwp_value. by iFrame.
  Qed.

  Lemma fpwp_write_na E l v v' :
    l ↦ v -∗ FPWP (Write Na1Ord (Lit (LitLoc l)) (of_val v')) @ E
      {{ _, l ↦ v' }}.
  Proof.
    iIntros "Hl". iApply fpwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m) "Hm".
    iDestruct (sq_heap_read with "Hm Hl") as %Hl.
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []).
      econstructor; [apply to_of_val | exact Hl]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst.
    match goal with H : to_val (of_val _) = Some _ |- _ =>
      rewrite to_of_val in H; injection H as <- end.
    iNext. iMod (sq_heap_write with "Hm Hl") as "[Hm Hl]".
    iModIntro. iFrame "Hm". iExists [(1%Qp, v')]. rewrite /fp_tokens /=.
    iFrame "Hl". iIntros "[Hl _]". by iApply (fpwp_value _ (LitV LitPoison)).
  Qed.

  Lemma fpwp_alloc E Φ :
    (▷ ∀ l, l ↦ LitV LitPoison -∗ †l…1 -∗ Φ (LitV (LitLoc l))) -∗
    FPWP (Alloc (Lit (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply fpwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
      do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext.
    iMod (sq_heap_alloc _ _ 1 with "Hm") as "[Hm [Hfree Hl]]"; [lia | done | ].
    rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
    iModIntro. iFrame "Hm". iExists [(1%Qp, LitV LitPoison)].
    rewrite /fp_tokens /=. iSplit; first done. iIntros "_".
    iApply (fpwp_value _ (LitV (LitLoc l))). iApply ("HΦ" with "Hl Hfree").
  Qed.
End fpwp.

(** Deallocation hands over no token: after the step the cells are no longer
    in memory, which already excludes every conflicting pending access. *)
Section fpwp_free.
  Context `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ}.

  Lemma fp_tokens_free l n :
    ⊢ fp_tokens (lr_free_events l n) (replicate n (1%Qp, LitV LitPoison)).
  Proof.
    revert l. induction n as [|n IH]=> l; first by iApply fp_tokens_nil.
    rewrite /fp_tokens /=. iSplit; first done. iApply IH.
  Qed.

  Lemma fpwp_free E (n : Z) l vl :
    n = length vl ->
    l ↦∗ vl -∗ †l…(length vl) -∗
    FPWP (Free (Lit (LitInt n)) (Lit (LitLoc l))) @ E {{ _, True }}.
  Proof.
    iIntros (Hn) "Hl Hf". iApply fpwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m) "Hm".
    iMod (sq_heap_free _ _ _ n Hn with "Hm Hl Hf") as "(%Hpos & %Hdom & Hm)".
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRFreeS. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext. iModIntro. iFrame "Hm".
    iExists (replicate (Z.to_nat (length vl)) (1%Qp, LitV LitPoison)).
    iSplitR; first by iApply fp_tokens_free. iIntros "_".
    by iApply (fpwp_value _ (LitV LitPoison)).
  Qed.
End fpwp_free.

(** ** Derived rules used by the examples *)

Section fpwp_derived.
  Context `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ}.

  Lemma fpwp_wand E e Φ Ψ :
    FPWP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ FPWP e @ E {{ Ψ }}.
  Proof.
    iLöb as "IH" forall (e). iIntros "Hwp HΦ".
    rewrite !(fpwp_unfold E e) /fpwp_pre.
    destruct (to_val e) as [v|].
    { iMod "Hwp". iModIntro. by iApply "HΦ". }
    iMod "Hwp" as "[[%Hno Hseq] | (%op & %k & %He & Hspec)]"; iModIntro.
    - iLeft. iSplit; first done. iIntros (m) "Hm".
      iMod ("Hseq" with "Hm") as "[$ Hstep]". iModIntro.
      iIntros (T e2 m2 Hs). iSpecialize ("Hstep" $! T e2 m2 with "[//]"). iNext.
      iMod "Hstep" as "[Hm (%ds & Htok & Hwp)]". iModIntro. iFrame "Hm".
      iExists ds. iFrame "Htok". iIntros "Htok".
      iApply ("IH" with "[Hwp Htok] HΦ"). by iApply "Hwp".
    - iRight. iExists op, k. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp". iModIntro.
      iApply ("IH" with "Hwp HΦ").
  Qed.

  Lemma fpwp_atomic_ext E1 E2 e op k Φ :
    lr_external e op k ->
    (forall x ov, ext_spec_post op x ov ⊢ ⌜is_Some (to_val (k ov))⌝) ->
    (|={E1,E2}=> FPWP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
      FPWP e @ E1 {{ Φ }}.
  Proof.
    intros He Ha. iIntros "Hwp".
    iApply (fpwp_lift_external _ _ _ _ _ He).
    iMod "Hwp" as "Hwp".
    iEval (rewrite (fpwp_ext_unfold _ _ _ _ _ He)) in "Hwp".
    iMod "Hwp" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
    iNext. iIntros (ov) "Hpost".
    iDestruct (Ha with "Hpost") as %[v Hv].
    iMod ("Hcont" with "Hpost") as "Hwp".
    apply of_to_val in Hv as <-. rewrite !fpwp_value_bupd.
    iMod "Hwp" as ">HΦ". by iModIntro.
  Qed.
End fpwp_derived.

From iris.proofmode Require Import coq_tactics reduction.

Lemma tac_fpwp_bind `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} K Δ E Φ e :
  envs_entails Δ (FPWP e @ E {{ v, FPWP fill K (of_val v) @ E {{ Φ }} }})%I ->
  envs_entails Δ (FPWP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. apply fpwp_bind. Qed.

Lemma tac_fpwp_pure `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} K Δ Δ' E e1 e2 φ n Φ :
  @PureExec sq_lang φ n e1 e2 -> φ ->
  MaybeIntoLaterNEnvs n Δ Δ' ->
  envs_entails Δ' (FPWP fill K e2 @ E {{ Φ }}) ->
  envs_entails Δ (FPWP fill K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => Hexec Hφ ? HΔ.
  rewrite into_laterN_env_sound HΔ. apply fpwp_pure_steps.
  exact (@pure_step_nsteps_ctx sq_lang (@ectx_language.fill sq_ectx_lang K)
    (@ectx_lang_ctx sq_ectx_lang K) n e1 e2 (Hexec Hφ)).
Qed.

Tactic Notation "fpwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (fpwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; apply (tac_fpwp_bind K); simpl)
  end.

Tactic Notation "fpwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (fpwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; eapply (tac_fpwp_pure K);
    [simpl; tc_solve | try done | tc_solve | simpl_subst])
  end.

(** The SC external rules, with the same contracts as for EXWP. *)
Section fp_concurrent_rules.
  Context `{!lrSqGS Σ}.
  Local Existing Instance lr_ext_specs.

  Lemma fp_conc_wp_read_sc E l q v :
    {{{ ▷ l ↦{q} v }}} FPWP (Read ScOrd (Lit $ LitLoc l) : sq_expr) @ E
    {{{ RET (v : sq_val); l ↦{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iApply (fpwp_lift_external _ _ (ALoad tt l) lr_result_expr).
    { apply (LREctxExternal []). constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists (q, v). simpl. iFrame "Hl".
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply fpwp_value. by iApply "HΦ".
  Qed.

  Lemma fp_conc_wp_write_sc E l (e : sq_expr) v v' :
    IntoVal e v ->
    {{{ ▷ l ↦ v' }}} FPWP (Write ScOrd (Lit $ LitLoc l) e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); l ↦ v }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    assert (Hv : to_val e = Some v).
    { rewrite -(@into_val sq_lang e v Hval). apply to_of_val. }
    iApply (fpwp_lift_external _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). by constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists v'. simpl. iFrame "Hl".
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply (fpwp_value _ (LitV LitPoison)). by iApply "HΦ".
  Qed.

  Lemma fp_conc_wp_cas_int E l z_exp (e_new : sq_expr) lit_new z_cur :
    IntoVal e_new (LitV lit_new) ->
    {{{ ▷ l ↦ LitV (LitInt z_cur) }}}
      FPWP (CAS (Lit $ LitLoc l) (Lit $ LitInt z_exp) e_new : sq_expr) @ E
    {{{ RET (LitV (lit_of_bool (bool_decide (z_cur = z_exp))) : sq_val);
        l ↦ (if decide (z_cur = z_exp) then LitV lit_new else LitV (LitInt z_cur)) }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    assert (Hv : to_val e_new = Some (LitV lit_new)).
    { rewrite -(@into_val sq_lang e_new (LitV lit_new) Hval). apply to_of_val. }
    iApply (fpwp_lift_external _ _
      (ACAS tt l (LitV (LitInt z_exp)) (LitV lit_new)) lr_result_expr).
    { apply (LREctxExternal []). by constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists (z_cur, z_exp). simpl. iFrame "Hl". iSplit; first done.
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply fpwp_value. by iApply "HΦ".
  Qed.

  Lemma fp_conc_wp_cas_int_suc E l z_exp (e_new : sq_expr) lit_new :
    IntoVal e_new (LitV lit_new) ->
    {{{ ▷ l ↦ LitV (LitInt z_exp) }}}
      FPWP (CAS (Lit $ LitLoc l) (Lit $ LitInt z_exp) e_new : sq_expr) @ E
    {{{ RET (LitV (LitInt 1) : sq_val); l ↦ LitV lit_new }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    iApply (fp_conc_wp_cas_int E l z_exp e_new lit_new z_exp Hval with "Hl").
    rewrite bool_decide_true; last done. rewrite decide_True; last done.
    done.
  Qed.

  Lemma fp_conc_wp_cas_int_fail E l z_exp (e_new : sq_expr) lit_new z_cur :
    IntoVal e_new (LitV lit_new) -> z_exp ≠ z_cur ->
    {{{ ▷ l ↦ LitV (LitInt z_cur) }}}
      FPWP (CAS (Lit $ LitLoc l) (Lit $ LitInt z_exp) e_new : sq_expr) @ E
    {{{ RET (LitV (LitInt 0) : sq_val); l ↦ LitV (LitInt z_cur) }}}.
  Proof.
    intros Hval Hne Φ. iIntros "Hl HΦ".
    iApply (fp_conc_wp_cas_int E l z_exp e_new lit_new z_cur Hval with "Hl").
    rewrite bool_decide_false; last congruence. rewrite decide_False; last congruence.
    done.
  Qed.

  Lemma fp_conc_wp_fork E (e : sq_expr) :
    {{{ ▷ FPWP e {{ _, True }} }}} FPWP (Fork e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); True }}}.
  Proof.
    iIntros (Φ) "He HΦ".
    iApply (fpwp_lift_external _ _ (ASpawn e) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iModIntro. iExists (). simpl. iFrame "He".
    iNext. iIntros (ov) "->". iMod "Hclose" as "_".
    iModIntro. iApply (fpwp_value _ (LitV LitPoison)). iApply "HΦ". done.
  Qed.

  Lemma fpwp_read_sc_atomic E1 E2 l Φ :
    (|={E1,E2}=> FPWP (Read ScOrd (Lit (LitLoc l))) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    FPWP (Read ScOrd (Lit (LitLoc l))) @ E1 {{ Φ }}.
  Proof.
    eapply (fpwp_atomic_ext _ _ _ (ALoad tt l) lr_result_expr).
    - apply (LREctxExternal []). constructor.
    - intros [q v] ov. simpl. iIntros "[-> _]".
      iPureIntro. exists v. apply to_of_val.
  Qed.

  Lemma fpwp_write_sc_atomic E1 E2 l v Φ :
    (|={E1,E2}=> FPWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    FPWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E1 {{ Φ }}.
  Proof.
    eapply (fpwp_atomic_ext _ _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
    - apply (LREctxExternal []). constructor. apply to_of_val.
    - intros x ov. iIntros "_". eauto.
  Qed.

  Lemma fpwp_cas_atomic E1 E2 l lit_exp lit_new Φ :
    (|={E1,E2}=> FPWP (CAS (Lit (LitLoc l)) (Lit lit_exp) (Lit lit_new)) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    FPWP (CAS (Lit (LitLoc l)) (Lit lit_exp) (Lit lit_new)) @ E1 {{ Φ }}.
  Proof.
    eapply (fpwp_atomic_ext _ _ _
      (ACAS tt l (LitV lit_exp) (LitV lit_new)) lr_result_expr).
    - apply (LREctxExternal []). by constructor.
    - intros [z_cur z_exp] ov. simpl. iIntros "[-> _]".
      iPureIntro. eexists. apply to_of_val.
  Qed.
End fp_concurrent_rules.
