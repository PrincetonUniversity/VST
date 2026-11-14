(** The EXWP examples [sqex_increment.v] and [sqex_shared_reads.v], verified
    in FPWP with the same rule interfaces. Their adequacy follows from
    [sqfp_adequacy], whose proof stays inside the logic. *)
From lrust.lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
Require Import VST.atomic_machine.lambda_rust.logic.sqfp_adequacy.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_increment.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_shared_reads.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_global_view.
(** Only for the statement [at_sem_adequate]. *)
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Set Default Proof Using "Type".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

Section proofs.
  Context `{!lrSqGS Σ}.

  Lemma fp_sc_increment_spec l Φ :
    inv counterN (counter_inv l) -∗ ▷ Φ #☠ -∗
    FPWP sc_increment #l {{ Φ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /sc_increment. iLöb as "IH".
    iIntros "HΦ". rewrite /sc_increment_loop. fpwp_pure (App _ _).
    fpwp_bind (Read _ _).
    iApply (fpwp_read_sc_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (fp_conc_wp_read_sc with "Hl").
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro.
    fpwp_pure (App _ _).
    fpwp_pure (BinOp _ _ _).
    fpwp_bind (CAS _ _ _).
    iApply (fpwp_cas_atomic _ (⊤ ∖ ↑counterN) _ (LitInt n) (LitInt (n + 1))).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n') "[>%Hn' Hl]".
    destruct (decide (n' = n)) as [->|Hneq].
    - iModIntro. iApply (fp_conc_wp_cas_int_suc with "Hl").
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists (n + 1). iFrame. iPureIntro. lia. }
      iModIntro. fpwp_pure (Case _ _).
      by iApply (fpwp_value _ (LitV LitPoison)).
    - iModIntro. iApply (fp_conc_wp_cas_int_fail with "Hl"); first congruence.
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists n'. iFrame. done. }
      iModIntro. fpwp_pure (Case _ _). iApply "IH". by iNext.
  Qed.

  Lemma fp_wait_for_two_spec l :
    inv counterN (counter_inv l) -∗
    FPWP wait_for_two #l {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /wait_for_two. iLöb as "IH".
    rewrite /wait_for_two_loop. fpwp_pure (App _ _).
    fpwp_bind (Read _ _).
    iApply (fpwp_read_sc_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (fp_conc_wp_read_sc with "Hl").
    iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro. fpwp_pure (App _ _). fpwp_pure (BinOp _ _ _).
    case_bool_decide as Hn2; fpwp_pure (Case _ _).
    - iApply (fpwp_value _ (LitV (LitInt n))). iPureIntro. by subst n.
    - iApply "IH".
  Qed.

  Lemma fp_two_increments_spec :
    ⊢ FPWP two_increments {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    rewrite /two_increments /sc_increment /wait_for_two
      /sc_increment_loop /wait_for_two_loop.
    fpwp_bind (Alloc _).
    iApply fpwp_alloc. iNext. iIntros (l) "Hl _".
    fpwp_pure (App _ _).
    fpwp_bind (Write _ _ _).
    iApply (fpwp_write_sc_atomic _ ⊤ _ #0).
    iModIntro. iApply (fp_conc_wp_write_sc with "[Hl]"); first by iNext.
    iNext. iIntros "Hl".
    (* Initialization is an external call, so its postcondition can allocate
       the invariant before the following ordinary computation and fork. *)
    iMod (inv_alloc counterN _ (counter_inv l) with "[Hl]") as "#Hinv".
    { iNext. iExists 0. iFrame. done. }
    iModIntro. fpwp_pure (App _ _).
    fpwp_bind (Fork _).
    iApply (fp_conc_wp_fork with "[]").
    { iNext. iApply (fp_sc_increment_spec with "Hinv"). done. }
    iNext. iIntros "_". fpwp_pure (App _ _).
    fpwp_bind (App sc_increment_loop _).
    iApply (fp_sc_increment_spec with "Hinv"). iNext.
    fpwp_pure (App _ _). by iApply fp_wait_for_two_spec.
  Qed.

  Lemma fp_shared_reads_spec :
    ⊢ FPWP shared_reads {{ v, ⌜v = #7⌝ }}.
  Proof.
    rewrite /shared_reads. fpwp_bind (Alloc _).
    iApply fpwp_alloc. iNext. iIntros (l) "Hl _".
    fpwp_pure (App _ _). fpwp_bind (Write _ _ _).
    iApply (fpwp_wand with "[Hl]").
    { by iApply (fpwp_write_na _ l (LitV LitPoison) (LitV (LitInt 7)) with "Hl"). }
    iIntros (ignored) "Hl". fpwp_pure (App _ _).
    iDestruct "Hl" as "[Hchild Hparent]".
    fpwp_bind (Fork _). iApply (fp_conc_wp_fork with "[Hchild]").
    - iNext. iApply (fpwp_wand with "[Hchild]").
      + by iApply (fpwp_read_na with "Hchild").
      + auto.
    - iNext. iIntros "_". fpwp_pure (App _ _).
      iApply (fpwp_wand with "[Hparent]").
      + by iApply (fpwp_read_na with "Hparent").
      + iIntros (v) "[$ _]".
  Qed.
End proofs.

Corollary fp_two_increments_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [two_increments] [(fun v => v = #2)] m.
Proof. apply (sqfp_adequacy Σ). intros. apply fp_two_increments_spec. Qed.

Corollary fp_shared_reads_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [shared_reads] [(fun v => v = #7)] m.
Proof. apply (sqfp_adequacy Σ). intros. apply fp_shared_reads_spec. Qed.

(** The racy program of [sqex_global_view.v] is rejected by FPWP as well. *)
Corollary race_prog_not_fpwp Σ `{!lrSqGpreS Σ} :
  ¬ (forall `{!lrSqGS Σ}, ⊢ FPWP race_prog {{ _, True }}).
Proof. intros Hwp. apply race_prog_unsafe. by apply (sqfp_adequacy Σ). Qed.
