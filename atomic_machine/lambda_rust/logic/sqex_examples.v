(** Examples for EXWP and their adequacy on the atomic machine.

    - [two_increments]: two threads increment a shared cell with CAS; the
      parent waits until it observes both increments and returns 2.
    - [shared_reads]: two fractional owners read the same location in
      separate threads, one atomically and one non-atomically. Both are
      reads, so they do not race. *)
From iris.proofmode Require Import proofmode.
From lrust.lang Require Import notation tactics.
From iris.base_logic.lib Require Import invariants.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_lr_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Local Existing Instance lrSqGS_invGS.

(** ** Programs *)

Definition sc_increment_loop : expr :=
  (rec: "inc" ["l"] :=
    let: "n" := !ˢᶜ "l" in
    if: CAS "l" "n" ("n" + #1)
    then #☠ else "inc" ["l"])%E.

Definition sc_increment (p : expr) : expr := sc_increment_loop [p].

Definition wait_for_two_loop : expr :=
  (rec: "wait" ["l"] :=
    let: "n" := !ˢᶜ "l" in
    if: "n" = #2 then "n" else "wait" ["l"])%E.

Definition wait_for_two (p : expr) : expr := wait_for_two_loop [p].

Definition two_increments : expr :=
  (let: "l" := Alloc #1 in
   "l" <-ˢᶜ #0 ;;
   Fork (sc_increment "l") ;;
   sc_increment "l" ;;
   wait_for_two "l")%E.

Definition counterN : namespace := nroot .@ "sqex_counter".

Definition counter_inv `{!lrSqGS Σ} (l : loc) : iProp Σ :=
  ∃ n : Z, ⌜0 ≤ n⌝ ∗ l ↦ #n.

Definition shared_reads : expr :=
  (let: "l" := Alloc #1 in
   "l" <- #7 ;;
   Fork (!ˢᶜ "l") ;;
   ! "l")%E.

(** The read runs under an application context, so its successor is a
    non-final beta redex before the same cell is written. *)
Definition na_read_then_write (l : loc) : expr :=
  App (Rec BAnon [BAnon] (Write Na1Ord (Lit (LitLoc l)) (Lit (LitInt 8))))
    [Read Na1Ord (Lit (LitLoc l))].

(** ** Proofs *)

Section proofs.
  Context `{!lrSqGS Σ}.

  Lemma na_read_then_write_spec E l :
    {{{ l ↦ LitV (LitInt 7) }}} EXWP na_read_then_write l @ E
    {{{ RET (LitV LitPoison : val); l ↦ LitV (LitInt 8) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". rewrite /na_read_then_write.
    exwp_bind (Read _ _).
    iApply (exwp_read_na with "Hl"). iNext. iIntros "Hl".
    exwp_pure (App _ _).
    iApply (exwp_write_na _ _ (LitV (LitInt 7)) (LitV (LitInt 8)) with "Hl").
    iIntros "!> Hl". by iApply "HΦ".
  Qed.

  Lemma sc_increment_spec l Φ :
    inv counterN (counter_inv l) -∗ ▷ Φ #☠ -∗
    EXWP sc_increment #l {{ Φ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /sc_increment. iLöb as "IH".
    iIntros "HΦ". rewrite /sc_increment_loop. exwp_pure (App _ _).
    exwp_bind (Read _ _).
    iApply (exwp_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (conc_wp_read_sc with "[Hl]"); first iExact "Hl".
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro.
    exwp_pure (App _ _).
    exwp_pure (BinOp _ _ _).
    exwp_bind (CAS _ _ _).
    iApply (exwp_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n') "[>%Hn' Hl]".
    destruct (decide (n' = n)) as [->|Hneq].
    - iModIntro. iApply (conc_wp_cas (b := true) with "[Hl]").
      { iNext. iSplitL ""; last iExact "Hl".
        iExists n, n. by rewrite bool_decide_true. }
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists (n + 1). iFrame. iPureIntro. lia. }
      iModIntro. exwp_pure (Case _ _).
      by iApply exwp_value'.
    - iModIntro. iApply (conc_wp_cas (b := false) with "[Hl]").
      { iNext. iSplitL ""; last iExact "Hl".
        iExists n', n. by rewrite bool_decide_false. }
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists n'. iFrame. done. }
      iModIntro. exwp_pure (Case _ _). iApply "IH". by iNext.
  Qed.

  Lemma wait_for_two_spec l :
    inv counterN (counter_inv l) -∗
    EXWP wait_for_two #l {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /wait_for_two. iLöb as "IH".
    rewrite /wait_for_two_loop. exwp_pure (App _ _).
    exwp_bind (Read _ _).
    iApply (exwp_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (conc_wp_read_sc with "[Hl]"); first iExact "Hl".
    iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro. exwp_pure (App _ _). exwp_pure (BinOp _ _ _).
    case_bool_decide as Hn2; exwp_pure (Case _ _).
    - iApply exwp_value'. iPureIntro. by subst n.
    - iApply "IH".
  Qed.

  Lemma two_increments_spec :
    ⊢ EXWP two_increments {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    rewrite /two_increments /sc_increment /wait_for_two
      /sc_increment_loop /wait_for_two_loop.
    exwp_bind (Alloc _).
    iApply exwp_alloc. iIntros "!>" (l) "Hl _".
    exwp_pure (App _ _).
    exwp_bind (Write _ _ _).
    iApply (exwp_atomic _ ⊤).
    iModIntro. iApply (conc_wp_write_sc with "[Hl]"); first by iNext.
    iNext. iIntros "Hl".
    (* Initialization is an external call, so its postcondition can allocate
       the invariant before the following ordinary computation and fork. *)
    iMod (inv_alloc counterN _ (counter_inv l) with "[Hl]") as "#Hinv".
    { iNext. iExists 0. iFrame. done. }
    iModIntro. exwp_pure (App _ _).
    exwp_bind (Fork _).
    iApply (conc_wp_fork with "[]").
    { iNext. iApply (sc_increment_spec with "Hinv"). done. }
    iNext. iIntros "_". exwp_pure (App _ _).
    exwp_bind (App sc_increment_loop _).
    iApply (sc_increment_spec with "Hinv"). iNext.
    exwp_pure (App _ _). by iApply wait_for_two_spec.
  Qed.

  Lemma shared_reads_spec :
    ⊢ EXWP shared_reads {{ v, ⌜v = #7⌝ }}.
  Proof.
    rewrite /shared_reads. exwp_bind (Alloc _).
    iApply exwp_alloc. iIntros "!>" (l) "Hl _".
    exwp_pure (App _ _). exwp_bind (Write _ _ _).
    iApply (exwp_write_na _ _ (LitV LitPoison) (LitV (LitInt 7)) with "Hl").
    iIntros "!> Hl". exwp_pure (App _ _).
    iDestruct "Hl" as "[Hchild Hparent]".
    exwp_bind (Fork _). iApply (conc_wp_fork with "[Hchild]").
    - (* The child reads atomically. *)
      iNext. iApply (conc_wp_read_sc with "[Hchild]"); first iExact "Hchild". by iIntros "!> _".
    - (* The parent reads non-atomically. *)
      iNext. iIntros "_". exwp_pure (App _ _).
      iApply (exwp_read_na with "Hparent"). by iIntros "!> _".
  Qed.

End proofs.

Corollary two_increments_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [two_increments] [(fun v => v = #2)] m.
Proof. apply (sqex_adequacy Σ). intros. apply two_increments_spec. Qed.

Corollary shared_reads_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [shared_reads] [(fun v => v = #7)] m.
Proof. apply (sqex_adequacy Σ). intros. apply shared_reads_spec. Qed.
