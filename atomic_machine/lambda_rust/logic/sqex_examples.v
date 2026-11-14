(** Examples for EXWP and their adequacy on the atomic machine.

    - [two_increments]: two threads increment a shared cell with CAS; the
      parent waits until it observes both increments and returns 2.
    - [shared_reads]: two fractional owners perform non-atomic reads in
      separate threads, so both reads may be between Try and Commit
      simultaneously.
    - [race_prog]: a non-atomic read races with a non-atomic write. It is
      unsafe on the atomic machine ([race_prog_unsafe]), so EXWP cannot
      verify it ([race_prog_not_exwp]). *)
From iris.proofmode Require Import proofmode.
From lrust.lang Require Import notation tactics.
From iris.base_logic.lib Require Import invariants.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.at_logic.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

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

Definition two_increments : sq_expr :=
  (let: "l" := Alloc #1 in
   "l" <-ˢᶜ #0 ;;
   Fork (sc_increment "l") ;;
   sc_increment "l" ;;
   wait_for_two "l")%E.

Definition counterN : namespace := nroot .@ "sqex_counter".

Definition counter_inv `{!lrSqGS Σ} (l : loc) : iProp Σ :=
  ∃ n : Z, ⌜0 ≤ n⌝ ∗ l ↦ #n.

Definition shared_reads : sq_expr :=
  (let: "l" := Alloc #1 in
   "l" <- #7 ;;
   Fork (! "l") ;;
   ! "l")%E.

(** The parent allocates [l], hands [l ↦ ☠] to a child that writes it
    non-atomically, and then reads [l] non-atomically. *)
Definition race_body : expr := (Fork ("l" <- #1) ;; !"l")%E.
Definition race_prog : sq_expr := (let: "l" := Alloc #1 in race_body)%E.

(** ** Proofs *)

Section proofs.
  Context `{!lrSqGS Σ}.

  Lemma sc_increment_spec l Φ :
    inv counterN (counter_inv l) -∗ ▷ Φ #☠ -∗
    EXWP sc_increment #l {{ Φ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /sc_increment. iLöb as "IH".
    iIntros "HΦ". rewrite /sc_increment_loop. exwp_pure (App _ _).
    exwp_bind (Read _ _).
    iApply (exwp_read_sc_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (conc_wp_read_sc with "Hl").
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro.
    exwp_pure (App _ _).
    exwp_pure (BinOp _ _ _).
    exwp_bind (CAS _ _ _).
    iApply (exwp_cas_atomic _ (⊤ ∖ ↑counterN) _ (LitInt n) (LitInt (n + 1))).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n') "[>%Hn' Hl]".
    destruct (decide (n' = n)) as [->|Hneq].
    - iModIntro. iApply (conc_wp_cas_int_suc with "Hl").
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists (n + 1). iFrame. iPureIntro. lia. }
      iModIntro. exwp_pure (Case _ _).
      by iApply (exwp_value _ (LitV LitPoison)).
    - iModIntro. iApply (conc_wp_cas_int_fail with "Hl"); first congruence.
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
    iApply (exwp_read_sc_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (conc_wp_read_sc with "Hl").
    iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro. exwp_pure (App _ _). exwp_pure (BinOp _ _ _).
    case_bool_decide as Hn2; exwp_pure (Case _ _).
    - iApply (exwp_value _ (LitV (LitInt n))). iPureIntro. by subst n.
    - iApply "IH".
  Qed.

  Lemma two_increments_spec :
    ⊢ EXWP two_increments {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    rewrite /two_increments /sc_increment /wait_for_two
      /sc_increment_loop /wait_for_two_loop.
    exwp_bind (Alloc _).
    iApply exwp_alloc. iNext. iIntros (l) "Hl _".
    exwp_pure (App _ _).
    exwp_bind (Write _ _ _).
    iApply (exwp_write_sc_atomic _ ⊤ _ #0).
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
    iApply exwp_alloc. iNext. iIntros (l) "Hl _".
    exwp_pure (App _ _). exwp_bind (Write _ _ _).
    iApply (exwp_wand with "[Hl]").
    { by iApply (exwp_write_na _ l (LitV LitPoison) (LitV (LitInt 7)) with "Hl"). }
    iIntros (ignored) "Hl". exwp_pure (App _ _).
    iDestruct "Hl" as "[Hchild Hparent]".
    exwp_bind (Fork _). iApply (conc_wp_fork with "[Hchild]").
    - iNext. iApply (exwp_wand with "[Hchild]").
      + by iApply (exwp_read_na with "Hchild").
      + auto.
    - iNext. iIntros "_". exwp_pure (App _ _).
      iApply (exwp_wand with "[Hparent]").
      + by iApply (exwp_read_na with "Hparent").
      + iIntros (v) "[$ _]".
  Qed.
End proofs.

Corollary two_increments_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [two_increments] [(fun v => v = #2)] m.
Proof. apply (sqex_adequacy Σ). intros. apply two_increments_spec. Qed.

Corollary shared_reads_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [shared_reads] [(fun v => v = #7)] m.
Proof. apply (sqex_adequacy Σ). intros. apply shared_reads_spec. Qed.



(** ** The racy program is unsafe on the atomic machine *)

Definition race_loc : loc := (1%positive, 0%Z).
Definition race_read : expr := Read Na1Ord (Lit (LitLoc race_loc)).
Definition race_write : expr := Write Na1Ord (Lit (LitLoc race_loc)) (Lit (LitInt 1)).
Definition race_main1 : expr := App (Rec BAnon [BNamed "l"] race_body) [Lit (LitLoc race_loc)].
Definition race_main2 : expr := App (Rec BAnon [BAnon] race_read) [Fork race_write].
Definition race_main3 : expr := App (Rec BAnon [BAnon] race_read) [Lit LitPoison].
Local Instance race_body_closed : Closed (BAnon :b: [BNamed "l"] +b+ []) race_body.
Proof. by vm_compute. Qed.
Local Instance race_read_closed : Closed (BAnon :b: [BAnon] +b+ []) race_read.
Proof. by vm_compute. Qed.

Definition race_mem1 : lr_mem := alloc_gmap (LitV LitPoison) race_loc (Z.to_nat 1) ∅.
Definition race_mem2 : lr_mem := <[race_loc := LitV (LitInt 1)]> race_mem1.

(** The child's write is pending when the parent reaches its read. *)
Lemma race_prog_reaches_race :
  exists tp mu,
    am_steps (AMCfg (sqex_pool [race_prog]) ∅ (sq_mu ∅)) (AMCfg tp race_mem2 mu) /\
    tp !! 0%nat = Some (Running race_read []) /\ mu !! race_loc = Some Wst.
Proof.
  eexists _, _. split; [|split].
  - (* Parent: Try the allocation. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 0%nat race_prog (lr_alloc_events race_loc (Z.to_nat 1))
        race_main1 race_mem1).
      - by vm_compute.
      - change race_prog with (fill [LetCtx (BNamed "l") race_body] (Alloc (Lit (LitInt 1)))).
        change race_main1 with (fill [LetCtx (BNamed "l") race_body] (Lit (LitLoc race_loc))).
        apply LREctxStep. apply LRAllocS; [lia | done].
      - reflexivity. }
    (* Parent: Commit the allocation. *)
    eapply rtc_l.
    { eapply (Core_Commit _ _ _ 0%nat race_main1).
      - by rewrite lookup_insert_eq.
      - done.
      - reflexivity. }
    (* Parent: beta-reduce the [let]. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 0%nat race_main1 [] race_main2 race_mem1).
      - by rewrite lookup_insert_eq.
      - apply (LREctxStep [] race_main1). apply LRBetaS.
        + by repeat constructor.
        + apply _.
        + by vm_compute.
      - reflexivity. }
    (* Parent: spawn the child as thread 1. *)
    eapply rtc_l.
    { eapply (Spawn _ _ _ 0%nat race_main2 race_write
        (fun ov => fill [AppRCtx (LamV [BAnon] race_read) [] []]
          ((fun _ => Lit LitPoison) ov)) 1%nat).
      - by rewrite lookup_insert_eq.
      - change race_main2 with
          (fill [AppRCtx (LamV [BAnon] race_read) [] []] (Fork race_write)).
        apply LREctxExternal. constructor.
      - by vm_compute.
      - intros k Hk. assert (k = 0%nat) as -> by lia. by rewrite lookup_insert_eq. }
    (* Parent: beta-reduce the sequence. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 0%nat race_main3 [] race_read race_mem1).
      - by vm_compute.
      - apply (LREctxStep [] race_main3). apply LRBetaS.
        + by repeat constructor.
        + apply _.
        + by vm_compute.
      - reflexivity. }
    (* Child: Try the non-atomic write; it reserves [race_loc] as [Wst]. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 1%nat race_write [lr_write_event race_loc]
        (Lit LitPoison) race_mem2).
      - by vm_compute.
      - apply (LREctxStep [] race_write).
        apply (LRWriteNaS _ _ _ (LitV LitPoison)); by vm_compute.
      - reflexivity. }
    apply rtc_refl.
  - by vm_compute.
  - by vm_compute.
Qed.

(** A non-atomic read of a location with a pending write cannot step. *)
Lemma race_read_stuck m mu :
  mu !! race_loc = Some Wst -> ¬ am_not_stuck (Running race_read []) m mu.
Proof.
  intros Hmu [(c & Heq & Hfinal) | (q' & Hstep)].
  - injection Heq as <-. destruct Hfinal as [v Hv]. discriminate.
  - inversion Hstep; subst; unfold tpool in *;
      apply lookup_singleton_Some in Hget as [_ Hget]; inversion Hget; subst;
      unfold race_read in *; try done;
      try (match goal with H : sqlang_at_external _ _ _ |- _ =>
        apply lr_external_head in H; [inversion H | solve_redex_shape] end).
    match goal with H : sqlang_step _ _ _ _ _ |- _ => rename H into Hseq end.
    apply lr_step_head in Hseq; last solve_redex_shape.
    inversion Hseq; subst. simpl in Hreserve.
    rewrite /rsv /= /rsv_Read Hmu in Hreserve. discriminate.
Qed.

Theorem race_prog_unsafe : ¬ at_sem_adequate [race_prog] [λ _, True] ∅.
Proof.
  intros Hadeq. destruct race_prog_reaches_race as (tp & mu & Hsteps & Hmain & Hmu).
  destruct (Hadeq _ _ _ Hsteps) as [Hsafe _].
  exact (race_read_stuck _ _ Hmu (Hsafe _ _ Hmain)).
Qed.

(** Hence EXWP cannot verify the racy program. *)
Corollary race_prog_not_exwp Σ `{!lrSqGpreS Σ} :
  ¬ (forall `{!lrSqGS Σ}, ⊢ EXWP race_prog {{ _, True }}).
Proof. intros Hwp. apply race_prog_unsafe. by apply (sqex_adequacy Σ). Qed.
