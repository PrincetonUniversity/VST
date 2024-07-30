From VST.typing Require Export type.
From VST.typing Require Import programs boolean int.
From VST.typing Require Import type_options.

Definition atomic_boolN : namespace := nroot.@"atomic_boolN".
Section atomic_bool.
  Context `{!typeG Σ} {cs : compspecs}.

  Program Definition atomic_bool (it : Ctypes.type) (PT PF : mpred) : type := {|
    (* ty_has_op_type ot mt := is_bool_ot ot it StrictBool; *)
    ty_has_op_type ot mt := (*is_bool_ot ot it stn*) ot = it;
    ty_own β l :=
      match β return _ with
      | Own => ∃ b, l ◁ₗ b @ boolean it ∗ if b then PT else PF
      | Shr => <affine> ⌜field_compatible it [] l⌝  ∗
               inv atomic_boolN (∃ b, l ◁ₗ b @ boolean it ∗ if b then PT else PF)
      end;
    ty_own_val v := ∃ b, v ◁ᵥ b @ boolean it ∗ if b then PT else PF;
  |}%I.
  Next Obligation.
    iIntros (??????) "H".
    iDestruct "H" as (b) "(H1 & H2)".
    Check with_refinement .
    Check ty_aligned _ _ MCNone .
    iDestruct (ty_aligned _ _ MCNone with "[$H1]") as %?; [done |].
    iSplitR => //.
    iApply inv_alloc. iNext. iExists b. iFrame.
  Qed.
  Next Obligation. iIntros (???????) "[% [Hb _]]". by iApply (ty_aligned with "Hb"). Qed.
  Next Obligation.
    iIntros (???????) "[% [Hb ?]]".
    iDestruct (ty_deref with "Hb") as (?) "[? ?]"; [done|].
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (?????????) "Hl [%b [Hb ?]]".
    iDestruct (ty_ref with "[] Hl Hb") as "?" => //.
    iExists b. iFrame.
  Qed.

  (*
  Global Instance alloc_alive_atomic_bool it β PT PF:
    AllocAlive (atomic_bool it PT PF) β True.
  Proof.
    constructor. have ?:= bytes_per_int_gt_0 it. destruct β.
    - iIntros (l) "? (%b&Hl&?)". by iApply (alloc_alive_alive with "[] Hl").
    - iIntros (l) "? (%&Hl)".
      iApply (heap_mapsto_alive_strong).
      iInv "Hl" as "(%b&>Hb&?)" "Hclose".
      iApply fupd_mask_intro; [set_solver|]. iIntros "_".
      rewrite /ty_own/=.
      iDestruct "Hb" as "(%v&%n&%&%&%&?)". iExists _, _. iFrame. iPureIntro.
      erewrite val_to_Z_length; [|done]. lia.
  Qed.
*)
  
End atomic_bool.
Notation "atomic_bool< it , PT , PF >" := (atomic_bool it PT PF)
  (only printing, format "'atomic_bool<' it ,  PT ,  PF '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ} {cs : compspecs}.

  Lemma subsume_atomic_bool_own_int A l n it PT PF T:
    (l ◁ₗ n @ int it -∗ ∃ x b, l ◁ₗ b @ boolean it ∗ (if b then PT x else PF x) ∗ T x)
    ⊢ subsume (l ◁ₗ n @ int it) (λ x : A, l ◁ₗ atomic_bool it (PT x) (PF x)) T.
  Proof.
    iIntros "HT Hl". iDestruct ("HT" with "Hl") as (??) "[? [? ?]]". by iFrame.
  Qed.
  Definition subsume_atomic_bool_own_int_inst := [instance subsume_atomic_bool_own_int].
  Global Existing Instance subsume_atomic_bool_own_int_inst.

  Lemma subsume_atomic_bool_own_bool A l (b : bool) it PT PF T:
    (∃ x, (if b then PT x else PF x) ∗ T x)
    ⊢ subsume (l ◁ₗ b @ boolean it) (λ x : A, l ◁ₗ atomic_bool it (PT x) (PF x)) T.
  Proof. iIntros "[% [? ?]] Hl". by iFrame. Qed.
  Definition subsume_atomic_bool_own_bool_inst := [instance subsume_atomic_bool_own_bool].
  Global Existing Instance subsume_atomic_bool_own_bool_inst.

  (*
  Check typed_read_end .
  Lemma type_read_atomic_bool l β it ot PT PF mc T:
    (⌜match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end⌝ ∗
      ∀ b v,
      case_destruct b (λ (b : bool) _,
        (* TODO: Should this have a trace? *)
        (if b then PT else PF) -∗
        (if b then PT else PF) ∗
        T v (atomic_bool it PT PF) (b @ boolean it)))
    ⊢ typed_read_end true ⊤ l β (atomic_bool it PT PF) ot mc T.
  Proof.
    iIntros "[%Hot HT]".
    iApply typed_read_end_mono_strong; [done|]. destruct β.
    - iIntros "[%b [Hl Hif]] !>". iExists _, _, True%I. iFrame. iSplitR; [done|].
      unshelve iApply (type_read_copy with "[HT Hif]"). { apply _. } simpl.
      iSplit; [by destruct ot; simplify_eq/=|]. iSplit; [done|]. iIntros (v) "_ Hl Hv".
      iDestruct ("HT" $! _ _) as (_) "HT".
      iDestruct ("HT" with "Hif") as "[Hif HT]". iExists _, _. iFrame "HT Hv".
      iExists _. by iFrame.
    - iIntros "[%Hly #Hinv] !>".
      iExists Own, tytrue, True%I. iSplit; [done|]. iSplit; [done|].
      iInv "Hinv" as (b) "[>Hl Hif]".
      iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
      iExists _, _, _. iFrame.
      unshelve iApply (type_read_copy with "[-]"). { apply _. } simpl.
      iSplit; [by destruct ot; simplify_eq/=|]. iSplit; [iPureIntro; solve_ndisj|].
      iIntros (v) "Hif Hl #Hv !>".
      iDestruct ("HT" $! _ _) as (_) "HT".
      iDestruct ("HT" with "Hif") as "[Hif HT]". iExists tytrue, tytrue.
      iSplit; [done|]. iSplit; [ done |]. iModIntro.
      iSplitL "Hl Hif". { iExists _. by iFrame. }
      iIntros "_ _ _ !>". iExists _, _. iFrame "∗Hv". by iSplit.
  Qed.
  Definition type_read_atomic_bool_inst := [instance type_read_atomic_bool].
  Global Existing Instance type_read_atomic_bool_inst | 10.

  Lemma type_write_atomic_bool l β it ot PT PF v ty T:
    (v ◁ᵥ ty -∗
     ⌜match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end⌝ ∗
     ∃ b, v ◁ᵥ b @ boolean it ∗ (if b then PT else PF) ∗ T (atomic_bool it PT PF))
    ⊢ typed_write_end true ⊤ ot v ty l β (atomic_bool it PT PF) T.
  Proof.
    iIntros "HT". iApply typed_write_end_mono_strong; [done|].
    iIntros "Hv Hl". iModIntro.
    iDestruct ("HT" with "Hv") as "(%&%x&#Hnew&Hif_new&HT)".
    destruct β.
    - iDestruct "Hl" as "[%bold [Hl Hif_old]]".
      iExists (_ @ boolean it)%I, _, _, True%I. iFrame "∗". iSplitR; [done|]. iSplitR; [done|].
      iApply type_write_own_copy. { by destruct ot; simplify_eq/=. }
      iSplit; [by destruct ot; simplify_eq/=|].
      iIntros "Hv _ Hl !>". iExists _. iFrame "HT". iExists _. by iFrame.
    - iExists tytrue, Own, tytrue, True%I. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
      iDestruct "Hl" as (?) "#Hinv".
      iInv "Hinv" as (b) "[>Hmt Hif]".
      iApply typed_write_end_mono_strong; [done|]. iIntros "_ _". iModIntro.
      iExists _, _, _, True%I. iFrame. iSplitR; [done|]. iSplitR; [done|].
      iApply type_write_own_copy. { by destruct ot; simplify_eq/=. }
      iSplit; [by destruct ot; simplify_eq/=|].
      iIntros "Hv _ Hl !>". iExists tytrue. iSplit; [done|]. iModIntro.
      iSplitL "Hif_new Hl". { iExists _. by iFrame. }
      iIntros "_ _ !>". iExists _. iFrame "HT". by iSplit.
  Qed.
  Definition type_write_atomic_bool_inst := [instance type_write_atomic_bool].
  Global Existing Instance type_write_atomic_bool_inst | 10.

  Lemma type_cas_atomic_bool (l : loc) β ot it PT PF lexp Pexp vnew Pnew T:
    (Pexp -∗ Pnew -∗ ⌜match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end⌝ ∗
      ∃ bexp bnew, lexp ◁ₗ bexp @ boolean it ∗ vnew ◁ᵥ bnew @ boolean it ∗
          ⌜ly_size (ot_layout ot) ≤ bytes_per_addr⌝%nat ∗ (
            ((if bexp then PT else PF) -∗
             (if bnew then PT else PF) ∗ (
                l ◁ₗ{β} atomic_bool it PT PF -∗ lexp ◁ₗ bexp @ boolean it -∗
                T (val_of_bool true) (true @ builtin_boolean))) ∧
            (l ◁ₗ{β} atomic_bool it PT PF -∗
             lexp ◁ₗ negb bexp @ boolean it -∗
             T (val_of_bool false) (false @ builtin_boolean))
           )
        )
    ⊢ typed_cas ot l (l ◁ₗ{β} (atomic_bool it PT PF))%I lexp Pexp vnew Pnew T.
  Proof.
    iIntros "HT Hl Hlexp Hvnew".
    iDestruct ("HT" with "Hlexp Hvnew") as "(%&%bexp&%bnew&Hlexp&#Hvnew&%&Hsub)".
    iIntros (Φ) "HΦ". destruct β.
    - iDestruct "Hl" as (b) "[Hb Hif]".
      destruct (decide (b = bexp)); subst.
      + iApply (wp_cas_suc_boolean with "Hb Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[Hsub _]". iDestruct ("Hsub" with "Hif") as "[Hif HT]".
        iApply "HΦ"; last first.
        * iApply ("HT" with "[Hb Hif] Hexp"). iExists bnew. by iFrame.
        * by iExists _.
      + iApply (wp_cas_fail_boolean with "Hb Hlexp") => //.
        iIntros "!# Hb Hexp". iDestruct "Hsub" as "[_ HT]".
        iApply "HΦ"; last first.
        * iApply ("HT" with "[Hb Hif]"). { iExists _. by iFrame. } by destruct b, bexp.
        * by iExists _.
    - iDestruct "Hl" as (?) "#Hinv".
      iInv "Hinv" as "Hb".
      iDestruct "Hb" as (b) "[>Hmt Hif]".
      destruct (decide (b = bexp)); subst.
      + iApply (wp_cas_suc_boolean with "Hmt Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[Hsub _]". iDestruct ("Hsub" with "Hif") as "[Hif HT]".
        iModIntro. iSplitL "Hb Hif". { iExists bnew. iFrame. }
        iApply "HΦ"; last first.
        * iApply ("HT" with "[] Hexp"). by iSplit.
        * by iExists _.
      + iApply (wp_cas_fail_boolean with "Hmt Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[_ HT]".
        iModIntro. iSplitL "Hb Hif". { by iExists b; iFrame; rewrite /i2v Hvnew. }
        iApply "HΦ"; last first.
        * iApply ("HT" with "[]"); first by iSplit. by destruct b, bexp.
        * by iExists _.
  Qed.
  Definition type_cas_atomic_bool_inst := [instance type_cas_atomic_bool].
  Global Existing Instance type_cas_atomic_bool_inst.
*)
End programs.

Global Typeclasses Opaque atomic_bool.
