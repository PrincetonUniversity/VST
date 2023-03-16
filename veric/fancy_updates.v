From stdpp Require Export coPset.
From iris_ora.algebra Require Import gmap agree.
From iris.proofmode Require Import proofmode.
From iris_ora.logic Require Export own.
From VST.veric Require Import wsat.
(*From iris.base_logic Require Export later_credits.*) (* TODO *)
From iris.prelude Require Import options.
Export wsatGS.
Import ouPred.

Local Definition ouPred_fupd_def `{!wsatGS Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P).
Local Definition ouPred_fupd_aux : seal (@ouPred_fupd_def). Proof. by eexists. Qed.
Definition ouPred_fupd := ouPred_fupd_aux.(unseal).
Global Arguments ouPred_fupd {Σ _}.
Local Lemma ouPred_fupd_unseal `{!wsatGS Σ} : @fupd _ ouPred_fupd = ouPred_fupd_def.
Proof. rewrite -ouPred_fupd_aux.(seal_eq) //. Qed.

Lemma ouPred_fupd_mixin `{!wsatGS Σ} : BiFUpdMixin (ouPredI (iResUR Σ)) ouPred_fupd.
Proof.
  split.
  - rewrite ouPred_fupd_unseal. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite ouPred_fupd_unseal /ouPred_fupd_def ownE_op //.
    by iIntros "($ & $ & HE) !> !> [$ $] !> !>" .
  - rewrite ouPred_fupd_unseal.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite ouPred_fupd_unseal.
    iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite ouPred_fupd_unseal. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite ouPred_fupd_unseal /ouPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite ouPred_fupd_unseal /ouPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance ouPred_bi_fupd `{!wsatGS Σ} : BiFUpd (ouPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := ouPred_fupd_mixin |}.

Global Instance ouPred_bi_bupd_fupd `{!wsatGS Σ} : BiBUpdFUpd (ouPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd ouPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

(*Global Instance ouPred_bi_fupd_plainly `{!wsatGS Σ} : BiFUpdPlainly (ouPredI (iResUR Σ)).
Proof.
  split.
  - rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros (E P) "H [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros (E P Q) "[H HQ] [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros (E P) "H [Hw HE]".
    iAssert (▷ ◇ ■ P)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros (E A Φ) "HΦ [Hw HE]".
    iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.*)

(* What's the linear equivalent of this?
Lemma fupd_plain_soundness `{!invGpreS Σ} E1 E2 (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !wsatGS Σ}, ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. apply bupd_plain_soundness; first by apply later_plain.
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  iPoseProof Hfupd as "H".
  rewrite (union_difference_L E1 ⊤); last done.
  rewrite ownE_op; last by set_solver.
  iDestruct "HE" as "[HE1 HE]".
  rewrite ouPred_fupd_unseal /ouPred_fupd_def.
  iMod ("H" with "[$]") as "[Hw [HE2 >H']]"; iFrame.
Qed.

Lemma step_fupdN_soundness `{!invGpreS Σ} φ n :
  (∀ `{Hinv: !wsatGS Σ}, ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_plain_soundness ⊤ ⊤ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iApply fupd_plainly_mask_empty. iMod "H".
  iMod (step_fupdN_plain with "H") as "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iMod "H" as %Hφ. auto.
Qed.

Lemma step_fupdN_soundness' `{!invGpreS Σ} φ n :
  (∀ `{Hinv: !wsatGS Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness _ n)=>Hinv. destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod Hiter as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.*)
