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
Global Instance ouPred_bi_fupd `{!wsatGS Σ} : BiFUpd (iProp Σ) :=
  {| bi_fupd_mixin := ouPred_fupd_mixin |}.

Global Instance ouPred_bi_bupd_fupd `{!wsatGS Σ} : BiBUpdFUpd (iProp Σ).
Proof. rewrite /BiBUpdFUpd ouPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

Lemma fupd_plain_soundness `{!wsatGpreS Σ} E1 E2 (P: iProp Σ) `{!Plain P} `{!Absorbing P}:
  (∀ `{Hinv: !wsatGS Σ}, ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. apply bupd_plain_soundness; first by apply later_plain.
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  iPoseProof Hfupd as "H".
  rewrite (union_difference_L E1 ⊤); last done.
  rewrite ownE_op; last by set_solver.
  iDestruct "HE" as "[HE1 HE]".
  rewrite ouPred_fupd_unseal /ouPred_fupd_def.
  iMod ("H" with "[$]") as "[Hw [HE2 >H']]"; by iFrame.
Qed.

(* an alternative to using BiFUpdPlainly, which doesn't hold in linear logics *)
Section fupd_plain.

Context `{!wsatGS Σ}.
Implicit Types (P : iProp Σ).

Lemma bupd_plainly P `{!Absorbing P}: (|==> ■ P) ⊢ P.
Proof.
  rewrite -{2}(absorbing P).
  rewrite /bi_absorbingly; ouPred.unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eexists _, _; split; last by split; [apply I | apply Hng'].
  rewrite right_id //.
Qed.

Lemma fupd_plainly_mask_empty E `{!Absorbing P}: (|={E,∅}=> ■ P) ⊢ |={E}=> P.
Proof.
  rewrite -{2}(absorbing P).
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "H [Hw HE]".
  iAssert (◇ ■ P)%I as "#>HP".
  { iApply bupd_plainly. iMod ("H" with "[$]") as "(_ & _ & #HP)".
    by iIntros "!> !>". }
  by iFrame.
Qed.

Lemma fupd_plainly_mask E E' P `{!Absorbing P}: (|={E,E'}=> ■ P) ⊢ |={E}=> P.
Proof.
  rewrite -(fupd_plainly_mask_empty).
  apply fupd_elim, (fupd_mask_intro_discard _ _ _). set_solver.
Qed.

Lemma fupd_plain_mask E E' P `{!Plain P} `{!Absorbing P}: (|={E,E'}=> P) ⊢ |={E}=> P.
Proof. by rewrite {1}(plain P) fupd_plainly_mask. Qed.

Lemma fupd_plainly_later E P `{!Absorbing P}: (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P.
Proof.
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "H [Hw HE]".
  iAssert (▷ ◇ ■ P)%I as "#HP".
  { iNext. iApply bupd_plainly. iMod ("H" with "[$]") as "(_ & _ & #HP)".
    by iIntros "!> !>". }
  iFrame. iIntros "!> !> !>". by iMod "HP".
Qed.

Lemma fupd_plain_later E P `{!Plain P} `{!Absorbing P}: (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P.
Proof. by rewrite {1}(plain P) fupd_plainly_later. Qed.

Lemma fupd_plainly_forall_2 E {A} (P : A → iProp Σ) `{!∀x, Absorbing (P x)}: (∀x, |={E}=> ■ P x) ={E}=∗ ∀x, P x.
Proof.
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "HP [Hw HE]".
  iAssert (◇ ■ ∀ x : A, P x)%I as "#>HP'".
  { iIntros (x). rewrite -(bupd_plainly (◇ ■ P x)%I).
    iMod ("HP" with "[$Hw $HE]") as "(_&_&#?)". by iIntros "!> !>". }
  by iFrame.
Qed.

Lemma fupd_plain_forall_2 E {A} (P : A → iProp Σ) `{!∀x, Plain (P x)} `{!∀x, Absorbing (P x)}: (∀x, |={E}=> P x) ={E}=∗ ∀x, P x.
Proof. rewrite -fupd_plainly_forall_2. apply bi.forall_mono; intros x; rewrite {1}(plain (P x)) //. Qed.

Lemma step_fupd_plain Eo Ei P `{!Plain P} `{!Absorbing P}: (|={Eo}[Ei]▷=> P) ⊢ |={Eo}=> ▷ ◇ P.
Proof.
  rewrite -(fupd_plain_mask _ Ei (▷ ◇ P)).
  apply fupd_elim. by rewrite fupd_plain_mask -fupd_plain_later.
Qed.

Lemma step_fupdN_plain Eo Ei n P `{!Plain P} `{!Absorbing P}: (|={Eo}[Ei]▷=>^n P) ⊢ |={Eo}=> ▷^n ◇ P.
Proof.
  induction n as [|n IH].
  - by rewrite -fupd_intro -bi.except_0_intro.
  - rewrite Nat.iter_succ step_fupd_fupd IH !fupd_trans step_fupd_plain.
    apply fupd_mono. destruct n as [|n]; simpl.
    * by rewrite bi.except_0_idemp.
    * by rewrite bi.except_0_later.
Qed.

End fupd_plain.

Lemma step_fupdN_soundness `{!wsatGpreS Σ} φ n :
  (∀ `{Hinv: !wsatGS Σ}, ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_plain_soundness ⊤ ∅ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iMod "H".
  iMod (step_fupdN_plain with "H") as "H". iModIntro.
  rewrite -bi.later_laterN bi.laterN_later.
  iNext. iMod "H" as %Hφ. auto.
Qed.

Lemma step_fupdN_soundness' `{!wsatGpreS Σ} φ n :
  (∀ `{Hinv: !wsatGS Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness _ n)=>Hinv. destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod Hiter as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.
