Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.veric Require Import res_predicates mpred lifting_expr lifting.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Section VST.

Context `{!VSTGS OK_ty Σ}.

  Definition inv `{!VSTGS OK_ty Σ} N (P : assert) := ∃ n, stack_level n ∗ ⎡inv N (P n)⎤.

  Global Instance inv_contractive N : Contractive (inv N).
  Proof. solve_contractive. Qed.

  Global Instance inv_ne N : NonExpansive (inv N).
  Proof. apply contractive_ne, _. Qed.

  Global Instance inv_proper N : Proper (equiv ==> equiv) (inv N).
  Proof. apply ne_proper, _. Qed.

  Global Instance inv_persistent N P : Persistent (inv N P).
  Proof. apply _. Qed.

  Global Instance inv_affine N P : Affine (inv N P).
  Proof. apply _. Qed.

  Global Instance inv_objective N P `{!Objective P}: Objective (inv N P).
  Proof.
    rewrite /Objective /inv; intros.
    rewrite /stack_level; monPred.unseal.
    iIntros "(% & _ & I)".
    iExists _; iSplit.
    { rewrite monPred_at_affinely //. }
    iModIntro; iApply invariants.inv_proper; last done.
    iSplit; by iApply objective_at.
  Qed.
  
  Lemma inv_alter N P Q : ⊢ inv N P -∗ □ ▷ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q.
  Proof.
    split => n; rewrite /inv /stack_level; monPred.unseal.
    iIntros "_" (? ->) "(% & L & HI) % -> #HPQ".
    rewrite monPred_at_affinely monPred_at_intuitionistically /=; iDestruct "L" as %->.
    iExists _; rewrite monPred_at_affinely; iSplit => //.
    iApply (inv_alter with "HI").
    iIntros "!> !> HP".
    iDestruct ("HPQ" with "[//] HP") as "($ & HQ)".
    by iApply "HQ".
  Qed.

  Lemma inv_iff N P Q : ⊢ inv N P -∗ □ ▷ (P ∗-∗ Q) -∗ inv N Q.
  Proof.
    iIntros "#HI #HPQ". iApply (inv_alter with "HI").
    iIntros "!> !> HP". iSplitL "HP".
    - by iApply "HPQ".
    - iIntros "HQ". by iApply "HPQ".
  Qed.

  Lemma inv_alloc N E P : ▷ P ⊢ |={E}=> inv N P.
  Proof.
    split => n; rewrite /inv /stack_level; monPred.unseal.
    iIntros "HP".
    iMod (inv_alloc with "HP") as "$".
    rewrite monPred_at_affinely //.
  Qed.

  Lemma inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ emp).
  Proof.
    split => n; rewrite /inv /stack_level; monPred.unseal.
    iIntros "_". iMod inv_alloc_open as "[$ Hclose]"; first done.
    iModIntro.
    rewrite monPred_at_affinely; iSplit => //.
    by iIntros (? ->).
  Qed.

  Lemma inv_acc E N P :
    ↑N ⊆ E → inv N P ⊢ |={E,E∖↑N}=> ▷ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    split => n; rewrite /inv /stack_level; monPred.unseal.
    iIntros "(% & L & HI)".
    rewrite monPred_at_affinely; iDestruct "L" as %->.
    iMod (inv_acc with "HI") as "($ & HI)"; first done.
    by iIntros "!>" (? ->).
  Qed.

  Lemma inv_combine N1 N2 N P Q :
    N1 ## N2 →
    ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    ⊢ inv N1 P -∗ inv N2 Q -∗ inv N (P ∗ Q).
  Proof.
    split => n; rewrite /inv /stack_level; monPred.unseal.
    iIntros "_" (? ->) "(% & L1 & HI1) % -> (% & L2 & HI2)".
    iDestruct (inv_combine with "HI1 HI2") as "HI"; [done..|].
    iExists j0; rewrite !monPred_at_affinely; iDestruct "L1" as %->; iDestruct "L2" as %->.
    by iFrame.
  Qed.

(*  Lemma except_0_inv N P : ◇ inv N P ⊢ inv N P.
  Proof.
    rewrite inv_unseal /inv_def. Search bi_except_0 Affine.
  Qed.*)

  (** ** Proof mode integration *)
(*  Global Instance is_except_0_inv N P : IsExcept0 (inv N P).
  Proof. apply except_0_inv. Qed.*)

  Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

  Global Instance into_acc_inv N P E:
    IntoAcc (X := unit) (inv N P)
            (↑N ⊆ E) emp (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply inv_acc.
  Qed.

  (** ** Derived properties *)
  Lemma inv_acc_strong E N P :
    ↑N ⊆ E → inv N P ⊢ |={E,E∖↑N}=> ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ emp.
  Proof.
    iIntros (?) "Hinv".
    iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
    iIntros (E') "HP".
    iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
    by rewrite left_id_L.
  Qed.

  Lemma inv_acc_timeless E N P `{!Timeless P} :
    ↑N ⊆ E → inv N P ⊢ |={E,E∖↑N}=> P ∗ (P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (?) "Hinv". iMod (inv_acc with "Hinv") as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  Lemma inv_split_l N P Q : inv N (P ∗ Q) ⊢ inv N P.
  Proof.
    iIntros "#HI". iApply inv_alter; eauto.
    iIntros "!> !> [$ $] $".
  Qed.
  Lemma inv_split_r N P Q : inv N (P ∗ Q) ⊢ inv N Q.
  Proof.
    rewrite (comm _ P Q). eapply inv_split_l.
  Qed.
  Lemma inv_split N P Q : inv N (P ∗ Q) ⊢ inv N P ∗ inv N Q.
  Proof.
    iIntros "#H".
    iPoseProof (inv_split_l with "H") as "$".
    iPoseProof (inv_split_r with "H") as "$".
  Qed.

End VST.
