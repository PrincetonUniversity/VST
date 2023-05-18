(* modified from iris.base_logic.lib.invariants *)

From stdpp Require Export namespaces.
From iris_ora.algebra Require Import gmap.
From iris.proofmode Require Import proofmode.
From VST.veric Require Export fancy_updates.
From VST.veric Require Import wsat.

(** Semantic Invariants *)
Local Definition inv_def `{!wsatGS Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ emp).
Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
Definition inv := inv_aux.(unseal).
Global Arguments inv {Σ _} N P.
Local Definition inv_unseal : @inv = @inv_def := inv_aux.(seal_eq).
Global Instance: Params (@inv) 2 := {}.

(** * Invariants *)
Section inv.
  Context `{!wsatGS Σ}.
  Implicit Types i : positive.
  Implicit Types N : namespace.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.

  (** ** Internal model of invariants *)
  Definition own_inv (N : namespace) (P : iProp Σ) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ ownI i P.

  Lemma own_inv_acc E N P :
    ↑N ⊆ E → own_inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    rewrite fancy_updates.ouPred_fupd_unseal /fancy_updates.ouPred_fupd_def.
    iDestruct 1 as (i) "[%Hi #HiP]".
    apply elem_of_subseteq_singleton in Hi.
    rewrite {1 4}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
    rewrite {1 5}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver.
    iIntros "(Hw & [HE $] & $) !> !>".
    iDestruct (ownI_open i with "[$Hw $HE $HiP]") as "($ & $ & HD)".
    iIntros "HP [Hw $] !> !>". iApply (ownI_close _ P). by iFrame.
  Qed.

  Lemma fresh_inv_name (E : gset positive) N : ∃ i, i ∉ E ∧ i ∈ (↑N:coPset).
  Proof.
    exists (coPpick (↑ N ∖ gset_to_coPset E)).
    rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
    apply coPpick_elem_of=> Hfin.
    eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
    apply gset_to_coPset_finite.
  Qed.

  Lemma own_inv_alloc N E P : ▷ P ={E}=∗ own_inv N P.
  Proof.
    rewrite fancy_updates.ouPred_fupd_unseal /fancy_updates.ouPred_fupd_def.
    iIntros "HP [Hw $]".
    iMod (ownI_alloc (.∈ (↑N : coPset)) P with "[$HP $Hw]")
      as (i ?) "[$ ?]"; auto using fresh_inv_name.
    do 2 iModIntro. iExists i. auto.
  Qed.

  (* This does not imply [own_inv_alloc] due to the extra assumption [↑N ⊆ E]. *)
  Lemma own_inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> own_inv N P ∗ (▷P ={E∖↑N, E}=∗ emp).
  Proof.
    rewrite fancy_updates.ouPred_fupd_unseal /fancy_updates.ouPred_fupd_def.
    iIntros (Sub) "[Hw HE]".
    iMod (ownI_alloc_open (.∈ (↑N : coPset)) P with "Hw")
      as (i ?) "(Hw & #Hi & HD)"; auto using fresh_inv_name.
    iAssert (ownE {[i]} ∗ ownE (↑ N ∖ {[i]}) ∗ ownE (E ∖ ↑ N))%I
      with "[HE]" as "(HEi & HEN\i & HE\N)".
    { rewrite -?ownE_op; [|set_solver..].
      rewrite assoc_L -!union_difference_L //. set_solver. }
    do 2 iModIntro. iFrame "HE\N". iSplitL "Hw HEi"; first by iApply "Hw".
    iSplitL "Hi".
    { iExists i. auto. }
    iIntros "HP [Hw HE\N]".
    iDestruct (ownI_close with "[$Hw $Hi $HP $HD]") as "[$ HEi]".
    do 2 iModIntro. iSplitL; [|done].
    iCombine "HEi HEN\i HE\N" as "HEN".
    rewrite -?ownE_op; [|set_solver..].
    rewrite assoc_L -!union_difference_L //; set_solver.
  Qed.

  Lemma own_inv_to_inv M P: own_inv M P -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_unseal. iIntros "!>" (E H).
    iPoseProof (own_inv_acc with "I") as "H"; eauto.
  Qed.

  (** ** Public API of invariants *)
  Global Instance inv_contractive N : Contractive (inv N).
  Proof. rewrite inv_unseal. solve_contractive. Qed.

  Global Instance inv_ne N : NonExpansive (inv N).
  Proof. apply contractive_ne, _. Qed.

  Global Instance inv_proper N : Proper (equiv ==> equiv) (inv N).
  Proof. apply ne_proper, _. Qed.

  Global Instance inv_persistent N P : Persistent (inv N P).
  Proof. rewrite inv_unseal. apply _. Qed.

  Global Instance inv_affine N P : Affine (inv N P).
  Proof. rewrite inv_unseal. apply _. Qed.

  Lemma inv_alter N P Q : inv N P -∗ □ ▷ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q.
  Proof.
    rewrite inv_unseal. iIntros "#HI #HPQ !>" (E H).
    iMod ("HI" $! E H) as "[HP Hclose]".
    iDestruct ("HPQ" with "HP") as "[$ HQP]".
    iIntros "!> HQ". iApply "Hclose". iApply "HQP". done.
  Qed.

  Lemma inv_iff N P Q : inv N P -∗ □ ▷ (P ∗-∗ Q) -∗ inv N Q.
  Proof.
    iIntros "#HI #HPQ". iApply (inv_alter with "HI").
    iIntros "!> !> HP". iSplitL "HP".
    - by iApply "HPQ".
    - iIntros "HQ". by iApply "HPQ".
  Qed.

  Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ emp).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]".
    iApply own_inv_to_inv. done.
  Qed.

  Lemma inv_acc E N P :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    rewrite inv_unseal /inv_def; iIntros (?) "#HI". by iApply "HI".
  Qed.

  Lemma inv_combine N1 N2 N P Q :
    N1 ## N2 →
    ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    inv N1 P -∗ inv N2 Q -∗ inv N (P ∗ Q).
  Proof.
    rewrite inv_unseal. iIntros (??) "#HinvP #HinvQ !>"; iIntros (E ?).
    iMod ("HinvP" with "[%]") as "[$ HcloseP]"; first set_solver.
    iMod ("HinvQ" with "[%]") as "[$ HcloseQ]"; first set_solver.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose [HP HQ]".
    iMod "Hclose" as "_". iMod ("HcloseQ" with "HQ") as "_". by iApply "HcloseP".
  Qed.

(*  Lemma except_0_inv N P : ◇ inv N P ⊢ inv N P.
  Proof.
    rewrite inv_unseal /inv_def /bi_except_0.
    iIntros "[? | $]".
    Search bi_later bi_affinely.
Search bi_except_0 bi_intuitionistically.
iIntros "#H !>" (E ?).
    iMod "H". by iApply "H".
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
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ emp.
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
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (?) "Hinv". iMod (inv_acc with "Hinv") as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  Lemma inv_split_l N P Q : inv N (P ∗ Q) -∗ inv N P.
  Proof.
    iIntros "#HI". iApply inv_alter; eauto.
    iIntros "!> !> [$ $] $".
  Qed.
  Lemma inv_split_r N P Q : inv N (P ∗ Q) -∗ inv N Q.
  Proof.
    rewrite (comm _ P Q). eapply inv_split_l.
  Qed.
  Lemma inv_split N P Q : inv N (P ∗ Q) -∗ inv N P ∗ inv N Q.
  Proof.
    iIntros "#H".
    iPoseProof (inv_split_l with "H") as "$".
    iPoseProof (inv_split_r with "H") as "$".
  Qed.

End inv.

