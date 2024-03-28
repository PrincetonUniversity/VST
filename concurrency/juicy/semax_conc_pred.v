Require Import VST.veric.SeparationLogic.
Require Import VST.concurrency.common.lksize.

Section mpred.

Context `{!heapGS Σ}.

Definition exclusive_mpred R : mpred := ((R ∗ R) -∗ False)%I.

Definition LKN := nroot .@ "LK".

Definition lock_inv : share -> val -> mpred -> mpred :=
  fun sh v R =>
    (∃ b : block, ∃ ofs : _, ⌜v = Vptr b ofs⌝ ∧
      inv LKN (∃ st, LKspec LKSIZE st sh (b, Ptrofs.unsigned ofs) ∗ if st then emp else R)).

Definition rec_inv sh v (Q R: mpred): mpred :=
  (R ∗-∗ Q ∗ ▷lock_inv sh v R).

Lemma lockinv_isptr sh v R : lock_inv sh v R ⊣⊢ (⌜isptr v⌝ ∧ lock_inv sh v R).
Proof.
  rewrite comm; apply add_andp.
  by iIntros "(% & % & -> & ?)".
Qed.

#[global] Instance lock_inv_nonexpansive sh v : NonExpansive (lock_inv sh v).
Proof.
  rewrite /lock_inv /LKspec; intros ??? Heq.
  do 9 f_equiv.
  simple_if_tac; first done.
  rewrite Heq //.
Qed.

End mpred.
