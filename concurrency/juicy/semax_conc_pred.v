Require Import VST.veric.SeparationLogic.
Require Import VST.concurrency.common.lksize.

Section mpred.

Context `{!heapGS Σ}.

Definition lock_inv : share -> val -> mpred -> mpred :=
  fun sh v R =>
    (∃ b : block, ∃ ofs : _,
      ⌜v = Vptr b ofs⌝ ∧
      LKspec LKSIZE R sh (b, Ptrofs.unsigned ofs)).

(*Definition rec_inv sh v (Q R: mpred): Prop :=
  (R = Q * |>lock_inv sh v R).

Definition weak_rec_inv sh v (Q R: mpred): mpred :=
  (! (R <=> Q * |>lock_inv sh v R))%pred.*)

Lemma lockinv_isptr sh v R : lock_inv sh v R ⊣⊢ (⌜isptr v⌝ ∧ lock_inv sh v R).
Proof.
  rewrite comm; apply add_andp.
  by iIntros "(% & % & -> & ?)".
Qed.

#[global] Instance lock_inv_nonexpansive sh v : NonExpansive (lock_inv sh v).
Proof.
  rewrite /lock_inv /LKspec; intros ??? Heq.
  do 9 f_equiv.
  rewrite Heq //.
Qed.

(*Lemma rec_inv1_nonexpansive: forall sh v Q,
  nonexpansive (weak_rec_inv sh v Q).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2.
  eapply predicates_hered.derives_trans; [| apply unfash_fash_equiv].
  eapply predicates_hered.derives_trans; [| apply iffp_equiv].
  apply predicates_hered.andp_right; auto.
  eapply predicates_hered.derives_trans; [| apply sepcon_equiv].
  apply predicates_hered.andp_right.
  {
    intros n ?.
    split; intros; hnf; intros; auto.
  }
  eapply predicates_hered.derives_trans, subtypes.eqp_later1.
  eapply predicates_hered.derives_trans, predicates_hered.now_later.
  apply nonexpansive_lock_inv.
Qed.

Lemma rec_inv2_nonexpansive: forall sh v R,
  nonexpansive (fun Q => weak_rec_inv sh v Q R).
Proof.
  intros.
  unfold weak_rec_inv.
  intros P1 P2.
  eapply predicates_hered.derives_trans; [| apply unfash_fash_equiv].
  eapply predicates_hered.derives_trans; [| apply iffp_equiv].
  apply predicates_hered.andp_right.
  {
    intros n ?.
    split; intros; hnf; intros; auto.
  }
  eapply predicates_hered.derives_trans; [| apply sepcon_equiv].
  apply predicates_hered.andp_right; auto.

  intros n ?.
  split; intros; hnf; intros; auto.
Qed.

Lemma rec_inv_weak_rec_inv: forall sh v Q R,
  rec_inv sh v Q R ->
  TT |-- weak_rec_inv sh v Q R.
Proof.
  intros.
  constructor.
  intros w _.
  hnf in H |- *.
  intros.
  rewrite H at 1 4.
  split; intros; hnf; intros; auto.
Qed.*)

End mpred.
