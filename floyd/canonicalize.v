Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.

Import LiftNotation.

Section mpred.

Context `{!heapGS Σ}.

Local Notation assert := (@assert Σ).
Local Notation do_canon := (@do_canon Σ).
Local Notation PROPx := (@PROPx _ Σ).

Lemma canon1: forall P1 B  P Q R,
   do_canon (⌜P1⌝ ∧ B) (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ do_canon B  (PROPx (P1::P) (LOCALx Q (SEPx R))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
normalize.
Qed.

Lemma canon2: forall Q1 B P Q R,
    do_canon (local (locald_denote Q1) ∧ B) (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ do_canon B (PROPx (P) (LOCALx (Q1::Q) (SEPx R))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
rewrite /= local_lift2_and.
iSplit.
- iIntros "(($ & $) & $)".
- iIntros "($ & $ & H & $)".
  rewrite bi.affinely_and; iDestruct "H" as "($ & $)".
Qed.

Definition nonlocal (Q: assert) : Prop := True.

Lemma canon3: forall R1 B P Q R,
    nonlocal ⎡R1⎤ ->
    do_canon (B ∗ ⎡R1⎤) (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
simpl.
iSplit.
- iIntros "(($ & $) & $)".
- iIntros "($ & $ & $ & $ & $)".
Qed.

Lemma canon3b: forall R1 B P Q R,
    nonlocal ⎡R1⎤ ->
    do_canon (⎡R1⎤ ∗ B) (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
rewrite (bi.sep_comm ⎡R1⎤ B).
apply canon3. auto.
Qed.

Lemma canon4: forall P, do_canon emp P ⊣⊢ P.
Proof.
apply bi.emp_sep.
Qed.

Lemma canon7: forall R1 P Q R,
   nonlocal ⎡R1⎤ ->
   do_canon ⎡R1⎤ (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros; simpl.
iSplit.
- iIntros "($ & $)".
- iIntros "($ & $ & $ & $)".
Qed.

Lemma canon8: forall R1 R2 R3 PQR,
    do_canon ((R1 ∧ R2) ∧ R3) PQR ⊣⊢ do_canon (R1 ∧ (R2 ∧ R3)) PQR.
Proof. intros; rewrite assoc; auto.
Qed.

Lemma start_canon: forall P, P ⊣⊢ do_canon P (PROPx nil (LOCALx nil (SEPx nil ))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
split => rho; monPred.unseal; rewrite /lift1 /=; unfold_lift.
rewrite !bi.True_and bi.sep_emp //.
Qed.

Lemma canon5: forall Q R S,
       nonlocal Q ->
       Q ∧ (local R ∧ S) ⊣⊢ local R ∧ (Q ∧ S).
Proof.
intros.
rewrite assoc (bi.and_comm Q) -assoc //.
Qed.

Lemma canon5b: forall Q R S,
       nonlocal Q ->
       Q ∧ (S ∧ local R) ⊣⊢ local R ∧ (Q ∧ S).
Proof.
intros.
rewrite assoc comm //.
Qed.

Lemma canon5c: forall Q R,
       nonlocal Q ->
       (Q ∧ local R) ⊣⊢ local R ∧ Q.
Proof.
intros.
apply bi.and_comm.
Qed.

Lemma canon6: forall Q R S,
       nonlocal Q ->
       Q ∧ (⌜R⌝ ∧ S) ⊣⊢ ⌜R⌝ ∧ (Q ∧ S).
Proof.
intros.
rewrite assoc (bi.and_comm Q) -assoc //.
Qed.

Lemma canon6b: forall Q R S,
       nonlocal Q ->
       Q ∧ (S ∧ ⌜R⌝) ⊣⊢ ⌜R⌝ ∧ (Q ∧ S).
Proof.
intros.
rewrite assoc comm //.
Qed.

Lemma canon6c: forall Q R,
       nonlocal Q ->
       (Q ∧ ⌜R⌝) ⊣⊢ ⌜R⌝ ∧ Q.
Proof.
intros.
apply bi.and_comm.
Qed.

Lemma canon17 : forall (P: Prop) PP (QR : assert), ⌜P⌝ ∧ (PROPx PP QR) ⊣⊢ PROPx (P::PP) QR.
Proof.
intros. unfold PROPx. simpl. normalize.
Qed.

Lemma finish_canon: forall R1 P Q R,
   do_canon ⎡R1⎤ (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
iSplit.
- iIntros "($ & $)".
- iIntros "($ & $ & $ & $)".
Qed.

Lemma restart_canon: forall P Q R, (PROPx P (LOCALx Q (SEPx R))) ⊣⊢ do_canon emp (PROPx P (LOCALx Q (SEPx R))).
Proof.
intros.
unfold do_canon. rewrite bi.emp_sep //.
Qed.

Lemma exp_do_canon:
   forall T (P: T -> assert) (Q: assert), do_canon (bi_exist P) Q ⊣⊢ ∃ x:_, do_canon (P x) Q.
Proof. intros; apply bi.sep_exist_r. Qed.

Lemma canon9: forall Q1 P Q R,
       local (locald_denote Q1) ∧ (PROPx P (LOCALx Q R)) ⊣⊢
         PROPx P (LOCALx (Q1::Q) R).
Proof.
intros; unfold PROPx, LOCALx; simpl.
rewrite local_lift2_and.
iSplit.
- iIntros "($ & $)".
- iIntros "($ & H & $)".
  rewrite bi.affinely_and; iDestruct "H" as "($ & $)".
Qed.

Lemma canon20: forall PQR, do_canon emp PQR ⊣⊢ PQR.
Proof.
intros. apply bi.emp_sep.
Qed.

End mpred.

Ltac check_nonlocal :=
  match goal with
  |  |- nonlocal (local _) => fail 1
  |  |- nonlocal (⌜_⌝) => fail 1
  |  |- nonlocal (bi_and _ _) => fail 1
  |  |- nonlocal (bi_sep _ _) => fail 1
  | |- _ => apply I
 end.

#[export] Hint Rewrite @canon1 @canon2 @canon4 @canon8 : canon.
#[export] Hint Rewrite @canon3 using check_nonlocal : canon.
#[export] Hint Rewrite @canon3b using check_nonlocal : canon.
#[export] Hint Rewrite @canon7 using check_nonlocal : canon.
#[export] Hint Rewrite <- @bi.sep_assoc : canon.

#[export] Hint Rewrite @canon5 using check_nonlocal : canon.
#[export] Hint Rewrite @canon5b using check_nonlocal : canon.
#[export] Hint Rewrite @canon5c using check_nonlocal : canon.
#[export] Hint Rewrite @canon6 using check_nonlocal : canon.
#[export] Hint Rewrite @canon6b using check_nonlocal : canon.
#[export] Hint Rewrite @canon6c using check_nonlocal : canon.
#[export] Hint Rewrite @canon17 : canon.

Ltac canonicalize_pre :=
  match goal with |- semax _ _ ?P _ _ =>
      rewrite (start_canon P); autorewrite with canon
  end.

#[export] Hint Rewrite @exp_do_canon: canon.
#[export] Hint Rewrite @exp_do_canon: norm2.
#[export] Hint Rewrite @canon9: canon.
#[export] Hint Rewrite @canon20: canon.
