Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.res_predicates.

Section env.

Context `{!envGS Σ}.

Definition stack_level (n : nat) : assert := <affine> monPred_in(I := stack_index) n.

Lemma stack_level_intro : ⊢ ∃ n, stack_level n.
Proof.
  by iDestruct (monPred_in_intro emp with "[]") as (?) "($ & _)".
Qed.

Lemma stack_level_elim : forall (P : assert) n, ⊢ stack_level n -∗ ⎡P n⎤ -∗ P.
Proof.
  intros; iIntros "#? H".
  iApply bi.impl_elim_r; iSplit; first iApply "H".
  by iApply monPred_in_elim.
Qed.

Lemma stack_level_embed : forall n (P : assert), ⊢ stack_level n -∗ P -∗ ⎡P n⎤.
Proof.
  split => ?; rewrite /stack_level; monPred.unseal.
  iIntros "_" (? [=]); rewrite monPred_at_affinely /=.
  iIntros ([=] ? [=]); subst; auto.
Qed.

Lemma stack_level_eq : forall a b, ⊢ stack_level a -∗ stack_level b -∗ ⌜a = b⌝.
Proof.
  split => n; rewrite /stack_level; monPred.unseal; setoid_rewrite monPred_at_affinely; simpl.
  iIntros; iPureIntro; congruence.
Qed.

Definition up1 (P : assert) : assert := assert_of (λ n, P (S n)).
Definition down1 (P : assert) : assert := assert_of (λ n, match n with | S n' => P n' | O => False end).
(* Unlike pred, this gives us a limited form of down1_up1, where any premise with down1 tells us that we're
   not at O. *)

Global Instance up1_nonexpansive : NonExpansive up1.
Proof. split => ? /=. apply H. Qed.

Global Instance down1_nonexpansive : NonExpansive down1.
Proof. split => l /=. destruct l => //. apply H. Qed.

Global Instance up1_proper : Proper (equiv ==> equiv) up1.
Proof. split => ? /=. apply H. Qed.

Global Instance down1_proper : Proper (equiv ==> equiv) down1.
Proof. split => l /=. destruct l => //. apply H. Qed.

Lemma up1_mono : forall P Q, (P ⊢ Q) -> up1 P ⊢ up1 Q.
Proof. split => n; apply H. Qed.

Lemma down1_mono : forall P Q, (P ⊢ Q) -> down1 P ⊢ down1 Q.
Proof. split => n /=. destruct n => //. apply H. Qed.

Lemma up1_plain : forall P, Plain P -> Absorbing P -> up1 P ⊣⊢ P.
Proof.
  intros.
  rewrite -(plain_plainly P).
  split => n /=; rewrite !monPred_at_plainly //.
Qed.

Lemma up1_down1 : forall P, up1 (down1 P) ⊣⊢ P.
Proof.
  split => n. done.
Qed.

Lemma up1_objective : forall P `{!Objective P}, P ⊣⊢ up1 P.
Proof.
  split => n /=.
  iSplit; iApply objective_at.
Qed.

Lemma up1_obj_elim : forall P `{!Objective P}, up1 P ⊢ P.
Proof. intros; by rewrite -up1_objective. Qed.

Lemma down1_obj_elim : forall P `{!Objective P}, down1 P ⊢ P.
Proof.
  split => n /=.
  destruct n => //.
  apply bi.False_elim.
Qed.

Lemma up1_sep : forall P Q, up1 (P ∗ Q) ⊣⊢ up1 P ∗ up1 Q.
Proof.
  split => n; by monPred.unseal.
Qed.

Lemma down1_sep : forall P Q, down1 (P ∗ Q) ⊣⊢ down1 P ∗ down1 Q.
Proof.
  split => n; monPred.unseal.
  destruct n => //.
  by rewrite bi.False_sep.
Qed.

Lemma down1_up1 : forall P, down1 (up1 P) ⊢ P.
Proof.
  split => n /=.
  destruct n; [apply bi.False_elim | done].
Qed.

Lemma down1_sep_up1 : forall P Q, ⊢ down1 P -∗ Q -∗ down1 P ∗ down1 (up1 Q).
Proof.
  split => n; monPred.unseal.
  iIntros "_ %% P %n' -> Q".
  destruct n'; [done | iFrame].
Qed.

Lemma up1_and : forall P Q, up1 (P ∧ Q) ⊣⊢ up1 P ∧ up1 Q.
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_and : forall P Q, down1 (P ∧ Q) ⊣⊢ down1 P ∧ down1 Q.
Proof.
  intros. split => n.
  destruct n; monPred.unseal => //.
  by rewrite bi.False_and.
Qed.

Lemma up1_emp : up1 emp ⊣⊢ emp.
Proof. split => n; by monPred.unseal. Qed.

Lemma up1_emp_2 : emp ⊢ up1 emp.
Proof. by rewrite up1_emp. Qed.

Lemma up1_intuitionistically P : up1 (□ P) ⊣⊢ □ (up1 P).
Proof. split => n /=; rewrite !monPred_at_intuitionistically //. Qed.

Lemma down1_intuitionistically P : down1 (□ P) ⊣⊢ □ (down1 P).
Proof. split => n /=. destruct n; rewrite !monPred_at_intuitionistically ?bi.intuitionistically_False //. Qed.

#[global] Instance up1_monoid_sep_homomorphism: MonoidHomomorphism bi_sep bi_sep equiv up1.
Proof.
  split; [split|]; try apply _.
  - apply up1_sep.
  - apply up1_emp.
Qed.

Lemma up1_big_sepL {A} f (l : list A) : up1 ([∗ list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, up1 (f k x).
Proof. apply (big_opL_commute _). Qed.

Lemma up1_big_sepL2 {A B} f (l1 : list A) (l2 : list B) : up1 ([∗ list] k↦x;y ∈ l1;l2, f k x y) ⊣⊢ [∗ list] k↦x;y ∈ l1;l2, up1 (f k x y).
Proof. rewrite !big_sepL2_alt up1_and -up1_objective; f_equiv. apply up1_big_sepL. Qed.

#[global] Instance up1_affine P `{!Affine P} : Affine (up1 P).
Proof. apply monPred_affine; simpl; apply _. Qed.

#[global] Instance down1_affine P `{!Affine P} : Affine (down1 P).
Proof. apply monPred_affine; simpl; apply _. Qed.

#[global] Instance up1_mono' : Proper (bi_entails ==> bi_entails) up1.
Proof. intros ??; apply up1_mono. Qed.

#[global] Instance up1_flip_mono' : Proper (bi_entails --> flip bi_entails) up1.
Proof. intros ??; apply up1_mono. Qed.

#[global] Instance into_sep_up1 P Q1 Q2: IntoSep P Q1 Q2 → IntoSep (up1 P) (up1 Q1) (up1 Q2).
Proof. rewrite /IntoSep=> ->. by rewrite up1_sep. Qed.

#[global] Instance from_sep_up1 P Q1 Q2: FromSep P Q1 Q2 → FromSep (up1 P) (up1 Q1) (up1 Q2).
Proof. rewrite /FromSep=> <-. by rewrite up1_sep. Qed.

#[global] Instance down1_mono' : Proper (bi_entails ==> bi_entails) down1.
Proof. intros ??; apply down1_mono. Qed.

#[global] Instance down1_flip_mono' : Proper (bi_entails --> flip bi_entails) down1.
Proof. intros ??; apply down1_mono. Qed.

#[global] Instance into_sep_down1 P Q1 Q2: IntoSep P Q1 Q2 → IntoSep (down1 P) (down1 Q1) (down1 Q2).
Proof. rewrite /IntoSep=> ->. by rewrite down1_sep. Qed.

#[global] Instance from_sep_down1 P Q1 Q2: FromSep P Q1 Q2 → FromSep (down1 P) (down1 Q1) (down1 Q2).
Proof. rewrite /FromSep=> <-. by rewrite down1_sep. Qed.

Inductive Lower1 : assert → assert → Prop :=
  | lower1 P Q : (P ⊢ up1 Q) → Lower1 P Q.
Existing Class Lower1.
Global Existing Instance lower1.
Global Hint Mode Lower1 ! - : typeclass_instances.
Global Hint Mode Lower1 - ! : typeclass_instances.

#[global] Instance lower1_up1 P : Lower1 (up1 P) P | 0.
Proof. done. Qed.
#[global] Instance lower1_objective P `{!Objective P} : Lower1 P P | 1.
Proof. split. by rewrite -up1_objective. Qed.
#[global] Instance lower1_down1 P : Lower1 P (down1 P) | 10.
Proof. split. by rewrite up1_down1. Qed.

Lemma modality_up1_mixin : modality_mixin up1
  (MIEnvTransform Lower1) (MIEnvTransform Lower1).
Proof.
  split; simpl; split_and?; intros;
    try select (Lower1 _ _) (fun H => destruct H);
    eauto using bi.equiv_entails_1_2, up1_emp_2, up1_sep, up1_and, up1_mono.
  rewrite up1_intuitionistically; by f_equiv.
Qed.
Definition modality_up1 := Modality _ modality_up1_mixin.

Global Instance from_modal_up1 P :
  FromModal True%type modality_up1 (up1 P) (up1 P) P | 1.
Proof. by rewrite /FromModal. Qed.

(* On the other hand, this version of down1 is not a modality, since we don't have
   emp ⊢ down1 emp (and if we did we wouldn't have any ability to eliminate down1_up1).
Inductive Raise1 : assert → assert → Prop :=
  | raise1 P Q : (P ⊢ down1 Q) → Raise1 P Q.
Existing Class Raise1.
Global Existing Instance raise1.
Global Hint Mode Raise1 ! - : typeclass_instances.
Global Hint Mode Raise1 - ! : typeclass_instances.

#[global] Instance raise1_down1 P : Raise1 (down1 P) P | 0.
Proof. done. Qed.
#[global] Instance raise1_objective P `{!Objective P} : Raise1 P P | 1.
Proof. split. by rewrite -down1_objective. Qed.
#[global] Instance raise1_up1 P : Raise1 P (up1 P) | 10.
Proof. split. by apply up1_mono. Qed.

Lemma modality_down1_mixin : modality_mixin down1
  (MIEnvTransform Raise1) (MIEnvTransform Raise1).
Proof.
  split; simpl; split_and?; intros;
    try select (Raise1 _ _) (fun H => destruct H);
    eauto using bi.equiv_entails_1_2, down1_sep, down1_and, down1_mono.
  rewrite up1_intuitionistically; by f_equiv.
Qed.
Definition modality_down1 := Modality _ modality_down1_mixin.
*)

End env.

Notation "⇑ P" := (up1 P) (at level 20): bi_scope.
Notation "⇓ P" := (down1 P) (at level 20) : bi_scope.
