Require Import VST.floyd.proofauto.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wandQ_frame.

Lemma ramify_PPQQ {A: Type} {NA: NatDed A} {SA: SepLog A} {CA: ClassicalSep A}: forall P Q,
  P |-- P * (Q -* Q).
Proof.
  intros.
  apply RAMIF_PLAIN.solve with emp.
  + rewrite sepcon_emp; auto.
  + rewrite emp_sepcon; auto.
Qed.

Lemma is_pointer_or_null_force_val_sem_cast_neutral: forall p,
  is_pointer_or_null p -> force_val (sem_cast_neutral p) = p.
Proof.
  intros.
  destruct p; try contradiction; reflexivity.
Qed.

Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, P |-- Q -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

