Require Import floyd.base.
Require Import Coq.Logic.JMeq.

Lemma eq_rect_JMeq: forall (A:Type) (x y: A) F (v: F x) (H: x = y), JMeq (eq_rect x F v y H) v.
Proof.
  intros.
  subst.
  rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Lemma eq_rect_r_JMeq: forall (A:Type) (x y: A) F (v: F x) (H: y = x), JMeq (eq_rect_r F v H) v.
Proof.
  intros.
  subst.
  unfold eq_rect_r; rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Lemma JMeq_sumtype_ll: forall A B C D x y, A = C -> B = D -> 
  (@JMeq (A + B) (inl x) (C + D) (inl y)) ->
  JMeq x y.
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
  reflexivity.
Qed.

Lemma JMeq_sumtype_rr: forall A B C D x y, A = C -> B = D -> 
  (@JMeq (A + B) (inr x) (C + D) (inr y)) ->
  JMeq x y.
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
  reflexivity.
Qed.

Lemma JMeq_sumtype_lr: forall A B C D x y, A = C -> B = D -> ~ (@JMeq (A + B) (inl x) (C + D) (inr y)).
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
Qed.

Lemma JMeq_sumtype_rl: forall A B C D x y, A = C -> B = D -> ~ (@JMeq (A + B) (inr x) (C + D) (inl y)).
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
Qed.

Ltac solve_JMeq_sumtype H :=
  match type of H with
  | JMeq ?x ?y =>
    destruct x; destruct y;
     [apply JMeq_sumtype_ll in H; auto
     |apply JMeq_sumtype_lr in H; auto; inversion H
     |apply JMeq_sumtype_rl in H; auto; inversion H
     |apply JMeq_sumtype_rr in H; auto]
  end.

Lemma JMeq_fst: forall A B C D (x: A*B) (y: C*D), A = C -> B = D -> JMeq x y -> JMeq (fst x) (fst y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  reflexivity.
Qed.

Lemma JMeq_snd: forall A B C D (x: A*B) (y: C*D), A = C -> B = D -> JMeq x y -> JMeq (snd x) (snd y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  reflexivity.
Qed.

Lemma eq_rect_r_eq_rect_r_eq_sym: forall {T} {A B: T} F x (H: A = B),
  eq_rect_r F (eq_rect_r F x H) (eq_sym H) = x.
Proof.
  intros.
  apply JMeq_eq.
  apply JMeq_sym.
  rewrite eq_rect_r_JMeq.
  rewrite eq_rect_r_JMeq.
  reflexivity.
Qed.

Lemma eq_rect_r_eq_rect_r_eq_sym': forall {T} {A B: T} F x (H: B = A),
  eq_rect_r F (eq_rect_r F x (eq_sym H)) H = x.
Proof.
  intros.
  apply JMeq_eq.
  apply JMeq_sym.
  rewrite eq_rect_r_JMeq.
  rewrite eq_rect_r_JMeq.
  reflexivity.
Qed.

