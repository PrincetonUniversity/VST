(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_rec.
Require Import VST.msl.predicates_sl.
Require Import VST.msl.subtypes.
Require Import VST.msl.subtypes_sl.

Local Open Scope pred.

Lemma conj_nonexpansive {A} `{ageable A} : forall (F G:pred A -> pred A),
  nonexpansive F ->
  nonexpansive G ->
  nonexpansive (fun x:pred A => F x && G x).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply subp_andp; apply eqp_subp; auto.
  apply subp_andp; apply eqp_subp2; auto.
Qed.

Lemma conj_contractive {A} `{ageable A} : forall F G,
  contractive F ->
  contractive G ->
  contractive (fun x => F x && G x).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply subp_andp; apply eqp_subp; auto.
  apply subp_andp; apply eqp_subp2; auto.
Qed.

Lemma impl_contractive {A} `{ageable A} : forall F G,
  contractive F ->
  contractive G ->
  contractive (fun x => F x --> G x).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply subp_imp.
  apply eqp_subp2; auto.
  apply eqp_subp; auto.
  apply subp_imp.
  apply eqp_subp; auto.
  apply eqp_subp2; auto.
Qed.

Lemma impl_nonexpansive {A} `{ageable A} : forall F G,
  nonexpansive F ->
  nonexpansive G ->
  nonexpansive (fun x => F x --> G x).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply subp_imp.
  apply eqp_subp2; auto.
  apply eqp_subp; auto.
  apply subp_imp.
  apply eqp_subp; auto.
  apply eqp_subp2; auto.
Qed.

Lemma forall_contractive {A} `{ageable A} : forall B (X : pred A -> B -> pred A),
  (forall x, (contractive (fun y => X y x))) ->
  contractive (fun x => (allp (X x))).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply subp_allp; intros.
  apply eqp_subp; auto.
  apply subp_allp; intros.
  apply eqp_subp2; auto.
Qed.

Lemma forall_nonexpansive {A} `{ageable A} : forall B (X : pred A -> B -> pred A),
  (forall x, (nonexpansive (fun y => X y x))) ->
  nonexpansive (fun x => (allp (X x))).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply subp_allp; intros.
  apply eqp_subp; auto.
  apply subp_allp; intros.
  apply eqp_subp2; auto.
Qed.

Lemma exists_contractive {A} `{ageable A} : forall B (X : pred A -> B -> pred A),
  (forall x, (contractive (fun y => X y x))) ->
  contractive (fun x => (exp (X x))).
Proof.
  unfold contractive; intros.
  apply subp_eqp; apply subp_exp; intros.
  apply eqp_subp; auto.
  apply eqp_subp2; auto.
Qed.

Lemma exists_nonexpansive {A} `{ageable A} : forall B (X : pred A -> B -> pred A),
  (forall x, (nonexpansive (fun y => X y x))) ->
  nonexpansive (fun x => (exp (X x))).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp; apply subp_exp; intros.
  apply eqp_subp; auto.
  apply eqp_subp2; auto.
Qed.

Lemma later_contractive {A} `{ageable A} : forall F,
  nonexpansive F ->
  contractive (fun X => (|>(F X))).
Proof.
  unfold nonexpansive, contractive; intros.
  apply subp_eqp.
  rewrite <- subp_later.
  apply box_positive; auto.
  apply eqp_subp; auto.
  rewrite <- subp_later.
  apply box_positive; auto.
  apply eqp_subp2; auto.
Qed.

Lemma const_nonexpansive {A: Type} {H: ageable A}: forall P: pred A,
  nonexpansive (fun _ => P).
Proof.
  intros.
  hnf; intros.
  intros w ? ? ?.
  clear.
  hnf; split; intros ? ? ?; auto.
Qed.

Lemma const_contractive {A: Type} {H: ageable A}: forall P: pred A,
  contractive (fun _ => P).
Proof.
  intros.
  hnf; intros.
  intros w ? ? ?.
  clear.
  hnf; split; intros ? ? ?; auto.
Qed.

Lemma identity_nonexpansive {A: Type} {H: ageable A}:
  nonexpansive (fun P: pred A => P).
Proof.
  hnf; intros.
  intros ?; auto.
Qed.

(*
Lemma box_contractive {A} `{ageable A} : forall F (M:modality),
  inclusion _ M fashionR ->
  contractive F ->
  contractive (fun X => box M (F X)).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply sub_box; auto.
  apply eqp_subp; auto.
  apply sub_box; auto.
  apply eqp_subp2; auto.
Qed.

Lemma box_nonexpansive {A} `{ageable A} : forall F (M:modality),
  inclusion _ M fashionR ->
  nonexpansive F ->
  nonexpansive (fun X => box M (F X)).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply sub_box; auto.
  apply eqp_subp; auto.
  apply sub_box; auto.
  apply eqp_subp2; auto.
Qed.

Lemma diamond_contractive {A} `{ageable A} : forall F (M:modality),
  inclusion _ M fashionR ->
  contractive F ->
  contractive (fun X => diamond M (F X)).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply sub_diamond; auto.
  apply eqp_subp; auto.
  apply sub_diamond; auto.
  apply eqp_subp2; auto.
Qed.

Lemma diamond_nonexpansive {A} `{ageable A} : forall F (M:modality),
  inclusion _ M fashionR ->
  nonexpansive F ->
  nonexpansive (fun X => diamond M (F X)).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply sub_diamond; auto.
  apply eqp_subp; auto.
  apply sub_diamond; auto.
  apply eqp_subp2; auto.
Qed.
*)

Lemma contractive_nonexpansive {A} `{ageable A} : forall F,
  contractive F ->
  nonexpansive F.
Proof.
  unfold contractive, nonexpansive; intros.
  apply @derives_trans with (|>(P <=>Q)); auto.
  apply now_later.
Qed.

Lemma sepcon_contractive {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall F G,
  contractive F ->
  contractive G ->
  contractive (fun x => F x * G x).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply subp_sepcon; apply eqp_subp; auto.
  apply subp_sepcon; apply eqp_subp2; auto.
Qed.

Lemma sepcon_nonexpansive {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall F G,
  nonexpansive F ->
  nonexpansive G ->
  nonexpansive (fun x => F x * G x).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply subp_sepcon; apply eqp_subp; auto.
  apply subp_sepcon; apply eqp_subp2; auto.
Qed.

Lemma wand_contractive {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall F G,
  contractive F ->
  contractive G ->
  contractive (fun x => F x -* G x).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  apply sub_wand.
  apply eqp_subp2; auto.
  apply eqp_subp; auto.
  apply sub_wand.
  apply eqp_subp; auto.
  apply eqp_subp2; auto.
Qed.

Lemma wand_nonexpansive {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall F G,
  nonexpansive F ->
  nonexpansive G ->
  nonexpansive (fun x => F x -* G x).
Proof.
  unfold nonexpansive; intros.
  apply subp_eqp.
  apply sub_wand.
  apply eqp_subp2; auto.
  apply eqp_subp; auto.
  apply sub_wand.
  apply eqp_subp; auto.
  apply eqp_subp2; auto.
Qed.

Lemma prove_contractive {A} `{ageable A} : forall F,
  (forall P Q,
    |>(P >=> Q) |-- F P >=> F Q) ->
  contractive F.
Proof.
  intros.
  unfold contractive.
  intros.
  apply subp_eqp.
  apply @derives_trans with (|>(P >=> Q)).
  apply box_positive.
  apply eqp_subp.
  hnf; auto.
  auto.
  apply @derives_trans with (|>(Q >=> P)).
  apply box_positive.
  apply eqp_subp2.
  hnf; auto.
  auto.
Qed.

Lemma prove_HOcontractive1 {A} `{ageable A} : forall X F,
  (forall P Q: X -> pred A,
    (ALL x:X, |>(P x >=> Q x) |--
        ALL x:X, F P x >=> F Q x)) ->
   HOcontractive F.
Proof.
  unfold HOcontractive.
  repeat intro.
  split.
  eapply H0; eauto.
  repeat intro; eapply H1; eauto.
  eapply H0; eauto.
  repeat intro; eapply H1; eauto.
Qed.


Lemma prove_HOcontractive {A} `{ageable A} : forall X F,
  (forall (P Q: X -> pred A) (x: X),
    (ALL x:X, (|> P x <=> |> Q x) |-- F P x >=> F Q x)) ->
   HOcontractive F.
Proof.
  unfold HOcontractive.
  intros. apply allp_right. intros.
  repeat intro.
  split.
  eapply H0; eauto.
  intro x; specialize (H1 x). apply eqp_later1. auto.
  eapply H0; eauto.
  intro x; specialize (H1 x). rewrite eqp_comm.
  apply eqp_later1. auto.
Qed.

Ltac sub_unfold :=
   match goal with
    | |- _ |-- ?A _ >=> ?A _ => unfold A
    | |- _ |-- ?A _ _ >=> ?A _ _ => unfold A
    | |- _ |-- ?A _ _ _ >=> ?A _ _ _ => unfold A
    | |- _ |-- ?A _ _ _ _ >=> ?A _ _ _ _ => unfold A
    | |- _ |-- ?A _ _ _ _ _ >=> ?A _ _ _ _ _ => unfold A
    | v: _ |- _ => destruct v
   end.

Hint Extern 2 (_ |-- _ >=> _) => sub_unfold : contractive.

Hint Resolve @prove_HOcontractive
  @subp_allp @subp_imp @subp_refl @subp_exp @subp_andp @subp_orp @subp_subp
  @allp_imp2_later_e1 @allp_imp2_later_e2 : contractive.

Lemma Rec_sub {A} `{ageable A} : forall G
  (F   : pred A -> pred A -> pred A)
  (HF1 : forall X, contractive (F X))
  (HF2 : forall R P Q, P >=> Q |-- F P R >=> F Q R)
  (HF3 : forall P Q X, |>(P >=> Q) |-- F X P >=> F X Q),
  forall P Q,
    G |-- P >=> Q ->
    G |-- Rec (F P) >=> Rec (F Q).
Proof.
  intros.
  apply @derives_trans with (P >=> Q); auto.
  clear H0.
  apply goedel_loeb; repeat intro.
  destruct H0.
  rewrite Rec_fold_unfold by auto.
  specialize ( HF2 (Rec (F Q)) P Q).
  specialize ( HF2 a H0 a').
  spec  HF2.  apply necR_level in H2; omega.
  eapply HF2; auto.
  rewrite Rec_fold_unfold in H3 by auto.
  generalize (HF3 (Rec (F P)) (Rec (F Q)) P); intros.
  specialize ( H5 a H4 a').
  spec H5.  apply necR_level in H2; omega.
  eapply H5; auto.
Qed.

Lemma HORec_sub {A} `{ageable A} : forall G B
  (F : pred A -> (B -> pred A) -> B -> pred A)
  (HF1 : forall X, HOcontractive (F X))
  (HF2 : forall R a P Q, P >=> Q |-- F P R a >=> F Q R a)
  (HF3 : forall P Q X, ALL b:B, |>(P b >=> Q b) |-- ALL b:B, F X P b >=> F X Q b),
  forall P Q,
    G |-- P >=> Q ->
    G |-- ALL b:B, HORec (F P) b >=> HORec (F Q) b.
Proof.
  intros.
  apply @derives_trans with (P>=>Q); auto.
  clear H0.
  apply goedel_loeb; repeat intro.
  destruct H0.
  rewrite HORec_fold_unfold by auto.
  specialize ( HF2 (HORec (F Q)) b P Q a H0 a').
  spec HF2. apply necR_level in H2; omega.
  apply HF2; auto.
  rewrite HORec_fold_unfold in H3 by auto.
  rewrite box_all in H4.
  specialize ( HF3 (HORec (F P)) (HORec (F Q)) P a H4 b a').
  spec HF3. apply necR_level in H2; omega.
  apply HF3; auto.
Qed.

Lemma Rec_contractive {A} `{ageable A} : forall
  (F   : pred A -> pred A -> pred A)
  (HF1 : forall X, contractive (F X))
  (HF2 : forall R, contractive (fun X => F X R)),
  contractive (fun X => Rec (F X)).
Proof.
  intros; hnf; intros.
  simpl.
  apply goedel_loeb; repeat intro.
  destruct H0.
  split; repeat intro.
  rewrite Rec_fold_unfold by auto.
  specialize ( HF2 (Rec (F Q)) P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H5; auto.
  rewrite Rec_fold_unfold in H4 by auto.
  generalize (HF1 P (Rec (F P)) (Rec (F Q))); intros.
  specialize ( H7 a).
  detach H7; auto.
  specialize ( H7 a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.

  rewrite Rec_fold_unfold by auto.
  specialize ( HF2 (Rec (F P)) P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H6; auto.
  rewrite Rec_fold_unfold in H4 by auto.
  generalize (HF1 Q (Rec (F P)) (Rec (F Q))); intros.
  specialize ( H7 a).
  detach H7; auto.
  specialize ( H7 a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.
Qed.

Lemma Rec_nonexpansive {A} `{ageable A} : forall
  (F   : pred A -> pred A -> pred A)
  (HF1 : forall X, contractive (F X))
  (HF2 : forall R, nonexpansive (fun X => F X R)),
  nonexpansive (fun X => Rec (F X)).
Proof.
  intros; hnf; intros.
  simpl.
  apply goedel_loeb; repeat intro.
  destruct H0.
  split; repeat intro.
  rewrite Rec_fold_unfold by auto.
  specialize ( HF2 (Rec (F Q)) P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H5; auto.
  rewrite Rec_fold_unfold in H4 by auto.
  generalize (HF1 P (Rec (F P)) (Rec (F Q))); intros.
  specialize ( H7 a).
  detach H7; auto.
  specialize ( H7 a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.

  rewrite Rec_fold_unfold by auto.
  specialize ( HF2 (Rec (F P)) P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H6; auto.
  rewrite Rec_fold_unfold in H4 by auto.
  generalize (HF1 Q (Rec (F P)) (Rec (F Q))); intros.
  specialize ( H7 a).
  detach H7; auto.
  specialize ( H7 a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.
Qed.


Lemma HORec_contractive {A} `{ageable A} : forall B
  (F : pred A -> (B -> pred A) -> B -> pred A)
  (HF1 : forall X, HOcontractive (F X))
  (HF2 : forall R a, contractive (fun X => F X R a)),
  forall a, contractive (fun X => HORec (F X) a).
Proof.
  intros; hnf; intros.
  simpl.
  cut (|>(P <=> Q) |-- ALL a:B, HORec (F P) a <=> HORec (F Q) a).
  repeat intro.
  eapply H0; eauto.

  clear a.
  apply goedel_loeb.
  repeat intro.
  destruct H0.
  split; repeat intro.
  rewrite HORec_fold_unfold by auto.
  specialize ( HF2 (HORec (F Q)) b P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H5; auto.
  rewrite HORec_fold_unfold in H4 by auto.
  generalize (HF1 P (HORec (F P)) (HORec (F Q))); intros.
  specialize ( H7 a).
  detach H7.
  specialize ( H7 b a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.
  rewrite <- box_all.
  auto.

  rewrite HORec_fold_unfold by auto.
  specialize ( HF2 (HORec (F P)) b P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H6; auto.
  rewrite HORec_fold_unfold in H4 by auto.
  generalize (HF1 Q (HORec (F P)) (HORec (F Q))); intros.
  specialize ( H7 a).
  detach H7.
  specialize ( H7 b a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.
  rewrite <- box_all.
  auto.
Qed.

Lemma HORec_nonexpansive {A} `{ageable A} : forall B
  (F : pred A -> (B -> pred A) -> B -> pred A)
  (HF1 : forall X, HOcontractive (F X))
  (HF2 : forall R a, nonexpansive (fun X => F X R a)),
  forall a, nonexpansive (fun X => HORec (F X) a).
Proof.
  intros; hnf; intros.
  simpl.
  cut (P <=> Q |-- ALL a:B, HORec (F P) a <=> HORec (F Q) a).
  repeat intro.
  eapply H0; eauto.

  clear a.
  apply goedel_loeb.
  repeat intro.
  destruct H0.
  split; repeat intro.
  rewrite HORec_fold_unfold by auto.
  specialize ( HF2 (HORec (F Q)) b P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H5; auto.
  rewrite HORec_fold_unfold in H4 by auto.
  generalize (HF1 P (HORec (F P)) (HORec (F Q))); intros.
  specialize ( H7 a).
  detach H7.
  specialize ( H7 b a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.
  rewrite <- box_all.
  auto.

  rewrite HORec_fold_unfold by auto.
  specialize ( HF2 (HORec (F P)) b P Q a H0 a').
  spec HF2. apply necR_level in H3; omega.
  destruct HF2.
  eapply H6; auto.
  rewrite HORec_fold_unfold in H4 by auto.
  generalize (HF1 Q (HORec (F P)) (HORec (F Q))); intros.
  specialize ( H7 a).
  detach H7.
  specialize ( H7 b a').  spec H7. apply necR_level in H3; omega.
  destruct H7; eauto.
  rewrite <- box_all.
  auto.
Qed.

Module Trashcan.

(* Note: This approach to proving HOcontractive doesn't automate
  as well as the methods above.*)

Lemma orp_HOcontractive {A}{agA: ageable A}: forall X (P Q: (X -> pred A) -> (X -> pred A)),
       HOcontractive P -> HOcontractive Q -> HOcontractive (fun R x => P R x || Q R x).
Proof.
 intros.
 intros F G n H2 x y Hy.
 specialize (H F G n H2 x y Hy). specialize (H0 F G n H2 x y Hy).
 destruct H, H0.
 split; (intros z Hz [?|?]; [left|right]); auto.
Qed.
Lemma andp_HOcontractive {A}{agA: ageable A}: forall X (P Q: (X -> pred A) -> (X -> pred A)),
       HOcontractive P -> HOcontractive Q -> HOcontractive (fun R x => P R x && Q R x).
Proof.
 intros.
 intros F G n H2 x y Hy.
 specialize (H F G n H2 x y Hy). specialize (H0 F G n H2 x y Hy).
 destruct H, H0.
 split; (intros z Hz [? ?]); split; auto.
Qed.
Lemma sepcon_HOcontractive {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}: forall X (P Q: (X -> pred A) -> (X -> pred A)),
       HOcontractive P -> HOcontractive Q -> HOcontractive (fun R x => P R x * Q R x).
Proof.
 intros.
 unfold HOcontractive in *|-.
 apply prove_HOcontractive; intros F G ?.
 specialize (H F G). specialize (H0 F G).
 apply subp_sepcon.
 eapply derives_trans.
 apply allp_derives; intro. rewrite <- eqp_later. apply derives_refl.
 eapply derives_trans; [ apply H | ].
 apply allp_left with x.
 apply fash_derives. apply andp_left1. auto.
 eapply derives_trans.
 apply allp_derives; intro. rewrite <- eqp_later. apply derives_refl.
 eapply derives_trans; [ apply H0 | ].
 apply allp_left with x.
 apply fash_derives. apply andp_left1. auto.
Qed.

Lemma const_HOcontractive{A}{agA: ageable A}: forall X (P : X -> pred A), HOcontractive (fun _ => P).
Proof.
 intros.
 apply prove_HOcontractive. intros. apply subp_refl.
Qed.

Lemma exp_HOcontractive {A}{agA: ageable A}:
  forall X Y (G: Y -> X -> X) (F: Y -> X -> pred A -> pred A),
   (forall y x, contractive (F y x)) ->
   HOcontractive (fun (R: X -> pred A) (x: X) => EX y: Y, F y x (R (G y x))).
Proof.
 intros.
 apply prove_HOcontractive; intros.
 apply subp_exp; intro y.
 specialize (H y x (P (G y x)) (Q (G y x))).
 eapply derives_trans; [ | apply eqp_subp; apply H].
 rewrite eqp_later.
 apply allp_left with (G y x). auto.
Qed.
Lemma const_contractive {A}{agA: ageable A}: forall P : pred A, contractive (fun _ => P).
Proof.
 intros.
 apply prove_contractive. intros. apply subp_refl.
Qed.
Lemma later_contractive' {A} `{ageable A} : contractive (box laterM).
Proof.
  unfold contractive; intros.
  apply subp_eqp.
  rewrite <- subp_later.
  apply box_positive; auto.
  apply eqp_subp; auto.
  rewrite <- subp_later.
  apply box_positive; auto.
  apply eqp_subp2; auto.
Qed.

End Trashcan.

