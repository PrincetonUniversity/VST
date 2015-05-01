Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

Section STRONGER.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Definition stronger {t: type} (v v': reptype t) : Prop :=
  forall sh, data_at sh t v |-- data_at sh t v'.

Definition data_equal {t} v1 v2 := forall sh, data_at sh t v1 = data_at sh t v2.

Notation "X '>>>' Y" := (stronger X Y) (at level 60, no associativity).
Notation "X '===' Y" := (data_equal X Y) (at level 60, no associativity).

Lemma stronger_refl: forall t (v: reptype t), v >>> v.
Proof.
  intros t v sh p.
  auto.
Qed.

Lemma eq_rect_r_stronger: forall {t1 t2} v0 v1 (H: t1 = t2),
  v0 >>> v1 ->
  eq_rect_r reptype v0 H >>> eq_rect_r reptype v1 H.
Proof.
  intros.
  generalize H.
  subst.
  intros.
  unfold eq_rect_r.
  rewrite <- !eq_rect_eq.
  auto.
Qed.
(*
Lemma stronger_data_at'_derives: forall sh t v0 v1 pos p,
  legal_alignas_type t = true ->
  (alignof t | pos) ->
  v0 >>> v1 ->
  field_compatible t nil (offset_val (Int.repr pos) p) ->
  data_at' sh type_id_env.empty_ti t pos v0 p |--
    data_at' sh type_id_env.empty_ti t pos v1 p.
Proof.
  intros.
  specialize (H1 sh (offset_val (Int.repr pos) p)).
  unfold data_at in H1.
  simpl in H1.
  unfold field_compatible in H2.
  destruct H2 as [? [? [? [? [? ?]]]]].
  normalize in H1.
  rewrite !data_at'_at_offset' with (pos := pos) by auto.
  rewrite !at_offset'_eq by (rewrite <- data_at'_offset_zero; reflexivity).
  exact H1.
Qed.
*)
(*
Lemma stronger_data_at'_nested_field_derives: forall sh t gfs t0 v0 v1 p,
  legal_alignas_type t = true ->
  nested_field_type2 t gfs = t0 ->
  legal_nested_field t gfs ->
  v0 >>> v1 ->
  size_compatible t p ->
  align_compatible t p ->
  data_at' sh type_id_env.empty_ti t0 (nested_field_offset2 t gfs) v0 p |--
    data_at' sh type_id_env.empty_ti t0 (nested_field_offset2 t gfs) v1 p.
Proof.
  intros.
  apply stronger_data_at'_derives; auto.
  + rewrite <- H0.
    apply nested_field_type2_nest_pred; auto.
  + rewrite <- H0.
    apply nested_field_offset2_type2_divide; auto.
  + rewrite <- H0.
    apply size_compatible_nested_field; auto.
  + rewrite <- H0.
    apply align_compatible_nested_field; auto.
Qed.
*)

Lemma stronger_trans: forall t (v0 v1 v2: reptype t),
  v0 >>> v1 -> v1 >>> v2 -> v0 >>> v2.
Proof.
  intros.
  intro sh.
  eapply derives_trans.
  apply H.
  apply H0.
Qed.

Lemma field_at_stronger: forall sh t gfs v0 v1,
  v0 >>> v1 ->
  field_at sh t gfs v0 |-- field_at sh t gfs v1.
Proof.
  intros.
  intros p.
  rewrite !field_at_data_at by exact H.
  simpl.
  normalize.
  apply H.
Qed.

Lemma stronger_array_ext: forall t0 n a (v0 v1: reptype (Tarray t0 n a)),
  (forall i, 0 <= i < n -> zl_nth i (unfold_reptype v0) >>> zl_nth i (unfold_reptype v1)) ->
  v0 >>> v1.
Proof.
  intros.
  intros sh p.  
  destruct (zlt n 0).
  {
    rewrite !data_at_data_at'.
    rewrite !data_at_lemmas.data_at'_ind.
    rewrite !aggregate_pred.aggregate_pred.array_pred_len_0 by omega.
    auto.
  }
  unfold data_at.
  erewrite field_at_Tarray; [| simpl; auto  | reflexivity | omega | ].
  Focus 2. {
    instantiate (1 := unfold_reptype v0).
    symmetry. apply (unfold_reptype_JMeq (Tarray t0 n a)).
  } Unfocus.
  erewrite field_at_Tarray; [| simpl; auto  | reflexivity | omega | ].
  Focus 2. {
    instantiate (1 := unfold_reptype v1).
    symmetry. apply (unfold_reptype_JMeq (Tarray t0 n a)).
  } Unfocus.
  apply array_at_ext_derives.
  intros.
  specialize (H i H0).
  apply field_at_stronger.
  rewrite H1, H2.
  auto.
Qed.

Lemma stronger_default_val: forall t v, v >>> default_val t.
Proof.
  intros.
  intros sh p.
  apply data_at_data_at_.
Qed.

Lemma data_equal_stronger: forall {t} (v1 v2: reptype t), (v1 === v2) <-> (v1 >>> v2) /\ (v2 >>> v1).
Proof.
  intros.
  split; intro.
  + split; intro sh; rewrite H; auto.
  + destruct H.
    intro sh; apply pred_ext; [apply H | apply H0].
Qed.

Lemma data_equal_JMeq:
  forall t t' a a' b b',
    t=t' ->
    @JMeq (reptype t) a (reptype t') a' ->
    @JMeq (reptype t) b (reptype t') b' ->
    data_equal a b -> data_equal a' b'.
Proof.
intros. subst t'.
apply JMeq_eq in H0. apply JMeq_eq in H1.
subst; auto.
Qed.

Lemma data_equal_refl: forall t (v: reptype t), v === v.
Proof.
  intros.
  intro sh; reflexivity.
Qed.

Lemma data_equal_sym: forall t (v1 v2: reptype t), v1 === v2 -> v2 === v1.
Proof.
  intros.
  intro sh.
  rewrite H.
  reflexivity.
Qed.

Lemma data_equal_trans: forall t (v1 v2 v3: reptype t), v1 === v2 -> v2 === v3 -> v1 === v3.
Proof.
  intros.
  intro sh.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma field_at_data_equal: forall sh t gfs v0 v1,
  v0 === v1 ->
  field_at sh t gfs v0 = field_at sh t gfs v1.
Proof.
  intros.
  destruct (data_equal_stronger v0 v1) as [? _].
  spec H0; [auto |].
  apply pred_ext; apply field_at_stronger; tauto.
Qed.

Lemma data_equal_array_ext: forall t0 n a (v0 v1: reptype (Tarray t0 n a)),
  (forall i, 0 <= i < n -> zl_nth i (unfold_reptype v0) === zl_nth i (unfold_reptype v1)) ->
  v0 === v1.
Proof.
  intros.
  apply data_equal_stronger; split; apply stronger_array_ext; auto.
  + intros.
    specialize (H i H0).
    destruct (data_equal_stronger (zl_nth i (unfold_reptype v0)) (zl_nth i (unfold_reptype v1))) as [? _].
    tauto.
  + intros.
    specialize (H i H0).
    destruct (data_equal_stronger (zl_nth i (unfold_reptype v0)) (zl_nth i (unfold_reptype v1))) as [? _].
    tauto.
Qed.

Lemma data_equal_zl_equiv: forall t n a (v v': reptype (Tarray t n a)),
  zl_equiv (unfold_reptype v) (unfold_reptype v') ->
  @data_equal (Tarray t n a) v v'.
Proof.
  intros.
  apply data_equal_array_ext.
  intros.
  specialize (H i H0).
  rewrite H.
  apply data_equal_refl.
Qed.

(* maybe not usefull any more *)
Lemma nth_list_repeat: forall A i n (x :A),
    nth i (list_repeat n x) x = x.
Proof.
 induction i; destruct n; simpl; auto.
Qed.

End STRONGER.

Module DataCmpNotations.
  Notation "X '>>>' Y" := (stronger X Y) (at level 60, no associativity).
  Notation "X '===' Y" := (data_equal X Y) (at level 60, no associativity).
End DataCmpNotations.

