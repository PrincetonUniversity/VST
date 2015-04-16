Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.rangespec_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.
Definition stronger {t: type} (v v': reptype t) : Prop :=
  forall sh, data_at sh t v |-- data_at sh t v'.

Definition data_equal {t} v1 v2 := forall sh, data_at sh t v1 = data_at sh t v2.

Module DataCmpNotations.
  Notation "X '>>>' Y" := (stronger X Y) (at level 60, no associativity).
  Notation "X '===' Y" := (data_equal X Y) (at level 60, no associativity).
End DataCmpNotations.

Import DataCmpNotations.

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
  (forall i, 0 <= i < n -> Znth i v0 (default_val _) >>> Znth i v1 (default_val _)) ->
  v0 >>> v1.
Proof.
  intros.
  intros sh p.
  unfold data_at; simpl.
  normalize.
  unfold array_at', rangespec.
  normalize.
  destruct (zlt n 0).
  {
    rewrite Z.sub_0_r.
    rewrite Z2Nat_neg by omega.
    simpl; auto.
  }
  assert (forall i : Z, n - Z.of_nat (nat_of_Z (n - 0)) <= i < n ->
    Znth i v0 (default_val t0) >>> Znth i v1 (default_val t0)).
  Focus 1. {
    intros.
    apply H.
    rewrite Z.sub_0_r in H4.
    rewrite Z2Nat.id in H4 by omega.
    omega.
  } Unfocus.
  assert (n - Z.of_nat (nat_of_Z (n - 0)) = 0) by (rewrite Z2Nat.id by omega; omega).
  assert (0 <= 0) by omega.
  revert H5 H6.
  generalize 0 at 2 4 5 9.
  induction (nat_of_Z (n - 0)); intros.
  + simpl. auto.
  + simpl.
    apply sepcon_derives.
    - assert (legal_alignas_type t0 = true).
      Focus 1. {
        change t0 with (nested_field_type2 (Tarray t0 n a) (ArraySubsc 0 :: nil)).
        apply nested_field_type2_nest_pred; auto.
      } Unfocus.
      assert (legal_nested_field (Tarray t0 n a) (ArraySubsc z :: nil)).
      Focus 1. {
        solve_legal_nested_field.
        rewrite Nat2Z.inj_succ in H5.
        omega.
      } Unfocus.
      apply stronger_data_at'_derives;
        [| | | unfold field_compatible; split; [|split; [| split; [| split; [| split]]]]]; auto.
      * apply Z.divide_mul_l.
        apply legal_alignas_sizeof_alignof_compat; auto.
      * apply H.
        rewrite Nat2Z.inj_succ in H5.
        omega.
      * autorewrite with norm.
        auto.
      * change (sizeof t0 * z)%Z with (nested_field_offset2 (Tarray t0 n a) (ArraySubsc z :: nil)).
        change t0 with (nested_field_type2 (Tarray t0 n a) (ArraySubsc z :: nil)) at 1.
        apply size_compatible_nested_field; auto.
      * change (sizeof t0 * z)%Z with (nested_field_offset2 (Tarray t0 n a) (ArraySubsc z :: nil)).
        change t0 with (nested_field_type2 (Tarray t0 n a) (ArraySubsc z :: nil)) at 1.
        apply align_compatible_nested_field; auto.
      * apply legal_nested_field_nil_lemma.
    - apply IHn0.
      * intros.
        apply H4.
        rewrite Nat2Z.inj_succ.
        omega.
      * rewrite Nat2Z.inj_succ in H5.
        omega.
      * omega.
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
  (forall i, 0 <= i < n -> Znth i v0 (default_val _) === Znth i v1 (default_val _)) ->
  v0 === v1.
Proof.
  intros.
  assert (forall i : Z, 0 <= i < n -> Znth i v0 (default_val t0) >>> Znth i v1 (default_val t0)).
  Focus 1. {
    intros.
    specialize (H i H0).
    destruct (data_equal_stronger (Znth i v0 (default_val t0)) (Znth i v1 (default_val t0))) as [? _].
    tauto.
  } Unfocus.
  assert (forall i : Z, 0 <= i < n -> Znth i v1 (default_val t0) >>> Znth i v0 (default_val t0)).
  Focus 1. {
    intros.
    specialize (H i H1).
    destruct (data_equal_stronger (Znth i v0 (default_val t0)) (Znth i v1 (default_val t0))) as [? _].
    tauto.
  } Unfocus.
  apply data_equal_stronger; split; apply stronger_array_ext; auto.
Qed.

Lemma data_equal_firstn: forall t n a (v v': list (reptype t)),
  firstn (Z.to_nat n) v = firstn (Z.to_nat n) v' ->
  @data_equal (Tarray t n a) v v'.
Proof.
  intros.
  apply data_equal_array_ext.
 fold reptype.
   intros.
 replace  (@Znth (reptype t) i v' (default_val t))
   with    (@Znth (reptype t) i v (default_val t)).
 apply data_equal_refl.
 unfold Znth.
 if_tac; auto.
 assert (Z.to_nat i < Z.to_nat n)%nat.
 apply Z2Nat.inj_lt; omega.
 forget (Z.to_nat n) as nn.
 forget (Z.to_nat i) as j.
 clear - H H2.
 revert nn v v' H H2; induction j; destruct nn, v,v'; simpl; intros; auto;
    try omega; inv H.
 auto.
 apply (IHj _ _ _ H3).
 omega.
Qed.

Lemma nth_list_repeat: forall A i n (x :A),
    nth i (list_repeat n x) x = x.
Proof.
 induction i; destruct n; simpl; auto.
Qed.

Lemma data_equal_list_repeat_default: forall t n a (v: list (reptype t)) m,
  @data_equal (Tarray t n a) v (v ++ list_repeat m (default_val t)).
Proof.
  intros.
  apply data_equal_array_ext.
  intros.
  unfold Znth; if_tac; [omega |].
  pattern v at 1.
  replace v with (v ++ nil) by (rewrite <- app_nil_r; reflexivity).
  destruct (lt_dec (Z.to_nat i) (length v)).
  + rewrite !app_nth1 by auto.
    apply data_equal_refl.
  + rewrite !app_nth2 by omega.
    rewrite nth_list_repeat.
    destruct (Z.to_nat i - length v)%nat; apply data_equal_refl.
Qed.

Lemma eq_JMeq: forall A (x y: A), x=y -> JMeq x y.
Proof. intros. subst. reflexivity.
Qed.
