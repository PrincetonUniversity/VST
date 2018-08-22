(* TODO: remove this file *)
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.closed_lemmas.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import VST.floyd.sublist.

Local Open Scope logic.

Section STRONGER.

Context {cs: compspecs}.

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

Lemma stronger_JMeq:
  forall t t' a a' b b',
    t=t' ->
    @JMeq (reptype t) a (reptype t') a' ->
    @JMeq (reptype t) b (reptype t') b' ->
    a >>> b -> a' >>> b'.
Proof.
intros. subst t'.
apply JMeq_eq in H0. apply JMeq_eq in H1.
subst; auto.
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
Lemma stronger_data_at_rec_derives: forall sh t v0 v1 pos p,
  legal_alignas_type t = true ->
  (alignof t | pos) ->
  v0 >>> v1 ->
  field_compatible t nil (offset_val (Int.repr pos) p) ->
  data_at_rec sh type_id_env.empty_ti t pos v0 p |--
    data_at_rec sh type_id_env.empty_ti t pos v1 p.
Proof.
  intros.
  specialize (H1 sh (offset_val (Int.repr pos) p)).
  unfold data_at in H1.
  simpl in H1.
  unfold field_compatible in H2.
  destruct H2 as [? [? [? [? [? ?]]]]].
  normalize in H1.
  rewrite !data_at_rec_at_offset' with (pos := pos) by auto.
  rewrite !at_offset'_eq by (rewrite <- data_at_rec_offset_zero; reflexivity).
  exact H1.
Qed.
*)
(*
Lemma stronger_data_at_rec_nested_field_derives: forall sh t gfs t0 v0 v1 p,
  legal_alignas_type t = true ->
  nested_field_type2 t gfs = t0 ->
  legal_nested_field t gfs ->
  v0 >>> v1 ->
  size_compatible t p ->
  align_compatible t p ->
  data_at_rec sh type_id_env.empty_ti t0 (nested_field_offset2 t gfs) v0 p |--
    data_at_rec sh type_id_env.empty_ti t0 (nested_field_offset2 t gfs) v1 p.
Proof.
  intros.
  apply stronger_data_at_rec_derives; auto.
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
 Zlength (unfold_reptype v0) = Zlength (unfold_reptype v1) ->
  (forall i, 0 <= i < n -> Znth i (unfold_reptype v0)  >>> Znth i (unfold_reptype v1)) ->
  v0 >>> v1.
Proof.
  intros; intros sh p.
  unfold data_at.
  destruct (zle n 0).
*
  unfold field_at.
  entailer.
  apply derives_refl'.
  f_equal.
  unfold nested_field_type; simpl.
  rewrite !data_at_rec_eq.
  rewrite Z.max_l by omega.
  unfold aggregate_pred.aggregate_pred.array_pred.
  unfold aggregate_pred.array_pred.
  simpl.
  extensionality Vundef.
  f_equal. f_equal.
  change (unfold_reptype v0) with v0.
  change (unfold_reptype v1) with v1.
  rewrite H. auto.
*
  assert_PROP (Zlength (unfold_reptype v0) = n). {
     entailer!. destruct H2 as [? _]. rewrite Z.max_r in H2 by omega. auto.
  }
  rewrite H1 in H. symmetry in H.
  unfold field_at.
  normalize.
  unfold at_offset.
  unfold nested_field_offset, nested_field_type;   simpl.
  rewrite !data_at_rec_eq.
  unfold aggregate_pred.aggregate_pred.array_pred.
  unfold aggregate_pred.array_pred.
  rewrite Z.max_r by omega. rewrite Z.sub_0_r.
  normalize.
  apply aggregate_pred.rangespec_ext_derives.
  intros.
  unfold at_offset.
  rewrite Z.sub_0_r.
  rewrite Z2Nat.id in H3 by omega. rewrite Z.add_0_l in H3.
  specialize (H0 _ H3 sh).
  unfold data_at, field_at in H0.
  simpl in H0.
  specialize (H0 (offset_val (sizeof t0 * i) p)).
  assert (field_compatible t0 nil (offset_val (sizeof t0 * i) p)). {
   destruct (zle (sizeof t0) 0).
  - assert (sizeof t0 = 0) by (pose proof (sizeof_pos t0); omega).
     rewrite H4. rewrite Z.mul_0_l.
     clear - H2 H4 H3.
    destruct H2 as [? [? [? [? ?]]]].
    destruct p; try contradiction.
    split3; [ | | split3]; auto.
    red. simpl. rewrite H4. rewrite Z.add_0_r.
    red in H1. simpl in H1. rewrite H4 in H1. rewrite Z.mul_0_l in H1.
    rewrite Ptrofs.add_zero. omega.
   red in H2|-*. apply align_compatible_rec_Tarray_inv with (i:=i) in H2; auto.
   rewrite H4 in H2. rewrite Z.mul_0_l, Z.add_0_r in H2. simpl.
    rewrite Ptrofs.add_zero. auto.
   -
    clear - H2 H3 g0.
    destruct H2 as [? [? [? [? ?]]]].
    assert (H5: 0 <= sizeof t0 * i < sizeof t0 * n). {
      replace 0 with (sizeof t0 * 0)%Z by (rewrite Z.mul_0_r; auto).
      pose proof (sizeof_pos t0).
      split.
      apply Zmult_le_compat_l; omega.
      apply Zmult_lt_compat_l; omega.
    }
    hnf in H1. destruct p; try contradiction.
    simpl in H1. rewrite Z.max_r in H1 by omega.
    split3; [ | | split3]; auto.
   +
    red. simpl.
    rewrite Ptrofs.add_unsigned.
    pose proof (Ptrofs.unsigned_range i0).
    rewrite (Ptrofs.unsigned_repr (_*_))
      by (change (Ptrofs.max_unsigned) with (Ptrofs.modulus - 1); omega).
    rewrite (Ptrofs.unsigned_repr)
      by (change (Ptrofs.max_unsigned) with (Ptrofs.modulus - 1); omega).
    assert (sizeof t0 * i + sizeof t0 <= sizeof t0 * n). {
       rewrite <- (Z.mul_1_r (sizeof t0)) at 2.
       rewrite <- Z.mul_add_distr_l.
      apply Zmult_le_compat_l; omega.
    }
    omega.
    +
     red in H2. apply align_compatible_rec_Tarray_inv with (i:=i) in H2; auto.
     unfold offset_val. 
     red.
     rewrite Ptrofs.add_unsigned.
    pose proof (Ptrofs.unsigned_range i0).
    rewrite (Ptrofs.unsigned_repr (_*_))
      by (change (Ptrofs.max_unsigned) with (Ptrofs.modulus - 1); omega).
    rewrite (Ptrofs.unsigned_repr)
      by (change (Ptrofs.max_unsigned) with (Ptrofs.modulus - 1); omega).
    auto.
  }
  rewrite !prop_true_andp in H0 by auto.
  unfold at_offset in H0.
  unfold nested_field_offset, nested_field_type in H0;   simpl in H0.
  rewrite !offset_offset_val in H0.
  rewrite Z.add_0_r in H0. apply H0.
Qed.

Lemma stronger_default_val: forall t v, v >>> default_val t.
Proof.
  intros.
  intros sh p.
  unfold data_at.
  apply field_at_field_at_.
Qed.

Lemma stronger_proj_reptype: forall t v1 v2,
  (v1 >>> v2) <->
  (forall gfs, legal_nested_field t gfs -> type_is_by_value (nested_field_type t gfs) = true ->
   proj_reptype t gfs v1 >>> proj_reptype t gfs v2).
Proof.
intros.
split; intros.
hnf; intros.
specialize (H sh).
unfold data_at in *.
intro p.
unfold field_at in *.
normalize.
unfold at_offset.
unfold nested_field_type at 1 4. simpl.
unfold nested_field_offset; simpl.
unfold nested_field_offset in H; simpl in H.
unfold at_offset in H.
unfold nested_field_type in H; simpl in H.
Abort.  (* probably true, but not needed *)

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
    a === b -> a' === b'.
Proof.
intros. subst t'.
apply JMeq_eq in H0. apply JMeq_eq in H1.
subst; auto.
Qed.

Lemma eq_rect_r_data_equal: forall {t1 t2} v0 v1 (H: t1 = t2),
  v0 === v1 ->
  eq_rect_r reptype v0 H === eq_rect_r reptype v1 H.
Proof.
  intros.
  generalize H.
  subst.
  intros.
  unfold eq_rect_r.
  rewrite <- !eq_rect_eq.
  auto.
Qed.

Instance Equiv_data_equal t: Equivalence (@data_equal t).
Proof.
  unfold data_equal; split.
  + intro; intros.
    reflexivity.
  + intro; intros.
    rewrite H; reflexivity.
  + intro; intros.
    rewrite H, H0; reflexivity.
Defined.

Lemma data_equal_refl': forall t (v v': reptype t), v = v' -> v === v'.
Proof.
  intros. subst. reflexivity.
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

Instance Proper_field_at: forall sh t gfs,
  Proper ((@data_equal _) ==> eq) (field_at sh t gfs).
Proof.
  intros.
  intro; intros.
  apply field_at_data_equal; auto.
Defined.

Lemma data_equal_array_ext: forall t0 n a (v0 v1: reptype (Tarray t0 n a)),
 Zlength (unfold_reptype v0) = Zlength (unfold_reptype v1) ->
  (forall i, 0 <= i < n ->
     Znth i (unfold_reptype v0) === Znth i (unfold_reptype v1)) ->
  v0 === v1.
Proof.
  intros.
  apply data_equal_stronger; split; apply stronger_array_ext; auto.
  + intros.
    specialize (H0 i H1).
    destruct (data_equal_stronger
                      (Znth i (unfold_reptype v0))
                      (Znth i (unfold_reptype v1))) as [? _].
    tauto.
  + intros.
    specialize (H0 i H1).
    destruct (data_equal_stronger
                      (Znth i (unfold_reptype v0))
                      (Znth i (unfold_reptype v1))) as [? _].
    tauto.
Qed.

(*
Lemma data_equal_zl_equiv: forall t n a (v v': reptype (Tarray t n a)),
  zl_equiv (unfold_reptype v) (unfold_reptype v') ->
  @data_equal (Tarray t n a) v v'.
Proof.
  intros.
  apply data_equal_array_ext.
  intros.
  specialize (H i H0).
  rewrite H.
  reflexivity.
Qed.

Lemma data_equal_zl_equiv': forall t n a v v',
  zl_equiv v v' ->
  @fold_reptype _ _ (Tarray t n a) v === @fold_reptype _ _ (Tarray t n a) v'.
Proof.
  intros.
  apply data_equal_zl_equiv.
  rewrite !unfold_fold_reptype.
  auto.
Qed.

Instance Proper_fold_reptype_array: forall t n a,
  Proper ((@zl_equiv (reptype t) (default_val _) (list_zlist _ _) 0 n)
               ==> (@data_equal (Tarray t n a))) (@fold_reptype _ _ (Tarray t n a)).
Proof.
  intros.
  intro; intros.
  apply data_equal_zl_equiv'.
  auto.
Defined.
*)

Lemma data_equal_proj_reptype: forall t v1 v2,
  (v1 === v2) <->
  (forall gfs, legal_nested_field t gfs -> type_is_by_value (nested_field_type t gfs) = true ->
   proj_reptype t gfs v1 === proj_reptype t gfs v2).
Proof.
  intros.
  rewrite data_equal_stronger.
  assert ((forall gfs : list gfield,
    legal_nested_field t gfs ->
    type_is_by_value (nested_field_type t gfs) = true ->
    proj_reptype t gfs v1 === proj_reptype t gfs v2) <->
    (forall gfs : list gfield,
    legal_nested_field t gfs ->
    type_is_by_value (nested_field_type t gfs) = true ->
    proj_reptype t gfs v1 >>> proj_reptype t gfs v2) /\
    (forall gfs : list gfield,
    legal_nested_field t gfs ->
    type_is_by_value (nested_field_type t gfs) = true ->
    proj_reptype t gfs v2 >>> proj_reptype t gfs v1)).
  {
    split; intros; [split; intros |].
    + specialize (H gfs H0 H1).
      rewrite data_equal_stronger in H.
      tauto.
    + specialize (H gfs H0 H1).
      rewrite data_equal_stronger in H.
      tauto.
    + rewrite data_equal_stronger; split; apply H; auto.
  }
(*  pose proof stronger_proj_reptype t v1 v2.
  pose proof stronger_proj_reptype t v2 v1.
  tauto.
*)
Abort.  (* not needed *)

End STRONGER.

Module DataCmpNotations.
  Notation "X '>>>' Y" := (stronger X Y) (at level 60, no associativity).
  Notation "X '===' Y" := (data_equal X Y) (at level 60, no associativity).
End DataCmpNotations.

Global Existing Instance Equiv_data_equal.
(*Global Existing Instance Proper_fold_reptype_array.*)
Global Existing Instance Proper_field_at.