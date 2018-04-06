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
  intros.
  intros sh p.
Admitted.
(*
  destruct (zlt n 0).
  {
    rewrite !data_at_data_at_rec. (* do not use it. *)
    apply andp_derives. apply prop_derives; intros [? ?].
    split; auto.
    admit.
    rewrite !data_at_lemmas.data_at_rec_ind.
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
  apply array_at_ext_derives; auto.
  intros.
  specialize (H0 i H1).
  apply field_at_stronger.
  rewrite H2, H3. rewrite Z.sub_0_r; auto.
Qed.
*)
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
Admitted.

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
  Focus 1. {
    split; intros; [split; intros |].
    + specialize (H gfs H0 H1).
      rewrite data_equal_stronger in H.
      tauto.
    + specialize (H gfs H0 H1).
      rewrite data_equal_stronger in H.
      tauto.
    + rewrite data_equal_stronger; split; apply H; auto.
  } Unfocus.
  pose proof stronger_proj_reptype t v1 v2.
  pose proof stronger_proj_reptype t v2 v1.
  tauto.
Qed.

End STRONGER.

Module DataCmpNotations.
  Notation "X '>>>' Y" := (stronger X Y) (at level 60, no associativity).
  Notation "X '===' Y" := (data_equal X Y) (at level 60, no associativity).
End DataCmpNotations.

Global Existing Instance Equiv_data_equal.
(*Global Existing Instance Proper_fold_reptype_array.*)
Global Existing Instance Proper_field_at.
