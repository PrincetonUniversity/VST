Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Fixpoint fieldlist_no_replicate (f: fieldlist) : bool :=
  match f with
  | Fnil => true
  | Fcons i _ f' => 
    andb (negb (isOK (field_type i f'))) (fieldlist_no_replicate f')
  end.

(************************************************

Lemmas about fieldlist_app

************************************************)

Lemma fieldlist_app_Fnil: forall f, fieldlist_app f Fnil = f.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl. rewrite IHf. reflexivity.
Defined.

Lemma fieldlist_app_Fcons: forall f1 i t f2, fieldlist_app f1 (Fcons i t f2) = fieldlist_app (fieldlist_app f1 (Fcons i t Fnil)) f2.
Proof.
  intros.
  induction f1.
  + reflexivity.
  + simpl.
    rewrite IHf1.
    reflexivity.
Defined.

Lemma fieldlist_app_field_type_isOK: forall i f1 f2, isOK (field_type i (fieldlist_app f1 f2)) = (isOK (field_type i f1) || isOK (field_type i f2)) %bool.
Proof.
  intros.
  induction f1; simpl.
  + reflexivity.
  + if_tac.
    - reflexivity.
    - exact IHf1.
Qed.

Lemma fieldlist_no_replicate_fact:
  forall f1 f2 i, fieldlist_no_replicate (fieldlist_app f1 f2) = true ->
  isOK (field_type i f1) = true -> isOK (field_type i f2) = true -> False.
Proof.
  intros.
  induction f1.
  + inversion H0.
  + simpl in H0, H.
    apply andb_true_iff in H.
    if_tac in H0.
    - destruct H as [? _].
      rewrite fieldlist_app_field_type_isOK in H.
      rewrite negb_true_iff, orb_false_iff in H.
      destruct H as [_ ?].
      subst.
      congruence.
    - destruct H as [_ ?].
      apply IHf1; auto.
Qed.

(************************************************

Lemmas about alignof and alignof_fields

************************************************)

Lemma alignof_fields_hd_divide: forall i t f, Zdivide (alignof t) (alignof_fields (Fcons i t f)).
Proof.
  intros.
  destruct (alignof_two_p t) as [n ?].
  destruct (alignof_fields_two_p (Fcons i t f)) as [m ?].
  assert ((alignof t) <= (alignof_fields (Fcons i t f))) by (apply Z.le_max_l).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide n m H1).
Qed.

Lemma alignof_fields_tl_divide: forall i t f, Zdivide (alignof_fields f) (alignof_fields (Fcons i t f)).
Proof.
  intros.
  destruct (alignof_fields_two_p f) as [n ?].
  destruct (alignof_fields_two_p (Fcons i t f)) as [m ?].
  assert (alignof_fields f <= alignof_fields (Fcons i t f)) by (apply Z.le_max_r).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide n m H1).
Qed.

Lemma alignof_type_divide_whole_fl: forall i t f, field_type i f = Errors.OK t -> (alignof t | alignof_fields f).
Proof.
  intros.
  induction f; simpl in H.
  + inversion H.
  + if_tac in H.
    - inversion H. apply alignof_fields_hd_divide.
    - eapply Z.divide_trans; [exact (IHf H) | apply alignof_fields_tl_divide].
Qed.

(****************************************************************

field_type_hd, field_type_mid, field_offset_hd, field_offset_mid

****************************************************************)

Lemma field_type_hd: forall i t f, field_type i (Fcons i t f) = Errors.OK t.
Proof.
  intros.
  simpl.
  if_tac; [reflexivity | congruence].
Defined.

Lemma field_type_mid: forall i t f' f, fieldlist_no_replicate (fieldlist_app f' (Fcons i t f)) = true -> field_type i (fieldlist_app f' (Fcons i t f)) = Errors.OK t.
Proof.
  intros.
  pose proof field_type_hd i t f.
  assert (isOK (field_type i (Fcons i t f)) = true) by (simpl; if_tac; [| congruence]; reflexivity).
  remember (Fcons i t f) as f''; clear Heqf'' f.
  pose proof (fun HH => fieldlist_no_replicate_fact _ _ _ H HH H1).
  clear H1.
  induction f'.
  + exact H0.
  + simpl in *.
    destruct (ident_eq i i0); [simpl in H2; congruence|].
    apply andb_true_iff in H; destruct H as [_ ?]. 
    exact (IHf' H H2).
Defined.

Lemma field_offset_hd: forall i t f, field_offset i (Fcons i t f) = Errors.OK 0.
Proof.
  intros.
  unfold field_offset.
  simpl.
  if_tac; [rewrite (align_0 _ (alignof_pos _)); reflexivity | congruence].
Defined.

Lemma field_offset_mid: forall i0 t0 i1 t1 f' f ofs, fieldlist_no_replicate (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = true -> field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK ofs -> field_offset i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK (align (ofs + sizeof t1) (alignof t0)).
Proof.
  intros.
  unfold field_offset in *.
  remember 0 as pos; clear Heqpos.
  revert pos H0; induction f'; intros.
  + simpl in *.
    if_tac.
    - if_tac in H; try congruence. inversion H.
    - if_tac in H; try congruence; clear H1.
      if_tac in H0; try congruence; clear H1.
      if_tac; try congruence.
  + simpl in *.
    apply andb_true_iff in H.
    destruct H.
    destruct (isOK (field_type i (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H';
      [rewrite fieldlist_app_field_type_isOK in H; rewrite H' in H;
       destruct (isOK (field_type i f')); inversion H|].
    simpl in H'.
    if_tac in H'; try solve [inversion H'].
    if_tac in H'; try solve [inversion H'].
    if_tac; try congruence.
    if_tac in H0; try congruence.
    apply (IHf' H1), H0.
Defined.

(****************************************************************

Other lemmas

****************************************************************)

Lemma field_offset_in_range': forall sid fld a fid ty,
  field_type fid fld = Errors.OK ty ->
  sizeof ty <= sizeof (Tunion sid fld a).
Proof.
  intros.
  simpl.
  pose proof alignof_pos (Tunion sid fld a).
  assert (sizeof_union fld <= align (sizeof_union fld) (alignof (Tunion sid fld a)))
    by (apply align_le; omega).
  cut (sizeof ty <= sizeof_union fld); [simpl in *; omega |].
  clear -H.
  induction fld.
  + inversion H.
  + simpl in *. if_tac in H.
    - inversion H.
      apply Z.le_max_l.
    - apply Zmax_bound_r, IHfld, H.
Qed.

