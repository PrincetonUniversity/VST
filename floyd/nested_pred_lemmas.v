Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.fieldlist.
Open Scope Z.

(************************************************

Definition, lemmas and useful samples of nested_pred

nested_pred only ensure the specific property to be true on nested types with
memory assigned, i.e. inside structure of pointer, function, empty array are
not included.

************************************************)

Lemma fold_right_map: forall {A B C} (f: B -> A -> A) (g: C -> B) (e: A) (l: list C),
  fold_right f e (map g l) = fold_right (fun c a => f (g c) a) e l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    rewrite IHl.
    reflexivity.
Qed.

Section NESTED_PRED.
Context {cs: compspecs}.

Definition nested_pred (atom_pred: type -> bool): type -> bool :=
  type_func
    (fun _ => bool)
    (fun t => atom_pred t)
    (fun t n a b => (atom_pred (Tarray t n a) && b)%bool)
    (fun id a bl => (atom_pred (Tstruct id a) && fold_right andb true (decay bl))%bool)
    (fun id a bl => (atom_pred (Tunion id a) && fold_right andb true (decay bl))%bool).

Definition nested_fields_pred (atom_pred: type -> bool) (m: members) : bool :=
  fold_right (fun it b => (nested_pred atom_pred (field_type (fst it) m) && b)%bool) true m.

Lemma nested_pred_eq: forall atom_pred t,
  nested_pred atom_pred t =
  match t with
  | Tarray t0 _ _ => (atom_pred t && nested_pred atom_pred t0)%bool
  | Tstruct id _
  | Tunion id _ => (atom_pred t && nested_fields_pred atom_pred (co_members (get_co id)))%bool
  | _ => atom_pred t
  end.
Proof.
  unfold nested_fields_pred.
  intros.
  unfold nested_pred.
  rewrite type_func_eq with (t0 := t) (A := (fun _ => bool)) at 1 by auto.
  destruct t; auto.
  + f_equal. unfold FTI_aux.
    rewrite decay_spec.
    rewrite fold_right_map.
    reflexivity.
  + f_equal. unfold FTI_aux.
    rewrite decay_spec.
    rewrite fold_right_map.
    reflexivity.
Defined.

Lemma nested_pred_atom_pred: forall (atom_pred: type -> bool) (t: type),
  nested_pred atom_pred t = true -> atom_pred t = true.
Proof.
  intros.
  rewrite nested_pred_eq in H by auto.
  destruct t; simpl in *;
  try apply andb_true_iff in H; try tauto.
Defined.

Lemma nested_fields_pred_nested_pred: forall (atom_pred: type -> bool) i m, in_members i m -> nested_fields_pred atom_pred m = true -> nested_pred atom_pred (field_type i m) = true.
Proof.
  intros.
  unfold nested_fields_pred in H0.
  rewrite <- fold_right_map in H0.
  eapply fold_right_andb; [exact H0 |].
  clear - H.
  rewrite <- map_map.
  apply in_map.
  change (field_type i m) with ((fun it => field_type (fst it) m) (i, field_type i m)).
  apply in_map.
  apply in_members_field_type.
  auto.
Defined.

Lemma nested_pred_Tarray: forall (atom_pred: type -> bool) t n a,
  nested_pred atom_pred (Tarray t n a) = true -> nested_pred atom_pred t = true.
Proof.
  intros.
  rewrite nested_pred_eq in H by auto.
  apply andb_true_iff in H.
  tauto.
Defined.

Lemma nested_pred_Tstruct: forall (atom_pred: type -> bool) id a,
  nested_pred atom_pred (Tstruct id a) = true -> nested_fields_pred atom_pred (co_members (get_co id)) = true.
Proof.
  intros.
  rewrite nested_pred_eq in H by auto.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_pred_Tstruct2: forall (atom_pred: type -> bool) id a i,
  nested_pred atom_pred (Tstruct id a) = true ->
  in_members i (co_members (get_co id)) ->
  nested_pred atom_pred (field_type i (co_members (get_co id))) = true.
Proof.
  intros.
  apply nested_pred_Tstruct in H.
  apply nested_fields_pred_nested_pred; auto.
Qed.

Lemma nested_pred_Tunion: forall (atom_pred: type -> bool) id a,
  nested_pred atom_pred (Tunion id a) = true -> nested_fields_pred atom_pred (co_members (get_co id)) = true.
Proof.
  intros.
  rewrite nested_pred_eq in H by auto.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_pred_Tunion2: forall (atom_pred: type -> bool) id a i,
  nested_pred atom_pred (Tunion id a) = true ->
  in_members i (co_members (get_co id)) ->
  nested_pred atom_pred (field_type i (co_members (get_co id))) = true.
Proof.
  intros.
  apply nested_pred_Tunion in H.
  apply nested_fields_pred_nested_pred; auto.
Qed.

Lemma complete_legal_cosu_type_Tstruct: forall id a,
  complete_legal_cosu_type (Tstruct id a) = true ->
  co_su (get_co id) = Struct.
Proof.
  intros.
  simpl in H.
  unfold get_co.
  destruct (cenv_cs ! id); auto.
  destruct (co_su c); congruence.
Qed.

Lemma complete_legal_cosu_type_Tunion: forall id a,
  complete_legal_cosu_type (Tunion id a) = true ->
  co_su (get_co id) = Union.
Proof.
  intros.
  simpl in H.
  unfold get_co.
  destruct (cenv_cs ! id); auto; try congruence.
  destruct (co_su c); congruence.
Qed.

Lemma Tarray_sizeof_0: forall t n a,
  sizeof (Tarray t n a) = 0 ->
  sizeof t = 0 \/ n <= 0.
Proof.
  intros.
  simpl in H.
  apply Z.eq_mul_0 in H.
  destruct H; auto.
  right.
  destruct (zlt 0 n); [| omega].
  rewrite Z.max_r in H by omega.
  omega.
Qed.

Lemma Tstruct_sizeof_0: forall id a,
  complete_legal_cosu_type (Tstruct id a) = true ->
  sizeof (Tstruct id a) = 0 ->
  forall i, in_members i (co_members (get_co id)) ->
  sizeof (field_type i (co_members (get_co id))) = 0 /\
  field_offset_next cenv_cs i (co_members (get_co id)) (co_sizeof (get_co id)) -
   (field_offset cenv_cs i (co_members (get_co id)) +
      sizeof (field_type i (co_members (get_co id)))) = 0.
Proof.
  intros.
  rewrite sizeof_Tstruct in H0.
  rewrite H0.
  apply sizeof_struct_0; auto.
  pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
  erewrite complete_legal_cosu_type_Tstruct in H2 by eauto.
  simpl in H2.
  pose proof align_le (sizeof_struct cenv_cs 0 (co_members (get_co id)))
     (co_alignof (get_co id)) (co_alignof_pos _).
  pose proof sizeof_struct_incr cenv_cs (co_members (get_co id)) 0.
  omega.
Qed.

Lemma Tunion_sizeof_0: forall id a,
  complete_legal_cosu_type (Tunion id a) = true ->
  sizeof (Tunion id a) = 0 ->
  forall i, in_members i (co_members (get_co id)) ->
  sizeof (field_type i (co_members (get_co id))) = 0.
Proof.
  intros.
  rewrite sizeof_Tunion in H0.
  apply sizeof_union_0; auto.
  pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
  erewrite complete_legal_cosu_type_Tunion in H2 by eauto.
  simpl in H2.
  pose proof align_le (sizeof_union cenv_cs (co_members (get_co id)))
     (co_alignof (get_co id)) (co_alignof_pos _).
  pose proof sizeof_union_pos cenv_cs (co_members (get_co id)).
  omega.
Qed.

End NESTED_PRED.

(************************************************

Arithmetic properties with nested_pred assumption.

************************************************)

Ltac pose_mod_le A :=
  let H := fresh "H" in
  pose proof Z.mod_le A Ptrofs.modulus;
  spec H; [try omega | spec H; [pose Ptrofs.modulus_pos; omega |]].

Ltac pose_mul_distr_l l r :=
  match r with
  | (?A + ?B)%Z => pose proof Z.mul_add_distr_l l A B;
                   pose_mul_distr_l l A;
                   pose_mul_distr_l l B
  | Z.succ ?A => let H := fresh "H" in
                 pose proof Z.mul_add_distr_l l A 1 as H;
                 replace (A + 1) with (Z.succ A) in H by omega;
                 pose_mul_distr_l l A
  | (?A - ?B)%Z => pose proof Z.mul_sub_distr_l l A B;
                   pose_mul_distr_l l A;
                   pose_mul_distr_l l B
  | _ => idtac
  end.


Ltac pose_size_mult' env t l :=
  match l with
  | nil => idtac
  | ?z :: ?l0 =>
    match l0 with
    | nil => pose_mul_distr_l (@sizeof env t) z
    | ?z0 :: _ => pose_mul_distr_l (@sizeof env t) z;
                  assert (@sizeof env t * z <= @sizeof env t * z0) by
                    (pose proof @sizeof_pos env t; apply Zmult_le_compat_l; omega);
                  pose_size_mult' env t l0
    end
  end.

Ltac pose_size_mult env t l :=
  pose_size_mult' env t l;
  try rewrite !Z.mul_0_r in *;
  try rewrite !Z.mul_1_r in *.

Definition align_alignof a b := align a b.

Definition sizeof_struct_le := sizeof_struct.

Ltac pose_align_le :=
  repeat
  match goal with
  | |- context [align ?A (@alignof ?env ?t)] =>
         assert (A <= align A (@alignof env t)) by (apply align_le, @alignof_pos);
         change (align A (@alignof env t)) with (align_alignof A (@alignof env t))
  | |- context [align ?A (co_alignof ?co)] =>
         let x := fresh "x" in
         assert (A <= align A (co_alignof co)) by (apply align_le; destruct (co_alignof_two_p co) as [x ?];
           pose proof two_power_nat_pos x; omega);
         change (align A (co_alignof co)) with (align_alignof A (co_alignof co))
  | |- context [sizeof_struct ?env ?A ?m] =>
         pose proof sizeof_struct_incr env m A;
         change (sizeof_struct env A m) with (sizeof_struct_le env A m)
  end;
  try unfold align_alignof in *;
  try unfold sizeof_struct_le in *.

Definition sizeofp := @sizeof.

Ltac pose_sizeof_pos :=
  repeat
  match goal with
  | |- context [@sizeof ?env ?t] =>
         pose proof @sizeof_pos env t;
         change (@sizeof env t) with (sizeofp env t)
  end;
  unfold sizeofp in *.

Ltac pose_sizeof_co t :=
  match t with
  | Tstruct ?id ?a =>
    pose proof sizeof_Tstruct id a;
    assert (sizeof_struct cenv_cs 0 (co_members (get_co id)) <= co_sizeof (get_co id)); [
      rewrite co_consistent_sizeof with (env := cenv_cs) by (apply get_co_consistent);
      rewrite complete_legal_cosu_type_Tstruct with (a0 := a) by auto;
      apply align_le, co_alignof_pos
       |]
  | Tunion ?id ?a =>
    pose proof sizeof_Tunion id a;
    assert (sizeof_union cenv_cs (co_members (get_co id)) <= co_sizeof (get_co id)); [
      rewrite co_consistent_sizeof with (env := cenv_cs) by (apply get_co_consistent);
      rewrite complete_legal_cosu_type_Tunion with (a0 := a) by auto;
      apply align_le, co_alignof_pos
       |]
  end.

Ltac pose_field :=
  match goal with
  | _ : complete_legal_cosu_type (Tstruct ?id ?a) = true |-
    context [@sizeof cenv_cs (field_type ?i (co_members (get_co ?id)))] =>
      pose_sizeof_co (Tstruct id a);
      let H := fresh "H" in
      pose proof field_offset_in_range i (co_members (get_co id)) as H;
      spec H; [solve [auto] |];
      pose proof @sizeof_pos cenv_cs (field_type i (co_members (get_co id)))
  | _ : complete_legal_cosu_type (Tunion ?id ?a) = true |-
    context [@sizeof cenv_cs (field_type ?i (co_members (get_co ?id)))] =>
      pose_sizeof_co (Tunion id a);
      let H := fresh "H" in
      pose proof sizeof_union_in_members i (co_members (get_co id)) as H;
      spec H; [solve [auto] |];
      pose proof @sizeof_pos cenv_cs (field_type i (co_members (get_co id)))
  | _ => idtac
  end;
  match goal with
  | _ : complete_legal_cosu_type (Tstruct ?id ?a) = true |-
    context [field_offset_next cenv_cs ?i (co_members (get_co ?id)) (co_sizeof (get_co ?id))] =>
      let H := fresh "H" in
      pose proof field_offset_next_in_range i (co_members (get_co id)) (co_sizeof (get_co id));
      spec H; [solve [auto] |];
      spec H; [solve [auto | pose_sizeof_co (Tstruct id a); auto] |]
  | _ => idtac
  end
.
