Require Import AggregateType.demo1.expr.
Require Import AggregateType.demo1.type_rec_functions.
Require Import AggregateType.demo1.path_rec_functions.

Definition field_at (t: type) (nf: list ident) (v: reptype (nested_field_type t nf)) (p: val) : Pred := at_offset (data_at_rec (nested_field_type t nf) v) (nested_field_offset t nf) p.

Definition data_at (t: type) (v: reptype t) (p: val) : Pred := field_at t nil v p.

Definition field_address (t: type) (nf: list ident) (p: val) : val := offset_val (nested_field_offset t nf) p.

(* Unfolding Equations *)
Lemma data_at_field_at: forall t v p,
  data_at t v p = field_at t nil v p.
Proof.
  reflexivity.
Qed.

Lemma field_at_Tint: forall t nf v1 v2 p,
  nested_field_type t nf = Tint ->
  JMeq v1 v2 ->
  field_at t nf v1 p = mapsto (field_address t nf p) v2.
Proof.
  intros.
  unfold field_at, field_address.
  revert v1 H0.
  rewrite H; intros.
  apply JMeq_eq in H0. subst v1.
  unfold at_offset.
  reflexivity.
Qed.

Lemma field_at_Tstruct: forall t nf id fs v p,
  nested_field_type t nf = Tstruct id fs ->
  members_no_replicate fs ->
  field_at t nf v p =
   (fix field_at_struct fs :=
      match fs with
      | Fnil => emp
      | Fcons (i0, t0) fs0 =>
                field_at t (i0 :: nf) (proj_reptype _ (i0 :: nil) v) p *
                field_at_struct fs0
      end) fs.
Proof.
  intros.
  unfold field_at, at_offset.
  simpl; revert v; rewrite H; simpl; clear H.
  set (ofs := nested_field_offset t nf); clearbody ofs; clear t.
  intros.

  assert (forall i, in_members i fs -> field_type i fs = field_type i fs) by auto.
  assert (forall i, in_members i fs -> JMeq (proj_struct i fs v) (proj_struct i fs v)) by (intros; apply JMeq_refl).
  revert H H1.
  generalize v at 2 4.
  generalize fs at 1 4 8 9 11 12 13 14.
  intros fs_full v' ? ?.
  induction fs as [| [i0 t0] fs0]; auto.
  simpl.
  intros.
  f_equal.
  + unfold at_offset.
    rewrite offset_offset_val.
    clear IHfs0.
    specialize (H i0 (or_introl eq_refl)).
    specialize (H1 i0 (or_introl eq_refl)).
    set (v0 := proj_struct i0 fs_full v') in *; clearbody v0; clear v'.
    revert v0 H1; rewrite <- H; intros.
    apply JMeq_eq in H1; rewrite <- H1.
    simpl.
    destruct (ident_eq i0 i0); [auto | congruence].
  + apply IHfs0.
    - destruct H0; auto.
    - intros.
      rewrite <- H by (right; auto).
      simpl.
      destruct (ident_eq i i0); [subst; destruct H0; tauto | auto].
    - intros.
      eapply JMeq_trans; [| apply H1; right; auto].
      simpl.
      destruct (ident_eq i i0); [subst; destruct H0; tauto | auto].
Qed.
(*
Fixpoint nested_reptype_fieldlist t nf (fs: fieldlist): Type :=
  match fs with
  | Fnil => unit
  | Fcons (i0, t0) fs0 =>
     (reptype (nested_field_type t (i0 :: nf)) * nested_reptype_fieldlist t nf fs0)%type
  end.

Fixpoint nested_field_at_fieldlist t nf (fs: fieldlist): nested_reptype_fieldlist t nf fs -> val -> Pred :=
  match fs with
  | Fnil => fun _ _ => emp
  | Fcons (i0, t0) fs0 =>
      fun v p => field_at t (i0 :: nf) (fst v) p * nested_field_at_fieldlist t nf fs0 (snd v) p
  end.

Lemma field_at_Tstruct: forall t nf id fs v1 v2 p,
  nested_field_type t nf = Tstruct id fs ->
  members_no_replicate fs ->
  JMeq v1 v2 ->
  field_at t nf v1 p = nested_field_at_fieldlist t nf fs v2 p.
Proof.
  intros.
  unfold field_at, at_offset.
  revert v1 H1; rewrite H; simpl; intros.
  simpl.
  assert (forall i, in_members i fs -> nested_field_offset t (i :: nf) = nested_field_offset t nf + field_offset i fs).
  Focus 1. {
    intros.
    simpl.
    rewrite H.
    reflexivity.
  } Unfocus.
  assert (forall i, in_members i fs -> nested_field_type t (i :: nf) = field_type i fs).
  Focus 1. {
    intros.
    simpl.
    rewrite H.
    reflexivity.
  } Unfocus.
  revert H2.
  generalize fs at 2 4.
  intros fs_full ?.
  clear H.
  induction fs as [| [i0 t0] fs0]; auto.
  simpl in v1, v2, H1 |- *.
  specialize (IHfs0 (snd v2) (proj2 H0) (snd v1)).
  assert (forall i : ident,
           in_members i fs0 ->
           nested_field_type t (i :: nf) = field_type i fs0).
  Focus 1. {
    intros.
    specialize (H3 i); simpl in H0, H3.
    destruct (ident_eq i i0); [subst i0; tauto |].
    apply H3; auto.
  } Unfocus.
  assert (forall i : ident,
           in_members i fs0 ->
           nested_field_offset t (i :: nf) =
           nested_field_offset t nf + field_offset i fs_full).
  Focus 1. {
    intros.
    apply H2.
    simpl; auto.
  } Unfocus.
  assert (t0 = nested_field_type t (i0 :: nf)).
  Focus 1. {
    specialize (H3 i0 (or_introl eq_refl)).
    simpl in H3.
    destruct (ident_eq i0 i0); [| congruence].
    auto.
  } Unfocus.
  assert (reptype_fieldlist fs0 = nested_reptype_fieldlist t nf fs0).
  Focus 1. {
    destruct H0 as [_ ?].
    clear - H0 H.
    induction fs0 as [| [i0 t0] fs0]; auto.
    simpl.
    f_equal.
    + specialize (H i0 (or_introl eq_refl)).
      simpl in H.
      destruct (ident_eq i0 i0); [| congruence].
      f_equal; symmetry; auto.
   + apply (IHfs0 (proj2 H0)).
     intros; specialize (H i (or_intror H1)).
     destruct H0.
     rewrite H; simpl.
     destruct (ident_eq i i0); auto.
     subst; tauto.
  } Unfocus.
  assert (JMeq (snd v1) (snd v2)).
  Focus 1. {
    apply JMeq_snd; auto.
    f_equal; auto.
  } Unfocus.
  assert (JMeq (fst v1) (fst v2)).
  Focus 1. {
    apply JMeq_fst; auto.
    f_equal; auto.
  } Unfocus.
  specialize (IHfs0 H7 H H4).
  f_equal.
  + unfold field_at, at_offset.
    rewrite offset_offset_val.
    rewrite H2 by (simpl; auto).
    clear - H5 H8.
    revert v1 v2 H8; simpl in H5 |- *; rewrite <- H5; intros.
    apply JMeq_eq in H8; rewrite H8; auto.
  + auto.
Qed.
*)
(* Ramification Premises for Nested Load/Store Rule *)

Lemma RP_one_layer: forall t nf f u v p,
  legal_field (nested_field_type t nf) f ->
  field_at t nf u p
   |-- field_at t (f :: nf)
         (proj_gfield_reptype (nested_field_type t nf) f u) p *
       (field_at t (f :: nf) v p -*
        field_at t nf (upd_gfield_reptype (nested_field_type t nf) f u v) p).
Proof.
  intros.
  unfold legal_field in H.
  remember (nested_field_type t nf) as t0 eqn:?H in H.
  destruct t0; [tauto | symmetry in H0].
Check field_at_Tstruct.
  rewrite field_at_Tstruct t nf id fs .
Lemma RP_field: forall t nf u v p,
  data_at t u p |-- field_at t nf (proj_reptype t nf u) p *
    (field_at t nf v p -* data_at t (upd_reptype t nf u v) p).
Proof.
  intros.
  induction nf.
  + apply RAMIF_PLAIN.solve with emp.
    - unfold data_at; simpl.
      rewrite sepcon_emp; apply derives_refl.
    - unfold data_at; simpl.
      rewrite emp_sepcon; apply derives_refl.
  + simpl.
    specialize (IHnf (upd_gfield_reptype _ a (proj_reptype t nf u) v)).
    eapply RAMIF_PLAIN.trans; eauto.
    clear.
    set (u' := proj_reptype t nf u); clearbody u'; clear u.

