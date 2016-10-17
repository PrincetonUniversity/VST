Require Import AggregateType.demo1.expr.
Require Import AggregateType.demo1.type_rec_functions.
Require Import AggregateType.demo1.path_rec_functions.

Definition field_at (t: type) (nf: list ident) (v: reptype (nested_field_type t nf)) (p: val) : Pred := data_at_rec (nested_field_type t nf) v (offset_val (nested_field_offset t nf) p).

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
  unfold field_at.
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
  + rewrite offset_offset_val.
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

Lemma field_at_Tstruct': forall t nf id fs v p i,
  nested_field_type t nf = Tstruct id fs ->
  members_no_replicate fs ->
  in_members i fs ->
  field_at t nf v p =
    field_at t (i :: nf) (proj_reptype _ (i :: nil) v) p *
     (fix field_at_struct fs :=
        match fs with
        | Fnil => emp
        | Fcons (i0, t0) fs0 =>
           (if (ident_eq i0 i)
            then emp
            else field_at t (i0 :: nf) (proj_reptype _ (i0 :: nil) v) p) *
           field_at_struct fs0
        end) fs.
Proof.
  intros.
  erewrite field_at_Tstruct by eauto.
  clear - H0 H1.
  revert H1.
  apply (@proj2
   (~ in_members i fs ->
      (fix field_at_struct (fs0 : fieldlist) : Pred :=
      match fs0 with
      | Fnil => emp
      | Fcons (i0, _) fs1 =>
          field_at t (i0 :: nf)
            (proj_reptype (nested_field_type t nf) (i0 :: nil) v) p *
          field_at_struct fs1
      end) fs =
   (fix field_at_struct (fs0 : fieldlist) : Pred :=
      match fs0 with
      | Fnil => emp
      | Fcons (i0, _) fs1 =>
          (if ident_eq i0 i
           then emp
           else
            field_at t (i0 :: nf)
              (proj_reptype (nested_field_type t nf) (i0 :: nil) v) p) *
          field_at_struct fs1
      end) fs)).
  induction fs as [| [i0 t0] fs0].
  + split; [auto | intros []].
  + specialize (IHfs0 (proj2 H0)).
    destruct IHfs0 as [IH0 IH1]; split.
    - intros.
      clear IH1.
      specialize (IH0 (fun im => H (or_intror im))).
      rewrite IH0.
      f_equal.
      destruct (ident_eq i0 i); [simpl in H; subst; tauto | auto].
    - intros.
      destruct (ident_eq i0 i).
      * rewrite emp_sepcon.
        subst i0.
        f_equal.
        apply IH0.
        destruct H0; auto.
      * rewrite <- sepcon_assoc, (sepcon_comm (field_at t (i :: nf) _ _)), sepcon_assoc.
        f_equal.
        apply IH1.
        destruct H1; [subst; tauto | auto].
Qed.

(* Ramification Premises for Nested Load/Store Rule *)

Lemma RP_one_layer: forall t nf f u v p,
  legal_nested_field t (f :: nf) ->
  legal_type t ->
  field_at t nf u p
   |-- field_at t (f :: nf)
         (proj_gfield_reptype (nested_field_type t nf) f u) p *
       (field_at t (f :: nf) v p -*
        field_at t nf (upd_gfield_reptype (nested_field_type t nf) f u v) p).
Proof.
  intros.
  destruct H.
  unfold legal_field in H1.
  remember (nested_field_type t nf) as t0 eqn:?H in H1.
  destruct t0; [tauto | symmetry in H2].
  pose proof legal_type_nested_field_type t nf H0 H.
  rewrite H2 in H3; apply nested_pred_atom_pred in H3.
  rewrite (field_at_Tstruct' t nf id fs u p f) by auto.
  rewrite (field_at_Tstruct' t nf id fs (upd_gfield_reptype (nested_field_type t nf) f u v) p f); auto.
  simpl proj_reptype.
  rewrite proj_upd_gfield_reptype_hit by (rewrite H2; auto).
  match goal with | |- _ * ?A |-- _ => apply RAMIF_PLAIN.solve with A end; auto.
  rewrite sepcon_comm.
  apply sepcon_derives; auto.
  clear.
  induction fs as [| [i0 t0] fs0]; auto.
  apply sepcon_derives.
  + destruct (ident_eq i0 f); auto.
    simpl.
    rewrite proj_upd_gfield_reptype_miss by congruence.
    auto.
  + apply IHfs0.
Qed.

Lemma RP_field: forall t nf u v p,
  legal_nested_field t nf ->
  legal_type t ->
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
    destruct H.
    specialize (IHnf (upd_gfield_reptype _ a (proj_reptype t nf u) v) H).
        eapply RAMIF_PLAIN.trans; try eassumption.
    apply RP_one_layer; simpl; auto.
Qed.

Lemma RP_mapsto: forall t nf u v p w0 w1,
  legal_nested_field t nf ->
  legal_type t ->
  nested_field_type t nf = Tint ->
  JMeq (proj_reptype t nf u) w0 ->
  JMeq v w1 ->
  data_at t u p |-- mapsto (field_address t nf p) w0 *
    (mapsto (field_address t nf p) w1 -* data_at t (upd_reptype t nf u v) p).
Proof.
  intros.
  pose proof RP_field t nf u v p H H0.
  erewrite !(field_at_Tint t nf) in H4; eassumption.
Qed.

Lemma Lemma1: forall t nf u p w,
  legal_nested_field t nf ->
  legal_type t ->
  nested_field_type t nf = Tint ->
  JMeq (proj_reptype t nf u) w ->
  data_at t u p |-- mapsto (field_address t nf p) w * TT.
Proof.
  intros.
  assert (JMeq (default_val (nested_field_type t nf)) Vundef) by (rewrite H1; auto).
  pose proof RP_mapsto t nf u (default_val _) p w Vundef H H0 H1 H2 H3.
  eapply derives_trans; [exact H4 |].
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

(* Reroot Equation *)
Lemma field_at_data_at: forall t nf v p,
  field_at t nf v p = data_at _ v (field_address t nf p).
Proof.
  intros.
  unfold data_at, field_at, field_address.
  simpl.
  rewrite offset_offset_val.
  rewrite Z.add_0_r.
  auto.
Qed.
