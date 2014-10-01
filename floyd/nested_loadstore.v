Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(**********************************************

nf_sub2: substraction in type
proj_except_reptype: big reptype value
proj_reptype: small reptype value
pair_reptype: reversion of proj/PROJ
upd_reptype
data_at_with_exception
data_at_with_exception * field_at = data_at

Comment: for now, ident_eq will be used throughout all these definition
because it is used in field_type and field_offset in compcert. However,
it should be replaced by Pos.eqb here and in compcert.

Further plan: multi substraction, which is useful for definion tree structure

mnf_sub: substraction in type
mproj_except_reptype: big reptype value
mproj_reptype: small reptype value
mnf_pair_reptype: reversion of proj/PROJ
mupd_reptype
data_at_with_mexception
data_at_with_mexception * [field_at] = data_at

**********************************************)

(*** type level ***)

Fixpoint all_fields_except_one (f: fieldlist) (id: ident) : option fieldlist :=
 match f with
 | Fnil => None
 | Fcons i t f0 =>
   if ident_eq id i
   then Some f0
   else match (all_fields_except_one f0 id) with
        | None => None
        | Some res => Some (Fcons i t res)
        end
 end.

Fixpoint all_fields_except_one2 (f: fieldlist) (id: ident) : fieldlist :=
 match f with
 | Fnil => Fnil
 | Fcons i t f0 =>
   if ident_eq id i
   then f0
   else Fcons i t (all_fields_except_one2 f0 id)
 end.

Fixpoint all_fields_replace_one (f: fieldlist) (id: ident) (t0: type) : option fieldlist :=
 match f with
 | Fnil => None
 | Fcons i t f0 =>
   if ident_eq id i
   then Some (Fcons i t0 f0)
   else match (all_fields_replace_one f0 id t0) with
        | None => None
        | Some res => Some (Fcons i t res)
        end
 end.

Fixpoint all_fields_replace_one2 (f: fieldlist) (id: ident) (t0: type) : fieldlist :=
 match f with
 | Fnil => Fnil
 | Fcons i t f0 =>
   if ident_eq id i
   then Fcons i t0 f0
   else Fcons i t (all_fields_replace_one2 f0 id t0)
 end.

Fixpoint nf_replace t ids t0: option type :=
  match ids with
  | nil => Some t0
  | id :: ids0 => 
    match nested_field_type2 t ids0 with
    | Tstruct i f a =>
      match all_fields_replace_one f id t0 with
      | Some f' => nf_replace t ids0 (Tstruct i f' a)
      | None => None
      end
    | Tunion i f a =>
      match all_fields_replace_one f id t0 with
      | Some f' => nf_replace t ids0 (Tunion i f' a)
      | None => None
      end
    | _ => None
    end
  end.

Fixpoint nf_replace2 t ids t0: type :=
  match ids with
  | nil => t0
  | id :: ids0 => 
    match nested_field_type2 t ids0 with
    | Tstruct i f a => nf_replace2 t ids0 (Tstruct i (all_fields_replace_one2 f id t0) a)
    | Tunion i f a => nf_replace2 t ids0 (Tunion i (all_fields_replace_one2 f id t0) a)
    | _ => t
    end
  end.

Definition nf_sub t id ids: option type :=
  match nested_field_type2 t ids with
  | Tstruct i f a =>
    match all_fields_except_one f id with
    | Some f' => nf_replace t ids (Tstruct i f' a)
    | None => None
    end
  | Tunion i f a =>
    match all_fields_except_one f id with
    | Some f' => nf_replace t ids (Tunion i f' a)
    | None => None
    end
  | _ => None
  end.

Definition nf_sub2 t id ids: type :=
  match nested_field_type2 t ids with
  | Tstruct i f a => nf_replace2 t ids (Tstruct i (all_fields_except_one2 f id) a)
  | Tunion i f a => nf_replace2 t ids (Tunion i (all_fields_except_one2 f id) a)
  | _ => t
  end.

Lemma is_Fnil_all_fields_replace_one2: forall f id t,
  is_Fnil (all_fields_replace_one2 f id t) = is_Fnil f.
Proof.
  intros.
  destruct f.
  + reflexivity.
  + simpl.
    if_tac; reflexivity.
Defined.

Lemma all_fields_except_one_all_fields_except_one2: forall f id,
  all_fields_except_one f id = Some (all_fields_except_one2 f id) \/
  all_fields_except_one f id = None /\ all_fields_except_one2 f id = f.
Proof.
  intros.
  induction f.
  + auto.
  + simpl; if_tac; [ |destruct IHf].
    - auto.
    - rewrite H0. auto.
    - destruct H0; rewrite H0, H1. auto.
Defined.

Lemma all_fields_replace_one_all_fields_replace_one2: forall f id t,
  all_fields_replace_one f id t = Some (all_fields_replace_one2 f id t) \/
  all_fields_replace_one f id t = None /\ all_fields_replace_one2 f id t = f.
Proof.
  intros.
  induction f.
  + auto.
  + simpl; if_tac; [ |destruct IHf].
    - auto.
    - rewrite H0. auto.
    - destruct H0; rewrite H0, H1. auto.
Defined.

Lemma all_fields_replace_one2_identical: forall f i t,
  (field_type i f = Errors.OK t \/ exists e, field_type i f = Errors.Error e) -> all_fields_replace_one2 f i t = f.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl in *.
    if_tac in H.
    - destruct H as [? | [? ?]]; inversion H; reflexivity.
    - rewrite (IHf H). reflexivity.
Defined.

Lemma nf_replace2_identical: forall t ids, t = nf_replace2 t ids (nested_field_type2 t ids).
Proof.
  intros.
  induction ids.
  + reflexivity.
  + simpl.
    destruct (nested_field_type2 t ids) eqn:?; auto.
    - (* Tstruct *)
      rewrite all_fields_replace_one2_identical; auto.
      erewrite nested_field_type2_cons; eauto.
      rewrite Heqt0.
      change (field_offset_rec a f 0) with (field_offset a f).
      solve_field_offset_type a f; eauto.
    - (* Tunion *)
      rewrite all_fields_replace_one2_identical; auto.
      erewrite nested_field_type2_cons; eauto.
      rewrite Heqt0.
      change (field_offset_rec a f 0) with (field_offset a f).
      solve_field_offset_type a f; eauto.
Defined.

Lemma nf_replace_nf_replace2: forall t ids t0,
  nf_replace t ids t0 = Some (nf_replace2 t ids t0) \/
  nf_replace t ids t0 = None /\ nf_replace2 t ids t0 = t.
Proof.
  induction ids; intros.
  + auto.
  + simpl. simpl; destruct (nested_field_type2 t ids) eqn:?; auto.
    - destruct (all_fields_replace_one_all_fields_replace_one2 f a t0) as [H | [H0 H1]].
      * rewrite H; auto.
      * rewrite H0, H1, <- Heqt1.
        rewrite <- nf_replace2_identical.
        auto.
    - destruct (all_fields_replace_one_all_fields_replace_one2 f a t0) as [H | [H0 H1]].
      * rewrite H; auto.
      * rewrite H0, H1, <- Heqt1.
        rewrite <- nf_replace2_identical.
        auto.
Defined.

Lemma nf_sub_nf_sub2: forall t id ids,
  nf_sub t id ids = Some (nf_sub2 t id ids) \/
  nf_sub t id ids = None /\ nf_sub2 t id ids = t.
Proof.
  intros.
  unfold nf_sub2, nf_sub.
  destruct (nested_field_type2 t ids) eqn:?; auto.
  + destruct (all_fields_except_one_all_fields_except_one2 f id) as [H | [H0 H1]].
    - rewrite H; auto.
      apply nf_replace_nf_replace2.
    - rewrite H0, H1, <- Heqt0.
      rewrite <- nf_replace2_identical.
      auto.
  + destruct (all_fields_except_one_all_fields_except_one2 f id) as [H | [H0 H1]].
    - rewrite H; auto.
      apply nf_replace_nf_replace2.
    - rewrite H0, H1, <- Heqt0.
      rewrite <- nf_replace2_identical.
      auto.
Defined.

Lemma nested_field_type2_nf_replace2_aux:
  forall i f t0,
  isOK (field_type i f) = true ->
   match field_offset i (all_fields_replace_one2 f i t0) with
   | Errors.OK _ =>
       match field_type i (all_fields_replace_one2 f i t0) with
       | Errors.OK t1 => t1
       | Errors.Error _ => Tvoid
       end
   | Errors.Error _ => Tvoid
   end = t0.
Proof.
  intros.
  unfold field_offset in *.
  revert H; generalize 0.
  induction f; intros.
  + inversion H.
  + unfold all_fields_replace_one. simpl in *.
    destruct (ident_eq i i0).
    - simpl; destruct (ident_eq i i0); [| congruence]; reflexivity.
    - simpl; destruct (ident_eq i i0); [congruence |].
      apply IHf, H.
Defined.

Lemma nested_field_type2_nf_replace2_aux':
  forall i f t0,
  isOK (field_type i f) = true ->
  match field_type i (all_fields_replace_one2 f i t0) with
  | Errors.OK t1 => t1
  | Errors.Error _ => Tvoid
  end = t0.
Proof.
  intros.
  unfold field_offset in *.
  revert H.
  induction f; intros.
  + inversion H.
  + unfold all_fields_replace_one. simpl in *.
    destruct (ident_eq i i0).
    - simpl; destruct (ident_eq i i0); [| congruence]; reflexivity.
    - simpl; destruct (ident_eq i i0); [congruence |].
      apply IHf, H.
Defined.

Lemma nested_field_type2_nf_replace2: forall t ids t0, isSome (nested_field_rec t ids) -> nested_field_type2 (nf_replace2 t ids t0) ids = t0.
Proof.
  intros.
  revert t0 H; induction ids; intros.
  + reflexivity.
  + simpl.
    solve_nested_field_rec_cons_isSome H.
    - (* Tstruct *)
      rewrite H2, nested_field_type2_cons, IHids by auto.
      apply nested_field_type2_nf_replace2_aux, H1.
    - (* Tunion *)
      rewrite H2, nested_field_type2_cons, IHids by auto.
      apply nested_field_type2_nf_replace2_aux', H1.
Defined.

Lemma all_fields_replace_one2_all_fields_replace_one2: forall f i t0 t1, all_fields_replace_one2 (all_fields_replace_one2 f i t0) i t1 = all_fields_replace_one2 f i t1.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl.
    if_tac.
    - simpl; if_tac; [| congruence]; reflexivity.
    - simpl; if_tac; [congruence |].
      f_equal. apply IHf.
Defined.

Lemma all_fields_replace_one_field_type_isSome_lemma: forall i f t0,
  isSome (all_fields_replace_one f i t0) <-> isOK (field_type i f) = true.
Proof.
  intros.
  induction f.
  + simpl. split; intros; firstorder.
  + simpl.
    destruct (ident_eq i i0); [simpl; tauto |].
    destruct (all_fields_replace_one f i t0), (field_type i f); simpl in *; congruence.
Defined.

Lemma nf_replace_nested_field_rec_isSome_lemma: forall t ids t0, isSome (nf_replace t ids t0) <-> isSome (nested_field_rec t ids).
Proof.
  intros.
  revert t0.
  induction ids; intros.
  + simpl. tauto.
  + eapply iff_trans; [| apply iff_sym, nested_field_rec_cons_isSome_lemma].
    simpl nf_replace; unfold nested_field_type2.
    destruct (nested_field_rec t ids) as [[z1 t1] |]; [destruct t1|];
    (split; intros; [try inversion H | destruct H as [? [? [? [? [? [? | ?]]]]]]]; try inversion H1).
    - assert (isSome (all_fields_replace_one f a t0))
        by (destruct (all_fields_replace_one f a t0); [simpl; exact I | inversion H]).
      apply all_fields_replace_one_field_type_isSome_lemma in H0.
      split; [exact I | exists i, f, a0; tauto].
    - apply (iff_sym (all_fields_replace_one_field_type_isSome_lemma _ _ t0)) in H0.
      destruct (all_fields_replace_one x0 a t0); [| inversion H0].
      apply (iff_sym (IHids (Tstruct x f0 x1))).
      simpl; auto.
    - assert (isSome (all_fields_replace_one f a t0))
        by (destruct (all_fields_replace_one f a t0); [simpl; exact I | inversion H]).
      apply all_fields_replace_one_field_type_isSome_lemma in H0.
      split; [exact I | exists i, f, a0; tauto].
    - apply (iff_sym (all_fields_replace_one_field_type_isSome_lemma _ _ t0)) in H0.
      destruct (all_fields_replace_one x0 a t0); [| inversion H0].
      apply (iff_sym (IHids (Tunion x f0 x1))).
      simpl; auto.
Defined.

Lemma nf_replace2_nf_replace2: forall t ids t0 t1, nf_replace2 (nf_replace2 t ids t0) ids t1 = nf_replace2 t ids t1.
Proof.
  intros.
  destruct (isSome_dec (nested_field_rec t ids)) as [H | H].
  + revert t0 t1 H.
    induction ids; intros.
    - reflexivity.
    - simpl.
      solve_nested_field_rec_cons_isSome H.
      * (* Tstruct *)
        rewrite H2, nested_field_type2_nf_replace2 by auto.
        erewrite IHids by auto.
        rewrite all_fields_replace_one2_all_fields_replace_one2.
        reflexivity.
      * (* Tunion *)
        rewrite H2, nested_field_type2_nf_replace2 by auto.
        erewrite IHids by auto.
        rewrite all_fields_replace_one2_all_fields_replace_one2.
        reflexivity.
  + pose proof nf_replace_nested_field_rec_isSome_lemma t ids t0.
    destruct (isSome_dec (nf_replace t ids t0)) as [H1 | H1];
    destruct (nf_replace_nf_replace2 t ids t0) as [? | [? ?]].
    - tauto.
    - tauto.
    - rewrite H2 in H1. simpl in H1; tauto.
    - rewrite H3 in *; reflexivity.
Defined.

Lemma nf_replace2_identical': forall t id ids, t = nf_replace2 (nf_sub2 t id ids) ids (nested_field_type2 t ids).
Proof.
  intros.
  unfold nf_sub2.
  pattern (nested_field_type2 t ids) at 1.
  destruct (nested_field_type2 t ids); try apply nf_replace2_identical.
  + rewrite nf_replace2_nf_replace2.
    apply nf_replace2_identical.
  + rewrite nf_replace2_nf_replace2.
    apply nf_replace2_identical.
Defined.

Lemma all_fields_except_one2_all_fields_replace_one2: forall id f t0,
  all_fields_except_one2 (all_fields_replace_one2 f id t0) id = all_fields_except_one2 f id.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl.
    if_tac.
    - simpl.
      if_tac; [reflexivity | congruence].
    - simpl.
      if_tac; [congruence | ].
      rewrite IHf.
      reflexivity.
Defined.


Lemma nf_sub2_nf_replace2: forall t id ids t0, nf_sub2 (nf_replace2 t (id :: ids) t0) id ids = nf_sub2 t id ids.
Proof.
  intros.
  simpl.
  destruct (nested_field_type2 t ids) eqn:?; auto.
  + (* Tstruct *)
    unfold nf_sub2.
    destruct (nf_replace_nf_replace2 t ids (Tstruct i (all_fields_replace_one2 f id t0) a)) as [? |[? ?]].
    - rewrite nested_field_type2_nf_replace2; [ |eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto].
      rewrite nf_replace2_nf_replace2, Heqt1.
      rewrite all_fields_except_one2_all_fields_replace_one2.
      reflexivity.
    - rewrite H0.
      reflexivity.
  + (* Tunion *)
    unfold nf_sub2.
    destruct (nf_replace_nf_replace2 t ids (Tunion i (all_fields_replace_one2 f id t0) a)) as [? |[? ?]].
    - rewrite nested_field_type2_nf_replace2;[ |eapply nested_field_type2_Tunion_nested_field_rec_isSome; eauto].
      rewrite nf_replace2_nf_replace2, Heqt1.
      rewrite all_fields_except_one2_all_fields_replace_one2.
      reflexivity.
    - rewrite H0.
      reflexivity.
Defined.

Lemma nf_sub2_nf_sub2_cons: forall t id id0 ids, nf_sub2 (nf_sub2 t id (id0 :: ids)) id0 ids = nf_sub2 t id0 ids.
Proof.
  intros.
  unfold nf_sub2 at 2.
  destruct (nested_field_type2 t (id0 :: ids)); auto.
  rewrite nf_sub2_nf_replace2; reflexivity.
  rewrite nf_sub2_nf_replace2; reflexivity.
Defined.

Lemma nested_field_type2_nf_sub2_Tstruct: forall t id ids i f a, nested_field_type2 t ids = Tstruct i f a -> nested_field_type2 (nf_sub2 t id ids) ids = Tstruct i (all_fields_except_one2 f id) a.
Proof.
  intros.
  unfold nf_sub2.
  rewrite H.
  rewrite nested_field_type2_nf_replace2
    by (eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto).
  reflexivity.
Defined.

Lemma nested_field_type2_nf_sub2_Tunion: forall t id ids i f a, nested_field_type2 t ids = Tunion i f a -> nested_field_type2 (nf_sub2 t id ids) ids = Tunion i (all_fields_except_one2 f id) a.
Proof.
  intros.
  unfold nf_sub2.
  rewrite H.
  rewrite nested_field_type2_nf_replace2
    by (eapply nested_field_type2_Tunion_nested_field_rec_isSome; eauto).
  reflexivity.
Defined.

(*** reptype level ***)

Lemma proj_reptype_aux: forall t ids,
  nested_field_type2 t ids =
  match ids with
  | nil => t
  | id :: ids0 =>
    match nested_field_type2 t ids0 with
    | Tstruct i f a => match field_offset_rec id f 0, field_type id f with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end
    | Tunion i f a  => match field_type id f with
                       | Errors.OK t0 => t0
                       | _ => Tvoid
                       end
    | _ => Tvoid
    end
  end.
Proof.
  intros.
  destruct ids; [apply nested_field_type2_nil | apply nested_field_type2_cons].
Defined.

Fixpoint proj_reptype_structlist id f ofs (v: reptype_structlist f) : 
  reptype (match field_offset_rec id f ofs, field_type id f with
           | Errors.OK _, Errors.OK t0 => t0
           | _, _ => Tvoid
           end) :=
  match f as f'
    return reptype_structlist f' -> reptype (match field_offset_rec id f' ofs, field_type id f' with
                                             | Errors.OK _, Errors.OK t0 => t0
                                             | _, _ => Tvoid
                                             end) with
  | Fnil => fun _ => default_val _
  | Fcons i0 t0 flds0 => 
    if is_Fnil flds0 as b
      return ((if b then reptype t0 else reptype t0 * reptype_structlist flds0) ->
              reptype (match (if ident_eq id i0
                             then Errors.OK (align ofs (alignof t0))
                             else field_offset_rec id flds0 (align ofs (alignof t0) + sizeof t0)),
                             (if ident_eq id i0 then Errors.OK t0 else field_type id flds0)
                       with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end))
    then fun v =>
      if ident_eq id i0 as b0
        return reptype (match (if b0
                             then Errors.OK (align ofs (alignof t0))
                             else field_offset_rec id flds0 (align ofs (alignof t0) + sizeof t0)),
                             (if b0 then Errors.OK t0 else field_type id flds0)
                        with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end)
      then v
      else default_val _
    else fun v => 
      if ident_eq id i0 as b0
        return reptype (match (if b0
                             then Errors.OK (align ofs (alignof t0))
                             else field_offset_rec id flds0 (align ofs (alignof t0) + sizeof t0)),
                             (if b0 then Errors.OK t0 else field_type id flds0)
                        with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end)
      then fst v
      else proj_reptype_structlist id flds0 (align ofs (alignof t0) + sizeof t0) (snd v)
  end v.

Fixpoint proj_reptype_unionlist id f (v: reptype_unionlist f) : 
  reptype (match field_type id f with
           | Errors.OK t0 => t0
           | _ => Tvoid
           end) :=
  match f as f'
    return reptype_unionlist f' -> reptype (match field_type id f' with
                                            | Errors.OK t0 => t0
                                            | _ => Tvoid
                                            end) with
  | Fnil => fun _ => default_val _
  | Fcons i0 t0 flds0 => 
    if is_Fnil flds0 as b
      return ((if b then reptype t0 else reptype t0 + reptype_unionlist flds0) ->
              reptype (match (if ident_eq id i0 then Errors.OK t0 else field_type id flds0) with
                       | Errors.OK t0 => t0
                       | _ => Tvoid
                       end))
    then fun v =>
      if ident_eq id i0 as b0
        return reptype (match (if b0 then Errors.OK t0 else field_type id flds0) with
                        | Errors.OK t0 => t0
                        | _ => Tvoid
                        end)
      then v
      else default_val _
    else fun v => 
      if ident_eq id i0 as b0
        return reptype (match (if b0 then Errors.OK t0 else field_type id flds0) with
                        | Errors.OK t0 => t0
                        | _ => Tvoid
                        end)
      then match v with
           | inl v0 => v0
           | _ => default_val _
           end
      else match v with
           | inr v0 => proj_reptype_unionlist id flds0 v0
           | _ => default_val _
           end
  end v.

Fixpoint proj_reptype (t: type) (ids: list ident) (v: reptype t) : reptype (nested_field_type2 t ids) :=
  let res :=
  match ids as ids'
    return reptype (match ids' with
                    | nil => t
                    | id :: ids0 =>
                      match nested_field_type2 t ids0 with
                      | Tstruct i f a => match field_offset_rec id f 0, field_type id f with
                                         | Errors.OK _, Errors.OK t0 => t0
                                         | _, _ => Tvoid
                                         end
                      | Tunion i f a  => match field_type id f with
                                         | Errors.OK t0 => t0
                                         | _ => Tvoid
                                         end
                      | _ => Tvoid
                      end
                    end)
  with
  | nil => v
  | id :: ids0 => 
    match nested_field_type2 t ids0 as T
      return reptype T -> reptype (match T with
                                   | Tstruct i f a => match field_offset_rec id f 0, field_type id f
                                                      with
                                                      | Errors.OK _, Errors.OK t0 => t0
                                                      | _, _ => Tvoid
                                                      end
                                   | Tunion i f a  => match field_type id f with
                                                      | Errors.OK t0 => t0
                                                      | _ => Tvoid
                                                      end
                                   | _ => Tvoid
                                   end)
    with
    | Tstruct i f a => fun v0 => proj_reptype_structlist id f 0 v0
    | Tunion i f a => fun v0 => proj_reptype_unionlist id f v0
    | _ => fun _ => default_val _
    end (proj_reptype t ids0 v)
  end
  in eq_rect_r reptype res (proj_reptype_aux t ids).

Fixpoint is_precise_proj_reptype_unionlist (f: fieldlist) (id: ident) (v: reptype_unionlist f) :=
  match f as f' return reptype_unionlist f' -> bool with
  | Fnil => fun _ => false
  | Fcons i0 t0 f0 =>
    if is_Fnil f0 as b
      return (if b then reptype t0 else (reptype t0 + reptype_unionlist f0)) -> bool
    then if ident_eq id i0
         then fun _ => true
         else fun _ => false
    else if ident_eq id i0
         then fun v => 
           match v with
           | inl _ => true
           | _ => false
           end
         else fun v =>
           match v with
           | inl _ => false
           | inr v' => is_precise_proj_reptype_unionlist f0 id v'
           end
  end v.

Fixpoint is_precise_proj_reptype (t: type) (ids: list ident) (v: reptype t) :=
  match ids with
  | nil => true
  | id :: ids0 =>
    (is_precise_proj_reptype t ids0 v &&
     match nested_field_type2 t ids0 as T
       return reptype T -> bool
     with
     | Tstruct _ _ _ => fun _ => true
     | Tunion i f a => fun v0 => is_precise_proj_reptype_unionlist f id v0
     | _ => fun _ => false
     end (proj_reptype t ids0 v)) % bool
  end.

Lemma gupd_reptype_structlist_aux: forall f i0 t0,
  all_fields_replace_one2 f i0 t0 = match f with
                                    | Fnil => Fnil
                                    | Fcons i1 t1 flds0 => 
                                      if ident_eq i0 i1
                                      then Fcons i1 t0 flds0
                                      else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0)
                                    end.
Proof.
  intros.
  destruct f; [|simpl; if_tac]; reflexivity.
Defined.

Fixpoint gupd_reptype_structlist f (i0: ident) (t0: type) (v: reptype_structlist f) (v0: reptype t0) : reptype_structlist (all_fields_replace_one2 f i0 t0) :=
  let res :=
  match f as f'
    return reptype_structlist f' -> 
           reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i1 t1 flds0 => 
                                 if ident_eq i0 i1
                                 then Fcons i1 t0 flds0
                                 else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0)
                               end)
  with
  | Fnil => fun _ => struct_default_val _
  | Fcons i1 t1 flds0 => fun v =>
   (if ident_eq i0 i1 as b
      return reptype_structlist (if b
                                 then Fcons i1 t0 flds0
                                 else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0))
    then
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t1 else reptype t1 * reptype_structlist flds0) ->
               (if b0 then reptype t0 else reptype t0 * reptype_structlist flds0)
      then fun _ => v0
      else fun v => (v0, snd v)
     ) v
    else
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t1 else reptype t1 * reptype_structlist flds0) ->
               (if is_Fnil (all_fields_replace_one2 flds0 i0 t0) then reptype t1 else reptype t1 * 
                   reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
      then
        if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b1
          return reptype t1 ->
                 (if b1 then reptype t1 else reptype t1 * 
                     reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
        then fun v => v
        else fun _ => (default_val _, struct_default_val _) (* impossible situation *)
      else
        if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b1
          return reptype t1 * reptype_structlist flds0 ->
                 (if b1 then reptype t1 else reptype t1 * 
                     reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
        then fun _ => default_val _
        else fun v => (fst v, gupd_reptype_structlist flds0 i0 t0 (snd v) v0)
      ) v
   )
  end v
  in
  eq_rect_r reptype_structlist res (gupd_reptype_structlist_aux f i0 t0).

Fixpoint gupd_reptype_unionlist f (i0: ident) (t0: type) (v0: reptype t0) : reptype_unionlist (all_fields_replace_one2 f i0 t0) :=
  let res :=
  match f as f'
    return reptype_unionlist (match f' with
                               | Fnil => Fnil
                               | Fcons i1 t1 flds0 => 
                                 if ident_eq i0 i1
                                 then Fcons i1 t0 flds0
                                 else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0)
                               end)
  with
  | Fnil => union_default_val _
  | Fcons i1 t1 flds0 => 
   (if ident_eq i0 i1 as b
      return reptype_unionlist (if b
                                 then Fcons i1 t0 flds0
                                 else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0))
    then
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t0 else reptype t0 + reptype_unionlist flds0)
      then v0
      else inl v0
     )
    else
     (if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b0
        return (if b0
                then reptype t1
                else reptype t1 + reptype_unionlist (all_fields_replace_one2 flds0 i0 t0))
      then default_val _
      else inr (gupd_reptype_unionlist flds0 i0 t0 v0)
      )
    )
  end
  in
  eq_rect_r reptype_unionlist res (gupd_reptype_structlist_aux f i0 t0).


Fixpoint gupd_reptype (t: type) (ids: list ident) (t0: type) (v: reptype t) (v0: reptype t0): reptype (nf_replace2 t ids t0) := 
  match ids as ids' return reptype (nf_replace2 t ids' t0) with
  | nil => v0
  | id :: ids0 => 
    match (nested_field_type2 t ids0) as T 
      return reptype T -> reptype (match T with
                                   | Tstruct i f a => nf_replace2 t ids0 
                                     (Tstruct i (all_fields_replace_one2 f id t0) a)
                                   | Tunion i f a => nf_replace2 t ids0 
                                     (Tunion i (all_fields_replace_one2 f id t0) a)
                                   | _ => t
                                   end)
    with
    | Tstruct i f a => fun v' => gupd_reptype t ids0 (Tstruct i (all_fields_replace_one2 f id t0) a) v 
                                 (gupd_reptype_structlist f id t0 v' v0)
    | Tunion i f a => fun _ => gupd_reptype t ids0 (Tunion i (all_fields_replace_one2 f id t0) a) v 
                                 (gupd_reptype_unionlist f id t0 v0)
    | _ => fun _ => default_val _
    end (proj_reptype t ids0 v)
  end.

Definition upd_reptype (t: type) (ids: list ident) (v: reptype t) (v0: reptype (nested_field_type2 t ids)): reptype t :=
  eq_rect_r reptype (gupd_reptype t ids (nested_field_type2 t ids) v v0) (nf_replace2_identical t ids).

Fixpoint proj_except_reptype_structlist (f: fieldlist) (id: ident) (v: reptype_structlist f): reptype_structlist (all_fields_except_one2 f id) :=
  let res :=
  match f as f'
    return reptype_structlist f' -> 
           reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i t f0 =>
                                   if ident_eq id i
                                   then f0
                                   else Fcons i t (all_fields_except_one2 f0 id)
                               end)
  with
  | Fnil => fun v => v
  | Fcons i t f0 => fun v => 
     if ident_eq id i as b
       return reptype_structlist (if b
                                  then f0
                                  else Fcons i t (all_fields_except_one2 f0 id))
     then
      (if (is_Fnil f0) as b0
         return (if b0 then reptype t else reptype t * reptype_structlist f0) -> reptype_structlist f0
       then fun _ => struct_default_val _
       else fun v => snd v) v
     else
      (if (is_Fnil f0) as b0
         return (if b0 then reptype t else reptype t * reptype_structlist f0) -> 
                (if is_Fnil (all_fields_except_one2 f0 id) then reptype t else 
                 reptype t * reptype_structlist (all_fields_except_one2 f0 id))
       then fun v => 
         if is_Fnil (all_fields_except_one2 f0 id) as b1
           return if b1 then reptype t else 
                  reptype t * reptype_structlist (all_fields_except_one2 f0 id)
         then v
         else (v, struct_default_val _)
       else fun v =>
         if is_Fnil (all_fields_except_one2 f0 id) as b1
           return if b1 then reptype t else 
                  reptype t * reptype_structlist (all_fields_except_one2 f0 id)
         then fst v
         else (fst v, proj_except_reptype_structlist f0 id (snd v))
      ) v
  end v
  in
  match f as f'
    return reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i t f0 =>
                                   if ident_eq id i
                                   then f0
                                   else Fcons i t (all_fields_except_one2 f0 id)
                               end) ->
           reptype_structlist (all_fields_except_one2 f' id)
  with
  | Fnil => fun v => v
  | _ => fun v => v
  end res.

Definition proj_except_reptype_unionlist (f: fieldlist) (id: ident): reptype_unionlist (all_fields_except_one2 f id) := union_default_val _.

Definition proj_except_reptype (t: type) (id: ident) (ids: list ident) (v: reptype t) : reptype (nf_sub2 t id ids) :=
  match nested_field_type2 t ids as T 
    return reptype T ->
           reptype match T with
                   | Tstruct i f a => nf_replace2 t ids (Tstruct i (all_fields_except_one2 f id) a)
                   | Tunion i f a => nf_replace2 t ids (Tunion i (all_fields_except_one2 f id) a)
                   | _ => t
                   end
  with
  | Tstruct i f a => fun v0 => gupd_reptype t ids (Tstruct i (all_fields_except_one2 f id) a) v 
                     (proj_except_reptype_structlist f id v0)
  | Tunion i f a => fun _ => gupd_reptype t ids (Tunion i (all_fields_except_one2 f id) a) v 
                     (proj_except_reptype_unionlist f id)
  | _ => fun _ => v
  end (proj_reptype t ids v).

Fixpoint pair_reptype_structlist (id: ident) (f: fieldlist) (ofs: Z)
  (v: reptype_structlist (all_fields_except_one2 f id)) 
  (v0: reptype match field_offset_rec id f ofs, field_type id f with
               | Errors.OK _, Errors.OK t0 => t0
               | _, _ => Tvoid
               end): reptype_structlist f :=
  match f as f'
    return reptype_structlist (all_fields_except_one2 f' id) ->
           reptype match field_offset_rec id f' ofs, field_type id f' with
                   | Errors.OK _, Errors.OK t0 => t0
                   | _, _ => Tvoid
                   end ->
           reptype_structlist f'
  with
  | Fnil => fun v _ => v
  | Fcons i t flds0 => 
    if ident_eq id i as b
      return reptype_structlist (if b then flds0 else Fcons i t (all_fields_except_one2 flds0 id)) ->
             reptype match (if b
                            then Errors.OK (align ofs (alignof t))
                            else field_offset_rec id flds0 (align ofs (alignof t) + sizeof t)),
                           (if b then Errors.OK t else field_type id flds0)
                     with
                     | Errors.OK _, Errors.OK t0 => t0
                     | _, _ => Tvoid
                     end ->
             if is_Fnil flds0 then reptype t else reptype t * reptype_structlist flds0
    then 
      if is_Fnil flds0 as b0
        return reptype_structlist flds0 -> reptype t ->
               (if b0 then reptype t else reptype t * reptype_structlist flds0)
      then fun _ v0 => v0
      else fun v v0 => (v0, v)
    else
      if is_Fnil flds0 as b0
        return (if is_Fnil (all_fields_except_one2 flds0 id)
                then reptype t else reptype t * 
                  reptype_structlist (all_fields_except_one2 flds0 id)) ->
               reptype match field_offset_rec id flds0 (align ofs (alignof t) + sizeof t),
                             field_type id flds0 with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end ->
               (if b0 then reptype t else reptype t * reptype_structlist flds0)
      then
        if is_Fnil (all_fields_except_one2 flds0 id) as b1
          return (if b1 then reptype t else reptype t * 
                  reptype_structlist (all_fields_except_one2 flds0 id)) ->
                  reptype match field_offset_rec id flds0 (align ofs (alignof t) + sizeof t),
                             field_type id flds0 with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end -> reptype t
        then fun v v0 => v
        else fun v v0 => fst v
      else
        if is_Fnil (all_fields_except_one2 flds0 id) as b1
          return (if b1 then reptype t else reptype t * 
                  reptype_structlist (all_fields_except_one2 flds0 id)) ->
                  reptype match field_offset_rec id flds0 (align ofs (alignof t) + sizeof t),
                             field_type id flds0 with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end -> reptype t * reptype_structlist flds0
        then fun v v0 => (v, pair_reptype_structlist id flds0 (align ofs (alignof t) + sizeof t) 
                             (struct_default_val _) v0)
        else fun v v0 => (fst v, pair_reptype_structlist id flds0 (align ofs (alignof t) + sizeof t) 
                                (snd v) v0)
  end v v0.

Lemma pair_reptype_aux: forall t id ids,
  match nested_field_type2 t ids with
  | Tstruct i f a => Tstruct i (all_fields_except_one2 f id) a
  | Tunion i f a => Tunion i (all_fields_except_one2 f id) a
  | _ => nested_field_type2 t ids
  end = nested_field_type2 (nf_sub2 t id ids) ids.
Proof.
  intros.
  unfold nf_sub2.
  destruct (nested_field_type2 t ids) eqn:?; auto.
  + (* Tstruct *)
    apply eq_sym, nested_field_type2_nf_replace2.
    eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto.
  + (* Tunion *)
    apply eq_sym, nested_field_type2_nf_replace2.
    eapply nested_field_type2_Tunion_nested_field_rec_isSome; eauto.
Defined.

Fixpoint pair_reptype (t: type) (id: ident) (ids: list ident) (v: reptype (nf_sub2 t id ids)) (v0: reptype (nested_field_type2 t (id :: ids))) : reptype t :=
  match nested_field_type2 t ids as T
    return reptype match T with
                   | Tstruct i f a => Tstruct i (all_fields_except_one2 f id) a
                   | Tunion i f a => Tunion i (all_fields_except_one2 f id) a
                   | _ => nested_field_type2 t ids
                   end ->
           reptype match T with
                   | Tstruct i f a => match field_offset_rec id f 0, field_type id f with
                                      | Errors.OK _, Errors.OK t0 => t0
                                      | _, _ => Tvoid
                                      end
                   | Tunion i f a  => match field_type id f with
                                      | Errors.OK t0 => t0
                                      | _ => Tvoid
                                      end
                   | _ => Tvoid
                   end ->
           t = nf_replace2 (nf_sub2 t id ids) ids T ->
           reptype t
  with
  | Tstruct i f a => fun v1 v0 H => eq_rect_r reptype 
                       (gupd_reptype _ ids (Tstruct i f a) v (pair_reptype_structlist id f 0 v1 v0)) H
  | _ => fun _ _ _ => default_val _
  end
  (eq_rect_r reptype (proj_reptype _ ids v) (pair_reptype_aux t id ids))
  (eq_rect_r reptype v0 (eq_sym (nested_field_type2_cons t id ids)))
  (nf_replace2_identical' t id ids).

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

Lemma proj_reptype_nil: forall t v, nested_legal_fieldlist t = true -> JMeq (proj_reptype t nil v) v.
Proof.
  intros.
  simpl.
  rewrite eq_rect_r_JMeq.
  reflexivity.
Qed.

Lemma proj_reptype_cons_Tstruct: forall t id ids i f a v v0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tstruct i f a ->
  JMeq (proj_reptype t ids v) v0 ->
  JMeq (proj_reptype t (id :: ids) v) (proj_reptype_structlist id f 0 v0).
Proof.
  intros.
  simpl in *.
  revert H1.
  generalize (proj_reptype t ids v) as v1.
  generalize (nested_field_type2_cons t id ids) as HH.
  rewrite H0.
  intros; clear v.
  rewrite eq_rect_r_JMeq.
  rewrite H1.
  reflexivity.
Qed.

Module Test.
  Definition T1 := Tstruct 1%positive (Fcons 101%positive tint (Fcons 102%positive tint Fnil)) noattr.
  Definition T2 := Tstruct 2%positive (Fcons 201%positive T1 (Fcons 202%positive T1 Fnil)) noattr.
  Definition T3 := Tstruct 3%positive (Fcons 301%positive T2 (Fcons 302%positive T2 Fnil)) noattr.

  Definition v : reptype T3 :=
   (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 5), Vint (Int.repr 6)), (Vint (Int.repr 7), Vint (Int.repr 8)))).

  Arguments eq_rect_r / {A} {x} P H {y} H0.
  Arguments proj_except_reptype / t id ids v.
  Arguments upd_reptype / t ids v v0.

  Lemma Test1: 
    JMeq (proj_reptype T3 (201%positive :: 302%positive :: nil) v) (Vint (Int.repr 5), Vint (Int.repr 6)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma Test2:
    JMeq (upd_reptype T3 (201%positive :: 302%positive :: nil) v 
    (Vint (Int.repr 15), Vint (Int.repr 16))) 
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 15), Vint (Int.repr 16)), (Vint (Int.repr 7), Vint (Int.repr 8)))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma Test3:
    JMeq (proj_except_reptype T3 201%positive (302%positive :: nil) v) 
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 7), Vint (Int.repr 8)))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma Test4:
    JMeq (pair_reptype T3 201%positive (302%positive :: nil)
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 7), Vint (Int.repr 8))))
    ((Vint (Int.repr 5), Vint (Int.repr 6)))) v.
  Proof.
    simpl.
    reflexivity.
  Qed.
End Test.
(*
Definition precise : mpred -> Prop := msl.predicates_sl.precise.

Lemma mapsto_precise: forall sh t v p, precise (mapsto sh t p v).
Proof.
Admitted.

Lemma emp_precise: precise emp.
Proof.
Admitted.

Lemma precise_sepcon: forall P Q, precise P -> precise Q -> precise (P * Q).
Proof.
Admitted.

Lemma precise_andp: forall P Q, precise P -> precise Q -> precise (P && Q).
Proof.
Admitted.

Lemma precise_prop_andp: forall P Q, precise Q -> precise (!! P && Q).
Proof.
Admitted.

Lemma precise_wand_sepcon: forall P Q, precise P -> P -* (P * Q) = Q.
Proof.
Admitted.

Lemma precise_sepcon_cancel: forall P Q R, precise P -> P * Q = P * R -> Q = R.
Proof.
  intros.
  rewrite <- precise_wand_sepcon with (P:= P) (Q := Q) by auto.
  rewrite <- precise_wand_sepcon with (P:= P) (Q := R) by auto.
  rewrite H0.
  reflexivity.
Qed.

(* Here, this precise can be set to be more stronger property, such as splittable precise. *)
Lemma mapsto__precise: forall sh t p, precise (mapsto_ sh t p).
Proof.
  intros.
  unfold mapsto_.
  apply mapsto_precise.
Qed.

Lemma FF_precise: precise (FF).
Proof.
  replace (@FF mpred Nveric) with (mapsto Tsh tint Vundef Vundef).
  apply mapsto_precise.
  unfold mapsto.
  reflexivity.
Qed.

Lemma memory_block_precise: forall sh n p, precise (memory_block sh n p).
Proof.
  intros.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  destruct p; try apply FF_precise.
  apply precise_prop_andp.
  forget (nat_of_Z (Int.unsigned n)) as nn; clear n.
  forget (Int.unsigned i) as ii; clear i.
  generalize ii.
  induction nn; intros.
  + apply emp_precise.
  + simpl. 
    apply precise_sepcon.
    apply mapsto_precise.
    apply IHnn.
Qed.

Lemma at_offset'_preserve_precise: forall P, (forall p, precise (P p)) -> 
  forall be p, P (offset_val (Int.repr 0) p) = P p -> precise (at_offset' P be p).
Proof.
  intros.
  rewrite at_offset'_eq by auto.
  apply H.
Qed.

Lemma spacer_precise: forall sh be ed p, precise (spacer sh be ed p).
Proof.
  intros.
  unfold spacer.
  if_tac.
  apply emp_precise.
  apply at_offset'_preserve_precise; [intros; apply memory_block_precise |].
  apply memory_block_offset_zero.
Qed.

Lemma withspacer_preserve_precise: forall sh be ed P p,
  precise (P p) -> precise (withspacer sh be ed P p).
Proof.
  intros.
  rewrite withspacer_spacer.
Opaque spacer.
  simpl.
Transparent spacer.
  apply precise_sepcon.
  apply spacer_precise.
  exact H.
Qed.

Lemma array_at'_preserve_precise: forall t sh P v lo hi p,
  (forall v p, precise (P v p)) -> precise (array_at' t sh P v lo hi p).
Proof.
  intros.
  unfold array_at'.
  apply precise_prop_andp.
  unfold rangespec.
  forget (nat_of_Z (hi - lo)) as nn; clear hi.
  generalize lo.
  induction nn; intros; simpl.
  + apply emp_precise.
  + apply precise_sepcon.
    apply H.
    apply IHnn.
Qed.

Lemma data_at'_precise: forall sh env t ofs v p, precise (data_at' sh env t ofs v p).
Proof.
  intros.
  apply (type_mut (fun t => forall ofs v p, precise (data_at' sh env t ofs v p))
                  (fun tl => True)
                  (fun fld => (forall al ofs v p, precise (sfieldlist_at' sh env fld al ofs v p)) /\
                              (forall al ofs v p, precise (ufieldlist_at' sh env fld al ofs v p))));
  intros; auto; try simpl;
  try (unfold at_offset2; apply at_offset'_preserve_precise;
       [| try (apply memory_block_offset_zero);
          try (apply mapsto_offset_zero);
          try (symmetry; apply array_at'_offset_zero)]).
  + apply memory_block_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + intros; apply array_at'_preserve_precise.
    apply H.
  + apply memory_block_precise.
  + destruct H as [H _]; apply H.
  + destruct H as [_ H]; apply H.
  + apply mapsto_precise.
  + simpl; split; intros; apply precise_prop_andp, emp_precise.
  + destruct H0.
    split; intros; destruct (is_Fnil f).
    - apply withspacer_preserve_precise, H.
    - apply precise_sepcon.
      apply withspacer_preserve_precise, H.
      apply H0.
    - apply withspacer_preserve_precise, H.
    - destruct v0.
      apply withspacer_preserve_precise, H.
      apply H1.
Qed.

Lemma data_at_precise: forall sh t v p, precise (data_at sh t v p).
Proof.
  intros; unfold data_at.
  simpl.
  apply precise_prop_andp, data_at'_precise.
Qed.

Lemma field_at_precise: forall sh t ids v p, precise (field_at sh t ids v p).
Proof.
  intros; unfold field_at.
  simpl.
  apply precise_prop_andp, data_at'_precise.
Qed.
*)
Lemma is_Fnil_fieldlist_app:
  forall f1 f2, is_Fnil (fieldlist_app f1 f2) = true -> is_Fnil f1 = true /\ is_Fnil f2 = true.
Proof.
  intros.
  destruct f1, f2; simpl in *; auto.
Qed.

Fixpoint reptype_suf_struct {fp fs: fieldlist} (v: reptype_structlist (fieldlist_app fp fs)) (vs: reptype_structlist fs) :=
  match fp as fp'
    return reptype_structlist (fieldlist_app fp' fs) -> Prop
  with
  | Fnil => fun v => v = vs
  | Fcons i0 t0 fp0 => 
    if (is_Fnil (fieldlist_app fp0 fs)) as b
      return (if b then reptype t0 else reptype t0 * reptype_structlist (fieldlist_app fp0 fs)) -> Prop
    then fun _ => True
    else fun v => reptype_suf_struct (snd v) vs
  end v.

Lemma reptype_suf_struct_Fnil: forall {f} (v: reptype_structlist f), exists v0, @reptype_suf_struct Fnil f v0 v /\ JMeq v0 v.
Proof.
  intros.
  simpl in v |- *.
  eauto.
Qed.

Lemma reptype_suf_struct_Fcons: forall f0 i0 t1 i1 t2 f v v0, @reptype_suf_struct f0 (Fcons i0 t1 (Fcons i1 t2 f)) v v0 -> exists v1, JMeq v v1 /\ @reptype_suf_struct (fieldlist_app f0 (Fcons i0 t1 Fnil)) (Fcons i1 t2 f) v1 (snd v0).
Proof.
  intros.
  induction f0.
  + simpl in *.
    exists v.
    rewrite H; auto.
  + simpl in v, H |- *.
    revert v H.
    destruct (is_Fnil (fieldlist_app f0 (Fcons i0 t1 (Fcons i1 t2 f)))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb.
      destruct Heqb as [_ H].
      inversion H.
    } Unfocus.
    destruct (is_Fnil (fieldlist_app (fieldlist_app f0 (Fcons i0 t1 Fnil))
                  (Fcons i1 t2 f))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb0.
      destruct Heqb0 as [_ H0].
      inversion H0.
    } Unfocus.
    intros.
    destruct (IHf0 (snd v) H) as [v2 [? ?]].
    exists (fst v, v2).
    split.
    - clear H1; revert v2 H0.
      rewrite <- fieldlist_app_Fcons.
      intros.
      rewrite <- H0.
      destruct v; reflexivity.
    - simpl.
      exact H1.
Qed.

Lemma proj_reptype_structlist_ofs: forall i f ofs ofs0 v,
  JMeq (proj_reptype_structlist i f ofs v) (proj_reptype_structlist i f ofs0 v).
Proof.
  intros.
  revert ofs ofs0.
  induction f; intros.
  + reflexivity.
  + simpl.
    if_tac.
    - revert v; simpl; if_tac; reflexivity.
    - revert v; simpl; destruct (is_Fnil f) eqn:?; intros.
      * destruct f; inversion Heqb; reflexivity.
      * apply IHf.
Qed.

Lemma proj_reptype_structlist_fieldlist_app: forall f0 f id t v v0,
  fieldlist_no_replicate (fieldlist_app f0 f) = true ->
  field_type id f = Errors.OK t ->
  @reptype_suf_struct f0 f v v0 ->
  JMeq (proj_reptype_structlist id (fieldlist_app f0 f) 0 v) (proj_reptype_structlist id f 0 v0).
Proof.
  intros.
  generalize 0 at 1 2.
  generalize 0.
  induction f0; intros.
  + simpl in v, H1 |- *.
    rewrite H1.
    apply proj_reptype_structlist_ofs.
  + simpl in H1 |- *.
    if_tac. (* whether id = i *)
    - pose proof (fieldlist_no_replicate_fact _ _ id H).
      simpl in H3.
      if_tac in H3; [| congruence].
      rewrite H0 in H3.
      pose proof H3 eq_refl eq_refl.
      inversion H5.
    - revert v H1; simpl.
      destruct (is_Fnil (fieldlist_app f0 f)) eqn:?; intros. (* whether fieldlist f0 f is Fnil *)
      * destruct (is_Fnil_fieldlist_app _ _ Heqb) as [_ ?].
        destruct f; [inversion H0 | inversion H3].
      * simpl in H.
        rewrite andb_true_iff in H.
        destruct H.
        apply IHf0; auto.
Qed.

Lemma proj_reptype_cons_hd_Tstruct_Fnil: forall i f0 i0 t0 a t id ids v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t ids = Tstruct i (fieldlist_app f0 (Fcons i0 t0 Fnil)) a ->
  JMeq (proj_reptype t ids v) vs ->
  @reptype_suf_struct f0 (Fcons i0 t0 Fnil) vs v0 ->
  JMeq (proj_reptype t (id :: ids) v) v0.
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t ids v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ ids H.
  rewrite H1 in H4.
  simpl in H4.
  apply andb_true_iff in H4; destruct H4 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_structlist_fieldlist_app; eauto.
  + simpl.
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

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

Lemma proj_reptype_cons_hd_Tstruct_Fcons: forall i f0 i0 t0 i1 t1 f a t id ids v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t ids = Tstruct i (fieldlist_app f0 (Fcons i0 t0 (Fcons i1 t1 f))) a ->
  JMeq (proj_reptype t ids v) vs ->
  @reptype_suf_struct f0 (Fcons i0 t0 (Fcons i1 t1 f)) vs v0 ->
  JMeq (proj_reptype t (id :: ids) v) (fst v0).
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t ids v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ ids H.
  rewrite H1 in H4.
  simpl in H4.
  apply andb_true_iff in H4; destruct H4 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_structlist_fieldlist_app; eauto.
  + simpl.
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

Definition nested_sfieldlist_at_sub: forall sh t id ids i f a0 p t0,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tstruct i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v1,
  JMeq (proj_reptype t ids v) v1 ->  
  field_at sh t ids (proj_reptype t ids v) p = 
  field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * P (proj_except_reptype_structlist f id v1)).
Proof.
  cut (forall sh t id ids i f a0 p t0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tstruct i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v0 v1,  
  JMeq (proj_reptype t ids v) v1 ->
  JMeq v0 v1 ->
  nested_sfieldlist_at sh t ids f v0 p = 
  field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * 
    P (proj_except_reptype_structlist f id v1))).
  Focus 1. {
    intro H; intros.
    assert (nested_reptype_structlist t ids f = reptype_structlist f).
      erewrite <- nested_reptype_structlist_lemma2; eauto.
      rewrite H2.
      reflexivity.
    destruct (H sh t id ids i f a0 p t0 H1 H2 H3) as [PH H5]; clear H.
    eexists; intros.
    pose (eq_rect_r (fun T => T) v1 H4) as v0.
    erewrite field_at_Tstruct; eauto.
    instantiate (2 :=  v0).
    eapply (H5 v v0 v1); eauto.
    + subst v0. apply eq_rect_r_JMeq with (F:=fun T => T).
    + destruct f; [inversion H3 | reflexivity].
    + rewrite H; subst v0. apply JMeq_sym, eq_rect_r_JMeq with (F:=fun T => T).
  } Unfocus.
  intros.
  change f with (fieldlist_app Fnil f) in H0.
  cut (sigT (fun P => forall (v : reptype t) (v0 : nested_reptype_structlist t ids f)
       (v1 : reptype_structlist f) (vs: reptype_structlist (fieldlist_app Fnil f)),
     JMeq (proj_reptype t ids v) vs ->
     reptype_suf_struct vs v1 ->
     JMeq v0 v1 ->
     nested_sfieldlist_at sh t ids f v0 p =
     field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p *
     P (proj_except_reptype_structlist f id v1))).
  Focus 1. {
    intro H2.
    destruct H2 as [P H3]; exists P.
    intros.
    destruct (reptype_suf_struct_Fnil v1) as [x [? ?]].
    eapply H3 with (vs := x); eauto.
    rewrite H6.
    exact H2.
  } Unfocus.
  revert H0.
  generalize Fnil.
  induction f; intros.
  + inversion H1.
  + assert (fieldlist_no_replicate (fieldlist_app f0 (Fcons i0 t1 f)) = true).
    Focus 1. {
      pose proof nested_field_type2_nest_pred eq_refl _ ids H.
      rewrite H0 in H2.
      simpl in H2.
      apply andb_true_iff in H2.
      tauto.
    } Unfocus.
    assert (reptype (nested_field_type2 t (i0 :: ids)) = reptype t1)
      by (erewrite nested_field_type2_Tstruct_mid; eauto).
    assert (nested_reptype_structlist t ids f = reptype_structlist f).
    Focus 1. {
      unfold nested_field_type2 in H0.
      valid_nested_field_rec t ids H0.
      subst t2.
      rewrite fieldlist_app_Fcons in H4.
      eapply eq_sym, nested_reptype_structlist_lemma; eauto.
    } Unfocus.
    simpl in H1.
    if_tac in H1. (* whether id = the ident of head field *)
    - clear IHf. 
      simpl nested_sfieldlist_at.
Opaque field_at proj_reptype spacer nested_sfieldlist_at.
      destruct f; simpl;
      (if_tac; [| congruence]);
      eexists; intros;
      rewrite withspacer_spacer; simpl.
Transparent field_at proj_reptype spacer nested_sfieldlist_at.
      * pose proof proj_reptype_cons_hd_Tstruct_Fnil i f0 i0 t1 a0 t id ids v vs v1 H H5 H0 H7 H8.
        subst.
        simpl in H10, H9.
        rewrite <- H10 in H9.
        apply JMeq_eq in H9.
        rewrite H9.
        rewrite sepcon_comm.
        match goal with
        | |- _ * ?T = _ => instantiate (1:= fun _ => T)
        end.
        eauto.
      * rewrite sepcon_comm with (Q := field_at sh t (i0 :: ids) (fst v0) p).
        rewrite sepcon_assoc.
        
        f_equal.
        Focus 1. {
          pose proof proj_reptype_cons_hd_Tstruct_Fcons i f0 i0 t1 i1 t2 f a0 t id ids v vs v1 H H5 H0 H7 H8.
          subst; f_equal.
          apply JMeq_eq.
          rewrite H10.
          apply JMeq_fst; eauto.
        } Unfocus.
        Focus 1. {
          match goal with
          | |- ?T * (?R _ _) = _ => instantiate (1:= fun v => T * R (eq_rect_r (fun T => T) v H4) p)
          end.
          simpl.
          f_equal. f_equal.
          apply JMeq_snd in H9; eauto.
          apply eq_sym, JMeq_eq.
          simpl in *; rewrite H9.
          apply (eq_rect_JMeq _ _ _ (fun y => y) (snd v1) (eq_sym H4)).
        } Unfocus.
    - destruct f; try (solve [inversion H1]).
      rewrite fieldlist_app_Fcons in H0.
      destruct (IHf H1 (fieldlist_app f0 (Fcons i0 t1 Fnil)) H0) as [PH IH]; clear IHf.
      cut (sigT (fun P :
            (if is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id) 
             then reptype t1
             else reptype t1 * reptype_structlist (all_fields_except_one2 (Fcons i1 t2 f) id))
             -> mpred =>
             forall (v : reptype t)
             (v0 : nested_reptype_structlist t ids (Fcons i0 t1 (Fcons i1 t2 f)))
             (v1 : reptype_structlist (Fcons i0 t1 (Fcons i1 t2 f)))
             (vs : reptype_structlist
                     (fieldlist_app f0 (Fcons i0 t1 (Fcons i1 t2 f)))),
             JMeq (proj_reptype t ids v) vs ->
             reptype_suf_struct vs v1 ->
             JMeq v0 v1 ->
             nested_sfieldlist_at sh t ids (Fcons i0 t1 (Fcons i1 t2 f)) v0 p =
             field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p *
             P (if is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id) as b
                  return if b 
                         then reptype t1
                         else reptype t1 * reptype_structlist 
                              (all_fields_except_one2 (Fcons i1 t2 f) id)
                then fst v1
                else (fst v1, proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1))))).
      Focus 1. {
        intro H6.
        destruct H6 as [P H6]. 
        simpl (all_fields_except_one2 (Fcons i0 t1 (Fcons i1 t2 f)) id).
        simpl proj_except_reptype_structlist.
        if_tac; [congruence | exists P; intros].
        eapply H6; eauto.
      } Unfocus.
      assert (forall (v0 : nested_reptype_structlist t ids (Fcons i0 t1 (Fcons i1 t2 f)))
       (v1 : reptype_structlist (Fcons i0 t1 (Fcons i1 t2 f))),
        JMeq v0 v1 -> (JMeq (fst v0) (fst v1) /\ JMeq (snd v0) (snd v1))) by
        (intros; split; [apply JMeq_fst | apply JMeq_snd]; eauto).
      
Opaque field_at proj_reptype spacer nested_sfieldlist_at proj_except_reptype_structlist.
      destruct (is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id)) eqn:HH; eexists; intros;
      replace (nested_sfieldlist_at sh t ids (Fcons i0 t1 (Fcons i1 t2 f)) v0 p) with
             ((withspacer sh
          (nested_field_offset2 t (i0 :: ids) +
           sizeof (nested_field_type2 t (i0 :: ids)))
          (align
             (nested_field_offset2 t (i0 :: ids) +
              sizeof (nested_field_type2 t (i0 :: ids))) 
             (alignof_hd (Fcons i1 t2 f))) (field_at sh t (i0 :: ids) (fst v0)) p *
          nested_sfieldlist_at sh t ids (Fcons i1 t2 f) (snd v0) p)) by reflexivity;
      rewrite withspacer_spacer; simpl.
Transparent field_at proj_reptype spacer nested_sfieldlist_at proj_except_reptype_structlist.
      * destruct (reptype_suf_struct_Fcons f0 i0 t1 i1 t2 f vs v1 H8) as [v2 [? ?]].
        assert (nested_sfieldlist_at sh t ids (Fcons i1 t2 f) (snd v0) p =
                field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p *
                PH (proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1))).
        Focus 1. {
          apply (IH v (snd v0) (snd v1) v2); eauto.
          + rewrite <- H10. exact H7.
          + apply JMeq_snd; eauto.
        } Unfocus.
        rewrite H12; clear H12 IH.
        destruct (H6 v0 v1 H9).
        match goal with
        | |- ?A2 * (?A1 _ _) * (_ * _) = _ => 
          instantiate (1:= fun v => A2 * A1 (eq_rect_r (fun T => T) v H3) p * (PH (struct_default_val _)))
        end.
        assert (all_fields_except_one2 (Fcons i1 t2 f) id = Fnil) by
          (destruct (all_fields_except_one2 (Fcons i1 t2 f) id); [trivial | inversion HH]).
        forget (proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1)) as tt'.
        forget (struct_default_val (all_fields_except_one2 (Fcons i1 t2 f) id)) as tt''.
        revert tt' tt'' PH.
        rewrite H14; intros.
        normalize.
        destruct tt', tt''.
        f_equal.
        rewrite sepcon_comm, <- sepcon_assoc.
        f_equal.
        f_equal.
        apply eq_sym, JMeq_eq.
        simpl in *; rewrite H12.
        erewrite eq_rect_JMeq with (F := fun T => T).
        reflexivity.
      * destruct (reptype_suf_struct_Fcons f0 i0 t1 i1 t2 f vs v1 H8) as [v2 [? ?]].
        assert (nested_sfieldlist_at sh t ids (Fcons i1 t2 f) (snd v0) p =
                field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p *
                PH (proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1))).
        Focus 1. {
          apply (IH v (snd v0) (snd v1) v2); eauto.
          + rewrite <- H10. exact H7.
          + apply JMeq_snd; eauto.
        } Unfocus.
        rewrite H12; clear H12 IH.
        destruct (H6 v0 v1 H9).
        match goal with
        | |- ?A2 * (?A1 _ _) * (_ * _) = _ => 
          instantiate (1:= fun v => A2 * A1 (eq_rect_r (fun T => T) (fst v) H3) p * PH (snd v))
        end.
        normalize.
        f_equal.
        rewrite sepcon_comm, <- sepcon_assoc.
        f_equal.
        f_equal.
        apply eq_sym, JMeq_eq.
        simpl in *; rewrite H12.
        erewrite eq_rect_JMeq with (F := fun T => T).
        reflexivity.
Qed.

Fixpoint reptype_suf_union {fp fs: fieldlist} (v: reptype_unionlist (fieldlist_app fp fs)) (vs: reptype_unionlist fs) :=
  match fp as fp'
    return reptype_unionlist (fieldlist_app fp' fs) -> Prop
  with
  | Fnil => fun v => v = vs
  | Fcons i0 t0 fp0 => 
    if (is_Fnil (fieldlist_app fp0 fs)) as b
      return (if b then reptype t0 else reptype t0 + reptype_unionlist (fieldlist_app fp0 fs)) -> Prop
    then fun _ => True
    else fun v => 
      match v with
      | inl _ => False
      | inr v' => reptype_suf_union v' vs
      end
  end v.

Lemma reptype_suf_union_Fnil: forall {f} (v: reptype_unionlist f), exists v0, @reptype_suf_union Fnil f v0 v /\ JMeq v0 v.
Proof.
  intros.
  simpl in v |- *.
  eauto.
Qed.

Lemma reptype_suf_union_Fcons: forall f0 i0 t1 i1 t2 f v v0, @reptype_suf_union f0 (Fcons i0 t1 (Fcons i1 t2 f)) v v0 -> exists v1, JMeq v v1 /\ (forall v2: reptype_unionlist (Fcons i1 t2 f), v0 = inr v2 -> @reptype_suf_union (fieldlist_app f0 (Fcons i0 t1 Fnil)) (Fcons i1 t2 f) v1 v2).
Proof.
  intros.
  induction f0.
  + simpl in *.
    exists v.
    split; [rewrite H | intros; subst]; auto.
  + simpl in v, H |- *.
    revert v H.
    destruct (is_Fnil (fieldlist_app f0 (Fcons i0 t1 (Fcons i1 t2 f)))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb.
      destruct Heqb as [_ H].
      inversion H.
    } Unfocus.
    destruct (is_Fnil (fieldlist_app (fieldlist_app f0 (Fcons i0 t1 Fnil))
                  (Fcons i1 t2 f))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb0.
      destruct Heqb0 as [_ H0].
      inversion H0.
    } Unfocus.
    intros.
    destruct v as [v | v]; [inversion H |].
    destruct (IHf0 v H) as [v2 [? ?]].
    exists (inr v2).
    split.
    - rewrite H0. reflexivity.
    - simpl.
      exact H1.
Qed.

Lemma proj_reptype_unionlist_fieldlist_app: forall f0 f id t v v0,
  fieldlist_no_replicate (fieldlist_app f0 f) = true ->
  field_type id f = Errors.OK t ->
  @reptype_suf_union f0 f v v0 ->
  JMeq (proj_reptype_unionlist id (fieldlist_app f0 f) v) (proj_reptype_unionlist id f v0).
Proof.
  intros.
  induction f0.
  + simpl in v, H1 |- *.
    rewrite H1.
    reflexivity.
  + simpl in H1 |- *.
    if_tac. (* whether id = i *)
    - pose proof (fieldlist_no_replicate_fact _ _ id H).
      simpl in H3.
      if_tac in H3; [| congruence].
      rewrite H0 in H3.
      pose proof H3 eq_refl eq_refl.
      inversion H5.
    - revert v H1; simpl.
      destruct (is_Fnil (fieldlist_app f0 f)) eqn:?; intros. (* whether fieldlist f0 f is Fnil *)
      * destruct (is_Fnil_fieldlist_app _ _ Heqb) as [_ ?].
        destruct f; [inversion H0 | inversion H3].
      * simpl in H.
        rewrite andb_true_iff in H.
        destruct H.
        destruct v as [v | v]; [inversion H1 |].
        apply IHf0; auto.
Qed.

Lemma proj_reptype_cons_hd_Tunion_Fnil: forall i f0 i0 t0 a t id ids v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t ids = Tunion i (fieldlist_app f0 (Fcons i0 t0 Fnil)) a ->
  JMeq (proj_reptype t ids v) vs ->
  @reptype_suf_union f0 (Fcons i0 t0 Fnil) vs v0 ->
  JMeq (proj_reptype t (id :: ids) v) v0.
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t ids v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ ids H.
  rewrite H1 in H4.
  simpl in H4.
  apply andb_true_iff in H4; destruct H4 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_unionlist_fieldlist_app; eauto.
  + simpl.
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

Lemma proj_reptype_cons_hd_Tunion_Fcons: forall i f0 i0 t0 i1 t1 f a t id ids v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t ids = Tunion i (fieldlist_app f0 (Fcons i0 t0 (Fcons i1 t1 f))) a ->
  JMeq (proj_reptype t ids v) vs ->
  @reptype_suf_union f0 (Fcons i0 t0 (Fcons i1 t1 f)) vs v0 ->
  forall v0', v0 = inl v0' ->
  JMeq (proj_reptype t (id :: ids) v) v0'.
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t ids v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ ids H.
  rewrite H1 in H5.
  simpl in H5.
  apply andb_true_iff in H5; destruct H5 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_unionlist_fieldlist_app; eauto.
  + simpl;
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

Definition nested_ufieldlist_at_sub: forall sh t id ids i f a0 p t0,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tunion i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v1,
  JMeq (proj_reptype t ids v) v1 ->
  is_precise_proj_reptype_unionlist f id v1 = true ->
  field_at sh t ids (proj_reptype t ids v) p = 
  field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * P).
Proof.
  cut (forall sh t id ids i f a0 p t0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tunion i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v0 (v1: reptype_unionlist f),  
  JMeq (proj_reptype t ids v) v1 ->
  JMeq v0 v1 ->
  is_precise_proj_reptype_unionlist f id v1 = true ->
  nested_ufieldlist_at sh t ids f v0 p = 
  field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * P)).
  Focus 1. {
    intro H; intros.
    assert (nested_reptype_unionlist t ids f = reptype_unionlist f).
      erewrite <- nested_reptype_unionlist_lemma2; eauto.
      rewrite H2.
      reflexivity.
    destruct (H sh t id ids i f a0 p t0 H1 H2 H3) as [PH H5]; clear H.
    eexists; intros.
    pose (eq_rect_r (fun T => T) v1 H4) as v0.
    erewrite field_at_Tunion; eauto.
    instantiate (2 := v0).
    eapply (H5 v v0 v1); eauto.
    + subst v0. apply eq_rect_r_JMeq with (F:=fun T => T).
    + destruct f; [inversion H3 | reflexivity].
    + rewrite H; subst v0. apply JMeq_sym, eq_rect_r_JMeq with (F:=fun T => T).
  } Unfocus.
  intros.
  change f with (fieldlist_app Fnil f) in H0.
  cut (sigT (fun P => forall (v : reptype t) (v0 : nested_reptype_unionlist t ids f)
       (v1 : reptype_unionlist f) (vs: reptype_unionlist (fieldlist_app Fnil f)),
     JMeq (proj_reptype t ids v) vs ->
     reptype_suf_union vs v1 ->
     JMeq v0 v1 ->
     is_precise_proj_reptype_unionlist f id v1 = true ->
     nested_ufieldlist_at sh t ids f v0 p =
     field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * P)).
  Focus 1. {
    intro H2.
    destruct H2 as [P H3]; exists P.
    intros.
    destruct (reptype_suf_union_Fnil v1) as [x [? ?]].
    eapply H3 with (vs := x); eauto.
    rewrite H6.
    exact H2.
  } Unfocus.
  revert H0.
  generalize Fnil.
  induction f; intros.
  + inversion H1.
  + assert (fieldlist_no_replicate (fieldlist_app f0 (Fcons i0 t1 f)) = true).
    Focus 1. {
      pose proof nested_field_type2_nest_pred eq_refl _ ids H.
      rewrite H0 in H2.
      simpl in H2.
      apply andb_true_iff in H2.
      tauto.
    } Unfocus.

    assert (reptype (nested_field_type2 t (i0 :: ids)) = reptype t1)
      by (erewrite nested_field_type2_Tunion_mid; eauto).
    assert (nested_reptype_unionlist t ids f = reptype_unionlist f).
    Focus 1. {
      unfold nested_field_type2 in H0.
      valid_nested_field_rec t ids H0.
      subst t2.
      rewrite fieldlist_app_Fcons in H4.
      eapply eq_sym, nested_reptype_unionlist_lemma; eauto.
    } Unfocus.
    simpl in H1.
    if_tac in H1. (* whether id = the ident of head field *)
    - clear IHf. 
      simpl nested_ufieldlist_at.
Opaque field_at proj_reptype spacer nested_ufieldlist_at.
      destruct f; simpl;
      eexists; intros; [| destruct v0];
      try (rewrite withspacer_spacer; simpl).
Transparent field_at proj_reptype spacer nested_ufieldlist_at.
      * pose proof proj_reptype_cons_hd_Tunion_Fnil i f0 i0 t1 a0 t id ids v vs v1 H H5 H0 H6 H7.
        subst.
        simpl in H10, H8.
        rewrite <- H10 in H8.
        apply JMeq_eq in H8.
        rewrite H8.
        rewrite sepcon_comm.
        match goal with
        | |- _ * ?T = _ => instantiate (1:= T)
        end.
        eauto.
      * rewrite sepcon_comm.
        f_equal.
        pose proof proj_reptype_cons_hd_Tunion_Fcons i f0 i0 t1 i1 t2 f a0 t id ids v vs v1 H H5 H0 H6 H7.
        destruct v1.
        {
          apply JMeq_sumtype_ll in H8; auto.
          subst; f_equal.
          apply JMeq_eq.
          erewrite H10; eauto.
        } 
        {
          apply JMeq_sumtype_lr in H8; tauto.
        }
      * if_tac in H9; [| congruence].
        destruct v1; [apply JMeq_sumtype_rl in H8; tauto | inversion H9].
    - destruct f; try (solve [inversion H1]).
      rewrite fieldlist_app_Fcons in H0.
      destruct (IHf H1 (fieldlist_app f0 (Fcons i0 t1 Fnil)) H0) as [PH IH]; clear IHf.
(*      assert (forall (v0 : nested_reptype_unionlist t ids (Fcons i0 t1 (Fcons i1 t2 f)))
       (v1 : reptype_unionlist (Fcons i0 t1 (Fcons i1 t2 f))),
        JMeq v0 v1 -> (JMeq (fst v0) (fst v1) /\ JMeq (snd v0) (snd v1))) by
        (intros; split; [apply JMeq_fst | apply JMeq_snd]; eauto).
*)      
Opaque field_at proj_reptype spacer nested_ufieldlist_at proj_except_reptype_unionlist.
      destruct (is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id)) eqn:HH; eexists; intros;
      replace (nested_ufieldlist_at sh t ids (Fcons i0 t1 (Fcons i1 t2 f)) v0 p) with
        (match v0 with
        | inl v0' =>
            withspacer sh
              (nested_field_offset2 t (i0 :: ids) +
               sizeof (nested_field_type2 t (i0 :: ids)))
              (nested_field_offset2 t ids + sizeof (nested_field_type2 t ids))
              (field_at sh t (i0 :: ids) v0') p
        | inr v0' =>
            nested_ufieldlist_at sh t ids (Fcons i1 t2 f) v0' p
        end);
      simpl in H8; solve_JMeq_sumtype H8;
      try (rewrite withspacer_spacer; simpl).
Transparent field_at proj_reptype spacer nested_ufieldlist_at proj_except_reptype_unionlist.
      * simpl in H9; if_tac in H9; congruence.
      * destruct (reptype_suf_union_Fcons f0 i0 t1 i1 t2 f vs (inr r) H7) as [v2 [? HHH]].
        pose proof HHH r eq_refl; clear HHH.
        erewrite IH; eauto.
        {
          rewrite <- H10.
          exact H6.
        }
        {
          simpl in H9.
          if_tac in H9; [congruence |].
          exact H9.
        }
      * simpl in H9; if_tac in H9; congruence.
      * destruct (reptype_suf_union_Fcons f0 i0 t1 i1 t2 f vs (inr r) H7) as [v2 [? HHH]].
        pose proof HHH r eq_refl; clear HHH.
        erewrite IH; eauto.
        {
          rewrite <- H10.
          exact H6.
        }
        {
          simpl in H9.
          if_tac in H9; [congruence |].
          exact H9.
        }
Qed.

Lemma proj_reptype_structlist_gupd_reptype_structlist_identical: forall f id t0 v v0,
  isSome (all_fields_replace_one f id t0) ->
  JMeq (proj_reptype_structlist id _ 0 (gupd_reptype_structlist f id t0 v v0)) v0.
Proof.
  intros.
  generalize 0; induction f; intros.
  + simpl in H.
    inversion H.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl. revert v. if_tac.
      * intros; if_tac; [| congruence]. reflexivity.
      * intros; if_tac; [| congruence]. reflexivity.
    - (* id <> i *)
      destruct (is_Fnil f) eqn:?.
      * destruct f; [| inversion Heqb].
        simpl in H; inversion H.
      * simpl; if_tac; [congruence |].
        rewrite (is_Fnil_all_fields_replace_one2 f id t0), Heqb.
        simpl.
        apply IHf.
        destruct (all_fields_replace_one f id t0); [auto | inversion H].
Qed.

Lemma proj_reptype_unionlist_gupd_reptype_unionlist_identical: forall f id t0 v0,
  isSome (all_fields_replace_one f id t0) ->
  JMeq (proj_reptype_unionlist id _ (gupd_reptype_unionlist f id t0 v0)) v0.
Proof.
  intros.
  induction f; intros.
  + simpl in H.
    inversion H.
  + simpl in *.
    destruct (ident_eq id i).
    - (* id = i *)
      simpl. if_tac; [| congruence].
      if_tac; reflexivity.
    - (* id <> i *)
      destruct (is_Fnil f) eqn:?.
      * destruct f; [| inversion Heqb].
        simpl in H; inversion H.
      * simpl; if_tac; [congruence |].
        rewrite (is_Fnil_all_fields_replace_one2 f id t0), Heqb.
        apply IHf.
        destruct (all_fields_replace_one f id t0); [auto | inversion H].
Qed.

Lemma proj_except_reptype_structlist_gupd_reptype_structlist: forall f id t0 v v0,
  JMeq (proj_except_reptype_structlist _ id (gupd_reptype_structlist f id t0 v v0)) (proj_except_reptype_structlist f id v).
Proof.
  intros.
  induction f.
  + simpl in *. destruct v. reflexivity.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl. if_tac; [| congruence].
      destruct f; simpl; reflexivity.
    - (* id <> i *)
      simpl. if_tac; [congruence |].
      destruct (is_Fnil f) eqn:?.
      * destruct f; [| inversion Heqb].
        reflexivity.
      * rewrite (is_Fnil_all_fields_replace_one2 f id t0), Heqb.
        simpl.
        pattern (all_fields_except_one2 (all_fields_replace_one2 f id t0) id) at 1 3.
        rewrite (all_fields_except_one2_all_fields_replace_one2 id f t0).
        if_tac; [reflexivity |].
        generalize (IHf (snd v)).
        match goal with
        | |- JMeq ?M _ -> _ => generalize M
        end.
        rewrite (all_fields_except_one2_all_fields_replace_one2 id f t0).
        intros.
        rewrite H1.
        reflexivity.
Qed.

Lemma proj_except_reptype_unionlist_gupd_reptype_unionlist: forall f id t0,
  JMeq (proj_except_reptype_unionlist (all_fields_replace_one2 f id t0) id) (proj_except_reptype_unionlist f id).
Proof.
  intros.
  induction f.
  + simpl in *. reflexivity.
  + simpl in *.
    unfold proj_except_reptype_unionlist.
    simpl.
    if_tac.
    - (* id = i *)
      simpl. if_tac; [| congruence].
      destruct f; simpl; reflexivity.
    - (* id <> i *)
      simpl. if_tac; [congruence |].
      destruct (is_Fnil f) eqn:?.
      * destruct f; [| inversion Heqb].
        reflexivity.
      * rewrite (all_fields_except_one2_all_fields_replace_one2 id f t0).
        reflexivity.
Qed.

Lemma gupd_reptype_structlist_gupd_reptype_structlist: forall f id t0 t1 v v0 v1,
  JMeq (gupd_reptype_structlist _ id t1 (gupd_reptype_structlist f id t0 v v0) v1)
    (gupd_reptype_structlist f id t1 v v1).
Proof.
  intros.
  revert t0 t1 v0 v1.
  induction f; intros.
  + simpl. reflexivity.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl; if_tac; [| congruence].
      simpl; if_tac; reflexivity.
    - (* id <> i *)
      simpl; if_tac; [congruence |].
      simpl.
      destruct (is_Fnil f) eqn:?.
      * simpl; rewrite !is_Fnil_all_fields_replace_one2, Heqb. reflexivity.
      * simpl; rewrite !is_Fnil_all_fields_replace_one2, Heqb.
        simpl. rewrite IHf.
        reflexivity.
Qed.

Lemma gupd_reptype_unionlist_gupd_reptype_unionlist: forall f id t0 t1 v1,
  JMeq (gupd_reptype_unionlist (all_fields_replace_one2 f id t0) id t1 v1)
    (gupd_reptype_unionlist f id t1 v1).
Proof.
  intros.
  revert t0 t1 v1.
  induction f; intros.
  + simpl. reflexivity.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl; if_tac; [| congruence].
      simpl; if_tac; reflexivity.
    - (* id <> i *)
      simpl; if_tac; [congruence |].
      simpl.
      destruct (is_Fnil f) eqn:?.
      * simpl; rewrite !is_Fnil_all_fields_replace_one2, Heqb. reflexivity.
      * simpl; rewrite !is_Fnil_all_fields_replace_one2, Heqb.
        simpl. rewrite IHf.
        reflexivity.
Qed.

Lemma proj_reptype_gupd_reptype: forall t ids v t0 v0,
  isSome (nested_field_rec t ids) ->
  JMeq (proj_reptype (nf_replace2 t ids t0) ids (gupd_reptype t ids t0 v v0)) v0.
Proof.
  intros.
  revert t v t0 v0 H.
  induction ids; intros.
  + simpl. reflexivity.
  + simpl; generalize (proj_reptype t ids v).
    solve_nested_field_rec_cons_isSome H; rewrite H2; intros.
    - (* Tstruct *)
      rewrite eq_rect_JMeq.
      generalize (IHids t v (Tstruct i (all_fields_replace_one2 f a t0) a0) (gupd_reptype_structlist f a t0 r v0) H0).
      generalize ((proj_reptype
        (nf_replace2 t ids (Tstruct i (all_fields_replace_one2 f a t0) a0))
        ids
        (gupd_reptype t ids (Tstruct i (all_fields_replace_one2 f a t0) a0) v
           (gupd_reptype_structlist f a t0 r v0)))).
      erewrite nested_field_type2_nf_replace2; eauto; intros.
      simpl in r0.
      rewrite H3.
      apply proj_reptype_structlist_gupd_reptype_structlist_identical.
      apply (iff_sym (all_fields_replace_one_field_type_isSome_lemma _ _ _)), H1.
    - (* Tunion *)
      rewrite eq_rect_JMeq.
      generalize (IHids t v (Tunion i (all_fields_replace_one2 f a t0) a0) (gupd_reptype_unionlist f a t0 v0) H0).
      generalize ((proj_reptype
        (nf_replace2 t ids (Tunion i (all_fields_replace_one2 f a t0) a0))
        ids
        (gupd_reptype t ids (Tunion i (all_fields_replace_one2 f a t0) a0) v
           (gupd_reptype_unionlist f a t0 v0)))).
      erewrite nested_field_type2_nf_replace2; eauto; intros.
      simpl in r0.
      rewrite H3.
      apply proj_reptype_unionlist_gupd_reptype_unionlist_identical.
      apply (iff_sym (all_fields_replace_one_field_type_isSome_lemma _ _ _)), H1.
Qed.

Lemma gupd_reptype_gupd_reptype: forall t ids t0 t1 v v0 v1,
  isSome (nested_field_rec t ids) ->
  JMeq (gupd_reptype (nf_replace2 t ids t0) ids t1 (gupd_reptype t ids t0 v v0) v1) (gupd_reptype t ids t1 v v1).
Proof.
  intros.
  revert t0 t1 v0 v1.
  induction ids; intros.
  + simpl. reflexivity.
  + simpl; generalize (proj_reptype t ids v).
    solve_nested_field_rec_cons_isSome H; rewrite H2; intros.
    - (* Tstruct *)
      generalize (proj_reptype_gupd_reptype t ids v (Tstruct i (all_fields_replace_one2 f a t0) a0)
        (gupd_reptype_structlist f a t0 r v0) H0).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite nested_field_type2_nf_replace2; eauto; intros.
      rewrite H3.
      rewrite (IHids H0).
      generalize (gupd_reptype_structlist_gupd_reptype_structlist f a t0 t1 r v0 v1).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite all_fields_replace_one2_all_fields_replace_one2.
      intros.
      rewrite H4.
      reflexivity.
    - (* Tunion *)
      generalize (proj_reptype_gupd_reptype t ids v (Tunion i (all_fields_replace_one2 f a t0) a0)
        (gupd_reptype_unionlist f a t0 v0) H0).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite nested_field_type2_nf_replace2; eauto; intros.
      rewrite (IHids H0).
      generalize (gupd_reptype_unionlist_gupd_reptype_unionlist f a t0 t1 v1).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite all_fields_replace_one2_all_fields_replace_one2.
      intros.
      rewrite H4.
      reflexivity.
Qed.

Lemma proj_except_reptype_proj_except_reptype_cons_Tstruct: forall t id id0 ids i f a t0 v,
  nested_field_type2 t (id0 :: ids) = Tstruct i f a ->
  field_type id f = Errors.OK t0 ->
  JMeq (proj_except_reptype (nf_sub2 t id (id0 :: ids)) id0 ids (proj_except_reptype t id (id0 :: ids) v)) (proj_except_reptype t id0 ids v).
Proof.
  intros.
  apply JMeq_sym.
  unfold proj_except_reptype at 3.
  unfold nf_sub2.
  generalize (proj_reptype t (id0 :: ids) v).
  rewrite H; intros.

  forget (proj_except_reptype_structlist f id r) as v0; clear r.
  clear t0 H0.
  revert v0.
  change (reptype_structlist (all_fields_except_one2 f id)) with (reptype (Tstruct i (all_fields_except_one2 f id) a)).
  forget (Tstruct i (all_fields_except_one2 f id) a) as t0.
  intros.

  assert (isSome (nested_field_rec t (id0 :: ids)))
    by (eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto).
  simpl.
  generalize (proj_reptype t ids v).
  solve_nested_field_rec_cons_isSome H0; rewrite H3; intros.
  + (* Tstruct *)
    generalize (proj_reptype_gupd_reptype t ids v 
      (Tstruct i0 (all_fields_replace_one2 f0 id0 t0) a0) 
      (gupd_reptype_structlist f0 id0 t0 r v0) H1).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by apply H1.
    intros.
    rewrite gupd_reptype_gupd_reptype by auto.
    simpl in r0, H4.
    rewrite H4.
    generalize (proj_except_reptype_structlist_gupd_reptype_structlist f0 id0 t0 r v0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    intros.
    rewrite H5.
    reflexivity.
  + (* Tunion *)
    generalize (proj_reptype_gupd_reptype t ids v 
      (Tunion i0 (all_fields_replace_one2 f0 id0 t0) a0) 
      (gupd_reptype_unionlist f0 id0 t0 v0) H1).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by apply H1.
    intros.
    rewrite gupd_reptype_gupd_reptype by auto.
    generalize (proj_except_reptype_unionlist_gupd_reptype_unionlist f0 id0 t0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    intros.
    rewrite H5.
    reflexivity.
Qed.

Lemma proj_except_reptype_proj_except_reptype_cons_Tstruct_eq_rect_r: forall t id id0 ids i f a t0 v,
  nested_field_type2 t (id0 :: ids) = Tstruct i f a ->
  field_type id f = Errors.OK t0 ->
  proj_except_reptype t id0 ids v = eq_rect_r reptype 
   (proj_except_reptype _ id0 ids (proj_except_reptype t id (id0 :: ids) v))
   (eq_sym (nf_sub2_nf_sub2_cons _ _ _ _)).
Proof.
  intros.
  apply eq_sym, JMeq_eq.
  rewrite (eq_rect_r_JMeq type _ _ reptype (proj_except_reptype (nf_sub2 t id (id0 :: ids)) id0 ids
           (proj_except_reptype t id (id0 :: ids) v)) (eq_sym (nf_sub2_nf_sub2_cons t id id0 ids))).
  eapply proj_except_reptype_proj_except_reptype_cons_Tstruct; eauto.
Qed.

Lemma proj_reptype_proj_except_reptype_Tstruct: forall t id ids i f a t0 v v1,
  nested_field_type2 t ids = Tstruct i f a ->
  field_type id f = Errors.OK t0 ->
  JMeq (proj_reptype t ids v) v1 ->
  JMeq (proj_reptype _ ids (proj_except_reptype t id ids v)) (proj_except_reptype_structlist f id v1).
Proof.
  intros.
  unfold proj_except_reptype, nf_sub2.
  revert H1; generalize (proj_reptype t ids v). rewrite H.
  intros. rewrite H1.
  apply proj_reptype_gupd_reptype.
  eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto.
Qed.

Lemma proj_reptype_proj_except_reptype_Tstruct_eq_rect_r: forall t id ids i f a t0 v v1
  (H: nested_field_type2 t ids = Tstruct i f a),
  field_type id f = Errors.OK t0 ->
  JMeq (proj_reptype t ids v) v1 ->
  proj_except_reptype_structlist f id v1 = eq_rect_r reptype (proj_reptype _ ids (proj_except_reptype t id ids v)) (eq_sym (nested_field_type2_nf_sub2_Tstruct _ _ _ _ _ _ H)).
Proof.
  intros.
  apply eq_sym, JMeq_eq.
  pose proof (eq_rect_r_JMeq type _ _ reptype (proj_reptype (nf_sub2 t id ids) ids (proj_except_reptype t id ids v)) (eq_sym (nested_field_type2_nf_sub2_Tstruct t id ids i f a H))).
  simpl reptype in H2. rewrite H2.
  eapply proj_reptype_proj_except_reptype_Tstruct; eauto.
Qed.

Lemma proj_reptype_upd_reptype: forall t ids v v0,
  isSome (nested_field_rec t ids) ->
  proj_reptype t ids (upd_reptype t ids v v0) = v0.
Proof.
  intros.
  apply JMeq_eq.
  unfold upd_reptype.
  generalize (eq_rect_r_JMeq type _ _ reptype (gupd_reptype t ids (nested_field_type2 t ids) v v0)
    (nf_replace2_identical t ids)).
  match goal with
  | |- JMeq ?M _ -> _ => generalize M
  end.
  pattern t at 1 2 7 8.
  rewrite (nf_replace2_identical t ids).
  intros.
  rewrite H0.
  apply proj_reptype_gupd_reptype, H.
Qed.

Lemma proj_except_reptype_gupd_reptype_cons: forall t id ids t0 v v0,
  isSome (nested_field_rec t (id :: ids)) ->
  JMeq (proj_except_reptype _ id ids (gupd_reptype t (id :: ids) t0 v v0))
    (proj_except_reptype t id ids v).
Proof.
  intros.
  unfold nf_sub2, proj_except_reptype.
  simpl gupd_reptype.
  simpl nf_replace2.
  generalize (proj_reptype t ids v).
  solve_nested_field_rec_cons_isSome H; rewrite H2; intros.
  + (* Tstruct *)
    generalize (proj_reptype_gupd_reptype t ids v (Tstruct i (all_fields_replace_one2 f id t0) a)
      (gupd_reptype_structlist f id t0 r v0) H0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by eauto.
    intros.
    rewrite H3.
    rewrite gupd_reptype_gupd_reptype by auto.
    generalize (proj_except_reptype_structlist_gupd_reptype_structlist f id _ r v0). 
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    intros.
    rewrite H4.
    reflexivity.
  + (* Tunion *)
    generalize (proj_reptype_gupd_reptype t ids v (Tunion i (all_fields_replace_one2 f id t0) a)
      (gupd_reptype_unionlist f id t0 v0) H0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by eauto.
    intros.
    rewrite gupd_reptype_gupd_reptype by auto.
    unfold proj_except_reptype_unionlist.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    reflexivity.
Qed.
    
Lemma proj_except_reptype_upd_reptype: forall t id ids v v0,
  isSome (nested_field_rec t (id :: ids)) ->
  proj_except_reptype t id ids (upd_reptype t (id :: ids) v v0) = proj_except_reptype t id ids v.
Proof.
  intros.
  apply JMeq_eq.
  unfold upd_reptype.
  generalize (eq_rect_r_JMeq type _ _ reptype (gupd_reptype t (id :: ids) (nested_field_type2 t (id :: ids)) v v0) (nf_replace2_identical t (id :: ids))).
  match goal with
  | |- JMeq ?M _ -> _ => generalize M
  end.
  pattern t at 1 2 7 8.
  rewrite (nf_replace2_identical t (id :: ids)).
  intros.
  rewrite H0.
  apply proj_except_reptype_gupd_reptype_cons, H.
Qed.

Definition nested_field_sub_aux: forall sh t id ids p, 
  nested_legal_fieldlist t = true ->
  legal_alignas_type t = true ->
  isSome (nested_field_rec t (id :: ids)) ->
  sigT (fun P => forall v, data_at sh t v p = field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * P (proj_except_reptype t id ids v)).
Proof.
  intros.
  revert id H1.
  induction ids; intros.
  + destruct t; try inversion H1.
    - (* Tstruct *)
Opaque proj_reptype.
      simpl.
Transparent proj_reptype.
      unfold nested_field_type in H1; simpl in H1.
      solve_field_offset_type id f; [clear H1 | inversion H1].
      destruct (nested_sfieldlist_at_sub sh (Tstruct i f a) id nil i f a p t H0 H eq_refl H3) as [P0 H1].
      exists P0; intros.
      rewrite data_at_field_at.
      pose proof H1 v v.
      simpl in H2. erewrite H2; eauto.
    - (* Tunion *)
Opaque proj_reptype.
      simpl.
Transparent proj_reptype.
      unfold nested_field_type in H1; simpl in H1.
      solve_field_offset_type id f; [clear H1 | inversion H1].
      admit.
  + remember (a:: ids) as ids0.
    solve_nested_field_rec_cons_isSome H1; subst ids0.
    - (* Tstruct *)
      destruct (IHids a H2) as [PH IH]; clear IHids.
      destruct (field_type id f) eqn:?; [|inversion H3].
      destruct (nested_sfieldlist_at_sub sh t id (a :: ids) i f a0 p t0 H0 H H4 Heqr) as [P0 H5].

      eexists; intros; rewrite IH.

      pose (eq_rect_r reptype (proj_reptype t (a :: ids) v) (eq_sym H4)) as v1.
      assert (JMeq (proj_reptype t (a :: ids) v) v1).
        subst v1.
        eapply JMeq_sym, eq_rect_r_JMeq.
      simpl reptype in v1, H6.
      erewrite H5; eauto.
      erewrite proj_except_reptype_proj_except_reptype_cons_Tstruct_eq_rect_r; eauto.
      erewrite proj_reptype_proj_except_reptype_Tstruct_eq_rect_r with (H := H4); eauto.
      rewrite sepcon_assoc.
      f_equal.
      instantiate (1 := fun v' => P0 (eq_rect_r reptype
        (proj_reptype (nf_sub2 t id (a :: ids)) (a :: ids) v')
        (eq_sym (nested_field_type2_nf_sub2_Tstruct t id (a :: ids) i f a0 H4))) *
        PH (eq_rect_r reptype
        (proj_except_reptype (nf_sub2 t id (a :: ids)) a ids v')
        (eq_sym (nf_sub2_nf_sub2_cons t id a ids)))).
Opaque eq_rect_r proj_reptype proj_except_reptype.
      simpl.
      reflexivity.
Transparent eq_rect_r proj_reptype proj_except_reptype.
    - (* Tunion *)
      admit.
Defined.

Definition field_except_at (sh: Share.t) t id ids (v: reptype (nf_sub2 t id ids)) (p: val) : mpred.
  destruct (nested_legal_fieldlist t) eqn:H; [| exact emp].
  destruct (legal_alignas_type t) eqn:H0; [| exact emp].
  destruct (isSome_dec (nested_field_rec t (id :: ids))); [| exact emp].
  destruct (nested_field_sub_aux sh t id ids p H H0 i).
  exact (x v).
Defined.

Opaque proj_reptype upd_reptype proj_except_reptype.

Lemma field_except_at_lemma: forall sh t id ids v,
  nested_legal_fieldlist t = true ->
  legal_alignas_type t = true ->
  isSome (nested_field_rec t (id :: ids)) ->
  data_at sh t v = field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) * 
    field_except_at sh t id ids (proj_except_reptype t id ids v).
Proof.
  intros.
  extensionality p.
  unfold field_except_at.
  generalize (@eq_refl bool (nested_legal_fieldlist t)).
  generalize (@eq_refl bool (legal_alignas_type t)).
  pattern (nested_legal_fieldlist t) at 2 3; rewrite H.
  pattern (legal_alignas_type t) at 2 3; rewrite H0.
  destruct (isSome_dec (nested_field_rec t (id :: ids))).
  + intros. simpl. destruct (nested_field_sub_aux sh t id ids p e0 e i).
    apply e1.
  + pose proof (n H1).
    inversion H2.
Qed.

Module NF.

Lemma NF_aux: forall e t ids, type_is_by_value (uncompomize e (nested_field_type2 t ids)) ->
  isSome (nested_field_rec t ids).
Proof.
  intros.
  unfold nested_field_type2 in H.
  destruct (nested_field_rec t ids) as [[? tt]|];
  [simpl; auto | inversion H].
Qed.

Lemma proj_reptype_upd_reptype: forall e t ids v v0,
  type_is_by_value (uncompomize e (nested_field_type2 t ids)) ->
  proj_reptype t ids (upd_reptype t ids v v0) = v0.
Proof.
  intros.
  apply proj_reptype_upd_reptype; auto.
  eapply NF_aux, H.
Qed.

Lemma proj_except_reptype_upd_reptype: forall e t id ids v v0,
  type_is_by_value (uncompomize e (nested_field_type2 t (id :: ids))) ->
  proj_except_reptype t id ids (upd_reptype t (id :: ids) v v0) = proj_except_reptype t id ids v.
  intros.
  apply proj_except_reptype_upd_reptype; auto.
  eapply NF_aux, H.
Qed.

Lemma field_except_at_lemma: forall e sh t id ids v,
  nested_legal_fieldlist t = true ->
  legal_alignas_type t = true ->
  type_is_by_value (uncompomize e (nested_field_type2 t (id :: ids))) ->
  data_at sh t v = field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) * 
    field_except_at sh t id ids (proj_except_reptype t id ids v).
Proof.
  intros.
  apply field_except_at_lemma; auto.
  eapply NF_aux, H1.
Qed.

Lemma lifted_field_except_at_lemma: forall e sh t id ids v,
  nested_legal_fieldlist t = true ->
  legal_alignas_type t = true ->
  type_is_by_value (uncompomize e (nested_field_type2 t (id :: ids))) ->
  `(data_at sh t) v = `(field_at sh t (id :: ids)) (`(proj_reptype t (id :: ids)) v) * 
    `(field_except_at sh t id ids) (`(proj_except_reptype t id ids) v).
Proof.
  intros.
  extensionality p rho.
  unfold_lift.
  simpl.
  erewrite field_except_at_lemma by eauto.
  reflexivity.
Qed.

End NF.

Lemma semax_nested_efield_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (typeof e1)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 ids tts)) t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq (proj_reptype (typeof e1) ids v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local `(tc_val (typeof (nested_efield e1 ids tts)) v) &&
        (`(data_at sh (typeof e1) v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 ids tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  destruct ids.
  + simpl (nested_efield e1 nil tts) in *.
    eapply semax_data_load_37'; eauto.
  + assert (type_is_by_value (uncompomize e (nested_field_type2 (typeof e1) (i :: ids)))).
      eapply is_neutral_cast_by_value; eauto.
      erewrite typeof_nested_efield; eauto.
    erewrite NF.field_except_at_lemma with (id := i) (ids := ids) in H5; eauto.
    eapply semax_max_path_field_load_37'; eauto.
    eapply derives_trans; [exact H5 |].
    normalize.
    apply andp_derives; [apply derives_refl |].
    unfold_lift. simpl; intros. rewrite sepcon_assoc.
    apply sepcon_derives; [apply derives_refl |].
    apply prop_right, I.
Qed.

Lemma semax_nested_efield_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (typeof e1)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 ids tts)) ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq (proj_reptype (typeof e1) ids v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 ids tts)) t v))) &&
        (`(data_at sh (typeof e1) v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 ids tts) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 ids tts)) t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  destruct ids.
  + simpl (nested_efield e1 nil tts) in *.
    eapply semax_data_cast_load_37'; eauto.
  + assert (type_is_by_value (uncompomize e (nested_field_type2 (typeof e1) (i :: ids)))).
      erewrite typeof_nested_efield; eauto.
    erewrite NF.field_except_at_lemma with (id := i) (ids := ids) in H5; eauto.
    eapply semax_max_path_field_cast_load_37'; eauto.
    eapply derives_trans; [exact H5 |].
    normalize.
    apply andp_derives; [apply derives_refl |].
    unfold_lift. simpl; intros. rewrite sepcon_assoc.
    apply sepcon_derives; [apply derives_refl |].
    apply prop_right, I.
Qed.

Lemma semax_nested_efield_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t : type) (ids: list ident) (tts: list type) (v: environ -> reptype (typeof e1)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof (nested_efield e1 ids tts) = t ->
      type_is_by_value t ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(data_at sh (typeof e1)) v (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 ids tts)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 ids tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(data_at sh (typeof e1))
                      (`(upd_reptype (typeof e1) ids) v
                        (`(valinject (nested_field_type2 (typeof e1) ids)) (eval_expr (Ecast e2 t))))
                          (eval_lvalue e1)
                            )))))).
Proof.
  intros.
  destruct ids.
  + simpl (nested_efield e1 nil tts) in *.
    change (`(upd_reptype (typeof e1) nil) v
                          (`(valinject (nested_field_type2 (typeof e1) nil))
                             (eval_expr (Ecast e2 t)))) with
                          (`(valinject (typeof e1))
                             (eval_expr (Ecast e2 t))).
    rewrite H0.
    eapply semax_data_store_nth; eauto.
    eapply derives_trans; [exact H5 |].
    unfold_lift; simpl; intros.
    rewrite <- H0.
    apply data_at_data_at_, H2.
  + apply semax_pre_simple with (P' := |> PROPx P (LOCALx (tc_lvalue Delta (nested_efield e1 (i :: ids) tts) :: tc_expr Delta (Ecast e2 t) :: Q) (SEPx R))).
    Focus 1. {
      hoist_later_left.
      apply later_derives.
      eapply derives_trans with (Q0 := PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))); [normalize|].
      rewrite (add_andp _ _ H7).
      entailer!.
    } Unfocus.
    assert (type_is_by_value (uncompomize e (nested_field_type2 (typeof e1) (i :: ids)))).
      rewrite <- H0 in H1. erewrite <- (typeof_nested_efield) in H1 by eauto. auto.
    erewrite NF.lifted_field_except_at_lemma with (id := i) (ids := ids) in H5; eauto.
    match goal with
    | |- appcontext [replace_nth n R ?M] =>
         replace M with ((`(field_at sh (typeof e1) (i :: ids)) 
            (`(valinject (nested_field_type2 (typeof e1) (i :: ids))) (eval_expr (Ecast e2 t))) *
           `(field_except_at sh (typeof e1) i ids) (`(proj_except_reptype (typeof e1) i ids) v))
                     (eval_lvalue e1))
    end.
    Focus 2. {
      unfold_lift.
      extensionality rho.
      simpl.
      erewrite NF.field_except_at_lemma with (id := i) (ids := ids); eauto.
      erewrite NF.proj_reptype_upd_reptype; eauto.
      erewrite NF.proj_except_reptype_upd_reptype; eauto.
    } Unfocus.
    rewrite (replace_nth_nth_error _ _ _ H4).
    eapply semax_pre_simple.
    {
      hoist_later_left.
      apply later_derives.
      rewrite insert_local.
      apply replace_nth_SEP'.
      eapply derives_trans; [| exact H5].
      simpl; intro; normalize.
    }
    rewrite replace_nth_replace_nth.
    clear H5.
    erewrite !SEP_replace_nth_isolate; eauto.
    replace (SEPx ((`(field_at sh (typeof e1) (i :: ids)) (`(proj_reptype (typeof e1) (i :: ids)) v) *
                  `(field_except_at sh (typeof e1) i ids) (`(proj_except_reptype (typeof e1) i ids) v))
                    (eval_lvalue e1) :: replace_nth n R emp)) with 
           (SEPx ((`(field_at sh (typeof e1) (i :: ids))
              (`(proj_reptype (typeof e1) (i :: ids)) v) (eval_lvalue e1) ::
            `(field_except_at sh (typeof e1) i ids)
              (`(proj_except_reptype (typeof e1) i ids) v) (eval_lvalue e1) :: replace_nth n R emp))).
    Focus 2. {
      extensionality.
      unfold SEPx.
      simpl.
      rewrite <- sepcon_assoc.
      reflexivity.
    } Unfocus.
    replace (SEPx ((`(field_at sh (typeof e1) (i :: ids))
                     (`(valinject (nested_field_type2 (typeof e1) (i :: ids)))
                        (eval_expr (Ecast e2 t))) *
                   `(field_except_at sh (typeof e1) i ids)
                       (`(proj_except_reptype (typeof e1) i ids) v))
                    (eval_lvalue e1) :: replace_nth n R emp)) with 
           (SEPx (replace_nth 0%nat ((`(field_at sh (typeof e1) (i :: ids))
              (`(proj_reptype (typeof e1) (i :: ids)) v) (eval_lvalue e1) ::
            `(field_except_at sh (typeof e1) i ids)
              (`(proj_except_reptype (typeof e1) i ids) v) (eval_lvalue e1) :: replace_nth n R emp))
             (`(field_at sh (typeof e1) (i :: ids))
              (`(valinject (nested_field_type2 (typeof e1) (i :: ids))) (eval_expr (Ecast e2 t)))
              (eval_lvalue e1)))).
    Focus 2. {
      simpl (replace_nth 0%nat).
      extensionality.
      unfold SEPx.
      simpl.
      rewrite <- sepcon_assoc.
      reflexivity.
    } Unfocus.
    eapply semax_post'; 
      [ |eapply semax_max_path_field_store_nth with (n0 := 0%nat) 
       (Rn0 := `(field_at sh (typeof e1) (i :: ids)) (`(proj_reptype (typeof e1) (i :: ids)) v)
       (eval_lvalue e1)); eauto].
    - simpl; intros; normalize.
    - simpl; intros; normalize.
      apply field_at_field_at_; auto.
    - simpl; intros; normalize.
Qed.

Lemma nested_efield_app: forall t ids0 ids1 tts0 tts1,
  length ids1 = length tts1 ->
  nested_efield (nested_efield t ids0 tts0) ids1 tts1 = 
    nested_efield t (ids1 ++ ids0) (tts1 ++ tts0).
Proof.
  intros.
  revert tts1 H.
  induction ids1; intros; destruct tts1; try solve [inversion H].
  + reflexivity.
  + inversion H.
    simpl.
    rewrite (IHids1 tts1 H1).
    reflexivity.
Qed.

Lemma legal_nested_efield_app: forall e t ids0 ids1 tts0 tts1,
  length ids1 = length tts1 ->
  legal_nested_efield e t (ids1 ++ ids0) (tts1 ++ tts0) = true ->
  legal_nested_efield e t ids0 tts0 = true.
Proof.
  intros.
  revert tts1 H H0.
  induction ids1; intros; destruct tts1; try solve [inversion H].
  + auto.
  + inversion H.
    simpl in H0.
    match type of H0 with
    |  (match ?M with | Some _ => _ | _ => _ end = true) => destruct M as [[? ?]|]; [|inversion H0]
    end.
    apply andb_true_iff in H0.
    destruct H0.
    eapply IHids1; eauto.
Qed.

Lemma nested_field_rec_uncompomize_cons: forall e t id ids,
  nested_field_rec (uncompomize e t) (id :: ids) = nested_field_rec t (id :: ids).
Proof.
  intros.
  destruct t; auto.
  revert id;
  induction ids; intros.
  reflexivity.
  simpl in *.
  rewrite (IHids a0).
  reflexivity.
Qed.

Lemma nested_field_type2_uncompomize: forall e t ids,
  uncompomize e (nested_field_type2 (uncompomize e t) ids) = uncompomize e (nested_field_type2 t ids).
Proof.
  intros.
  destruct t; try reflexivity.
  destruct ids; try reflexivity.
  unfold nested_field_type2.
  rewrite nested_field_rec_uncompomize_cons.
  reflexivity.
Qed.

Lemma uncompomize_uncompomize: forall e t, uncompomize e (uncompomize e t) = uncompomize e t.
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma legal_nested_efield_app': forall e t ids0 ids1 tts0 tts1,
  length ids1 = length tts1 ->
  legal_nested_efield e t (ids1 ++ ids0) (tts1 ++ tts0) = true ->
  legal_nested_efield e (uncompomize e (nested_field_type2 t ids0)) ids1 tts1 = true.
Proof.
Opaque uncompomize nested_field_rec.
  intros.
  revert tts1 H H0.
  induction ids1; intros; destruct tts1; try solve [inversion H].
  + simpl in *. rewrite uncompomize_uncompomize. apply eqb_type_refl.
  + simpl in *.
    rewrite nested_field_rec_uncompomize_cons.
    valid_nested_field_rec t (a :: ids1 ++ ids0) H0.
    rewrite andb_true_iff in H0.
    assert (isSome (nested_field_rec t ((a :: ids1) ++ ids0))) by (simpl; rewrite H1; simpl; auto).
    pose proof nested_field_rec_app_isSome _ _ _ H2.
    pose proof nested_field_rec_app_isSome' _ _ _ H2.
    valid_nested_field_rec (nested_field_type2 t ids0) (a :: ids1) H4.
    destruct H0.
    rewrite IHids1 by auto.
    unfold nested_field_type2 in H5.
    valid_nested_field_rec t ids0 H3.
    pose proof nested_field_rec_app _ _ _ _ _ _ _ H7 H5.
    simpl in H8.
    rewrite H1 in H8.
    inversion H8.
    subst.
    rewrite H6.
    reflexivity.
Transparent uncompomize nested_field_rec. 
Qed.

Lemma nested_legal_fieldlist_uncompomize: forall e t,
  nested_legal_fieldlist (uncompomize e t) = nested_legal_fieldlist t.
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma legal_alignas_type_uncompomize: forall e t,
  legal_alignas_type (uncompomize e t) = legal_alignas_type t.
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma nested_field_rec_Tcomp_ptr_cons: forall i a id ids,
  nested_field_rec (Tcomp_ptr i a) (id :: ids) = None.
Proof.
  intros.
  revert id.
  induction ids; intros.
  - reflexivity.
  - simpl in *; rewrite (IHids a0); reflexivity.
Qed.

Lemma nested_field_rec_Tpointer_cons: forall t a id ids,
  nested_field_rec (Tpointer t a) (id :: ids) = None.
Proof.
  intros.
  revert id.
  induction ids; intros.
  - reflexivity.
  - simpl in *; rewrite (IHids a0); reflexivity.
Qed.

Lemma proj_reptype_uncompomize: forall e t ids v v',
  JMeq v v' -> JMeq (proj_reptype t ids v) (proj_reptype (uncompomize e t) ids v').
Proof.
Transparent proj_reptype.
  intros.
  destruct t; revert v' H; simpl; intros; rewrite H; try reflexivity.
  destruct ids.
  + reflexivity.
  + match goal with
    | |- @JMeq (reptype ?A) ?x (reptype ?B) ?y => cut (A = Tvoid /\ B = Tvoid); 
        [intros; forget x as X; forget y as Y|]
    end.
    revert X Y.
    destruct H0.
    rewrite H0, H1.
    intros.
    destruct X, Y.
    reflexivity.
    unfold nested_field_type2.
    rewrite nested_field_rec_Tpointer_cons, nested_field_rec_Tcomp_ptr_cons.
    split; reflexivity.
Opaque proj_reptype.
Qed.

Lemma upd_reptype_uncompomize: forall e t ids v v' v0 v0',
  JMeq v v' -> JMeq v0 v0' -> JMeq (upd_reptype t ids v v0) (upd_reptype (uncompomize e t) ids v' v0').
Proof.
Transparent upd_reptype.
Opaque reptype.
  intros.
  destruct t; revert v' v0' H H0; simpl; intros; rewrite H; try rewrite H0; try reflexivity.
  erewrite eq_rect_JMeq with (F := (fun y : type => reptype y)).
  erewrite eq_rect_JMeq with (F := (fun y : type => reptype y)).
Transparent reptype.
  destruct ids.
  + simpl. exact H0.
  + destruct ids.
    - simpl. reflexivity.
    - pose proof nested_field_rec_Tpointer_cons (type_id_env.look_up_ident_default i e) a i1 ids.
      pose proof nested_field_rec_Tcomp_ptr_cons i a i1 ids.
Opaque nested_field_type2.
      forget (i1 :: ids) as ids'.
      clear ids.
      simpl.
      generalize ((proj_reptype (Tcomp_ptr i a) ids' v')).
      generalize ((proj_reptype (Tpointer (type_id_env.look_up_ident_default i e) a)
                ids' v')).
Transparent nested_field_type2.
      unfold nested_field_type2.
      rewrite H1.
      rewrite H2.
      intros.
      reflexivity.
Qed.

Lemma semax_nested_efield_field_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids0 ids1: list ident) (tts0 tts1: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids0)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) t = true ->
      legal_alignas_type (typeof e1) = true ->
      length ids1 = length tts1 ->
      legal_nested_efield e (typeof e1) (ids1 ++ ids0) (tts1 ++ tts0) = true ->
      JMeq (proj_reptype (nested_field_type2 (typeof e1) ids0) ids1 v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) &&
        local `(tc_val (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) v) &&
        (`(field_at sh (typeof e1) ids0 v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0)))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  remember v' as v''.
  assert (JMeq v' v'') by (subst; reflexivity).
  clear Heqv''.
  revert v' H7.
  pattern (reptype (nested_field_type2 (typeof e1) ids0)) at 1 2.
  rewrite <- (uncompomize_reptype e (nested_field_type2 (typeof e1) ids0)).
  intros.
  rewrite (proj_reptype_uncompomize _ _ ids1 _ _ (JMeq_sym H7)) in H5.

  assert (legal_nested_efield e (typeof e1) ids0 tts0 = true)
    by (eapply legal_nested_efield_app; eauto).

  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
           local (tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) &&
           local `(tc_val (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) v) &&
           (`(data_at sh (uncompomize e (nested_field_type2 (typeof e1) ids0)) v')
           (eval_lvalue (nested_efield e1 ids0 tts0)) * TT)).
  {
    eapply derives_trans; [exact H6 | apply andp_derives; [apply derives_refl |]].
    simpl; intro rho.
    unfold_lift.
    rewrite field_at_data_at by auto.
    rewrite !at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
    erewrite <- uncompomize_data_at by eauto.
    erewrite eval_lvalue_nested_efield by eauto.
    entailer!.
  }
  clear H6.
  clear H7 v''.

  revert v' H5 H9.
  erewrite typeof_nested_efield by eauto.
  intros.
  rewrite <- nested_efield_app by auto.

  eapply semax_nested_efield_load_37'.
  + erewrite <- typeof_nested_efield by eauto.
    rewrite nested_legal_fieldlist_uncompomize.
    apply nested_field_type2_nest_pred; auto.
  + exact H0.
  + rewrite nested_efield_app by auto.
    exact H1.
  + erewrite <- typeof_nested_efield by eauto.
    rewrite legal_alignas_type_uncompomize.
    apply nested_field_type2_nest_pred; auto.
  + erewrite <- typeof_nested_efield by eauto.
    erewrite legal_nested_efield_app'; eauto.
  + exact H5.
  + rewrite nested_efield_app by auto.
    exact H9.
Qed.

Lemma semax_nested_efield_field_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids0 ids1: list ident) (tts0 tts1: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids0)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) ->
      legal_alignas_type (typeof e1) = true ->
      length ids1 = length tts1 ->
      legal_nested_efield e (typeof e1) (ids1 ++ ids0) (tts1 ++ tts0) = true ->
      JMeq (proj_reptype (nested_field_type2 (typeof e1) ids0) ids1 v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) t v))) &&
        (`(field_at sh (typeof e1) ids0 v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0)) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  remember v' as v''.
  assert (JMeq v' v'') by (subst; reflexivity).
  clear Heqv''.
  revert v' H7.
  pattern (reptype (nested_field_type2 (typeof e1) ids0)) at 1 2.
  rewrite <- (uncompomize_reptype e (nested_field_type2 (typeof e1) ids0)).
  intros.
  rewrite (proj_reptype_uncompomize _ _ ids1 _ _ (JMeq_sym H7)) in H5.

  assert (legal_nested_efield e (typeof e1) ids0 tts0 = true)
    by (eapply legal_nested_efield_app; eauto).

  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
           local (tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) &&
           local `(tc_val t (eval_cast
                    (typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0)))
                    t v)) &&
           (`(data_at sh (uncompomize e (nested_field_type2 (typeof e1) ids0)) v')
           (eval_lvalue (nested_efield e1 ids0 tts0)) * TT)).
  {
    eapply derives_trans; [exact H6 | apply andp_derives; [apply derives_refl |]].
    simpl; intro rho.
    unfold_lift.
    rewrite field_at_data_at by auto.
    rewrite !at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
    erewrite <- uncompomize_data_at by eauto.
    erewrite eval_lvalue_nested_efield by eauto.
    entailer!.
  }
  clear H6.
  clear H7 v''.

  revert v' H5 H9.
  erewrite typeof_nested_efield by eauto.
  intros.
  rewrite <- nested_efield_app by auto.

  eapply semax_nested_efield_cast_load_37'.
  + erewrite <- typeof_nested_efield by eauto.
    rewrite nested_legal_fieldlist_uncompomize.
    apply nested_field_type2_nest_pred; auto.
  + exact H0.
  + rewrite nested_efield_app by auto.
    exact H1.
  + erewrite <- typeof_nested_efield by eauto.
    rewrite legal_alignas_type_uncompomize.
    apply nested_field_type2_nest_pred; auto.
  + erewrite <- typeof_nested_efield by eauto.
    erewrite legal_nested_efield_app'; eauto.
  + exact H5.
  + rewrite nested_efield_app by auto.
    exact H9.
Qed.

Lemma semax_nested_efield_field_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t : type) (ids0 ids1: list ident) (tts0 tts1: list type)
      (v: environ -> reptype (nested_field_type2 (typeof e1) ids0)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0)) = t ->
      type_is_by_value t ->
      legal_alignas_type (typeof e1) = true ->
      length ids1 = length tts1 ->
      legal_nested_efield e (typeof e1) (ids1 ++ ids0) (tts1 ++ tts0) = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh (typeof e1) ids0) v (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0)) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh (typeof e1) ids0)
                      (`(upd_reptype (nested_field_type2 (typeof e1) ids0) ids1) v
                        (`(valinject (nested_field_type2 (nested_field_type2 (typeof e1) ids0) ids1)) (eval_expr (Ecast e2 t))))
                          (eval_lvalue e1)
                            )))))).
Proof.
  intros.
  remember v as v''.
  assert (JMeq v v'') by (subst; reflexivity).
  clear Heqv''.
  revert v H9.
  pattern (reptype (nested_field_type2 (typeof e1) ids0)) at 1 2.
  rewrite <- (uncompomize_reptype e (nested_field_type2 (typeof e1) ids0)).
  intros.

  rewrite <- nested_efield_app by auto.
  assert (legal_nested_efield e (typeof e1) ids0 tts0 = true)
    by (eapply legal_nested_efield_app; eauto).

  match goal with
  | |- appcontext [replace_nth ?n _ ?Rnn] =>
    replace Rnn with
      (local (`(size_compatible (typeof e1)) (eval_lvalue e1)) && 
       local (`(align_compatible (typeof e1)) (eval_lvalue e1)) &&
       local `(isSome (nested_field_rec (typeof e1) ids0)) &&
       `(data_at sh (uncompomize e (nested_field_type2 (typeof e1) ids0))) 
            (`(upd_reptype (uncompomize e (nested_field_type2 (typeof e1) ids0))
                            ids1) v
                          (`(valinject
                               (nested_field_type2
                                  (uncompomize e (nested_field_type2 (typeof e1) ids0)) ids1))
                             (eval_expr (Ecast e2 t)))) (eval_lvalue (nested_efield e1 ids0 tts0)))
  end.
  Focus 2. {
    extensionality rho.
    unfold local, lift1. unfold_lift.
Opaque upd_reptype.
    simpl.
Transparent upd_reptype.
    rewrite field_at_data_at by auto.
    rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
    erewrite eval_lvalue_nested_efield by eauto.
    rewrite <- data_at_offset_zero.
    erewrite <- uncompomize_data_at. reflexivity.
    apply upd_reptype_uncompomize.
    + clear -H9. revert v H9.
      rewrite uncompomize_reptype. intros.
      rewrite H9. reflexivity.
    + erewrite <- uncompomize_valinject with (e := e) by eauto.
      rewrite <- nested_field_type2_uncompomize.
      erewrite uncompomize_valinject with (e := e) by eauto.
      reflexivity.
  } Unfocus.
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |-- 
          local (`(size_compatible (typeof e1)) (eval_lvalue e1)) && 
          local (`(align_compatible (typeof e1)) (eval_lvalue e1)) &&
          local `(isSome (nested_field_rec (typeof e1) ids0)) &&
          `(data_at sh (uncompomize e (nested_field_type2 (typeof e1) ids0))) v
          (eval_lvalue (nested_efield e1 ids0 tts0))).
  {
    eapply derives_trans; [exact H6 |].
    simpl; intros rho.
    unfold local, lift1. unfold_lift.
    simpl.
    rewrite field_at_data_at by auto.
    rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
    erewrite eval_lvalue_nested_efield by eauto.
    rewrite <- data_at_offset_zero.
    apply derives_refl'.
    erewrite <- uncompomize_data_at.
    + reflexivity.
    + clear -H9. revert v H9.
      rewrite uncompomize_reptype. intros.
      rewrite H9. reflexivity.
  }
  clear H6.
  clear v'' H9.

  eapply semax_pre_simple.
  {
    hoist_later_left.
    rewrite insert_local.
    apply later_derives.
    instantiate (1 := PROPx P
     (LOCALx
        (tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))
         :: tc_expr Delta (Ecast e2 t) :: Q)
        (SEPx
           (replace_nth n R
              (local (`(size_compatible (typeof e1)) (eval_lvalue e1)) &&
               local (`(align_compatible (typeof e1)) (eval_lvalue e1)) &&
               local `(isSome (nested_field_rec (typeof e1) ids0)) &&
               `(data_at sh
                   (uncompomize e (nested_field_type2 (typeof e1) ids0))) v
                 (eval_lvalue (nested_efield e1 ids0 tts0))))))).
    rewrite (add_andp _ _ H8).
    rewrite (replace_nth_nth_error _ _ _ H5) at 1.
(*    remember (tc_environ Delta :: Q). *)
    rewrite <- insert_local with
      (Q1 := tc_lvalue Delta (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))).
    rewrite <- insert_local with
      (Q1 := tc_expr Delta (Ecast e2 t)).
    rewrite andp_comm.
    eapply derives_trans; [apply andp_derives; [apply derives_refl | ] |].
    eapply replace_nth_SEP', H11.
    rewrite andp_assoc.
    rewrite !insert_local.
    simpl; intros; normalize.
  }  
  repeat rewrite !andp_assoc.
  repeat
    match goal with
    | |- appcontext [replace_nth _ ?RR (local ?Q1 && ?Q2)] =>
       erewrite (extract_local_in_SEP n Q1) with (R := replace_nth n RR (local Q1 && Q2))
         by (erewrite nth_error_replace_nth by eauto; reflexivity);
       rewrite replace_nth_replace_nth
    end.
  revert v H11.
  erewrite typeof_nested_efield by eauto.
  intros.
  match goal with
  | |- semax _ ?p _  _ =>
      let Pre := fresh "Pre" in
      remember p as Pre;
      erewrite <- replace_nth_replace_nth;
      subst Pre
  end.
  eapply semax_post'.
  {
    instantiate (1 := (`(data_at sh (typeof (nested_efield e1 ids0 tts0))) v
       (eval_lvalue (nested_efield e1 ids0 tts0)))).
    instantiate (1 := 
      PROPx P
         (LOCALx
            (`(isSome (nested_field_rec (typeof e1) ids0))
             :: `(align_compatible (typeof e1)) (eval_lvalue e1)
                :: `(size_compatible (typeof e1)) (eval_lvalue e1) :: tc_lvalue Delta
                         (nested_efield e1 (ids1 ++ ids0) (tts1 ++ tts0))
                       :: tc_expr Delta (Ecast e2 t) :: Q)
            (SEPx
               (replace_nth n (replace_nth n R (`(data_at sh (typeof (nested_efield e1 ids0 tts0))) v
       (eval_lvalue (nested_efield e1 ids0 tts0))))
                  (`(data_at sh (typeof (nested_efield e1 ids0 tts0)))
                     (`(upd_reptype (typeof (nested_efield e1 ids0 tts0))
                          ids1) v
                        (`(valinject
                             (nested_field_type2
                                (typeof (nested_efield e1 ids0 tts0)) ids1))
                           (eval_expr (Ecast e2 t))))
                     (eval_lvalue (nested_efield e1 ids0 tts0))))))).
    simpl; intros; normalize.
  }
  eapply semax_nested_efield_store_nth.
  + erewrite <- typeof_nested_efield by eauto.
    rewrite nested_legal_fieldlist_uncompomize.
    apply nested_field_type2_nest_pred; auto.
  + rewrite nested_efield_app by auto.
    exact H0.
  + exact H1.
  + erewrite <- typeof_nested_efield by eauto.
    rewrite legal_alignas_type_uncompomize.
    apply nested_field_type2_nest_pred; auto.
  + erewrite <- typeof_nested_efield by eauto.
    erewrite legal_nested_efield_app'; eauto.
  + erewrite nth_error_replace_nth by eauto.
    reflexivity.
  + simpl; intros; normalize.
  + exact H7.
  + rewrite nested_efield_app by auto.
    simpl; intros; normalize.
Qed.

(*

(* Here is potentially another way of defining proj_reptype. This definition *)
(* is less efficient but easier to prove properties. In principle,           *)
(* gupd_reptype and other functions can all be defined in this style.        *)
Fixpoint proj_reptype_structlist t id ids f (v: nested_reptype_structlist t ids f) : reptype (nested_field_type2 t (id :: ids)) :=
  match f as f'
    return nested_reptype_structlist t ids f' -> reptype (nested_field_type2 t (id :: ids)) with
  | Fnil => fun _ => default_val _
  | Fcons i0 t0 flds0 => 
    if is_Fnil flds0 as b
      return ((if b 
               then reptype (nested_field_type2 t (i0 :: ids)) 
               else reptype (nested_field_type2 t (i0 :: ids)) * 
                    nested_reptype_structlist t ids flds0) ->
              reptype (nested_field_type2 t (id :: ids)))
    then fun v =>
      match ident_eq id i0 with
      | left H => eq_rect_r (fun i => reptype (nested_field_type2 t (i :: ids))) v H
      | right H => default_val _
      end
    else fun v => 
      match ident_eq id i0 with
      | left H => eq_rect_r (fun i => reptype (nested_field_type2 t (i :: ids))) (fst v) H
      | right _ => proj_reptype_structlist t id ids flds0 (snd v)
      end
  end v.

Lemma proj_reptype_aux: forall t ids, 
  nested_legal_fieldlist t = true ->
  match nested_field_type2 t ids with
  | Tstruct i f a => nested_reptype_structlist t ids f
  | _ => reptype (nested_field_type2 t ids)
  end = reptype (nested_field_type2 t ids).
Proof.
  intros.
  destruct (nested_field_type2 t ids) eqn:HH; auto.
  rewrite <- HH.
  eapply eq_sym, nested_reptype_structlist_lemma2; eauto.
Defined.

Fixpoint proj_reptype_rec (t: type) (ids: list ident) (H: nested_legal_fieldlist t = true) (v: reptype t) : reptype (nested_field_type2 t ids) :=
  match ids as ids' return reptype (nested_field_type2 t ids')
  with
  | nil => eq_rect_r reptype v (nested_field_type2_nil t)
  | id :: ids0 =>
    match nested_field_type2 t ids0 as T
      return match T with
             | Tstruct i f a => nested_reptype_structlist t ids0 f
             | _ => reptype (nested_field_type2 t ids0)
             end -> reptype (nested_field_type2 t (id :: ids0))
    with
    | Tstruct i f a => fun v => proj_reptype_structlist t id ids0 f v
    | _ => fun _ => default_val _
    end (eq_rect_r (fun T => T) (proj_reptype_rec t ids0 H v) (proj_reptype_aux t ids0 H))
  end.

Definition proj_reptype t ids v :=
 (if nested_legal_fieldlist t as b
    return nested_legal_fieldlist t = b -> reptype (nested_field_type2 t ids)
  then fun H => proj_reptype_rec t ids H v
  else fun _ => default_val _) eq_refl.

Arguments proj_reptype / t ids v.

Lemma proj_reptype_nil: forall t v, nested_legal_fieldlist t = true -> JMeq (proj_reptype t nil v) v.
Proof.
  intros.
  simpl.
  generalize (@eq_refl bool (nested_legal_fieldlist t)).
  pattern (nested_legal_fieldlist t) at 2 3.
  rewrite H; intros.
  rewrite eq_rect_r_JMeq.
  reflexivity.
Qed.

Lemma proj_reptype_cons_Tstruct: forall t id ids i f a v v0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tstruct i f a ->
  JMeq (proj_reptype t ids v) v0 ->
  JMeq (proj_reptype t (id :: ids) v) (proj_reptype_structlist t id ids f v0).
Proof.
  intros.
  simpl in *.
  revert H1.
  generalize (@eq_refl bool (nested_legal_fieldlist t)) as HH.
  pattern (nested_legal_fieldlist t) at 2 3 7.
  rewrite H.
  intros.
  match goal with
  | |- JMeq (_ ?T) _ =>
    assert (JMeq T (proj_reptype_rec t ids HH v)) as H2
      by apply eq_rect_r_JMeq with (F := fun T => T);
    revert H2;
    generalize T
  end.
  pattern (nested_field_type2 t ids) at 1 11 22.
  rewrite H0.
  intros.
  rewrite H1 in H2.
  rewrite H2.
  reflexivity.
Qed.

*)
















































