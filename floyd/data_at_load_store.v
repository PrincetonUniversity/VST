Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import floyd.data_at_lemmas.
Require Import Coq.Logic.JMeq.
Opaque alignof.


Local Open Scope logic.

(***************************************

Load/store lemmas about data_at

***************************************)

Lemma is_neutral_reptype: forall t t', is_neutral_cast t t' = true -> reptype t = val.
Proof.
  intros.
  destruct t, t'; try inversion H; try reflexivity.
Qed.

Lemma look_up_empty_ti: forall i, look_up_ident_default i empty_ti = Tvoid.
Proof.
  intros.
  unfold look_up_ident_default.
  rewrite PTree.gempty.
  reflexivity.
Qed.

Lemma is_neutral_data_at: forall sh t t' v v' p,
  is_neutral_cast t t' = true ->
  JMeq v v' ->
  data_at sh t v p = mapsto sh t p v'.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl in v;
  try (unfold data_at; simpl; rewrite H0; reflexivity).
Qed.

Lemma is_neutral_lifted_data_at: forall sh t t' v (v':val) p,
  is_neutral_cast t t' = true ->
  JMeq v v' ->
  `(data_at sh t v) p = `(mapsto sh t) p `(v').
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at; try assumption.
  exact H.
Qed.

Lemma is_neutral_data_at_: forall sh t t' p, is_neutral_cast t t' = true -> data_at_ sh t p = mapsto_ sh t p.
Proof.
  intros.
  unfold data_at_, mapsto_.
  destruct t, t'; try inversion H; simpl default_val; unfold data_at; simpl; reflexivity.
Qed.

Lemma is_neutral_lifted_data_at_: forall sh t t', is_neutral_cast t t' = true -> `(data_at_ sh t) = `(mapsto_ sh t).
Proof.
  intros.
  unfold liftx, lift. simpl.
  repeat extensionality.
  eapply is_neutral_data_at_; try assumption.
  exact H.
Qed.

(* 
Is it possible that (typeof e1)  is a composite point? According to the 
definition of expr and typeof, it is possible. But maybe AST is not possible.
*)

Lemma semax_data_load: 
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (sh : Share.t) (id : ident) 
         (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (e1 : expr) 
         (t2 : type) (v2 : reptype (typeof e1)) (v2' : val),
       typeof_temp Delta id = Some t2 ->
       is_neutral_cast (typeof e1) t2 = true ->
       JMeq v2 v2' ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v2') &&
           (`(data_at sh (typeof e1) v2) (eval_lvalue e1) * TT) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sset id e1)
         (normal_ret_assert
            (EX  old : val,
             PROPx P
               (LOCALx (`eq (eval_id id) `v2' :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  rename H0 into Htype.
  eapply semax_load_37'.
  + exact H.
  + exact Htype.
  + instantiate (1:=sh).
    apply (derives_trans _ _ _ H2).
    apply andp_derives; [normalize |].
    remember (eval_lvalue e1) as p.
    go_lower.
    erewrite is_neutral_data_at; [apply derives_refl | exact Htype | exact H1].
Qed.

Lemma semax_store_nth':
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1 : type),
       typeof e1 = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(mapsto_ sh t1) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign e1 e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(mapsto sh t1) (eval_lvalue e1)
                           (eval_expr (Ecast e2 t1)) )))))).
Proof.
  intros.
  simpl (eval_expr (Ecast e2 t1)).
  unfold force_val1.
  eapply semax_store_nth.
  + exact H.
  + exact H0.
  + exact H1.
  + exact H2.
  + exact H3.
Qed.

Lemma replace_nth_SEP': forall P Q R n Rn Rn' x, Rn x |-- Rn' x -> (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn)))) x |-- (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn')))) x.
Proof.
  intros.
  normalize.
  revert R.
  induction n.
  + destruct R.
    - simpl. cancel.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma replace_nth_SEP: forall P Q R n Rn Rn', Rn |-- Rn' -> PROPx P (LOCALx Q (SEPx (replace_nth n R Rn))) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
  simpl; intros.
  apply replace_nth_SEP'.
  apply H.
Qed.

Lemma semax_data_store_nth:
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1 : type) (v: val) (v' : reptype t1),
       is_neutral_cast t1 t1 = true ->
       JMeq v' v ->
       typeof e1 = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(data_at_ sh t1) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
       PROPx P (LOCALx Q (SEPx (replace_nth n R (`(data_at_ sh t1) (eval_lvalue e1)) ))) |-- local (`(eq) (eval_expr (Ecast e2 t1)) `v) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign e1 e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(data_at sh t1 v') (eval_lvalue e1)
                          )))))).
Proof.
  intros until v'. intro Htype. intros.
  erewrite is_neutral_lifted_data_at; [|exact Htype| exact H].
  erewrite is_neutral_lifted_data_at_ in H2; [|exact Htype].
  erewrite is_neutral_lifted_data_at_ in H5; [|exact Htype].
  eapply semax_post0; [| eapply semax_store_nth'].
  Focus 2. exact H0.
  Focus 2. exact H1.
  Focus 2. exact H2.
  Focus 2. exact H3.
  Focus 2. eapply derives_trans. exact H4. cancel.
  apply normal_ret_assert_derives'.

  eapply derives_trans.
  + instantiate (1:= PROPx P
     (LOCALx (`eq (eval_expr (Ecast e2 t1)) `v :: Q) (SEPx (replace_nth n R (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))).
    assert (
    PROPx P
     (LOCALx Q
        (SEPx
           (replace_nth n R
              (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))
    |--
    PROPx P
     (LOCALx Q
        (SEPx
           (replace_nth n R
              (`(mapsto_ sh t1) (eval_lvalue e1)))))).
      apply replace_nth_SEP. unfold liftx, lift. simpl. intros. apply mapsto_mapsto_.
    unfold PROPx, LOCALx.
    unfold PROPx, LOCALx in H5, H6.
    simpl.
    simpl in H5, H6.
    intros.
    rewrite local_lift2_and.
    simpl.
    repeat try apply andp_right.
    - apply andp_left1; cancel.
    - eapply derives_trans; [exact (H6 x) |exact (H5 x)].
    - apply andp_left2; apply andp_left1; cancel.
    - apply andp_left2; apply andp_left2; cancel.
  + rewrite <- insert_local.
    unfold local, lift1.
Opaque eval_expr.
    simpl; intros.
    remember PROPx.
    normalize.
    subst m.
    unfold liftx, lift in H6; simpl in H6.
Transparent eval_expr.
    subst v.
    apply replace_nth_SEP'.
    unfold liftx, lift. cancel.
Qed.

(********************************************

Max length ids nested_data_at load store

********************************************)

Lemma is_neutral_reptype': forall t t' t'',
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  reptype t = val.
Proof.
  intros.
  destruct t, t', t''; try inversion H; try inversion H0; try reflexivity.
Qed.

Lemma is_neutral_data_at': forall sh t t' t'' v v' p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v' v ->
  data_at sh t v p = mapsto sh t' p v'.
Proof.
  intros.
  destruct t, t', t''; try inversion H; try inversion H0; simpl in v;
  try (unfold data_at; simpl; rewrite H1; reflexivity).
Qed.

Lemma is_neutral_lifted_data_at': forall sh t t' t'' v (v': val) p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v' v ->
  `(data_at sh t v) p = `(mapsto sh t') p `v'.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at'; try assumption.
  exact H0.
Qed.

Lemma is_neutral_data_at_': forall sh t t' t'' p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  data_at_ sh t p = mapsto_ sh t' p.
Proof.
  intros.
  destruct t, t', t''; try inversion H; try inversion H0;
  try (unfold data_at; simpl; reflexivity).
Qed.

Lemma is_neutral_lifted_data_at_': forall sh t t' t'' p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  `(data_at_ sh t) p = `(mapsto_ sh t') p.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at_'; try assumption.
  exact H0.
Qed.

Lemma semax_data_load':
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (sh : Share.t) (id : ident) 
      (P : list Prop) (Q : list (environ -> Prop))
      (R : list (environ -> mpred)) (e1 : expr) 
      (t1 t2 : type) (v2 : reptype t1) (v2' : val),
      uncompomize t1 = typeof e1 ->
      is_neutral_cast (typeof e1) t2 = true ->
      typeof_temp Delta id = Some t2 ->
      JMeq v2' v2 ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
      |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v2') &&
          (`(data_at sh t1 v2) (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sset id e1)
         (normal_ret_assert
            (EX  old : val,
             PROPx P
               (LOCALx (`eq (eval_id id) `v2' :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_load_37'.
  + exact H1.
  + exact H0.
  + instantiate (1:=sh).
    apply (derives_trans _ _ _ H3).
    apply andp_derives; [normalize |].
    forget (eval_lvalue e1) as p.
    go_lower.
    erewrite is_neutral_data_at'; [apply derives_refl| | |]; try assumption.
    exact H0.
Qed.

Fixpoint legal_nested_efield t (ids: list ident) (tts: list type) : bool :=
  match ids, tts with
  | nil, nil => eqb_type (uncompomize t) t
  | nil, _ => false
  | _ , nil => false
  | cons id ids', cons t_ tts' => 
    match nested_field_rec t ids with
    | Some (_, ttt) => (legal_nested_efield t ids' tts' && 
                       eqb_type (uncompomize ttt) t_)%bool
    | None => false
    end
  end.

Lemma legal_nested_efield_cons: forall id ids t tts e,
  legal_nested_efield (typeof e) (id :: ids) (t :: tts) = true ->
  legal_nested_efield (typeof e) ids tts = true.
Proof.
  intros.
  simpl in H.
  valid_nested_field_rec (typeof e) ids H.
  destruct t0; inversion H; clear H2;
  (solve_field_offset_type id f; [|inversion H]);
  apply andb_true_iff in H;
  destruct H;
  rewrite H, H1;
  reflexivity.
Qed.

Fixpoint nested_efield (e: expr) (ids: list ident) (tts: list type) : expr :=
  match ids, tts with
  | nil, _ => e
  | _, nil => e
  | cons id ids', cons t_ tts' => Efield (nested_efield e ids' tts') id t_
  end.

Fixpoint compute_nested_efield e : expr * list ident * list type :=
  match e with
  | Efield e' id t => 
    match compute_nested_efield e' with
    | (e'', ids, tts) => (e'', id :: ids, t :: tts)
    end
  | _ => (e, nil, nil)
  end.

Lemma compute_nested_efield_lemma: forall e,
  match compute_nested_efield e with
  | (e', ids, tts) => nested_efield e' ids tts = e
  end.
Proof.
  intros.
  induction e; try reflexivity.
  simpl.
  destruct (compute_nested_efield e) as ((?, ?), ?).
  simpl.
  rewrite IHe.
  reflexivity.
Qed.

Lemma typeof_nested_efield: forall e ids tts,
  legal_nested_efield (typeof e) ids tts = true ->
  eqb_type (uncompomize (nested_field_type2 (typeof e) ids))
  (typeof (nested_efield e ids tts)) = true .
Proof.
  intros.
  revert tts H.
  induction ids; intros; destruct tts; unfold nested_field_type2 in *; simpl in *.
  + exact H.
  + inversion H.
  + inversion H.
  + valid_nested_field_rec (typeof e) ids H.
    destruct t0; inversion H; clear H2;
    (solve_field_offset_type a f; [|inversion H]);
    apply andb_true_iff in H;
    destruct H as [H HH];
    rewrite H, HH;
    reflexivity.
Qed.

Lemma eval_lvalue_nested_efield: forall e ids tts rho,
  legal_nested_efield (typeof e) ids tts = true ->
  offset_val (Int.repr (nested_field_offset2 (typeof e) ids)) (eval_lvalue e rho) = 
  offset_val Int.zero (eval_lvalue (nested_efield e ids tts) rho).
Proof.
  intros.
  assert (offset_val (Int.repr (nested_field_offset2 (typeof e) ids + 0)) (eval_lvalue e rho) = 
          offset_val (Int.repr 0) (eval_lvalue (nested_efield e ids tts) rho)); [|
    replace (nested_field_offset2 (typeof e) ids + 0) with 
      (nested_field_offset2 (typeof e) ids) in H0 by omega;
    exact H0].
  forget 0 as pos;
  revert pos tts H.
  induction ids; intros; destruct tts; unfold nested_field_offset2 in *; simpl.
  + reflexivity.
  + reflexivity.
  + inversion H.
  + unfold eval_field.
    pose proof legal_nested_efield_cons _ _ _ _ _ H.
    pose proof typeof_nested_efield _ _ _ H0.
    unfold nested_field_type2 in H1.
    valid_nested_field_rec (typeof e) ids H. 
    apply eqb_type_true in H1.
    destruct t0; inversion H; clear H4; simpl uncompomize in H1; rewrite <- H1.
    - solve_field_offset_type a f; [|inversion H].
      unfold liftx, lift; simpl.
      apply andb_true_iff in H.
      destruct H.
      rewrite offset_offset_val, add_repr, Zplus_assoc_reverse.
      apply (IHids _ _ H).
    - solve_field_offset_type a f; [|inversion H].
      unfold liftx, lift; simpl.
      apply andb_true_iff in H.
      destruct H.
      rewrite <- field_mapsto.offset_val_force_ptr.
      rewrite offset_offset_val, int_add_repr_0_l.
      apply (IHids _ _ H).
Qed.

Lemma semax_nested_data_load':
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (sh : Share.t) (id : ident) 
         (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (e1 : expr) 
         (t2 : type) (ids: list ident) (tts: list type)
         (v2 : reptype (nested_field_type2 (typeof e1) ids)) (v2' : val),
       uncompomize (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
       is_neutral_cast (typeof (nested_efield e1 ids tts)) t2 = true ->
       legal_alignas_type (typeof e1) = true ->
       legal_nested_efield (typeof e1) ids tts = true ->
       typeof_temp Delta id = Some t2 ->
       JMeq v2' v2 ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
           local `(tc_val (typeof (nested_efield e1 ids tts)) v2') &&
           (`(nested_data_at sh (typeof e1) ids v2) (eval_lvalue e1) * TT) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sset id (nested_efield e1 ids tts))
         (normal_ret_assert
            (EX  old : val,
             PROPx P
               (LOCALx (`eq (eval_id id) `v2' :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_data_load'.
  + exact H.
  + exact H0.
  + exact H3.
  + exact H4.
  + eapply derives_trans; [exact H5|].
    instantiate (1:=sh).
    apply andp_derives; [normalize |].
    remember eval_lvalue as v.
    go_lower.
    subst v.
    rewrite nested_data_at_data_at; [| exact H1].
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    rewrite (eval_lvalue_nested_efield _ _ tts); [| exact H2].
    rewrite <- data_at_offset_zero.
    apply derives_refl.
Qed.

Lemma semax_data_store_nth':
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1 t2: type) (v: val) (v' : reptype t2),
       uncompomize t2 = t1 ->
       is_neutral_cast t1 t1 = true ->
       JMeq v v' ->
       typeof e1 = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(data_at_ sh t2) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
       PROPx P (LOCALx Q (SEPx (replace_nth n R (`(data_at_ sh t2) (eval_lvalue e1)) ))) |-- local (`(eq) (eval_expr (Ecast e2 t1)) `v) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign e1 e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(data_at sh t2 v') (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  erewrite is_neutral_lifted_data_at'; [| exact H | exact H0 | exact H1].
  erewrite is_neutral_lifted_data_at_' in H4; [| exact H | exact H0].
  erewrite is_neutral_lifted_data_at_' in H7; [| exact H | exact H0].
  eapply semax_post0; [| eapply semax_store_nth'].
  Focus 2. exact H2.
  Focus 2. exact H3.
  Focus 2. exact H4.
  Focus 2. exact H5.
  Focus 2. eapply derives_trans. exact H6. cancel.
  apply normal_ret_assert_derives'.

  eapply derives_trans.
  + instantiate (1:= PROPx P
     (LOCALx (`eq (eval_expr (Ecast e2 t1)) `v :: Q) (SEPx (replace_nth n R (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))).
    assert (
    PROPx P
     (LOCALx Q
        (SEPx
           (replace_nth n R
              (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))
    |--
    PROPx P
     (LOCALx Q
        (SEPx
           (replace_nth n R
              (`(mapsto_ sh t1) (eval_lvalue e1)))))).
      apply replace_nth_SEP. unfold liftx, lift. simpl. intros. apply mapsto_mapsto_.
    unfold PROPx, LOCALx.
    unfold PROPx, LOCALx in H5, H6.
    simpl.
    simpl in H5, H6.
    intros.
    rewrite local_lift2_and.
    simpl.
    repeat try apply andp_right.
    - apply andp_left1; cancel.
    - eapply derives_trans; [exact (H8 x) |exact (H7 x)].
    - apply andp_left2; apply andp_left1; cancel.
    - apply andp_left2; apply andp_left2; cancel.
  + rewrite <- insert_local.
    unfold local, lift1.
Opaque eval_expr.
    simpl; intros.
    remember PROPx.
    normalize.
    subst m.
    unfold liftx, lift in H8; simpl in H8.
Transparent eval_expr.
    subst v.
    apply replace_nth_SEP'.
    unfold liftx, lift. cancel.
Qed.

Lemma semax_nested_data_store':
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1: type) ids tts (v: val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
       uncompomize (nested_field_type2 (typeof e1) ids) = t1 ->
       is_neutral_cast t1 t1 = true ->
       legal_alignas_type (typeof e1) = true ->
       legal_nested_efield (typeof e1) ids tts = true ->
       JMeq v v' ->
       typeof (nested_efield e1 ids tts) = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(nested_data_at_ sh (typeof e1) ids) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta (nested_efield e1 ids tts)) && 
           local (tc_expr Delta (Ecast e2 t1)) ->
       PROPx P (LOCALx Q (SEPx (replace_nth n R (`(nested_data_at_ sh (typeof e1) ids) (eval_lvalue e1))))) |-- local (`(eq) (eval_expr (Ecast e2 t1)) `v) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign (nested_efield e1 ids tts) e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(nested_data_at sh (typeof e1) ids v') (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  assert (forall v, (`(data_at sh (nested_field_type2 (typeof e1) ids) v)
                 (eval_lvalue (nested_efield e1 ids tts))) =
              (`(nested_data_at sh (typeof e1) ids v) (eval_lvalue e1))).
    intros.
    rewrite nested_data_at_data_at; [|exact H1].
    rewrite lifted_at_offset'_eq; [| intros; rewrite <- data_at_offset_zero; reflexivity].
    unfold liftx, lift; simpl. extensionality rho.
    rewrite (eval_lvalue_nested_efield _ _ tts); [|exact H2].
    rewrite <- data_at_offset_zero.
    reflexivity.
  rewrite <- H10.
  eapply semax_data_store_nth'; [exact H| exact H0 | exact H3 | exact H4 | | | auto | exact H8 |].
  - exact H5.
  - unfold data_at_. unfold nested_data_at_ in H4.
    rewrite H10.
    exact H6.
  - unfold data_at_. unfold nested_data_at_ in H9.
    rewrite H10.
    exact H9.
Qed.
