Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.type_id_env.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.loadstore_mapsto.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(***************************************

Load/store lemmas about data_at:
  semax_data_load_37'.
  semax_data_cast_load_37'.
  semax_data_store_nth.

***************************************)

Lemma is_neutral_cast_by_value: forall t t', 
  is_neutral_cast t t' = true ->
  type_is_by_value t = true.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl; auto.
Qed.

Lemma is_neutral_reptype: forall t t', is_neutral_cast t t' = true -> reptype t = val.
Proof.
  intros.
  eapply by_value_reptype, is_neutral_cast_by_value, H.
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
  data_at sh t v p = !! field_compatible t nil p && mapsto sh t p v'.
Proof.
  intros.
  apply by_value_data_at; try assumption.
  eapply is_neutral_cast_by_value, H.
Qed.

Lemma is_neutral_lifted_data_at: forall sh t t' v (v':val) (p: environ -> val),
  is_neutral_cast t t' = true ->
  JMeq v v' ->
  `(data_at sh t v) p = local (`(field_compatible t nil) p) && `(mapsto sh t) p `(v').
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  erewrite is_neutral_data_at; [| exact H| exact H0].
  reflexivity.
Qed.

Lemma is_neutral_data_at_: forall sh t t' p, 
  is_neutral_cast t t' = true ->
  data_at_ sh t p = !! field_compatible t nil p && mapsto_ sh t p.
Proof.
  intros.
  apply by_value_data_at_; try assumption.
  eapply is_neutral_cast_by_value, H.
Qed.

Lemma is_neutral_lifted_data_at_: forall sh t t' p,
  is_neutral_cast t t' = true ->
  `(data_at_ sh t) p = local (`(field_compatible t nil) p) && `(mapsto_ sh t) p.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at_; try assumption.
  exact H.
Qed.

Lemma semax_data_load_37':
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1 : expr) 
    (t : type) (v : val) (v' : reptype (typeof e1)),
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e1) t = true ->
    JMeq v' v ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
      local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v) &&
      (`(data_at sh (typeof e1) v') (eval_lvalue e1) * TT) ->
    semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
      (Sset id e1)
        (normal_ret_assert
          (EX  old : val,
            PROPx P
              (LOCALx (temp id v :: map (subst id `old) Q)
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
    erewrite is_neutral_data_at; [normalize| exact Htype | exact H1].
Qed.

Lemma semax_data_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
    (t: type) (v: val) (v' : reptype (typeof e1)),
    typeof_temp Delta id = Some t ->
    type_is_by_value (typeof e1) = true ->
    JMeq v' v ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
      local (tc_lvalue Delta e1) &&
      local (`(tc_val t (eval_cast (typeof e1) t v))) &&
      (`(data_at sh (typeof e1) v') (eval_lvalue e1) * TT) ->
    semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id (Ecast e1 t))
        (normal_ret_assert (EX old:val, 
          PROPx P 
            (LOCALx (temp id (eval_cast (typeof e1) t v) :: map (subst id (`old)) Q)
              (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_cast_load_37'.
  exact H.
  eapply derives_trans; [exact H2 |].
  apply andp_derives; [apply derives_refl |].
  unfold liftx, lift; simpl; intros.
  erewrite by_value_data_at; [normalize | exact H0 | exact H1].
Qed.

Lemma semax_data_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh n P Q R Rn (e1 e2 : expr)
      (t : type),
      typeof e1 = t ->
      type_is_by_value t = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (Rn :: nil))) |--
        `(data_at_ sh t) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(data_at sh t) (`(valinject t) (eval_expr (Ecast e2 t))) (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  erewrite lifted_by_value_data_at; [|exact H0].
  erewrite lifted_by_value_data_at_ in H2; [|exact H0].
  
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (Rn :: nil))) |-- 
    local (`(field_compatible t nil) (eval_lvalue e1)) && Rn).
  {
    apply andp_right; [| apply remove_PROP_LOCAL_left'; apply derives_refl].
    eapply derives_trans; [exact H2|apply andp_left1; apply derives_refl].
  }
  eapply semax_pre_simple.
  {
    hoist_later_left.
    apply later_derives.
    rewrite insert_local.
    instantiate (1:= PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (replace_nth n R (local (`(field_compatible t nil) (eval_lvalue e1)) && Rn))))).
    rewrite (replace_nth_nth_error R _ _ H1) at 1.

    apply replace_nth_SEP', H5.
  }
    
  rewrite (replace_nth_SEP_andp_local P _ R n Rn) by (exact H1).
  rewrite <- replace_nth_nth_error by exact H1.

  rewrite (replace_nth_SEP_andp_local P _ R n Rn) by (exact H1).

  (*rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H5 by (exact H1).*)

  eapply semax_post0; [| eapply semax_store_nth].
  + apply normal_ret_assert_derives'.
    simpl; intro; normalize.
  + exact H.
  + exact H1.
  + erewrite (replace_nth_nth_error (_ :: nil) 0%nat) by reflexivity.
    erewrite <- replace_nth_SEP_andp_local by reflexivity.
    erewrite (replace_nth_nth_error (_ :: nil) 0%nat) by reflexivity.
    erewrite <- replace_nth_SEP_andp_local by reflexivity.
    unfold replace_nth.  
    eapply derives_trans; [eapply derives_trans; [| exact H2]|].
    - remember eval_lvalue.
      go_lower; normalize.
    - apply andp_left2; apply derives_refl.
  + exact H3.
  + eapply derives_trans; [|exact H4].
    go_lower; normalize.
Qed.

(***************************************

Load/store lemmas about data_at with uncompomize function on type:
  semax_ucdata_load_37'.
  semax_ucdata_cast_load_37'.
  semax_ucdata_store_nth.

***************************************)

Lemma is_neutral_reptype': forall e t t' t'',
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  reptype t = val.
Proof.
  intros.
  destruct t, t', t''; try inversion H; try inversion H0; try reflexivity.
Qed.

Lemma is_neutral_data_at': forall sh e t t' t'' v v' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v v' ->
  data_at sh t v p =
  (!! field_compatible (uncompomize e t) nil p) && mapsto sh t' p v'.
Proof.
  intros.
  subst t'.
  apply uncompomize_by_value_data_at; try assumption.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma repinject_JMeq: forall e t v, type_is_by_value (uncompomize e t) = true -> JMeq v (repinject t v).
Proof.
  intros.
  destruct t; try inversion H; try reflexivity.
Qed.

Lemma is_neutral_data_at'': forall sh e t t' t'' v v' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  repinject _ v = v' ->
  data_at sh t v p =
  (!! field_compatible (uncompomize e t) nil p) && mapsto sh t' p v'.
Proof.
  intros.
  eapply is_neutral_data_at'; eauto.
  subst.
  eapply repinject_JMeq.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma is_neutral_lifted_data_at': forall sh e t t' t'' v (v': val) p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v v' ->
  `(data_at sh t v) p =
  local (`(field_compatible (uncompomize e t) nil) p) && `(mapsto sh t') p `v'.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at'; try assumption.
  exact H0.
Qed.

Lemma is_neutral_data_at_': forall sh e t t' t'' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  data_at_ sh t p =
  (!! field_compatible (uncompomize e t) nil p) && mapsto_ sh t' p.
Proof.
  intros.
  subst t'.
  apply uncompomize_by_value_data_at_; try assumption.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma is_neutral_lifted_data_at_': forall sh e t t' t'' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  `(data_at_ sh t) p =
  local (`(field_compatible (uncompomize e t) nil) p) && `(mapsto_ sh t') p.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at_'; try assumption.
  exact H0.
Qed.

Lemma semax_ucdata_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1 : expr) 
      (t1 t2 : type) (v : val) (v' : reptype t1),
      typeof_temp Delta id = Some t2 ->
      is_neutral_cast (typeof e1) t2 = true ->
      repinject _ v' = v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
      |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v) &&
        (!! (uncompomize e t1 = typeof e1)) &&
        (`(data_at sh t1 v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e1)
          (normal_ret_assert
            (EX  old : val,
              PROPx P
                (LOCALx (temp id v :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_load_37'.
  + exact H.
  + exact H0.
  + instantiate (1:=sh).
    apply (derives_trans _ _ _ H2).
    normalize.
    apply andp_derives; [normalize |].
    forget (eval_lvalue e1) as p.
    go_lower.
    erewrite is_neutral_data_at''; [normalize| | |]; try eassumption.
Qed.

Lemma semax_ucdata_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t1 t2: type) (v: val) (v' : reptype t2),
      typeof_temp Delta id = Some t1 ->
      type_is_by_value (typeof e1) = true ->
      repinject _ v' = v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta e1) &&
        local (`(tc_val t1 (eval_cast (typeof e1) t1 v))) &&
        (!! (uncompomize e t2 = typeof e1)) &&
        (`(data_at sh t2 v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast e1 t1))
          (normal_ret_assert
            (EX old:val, 
              PROPx P 
                (LOCALx (temp id (eval_cast (typeof e1) t1 v) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_cast_load_37'.
  + exact H.
  + eapply derives_trans; [exact H2 |].
    normalize.
    apply andp_derives; [apply derives_refl |].
    unfold liftx, lift; simpl; intros.
    erewrite uncompomize_by_value_data_at with (e := e); [rewrite H3; normalize | rewrite H3; exact H0 |].
    subst.
    eapply repinject_JMeq.
    rewrite <- H3 in H0.
    exact H0.
Qed.

Lemma semax_ucdata_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t1 t2: type),
      typeof e1 = t1 ->
      type_is_by_value t1 = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |-- `(data_at_ sh t2) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) &&
        (!! (uncompomize e t2 = t1))->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(data_at sh t2) (`(valinject t2) (eval_expr (Ecast e2 t1))) (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  eapply semax_pre_simple; [| eapply semax_post'].
  Focus 1. {
    hoist_later_left.
    apply later_derives.
    rewrite insert_local.
    rewrite (add_andp _ _ H4).
    instantiate (1 := PROPx ((uncompomize e t2 = t1) :: P)
                      (LOCALx ((`(field_compatible (uncompomize e t2) nil)
                                 (eval_lvalue e1)) ::
                               Q) (SEPx R))).
    assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
      local (`(field_compatible (uncompomize e t2) nil) (eval_lvalue e1))).
    Focus 1. {
      rewrite (add_andp _ _ H4).
      erewrite SEP_nth_isolate with (R := R) by exact H1.
      apply derives_trans with (!!(uncompomize e t2 = t1) &&
        (PROPx P (LOCALx (tc_environ Delta :: Q) SEP (Rn)) * TT)).
      + simpl; intros; normalize; cancel.
      + rewrite (add_andp _ _ H2).
        simpl; intros; normalize.
        erewrite uncompomize_by_value_data_at_ with (e:=e); [| rewrite H5; exact H0].
        normalize.
    } Unfocus.
    rewrite (add_andp _ _ H5).
    simpl; intros; normalize.
  } Unfocus.
  Focus 2. {
    eapply semax_store_nth.
    + exact H.
    + exact H1.
    + rewrite <- move_prop_from_LOCAL.
      rewrite <- insert_local.
      repeat rewrite LOCAL_2_hd, <- insert_local.
      rewrite (add_andp _ _ H2).
      simpl; intros; normalize.
      apply andp_left2.
      erewrite uncompomize_by_value_data_at_ with (e:=e); [| rewrite H5; exact H0].
      rewrite H5.
      apply andp_left2.
      apply derives_refl.
    + exact H3.
    + eapply derives_trans; [eapply derives_trans; [| exact H4] |]; simpl; intros; normalize.
  } Unfocus.
  erewrite SEP_replace_nth_isolate by exact H1.
  remember (replace_nth n R emp) as tmp.
  erewrite SEP_replace_nth_isolate by exact H1.
  subst tmp.
  simpl; intros; normalize.
  erewrite uncompomize_by_value_data_at with (e:=e); [| rewrite H5; exact H0 |].
  instantiate (1 := (force_val1 (sem_cast (typeof e2) (typeof e1)) (eval_expr e2 x))).
  normalize.
  rewrite H5; cancel.
  simpl.
  rewrite <- uncompomize_valinject with (e := e).
  apply valinject_JMeq.
  rewrite H5.
  exact H0.
Qed.
