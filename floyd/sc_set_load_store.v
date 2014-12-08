Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.type_id_env.
Require Import floyd.efield_lemmas.
Require Import floyd.nested_field_re_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(************************************************

The set, load, cast-load and store rules used before Dec 3. 2014

************************************************)

Lemma semax_SC_set:
  forall {Espec: OracleKind},
    forall Delta id P Q R (e2: expr) t v,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (implicit_deref (typeof e2)) t = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq v) (eval_expr e2)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_expr Delta e2) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id e2)
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (temp id v :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
    local (tc_expr Delta e2) && local (tc_temp_id id (typeof e2) Delta e2)).
  {
    apply andp_right.
    + eapply derives_trans; [exact H2 | apply derives_refl].
    + unfold tc_temp_id.
      unfold typecheck_temp_id.
      unfold typeof_temp in H.
      destruct ((temp_types Delta) ! id) as [[? ?]|]; [| inversion H].
      inversion H; clear H; subst.
      rewrite H0.
      simpl denote_tc_assert; simpl; intros.
      unfold local, lift1.
      apply prop_right.
      apply neutral_isCastResultType, H0.
  }
  eapply semax_pre_simple.
  {
    hoist_later_left.
    rewrite insert_local.
    rewrite (add_andp _ _ H3).
    rewrite andp_comm.
    rewrite (add_andp _ _ H1).
    apply later_derives.
    apply andp_derives; [apply derives_refl |].
    apply andp_derives; [| apply derives_refl].
    rewrite <- insert_local.
    apply andp_left2.
    apply derives_refl.
  }
  eapply semax_post'; [| apply semax_set_forward].
  normalize.
  apply (exp_right old).
  rewrite subst_andp, subst_PROP.
  rewrite <- insert_local.
  rewrite subst_local.
  rewrite subst_lift1C.
  entailer!.
Qed.

Lemma semax_SC_field_load:
  forall {Espec: OracleKind},
    forall Delta sh e n id P Q R Rn (e1: expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t = true ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        efield_denote (efs1 ++ efs0) (gfs1 ++ gfs0) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh t_root gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 t_root gfs0) gfs1 v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) v) &&
        local (tc_efield Delta (efs1 ++ efs0)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (temp id v :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_extract_later_prop'; [exact H10 | clear H10; intro H10].
  eapply semax_nested_efield_field_load_37'; eauto.
  apply andp_right; [apply andp_right; [exact H9 | exact H6] |].
  rewrite (add_andp _ _ H5).
  eapply derives_trans; [apply andp_derives; [| apply derives_refl] |].
  eapply nth_error_SEP_sepcon_TT; eauto.
  entailer!.
Qed.

Lemma semax_SC_field_cast_load:
  forall {Espec: OracleKind},
    forall Delta sh e n id P Q R Rn (e1: expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        efield_denote (efs1 ++ efs0) (gfs1 ++ gfs0) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh t_root gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 t_root gfs0) gfs1 v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_LR Delta e1 lr) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t v))) &&
        local (tc_efield Delta (efs1 ++ efs0)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (temp id (eval_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t v) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_extract_later_prop'; [exact H10 | clear H10; intro H10].
  eapply semax_nested_efield_field_cast_load_37'; eauto.
  apply andp_right; [apply andp_right; [exact H9 | exact H6] |].
  rewrite (add_andp _ _ H5).
  eapply derives_trans; [apply andp_derives; [| apply derives_refl] |].
  eapply nth_error_SEP_sepcon_TT; eauto.
  entailer!.
Qed.

Lemma semax_SC_field_store:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v0: val) (v: reptype (nested_field_type2 t_root gfs0)) lr,
      typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) = t ->
      type_is_by_value t ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        efield_denote (efs1 ++ efs0) (gfs1 ++ gfs0) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh t_root gfs0 v p) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_LR Delta e1 lr) && 
        local (tc_expr Delta (Ecast e2 t)) &&
        local (tc_efield Delta (efs1 ++ efs0)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh t_root gfs0
                      (upd_reptype (nested_field_type2 t_root gfs0) gfs1 v (valinject _ v0)) p)))
                            )))).
Proof.
  intros.
  eapply semax_extract_later_prop'; [exact H11 | clear H11; intro H11].
  eapply semax_pre_simple.
  {
    hoist_later_left.
    rewrite insert_local.
    rewrite (add_andp _ _ H5).
    rewrite andp_comm.
    rewrite (add_andp _ _ H6).
    rewrite <- andp_assoc.
    rewrite insert_local.
    rewrite andp_comm.
    rewrite insert_local.
    apply derives_refl.
  }
  eapply semax_post'; [ | eapply semax_nested_efield_field_store_nth with (v1 := `v); eauto].
  + eapply derives_trans; [apply replace_nth_SEP' |].
    Focus 2. {
      rewrite <- !insert_local.
      rewrite <- !andp_assoc.
      apply andp_left2.
      apply derives_refl.
    } Unfocus.
    entailer!.
  + do 3 rewrite <- insert_local.
    rewrite <- !andp_assoc.
    eapply derives_trans; [apply andp_derives; [apply derives_refl | exact H8] |].
    entailer!.
  + rewrite (andp_comm _ (efield_denote (efs1 ++ efs0) (gfs1 ++ gfs0))).
    rewrite andp_assoc.
    apply andp_right.
    - eapply derives_trans; [| exact H7].
      entailer!.
    - rewrite andp_assoc.
      rewrite (andp_comm (local (tc_efield _ _))).
      rewrite <- andp_assoc.
      eapply derives_trans; [| exact H10].
      entailer!.
Qed.

(************************************************

The set, load, cast-load and store rules will be used in the future.

************************************************)

Require Import floyd.local2ptree.

Definition msubst_eval_LR T1 T2 e lr :=
  match lr with
  | LLLL => msubst_eval_lvalue T1 T2 e
  | RRRR => msubst_eval_expr T1 T2 e
  end.

Lemma semax_PTree_set:
  forall {Espec: OracleKind},
    forall Delta id P T1 T2 R (e2: Clight.expr) t v,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (implicit_deref (typeof e2)) t = true ->
      msubst_eval_expr T1 T2 e2 = Some v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        local (tc_expr Delta e2) ->
      semax Delta (|> (assertD P (localD T1 T2) R))
        (Sset id e2)
          (normal_ret_assert
            (assertD P (localD (PTree.set id v T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_local in H2.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_set; eauto.
    instantiate (1 := v).
    rewrite <- insert_local.
    apply andp_left2.
    apply msubst_eval_expr_eq, H1.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.

Lemma semax_PTree_load:
  forall {Espec: OracleKind},
    forall Delta sh e n id P T1 T2 R Rn (e1: expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t = true ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_efield_denote T1 T2 (efs1 ++ efs0) = Some (gfs1 ++ gfs0) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) (Rn :: nil)) |--
        `(field_at sh t_root gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 t_root gfs0) gfs1 v') v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        local (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) v) &&
        local (tc_efield Delta (efs1 ++ efs0)) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax Delta (|>assertD P (localD T1 T2) R) 
        (Sset id (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)))
          (normal_ret_assert
            (assertD P (localD (PTree.set id v T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_local in H7, H9, H10.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_field_load with (n0 := n); eauto.
    + apply map_nth_error, H4.
    + rewrite <- insert_local.
      apply andp_left2.
      destruct lr;
      unfold eval_LR;
      unfold msubst_eval_LR in H5.
      - apply msubst_eval_lvalue_eq, H5.
      - apply msubst_eval_expr_eq, H5.
    + rewrite <- insert_local.
      apply msubst_efield_denote_equiv, H6.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.

Lemma semax_PTree_cast_load:
  forall {Espec: OracleKind},
    forall Delta sh e n id P T1 T2 R Rn (e1: expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_efield_denote T1 T2 (efs1 ++ efs0) = Some (gfs1 ++ gfs0) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) (Rn :: nil)) |--
        `(field_at sh t_root gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 t_root gfs0) gfs1 v') v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        local (tc_LR Delta e1 lr) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t v))) &&
        local (tc_efield Delta (efs1 ++ efs0)) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax Delta (|>assertD P (localD T1 T2) R) 
        (Sset id (Ecast (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) t))
          (normal_ret_assert
            (assertD P (localD (PTree.set id (eval_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t v) T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_local in H7, H9, H10.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_field_cast_load with (n0 := n); eauto.
    + apply map_nth_error, H4.
    + rewrite <- insert_local.
      apply andp_left2.
      destruct lr;
      unfold eval_LR;
      unfold msubst_eval_LR in H5.
      - apply msubst_eval_lvalue_eq, H5.
      - apply msubst_eval_expr_eq, H5.
    + rewrite <- insert_local.
      apply msubst_efield_denote_equiv, H6.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.

Lemma semax_PTree_store:
  forall {Espec: OracleKind},
    forall Delta sh e n P T1 T2 R Rn (e1 e2 : expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v0: val) (v: reptype (nested_field_type2 t_root gfs0)) lr,
      typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) = t ->
      type_is_by_value t ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_eval_expr T1 T2 (Ecast e2 t) = Some v0 ->
      msubst_efield_denote T1 T2 (efs1 ++ efs0) = Some (gfs1 ++ gfs0) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) (Rn :: nil))  |--
        `(field_at sh t_root gfs0 v p) ->
      writable_share sh ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        local (tc_LR Delta e1 lr) && 
        local (tc_expr Delta (Ecast e2 t)) &&
        local (tc_efield Delta (efs1 ++ efs0)) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax Delta (|>assertD P (localD T1 T2) R) 
        (Sassign (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) e2)
          (normal_ret_assert
            (assertD P (localD T1 T2)
                  (replace_nth n R
                    (field_at sh t_root gfs0
                      (upd_reptype (nested_field_type2 t_root gfs0) gfs1 v (valinject _ v0)) p)))).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_local in H8, H10, H11.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_field_store with (n0 := n); eauto.
    + apply map_nth_error, H4.
    + rewrite <- insert_local.
      apply andp_left2.
      destruct lr;
      unfold eval_LR;
      unfold msubst_eval_LR in H5.
      - apply msubst_eval_lvalue_eq, H5.
      - apply msubst_eval_expr_eq, H5.
    + rewrite <- insert_local.
      apply andp_left2.
      apply msubst_eval_expr_eq, H6.
    + rewrite <- insert_local.
      apply msubst_efield_denote_equiv, H7.
  } Unfocus.
  rewrite map_replace_nth.
  auto.
Qed.

Definition proj_val t_root gfs v :=
   repinject (nested_field_type2 t_root gfs) (proj_reptype t_root gfs v).

Definition upd_val t_root gfs v v0 :=
   upd_reptype t_root gfs v (valinject (nested_field_type2 t_root gfs) v0).

Definition nested_efield_rel e efs tts e0 := (nested_efield e efs tts = e0).
