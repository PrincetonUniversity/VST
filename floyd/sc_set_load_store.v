Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

Lemma semax_SC_set:
  forall {Espec: OracleKind},
    forall Delta id P Q R (e2: expr) t v,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e2) t = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq v) (eval_expr e2)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_expr Delta e2) &&
        local `(tc_val (typeof e2) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id e2)
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
    local (tc_expr Delta e2) && local (tc_temp_id id (typeof e2) Delta e2)).
  {
    apply andp_right.
    + eapply derives_trans; [exact H2 | apply andp_left1; apply derives_refl].
    + unfold tc_temp_id.
      unfold typecheck_temp_id.
      unfold typeof_temp in H.
      destruct ((temp_types Delta) ! id) as [[? ?]|]; [| inversion H].
      inversion H; clear H; subst.
      assert (is_neutral_cast (implicit_deref (typeof e2)) t = true).
        destruct (typeof e2), t; try inversion H0; simpl implicit_deref; try reflexivity.
      rewrite H.
      simpl denote_tc_assert; simpl; intros.
      unfold local, lift1.
      apply prop_right.
      apply neutral_isCastResultType, H.
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
      (t : type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 (typeof e1) gfs0)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t = true ->
      legal_alignas_type (typeof e1) = true ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e (typeof e1) (gfs1 ++ gfs0) (tts1 ++ tts0) = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        efield_denote Delta (efs1 ++ efs0) (gfs1 ++ gfs0) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh (typeof e1) gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 (typeof e1) gfs0) gfs1 v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) &&
        local `(tc_val (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_nested_efield_field_load_37'; eauto.
  apply andp_right; [apply andp_right; [exact H11 | exact H8] |].
  rewrite (add_andp _ _ H7).
  eapply derives_trans; [apply andp_derives; [| apply derives_refl] |].
  eapply nth_error_SEP_sepcon_TT; eauto.
  entailer!.
Qed.

Lemma semax_SC_field_cast_load:
  forall {Espec: OracleKind},
    forall Delta sh e n id P Q R Rn (e1: expr)
      (t : type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 (typeof e1) gfs0)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) ->
      legal_alignas_type (typeof e1) = true ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e (typeof e1) (gfs1 ++ gfs0) (tts1 ++ tts0) = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        efield_denote Delta (efs1 ++ efs0) (gfs1 ++ gfs0) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh (typeof e1) gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 (typeof e1) gfs0) gfs1 v') v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta e1) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t v))) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_nested_efield_field_cast_load_37'; eauto.
  apply andp_right; [apply andp_right; [exact H11 | exact H8] |].
  rewrite (add_andp _ _ H7).
  eapply derives_trans; [apply andp_derives; [| apply derives_refl] |].
  eapply nth_error_SEP_sepcon_TT; eauto.
  entailer!.
Qed.

Lemma semax_SC_field_store:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t : type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v0: val) (v: reptype (nested_field_type2 (typeof e1) gfs0)),
      nested_legal_fieldlist (typeof e1) = true ->
      typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) = t ->
      type_is_by_value t ->
      legal_alignas_type (typeof e1) = true ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e (typeof e1) (gfs1 ++ gfs0) (tts1 ++ tts0) = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        efield_denote Delta (efs1 ++ efs0) (gfs1 ++ gfs0) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh (typeof e1) gfs0 v p) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh (typeof e1) gfs0
                      (upd_reptype (nested_field_type2 (typeof e1) gfs0) gfs1 v (valinject _ v0)) p)))
                            )))).
Proof.
  intros.
  eapply semax_pre_simple.
  {
    hoist_later_left.
    rewrite insert_local.
    rewrite (add_andp _ _ H7).
    rewrite andp_comm.
    rewrite (add_andp _ _ H8).
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
    eapply derives_trans; [apply andp_derives; [apply derives_refl | exact H10] |].
    entailer!.
  + apply andp_right.
    - eapply derives_trans; [| exact H12].
      entailer!.
    - eapply derives_trans; [| exact H9].
      entailer!.
Qed.



