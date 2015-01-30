Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.type_id_env.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.loadstore_data_at.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(********************************************

Max length ids field_at load store:
  semax_max_path_field_load_37'.
  semax_max_path_field_cast_load_37'.
  semax_max_path_field_store_nth.

********************************************)

Lemma semax_max_path_field_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 t_root gfs)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      legal_nested_efield e t_root e1 gfs tts lr = true ->
      repinject _ v' = v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
        local (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        (`(field_at sh t_root gfs v') (eval_LR e1 lr) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (temp id v :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_ucdata_load_37'.
  + exact H.
  + exact H0.
  + exact H2.
  + eapply derives_trans; [exact H3|].
    instantiate (1:=sh).
    instantiate (1:=e).
    rewrite (andp_comm _ (_ * _)).
    rewrite !andp_assoc.
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ _ lr H1)).
    simpl; intro rho; normalize.
    rewrite field_at_isptr.
    rewrite field_at_data_at.
    normalize.
    pose proof (eval_lvalue_nested_efield Delta e t_root e1 efs gfs tts lr H1 rho).
    pose proof (tc_lvalue_nested_efield Delta e t_root e1 efs gfs tts lr H1 rho).
    normalize in H9.
    normalize in H10.
    rewrite (add_andp _ _ H9).
    rewrite (add_andp _ _ H10).
    normalize.
    rewrite H11.
    apply andp_left1.
    apply derives_refl.
Qed.

Lemma semax_max_path_field_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 t_root gfs)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      legal_nested_efield e t_root e1 gfs tts lr = true ->
      repinject _ v' = v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_LR Delta e1 lr) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v))) &&
        local (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        (`(field_at sh t_root gfs v') (eval_LR e1 lr) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (temp id (eval_cast (typeof (nested_efield e1 efs tts)) t v) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_ucdata_cast_load_37'; try eassumption.
  + eapply derives_trans; [exact H3|].
    instantiate (1:=sh).
    instantiate (1:=e).
    rewrite (andp_comm _ (_ * _)).
    rewrite !andp_assoc.
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ _ lr H1)).
    simpl; intro rho; normalize.
    rewrite field_at_isptr.
    rewrite field_at_data_at.
    normalize.
    pose proof (eval_lvalue_nested_efield Delta e t_root e1 efs gfs tts lr H1 rho).
    pose proof (tc_lvalue_nested_efield Delta e t_root e1 efs gfs tts lr H1 rho).
    normalize in H9.
    normalize in H10.
    rewrite (add_andp _ _ H9).
    rewrite (add_andp _ _ H10).
    normalize.
    rewrite H11.
    apply andp_left1.
    apply derives_refl.
Qed.

Lemma lower_andp_lifted_val:
  forall (P Q: val->mpred) v, 
  (`(P && Q) v) = (`P v && `Q v).
Proof. reflexivity. Qed.

Lemma remove_one_LOCAL_left: forall P Q0 Q R S,
  PROPx P (LOCALx Q R) |-- S -> PROPx P (LOCALx (Q0 :: Q) R) |-- S.
Proof.
  intros.
  simpl in H |- *.
  intro rho; specialize (H rho).
  unfold PROPx, LOCALx, SEPx in *.
  normalize.
  normalize in H.
Qed.

Lemma semax_max_path_field_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type) lr,
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t = true ->
      legal_nested_efield e t_root e1 gfs tts lr = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at_ sh t_root gfs) (eval_LR e1 lr) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_LR Delta e1 lr) && 
        local (tc_efield Delta efs) &&
        efield_denote efs gfs &&
                local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh t_root gfs)
                      (`(valinject (nested_field_type2 t_root gfs)) (eval_expr (Ecast e2 t))) 
                        (eval_LR e1 lr)
                          )))))).
Proof.
  intros.
  eapply semax_pre_simple; [| eapply semax_post'].
  Focus 1. {
    hoist_later_left.
    apply later_derives.
    rewrite insert_local.
    instantiate (1 := 
      PROPx P
      (LOCALx (tc_expr Delta (Ecast e2 t) ::
               tc_lvalue Delta (nested_efield e1 efs tts) ::
               `eq (eval_lvalue (nested_efield e1 efs tts))
                 (`(field_address t_root gfs) (eval_LR e1 lr)) ::
               `((uncompomize e (nested_field_type2 t_root gfs) =
                 typeof (nested_efield e1 efs tts))) ::
               Q) (SEPx R))).
    assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`isptr (eval_LR e1 lr))).
    Focus 1. {
      erewrite SEP_nth_isolate with (R := R) by exact H2.
      apply derives_trans with ((PROPx P (LOCALx (tc_environ Delta :: Q) SEP (Rn)) * TT)).
      - simpl; intros; normalize; cancel.
      - rewrite (add_andp _ _ H3).
        simpl; intro rho.
        unfold_lift.
        rewrite field_at__isptr.
        normalize.
    } Unfocus.
    assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
      local (tc_expr Delta (Ecast e2 t)) &&
      (local (tc_lvalue Delta (nested_efield e1 efs tts)) &&
       local (`eq (eval_lvalue (nested_efield e1 efs tts)) 
         (`(field_address t_root gfs) (eval_LR e1 lr))) &&
       !! (uncompomize e (nested_field_type2 t_root gfs) = typeof (nested_efield e1 efs tts)))).
    Focus 1. {
      apply andp_right.
      + eapply derives_trans; [exact H5 |].
        apply andp_left2.
        apply derives_refl.
      + rewrite (add_andp _ _ H5).
        rewrite (add_andp _ _ H6).
        simpl; intro rho; normalize.
        normalize.
        pose proof (eval_lvalue_nested_efield Delta e t_root e1 efs gfs tts lr H1 rho).
        pose proof (tc_lvalue_nested_efield Delta e t_root e1 efs gfs tts lr H1 rho).
        pose proof (typeof_nested_efield _ Delta t_root _ efs _ _ lr H1 rho).
        normalize in H14.
        normalize in H15.
        normalize in H16.
        rewrite (add_andp _ _ H14).
        rewrite (add_andp _ _ H15).
        rewrite (add_andp _ _ H16).
        normalize.
    } Unfocus.
    rewrite (add_andp _ _ H7).
    simpl; intros; normalize.
  } Unfocus.
  Focus 2. {
    eapply semax_ucdata_store_nth.
    + exact H.
    + exact H0.
    + exact H2.
    + repeat rewrite LOCAL_2_hd, <- insert_local.
      rewrite (add_andp _ _ H3).
      simpl; intro rho; normalize.
      rewrite field_at__data_at_.
      rewrite H8.
      apply andp_left2.
      normalize.
    + exact H4.
    + instantiate (1 := e).
      rewrite <- H.
      simpl; intro rho; normalize.
  } Unfocus.
  match goal with
  | |- ?L |-- ?R =>
      remember L as LL eqn:HL;
      remember R as RR eqn:HR;
      erewrite SEP_replace_nth_isolate in HL by exact H2;
      erewrite SEP_replace_nth_isolate in HR by exact H2;
      subst LL RR
  end.
  simpl; intro rho; normalize.
  apply sepcon_derives; [| apply derives_refl].
  rewrite field_at_data_at.
  rewrite H9.
  normalize.
Qed.
