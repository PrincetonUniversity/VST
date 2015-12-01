Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.loadstore_mapsto.

Local Open Scope logic.

Lemma is_neutral_cast_by_value: forall t t', 
  is_neutral_cast t t' = true ->
  type_is_by_value t = true.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl; auto.
Qed.

Ltac solve_andp' :=
  first [ apply derives_refl
        | apply andp_left1; solve_andp'
        | apply andp_left2; solve_andp'].

Ltac solve_andp := repeat apply andp_right; solve_andp'.

(********************************************

Max length gfs field_at load store:
  semax_max_path_field_load_nth_ram.
  semax_max_path_field_cast_load_nth_ram.
  semax_max_path_field_store_nth_ram.

********************************************)

Section LOADSTORE_FIELD_AT.

Context {cs: compspecs}.

Lemma self_ramify_trans: forall {A} `{SepLog A} (g m l: A), g |-- m * TT -> m |-- l * TT -> g |-- l * TT.
Proof.
  intros A ND SL ? ? ? ? ?.
  eapply derives_trans; [exact H |].
  eapply derives_trans; [apply sepcon_derives; [exact H0 | apply derives_refl] |].
  rewrite sepcon_assoc.
  apply sepcon_derives; auto.
Qed.

Lemma semax_max_path_field_load_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e1: expr) Pre
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      readable_share sh ->
      forallb subst_localdef_ok Q = true ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (temp id v :: map (subst_localdef id old) Q)
                  (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H0.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs).
  Focus 1. {
    eapply derives_trans; [exact H10 |].
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H5)).
    normalize.
    apply prop_right; symmetry; auto.
  } Unfocus.
  rewrite H12 in H11.
  assert_PROP (field_compatible t_root gfs p).
  Focus 1. {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H8 |].
    rewrite field_at_compatible'.
    normalize.
  } Unfocus.
  eapply semax_load_nth_ram; try eassumption;
  [ idtac
  | idtac
  | apply andp_right].
  + rewrite (add_andp _ _ H9), (add_andp _ _ H10).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; eassumption].
    rewrite <- insert_local; solve_andp.
  + eapply self_ramify_trans; [exact H8 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; [auto | rewrite <- H12; auto | auto | eauto].
  + rewrite (add_andp _ _ H9), (add_andp _ _ H10).
    eapply derives_trans; [| eapply tc_lvalue_nested_efield; eassumption].
    rewrite <- insert_local; solve_andp.
  + eapply derives_trans; [exact H10 |].
    rewrite H12; solve_andp.
Qed.

Lemma semax_max_path_field_cast_load_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e1: expr) Pre
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (p v: val) (v' : reptype (nested_field_type t_root gfs)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      readable_share sh ->
      forallb subst_localdef_ok Q = true ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        local `(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v)) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (temp id (eval_cast (typeof (nested_efield e1 efs tts)) t v)
                                :: map (subst_localdef id old) Q)
                  (SEPx R)))).
Proof.
  intros until 3. intro OKsubst; intros.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs).
  Focus 1. {
    eapply derives_trans; [exact H9 |].
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H4)).
    normalize.
    apply prop_right; symmetry; auto.
  } Unfocus.
  rewrite H10 in H0.
  assert_PROP (field_compatible t_root gfs p).
  Focus 1. {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H7 |].
    rewrite field_at_compatible'.
    normalize.
  } Unfocus.
  rewrite H10.
  eapply semax_cast_load_nth_ram; try eassumption;
  [ idtac | idtac | apply andp_right].
  + rewrite (add_andp _ _ H8), (add_andp _ _ H9).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; eassumption].
    rewrite <- insert_local; solve_andp.
  + eapply self_ramify_trans; [exact H7 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; [auto | rewrite <- H10; auto | auto | eauto].
  + rewrite (add_andp _ _ H8), (add_andp _ _ H9).
    eapply derives_trans; [| eapply tc_lvalue_nested_efield; eassumption].
    rewrite <- insert_local; solve_andp.
  + eapply derives_trans; [exact H9 |].
    rewrite H10; solve_andp.
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
  autorewrite with subst norm1 norm2; normalize.
  normalize in H.
  autorewrite with subst norm1 norm2 in H; normalize in H; normalize.  
Qed.

Lemma semax_max_path_field_store_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh P Q R (e1 e2 : expr) Pre Post
      (t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)) lr,
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      writable_share sh ->
      forallb subst_localdef_ok Q = true ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- field_at_ sh t_root gfs p *
        (field_at sh t_root gfs v' p -* Post) ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        local (`(eq v) (eval_expr (Ecast e2 (typeof (nested_efield e1 efs tts))))) ->
      PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |--
        (tc_LR Delta e1 lr) && 
        (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        (tc_expr Delta (Ecast e2 (typeof (nested_efield e1 efs tts)))) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R Post))))).
Proof.
  intros until 2. intros OKsubst. intros.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs).
  Focus 1. {
    eapply derives_trans; [exact H9 |].
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H3)).
    normalize.
    apply prop_right; symmetry; auto.
  } Unfocus.
  assert_PROP (field_compatible t_root gfs p).
  Focus 1. {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H6 |].
    unfold field_at_; rewrite (field_at_compatible' _ _ _ (default_val _)).
    normalize.
  } Unfocus.
  rewrite H10 in H.
  eapply semax_store_nth_ram; eauto.
  4: apply andp_right.
  + rewrite (add_andp _ _ H7), (add_andp _ _ H9).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; eassumption].
    rewrite <- insert_local; solve_andp.
  + rewrite <- H10; exact H8.
  + eapply RAMIF_PLAIN.trans; [exact H6 |].
    apply mapsto_field_at_ramify; [auto | rewrite <- H10; auto | | auto].
    symmetry; apply by_value_default_val; auto.
  + rewrite (add_andp _ _ H7), (add_andp _ _ H9).
    eapply derives_trans; [| eapply tc_lvalue_nested_efield; eassumption].
    rewrite <- insert_local; solve_andp.
  + eapply derives_trans; [exact H9 |].
    rewrite H10; solve_andp.
Qed.

End LOADSTORE_FIELD_AT.
