Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.loadstore_mapsto.

Local Open Scope logic.

Lemma is_neutral_cast_by_value: forall t t',
  is_neutral_cast t t' = true ->
  type_is_by_value t = true.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl; auto.
Qed.

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

Lemma semax_load_nth_ram_field_at :
  forall {Espec: OracleKind}{cs: compspecs} n (Delta: tycontext) sh id P Q R e1 Pre
    t_id t_root gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs)),
    typeof e1 = nested_field_type t_root gfs ->
    typeof_temp Delta id = Some t_id ->
    is_neutral_cast (nested_field_type t_root gfs) t_id = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
    readable_share sh ->
    Pre |-- field_at sh t_root gfs v_reptype p * TT ->
    JMeq v_reptype v_val ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      (tc_lvalue Delta e1) && local (`(tc_val (nested_field_type t_root gfs) v_val)) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id e1)
      (normal_ret_assert
         (PROPx P
           (LOCALx (temp id v_val :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H1.
  eapply semax_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: rewrite H; assumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  eapply self_ramify_trans; [exact H6 |].
  eapply RAMIF_PLAIN.weak_ramif_spec.
  apply mapsto_field_at_ramify; auto.
  eapply JMeq_sym; exact H7.
Qed.

(* TODO: delete it *)
Lemma semax_max_path_field_load_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e1: expr) Pre
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      readable_share sh ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        local (efield_denote efs gfs) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H0.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs).
  {
    eapply derives_trans; [exact H9 |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    apply prop_right.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  rewrite H11 in H10.
  assert_PROP (field_compatible t_root gfs p).
  {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2;
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H7 |].
    rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_load_nth_ram; try eassumption;
  [ idtac
  | idtac
  | apply andp_right].
  + rewrite (add_andp _ _ H8), (add_andp _ _ H9).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; eassumption].
    solve_andp.
  + eapply self_ramify_trans; [exact H7 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; [auto | rewrite <- H11; auto | auto | eauto].
  + rewrite (add_andp _ _ H8), (add_andp _ _ H9).
    eapply derives_trans; [| eapply tc_lvalue_nested_efield; eassumption].
    solve_andp.
  + eapply derives_trans; [exact H9 |].
    rewrite H11; solve_andp.
Qed.

(* TODO: delete it *)
Lemma semax_max_path_field_load_nth_ram':
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) Pre
      (t t_root: type) (gfs: list gfield)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      typeof e = nested_field_type t_root gfs ->
      readable_share sh ->
      type_is_volatile (typeof e) = false ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H0.
  rewrite H1 in H8.
  assert_PROP (field_compatible t_root gfs p). {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2;
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H6 |].
    rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_load_nth_ram; try eassumption.
  + eapply self_ramify_trans; [exact H6 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; try rewrite <- H1; eauto.
Qed.

(* TODO: delete it *)
Lemma semax_max_path_field_load_nth_ram'':
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e1: expr) Pre
      (t t_root: type) (efs: list efield) (gfsA gfsB: list gfield) (tts: list type)
      (a v : val) (v' : reptype (nested_field_type t_root (gfsB ++ gfsA))) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      readable_share sh ->
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root (gfsB ++ gfsA) v' a * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfsA a)) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        local (efield_denote efs gfsB) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros until 0. intros TId Cast Rsh EqLr Volatile Lnf JM GetR F Evale1 Tc.
  pose proof is_neutral_cast_by_value _ _ Cast as ByVal.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root (gfsB ++ gfsA)) as EqT. {
    rewrite <- nested_field_type_nested_field_type.
    eapply derives_trans; [exact Tc |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    apply prop_right.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  rewrite EqT in ByVal.
  assert_PROP (field_compatible t_root (gfsB ++ gfsA) a) as Fc. {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2;
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply F |].
    rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_load_nth_ram with (p := (field_address t_root (gfsB ++ gfsA) a)).
  + exact EqT.
  + exact TId.
  + exact Cast.
  + rewrite field_address_app.
    rewrite (add_andp _ _ Evale1), (add_andp _ _ Tc).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; try eassumption].
    - solve_andp.
    - apply field_compatible_app. exact Fc.
    - rewrite nested_field_type_nested_field_type. exact ByVal.
  + eassumption.
  + eassumption.
  + eapply self_ramify_trans; [exact F |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; [auto | rewrite <- EqT; auto | auto | eauto].
  + apply andp_right.
    - rewrite (add_andp _ _ Evale1), (add_andp _ _ Tc).
      eapply derives_trans; [| eapply tc_lvalue_nested_efield].
      * solve_andp.
      * eapply field_compatible_app. exact Fc.
      * eassumption.
      * eassumption.
      * rewrite nested_field_type_nested_field_type. exact ByVal.
    - eapply derives_trans; [exact Tc |].
      rewrite EqT. solve_andp.
Qed.

Lemma semax_cast_load_nth_ram_field_at :
  forall {Espec: OracleKind}{cs: compspecs} n (Delta: tycontext) sh id P Q R e1 Pre
    t_to t_root gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs)),
    typeof e1 = nested_field_type t_root gfs ->
    type_is_by_value (nested_field_type t_root gfs) = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    typeof_temp Delta id = Some t_to ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
     cast_pointer_to_bool (nested_field_type t_root gfs) t_to = false ->
    readable_share sh ->
    Pre |-- field_at sh t_root gfs v_reptype p * TT ->
    JMeq v_reptype v_val ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && local (`(tc_val t_to (eval_cast (nested_field_type t_root gfs) t_to v_val))) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
     (Sset id (Ecast e1 t_to))
     (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast (nested_field_type t_root gfs) t_to v_val) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  eapply semax_cast_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  eapply self_ramify_trans; [exact H7 |].
  eapply RAMIF_PLAIN.weak_ramif_spec.
  apply mapsto_field_at_ramify; auto.
  eapply JMeq_sym; exact H8.
Qed.

(* TODO: delete it *)
Lemma semax_max_path_field_cast_load_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e1: expr) Pre
      (t t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (p v: val) (v' : reptype (nested_field_type t_root gfs)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
     cast_pointer_to_bool (typeof (nested_efield e1 efs tts)) t = false ->
      readable_share sh ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        local (efield_denote efs gfs) &&
        local `(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v)) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id (eval_cast (typeof (nested_efield e1 efs tts)) t v) :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros until 2. intro HCAST; intros.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs).
  {
    eapply derives_trans; [exact H9 |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    apply prop_right.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  rewrite H10 in H0.
  assert_PROP (field_compatible t_root gfs p).
  {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2; apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H7 |].
    rewrite field_at_compatible'.
    normalize.
  }
  rewrite H10.
  eapply semax_cast_load_nth_ram; try eassumption;
  [ idtac |  rewrite <- H10; eassumption | idtac | apply andp_right].
  + rewrite (add_andp _ _ H8), (add_andp _ _ H9).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; eassumption].
    solve_andp.
  + eapply self_ramify_trans; [exact H7 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; [auto | rewrite <- H10; auto | auto | eauto].
  + rewrite (add_andp _ _ H8), (add_andp _ _ H9).
    eapply derives_trans; [| eapply tc_lvalue_nested_efield; eassumption].
    solve_andp.
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

Lemma semax_store_nth_ram_field_at:
  forall {Espec: OracleKind} {cs: compspecs} n Delta sh P Q R e1 e2 Pre Post
    t_root gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs)),
    typeof e1 = nested_field_type t_root gfs ->
    type_is_by_value (nested_field_type t_root gfs) = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq v_val) (eval_expr (Ecast e2 (nested_field_type t_root gfs)))) ->
    JMeq v_val v_reptype ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    Pre |-- field_at_ sh t_root gfs p * (field_at sh t_root gfs v_reptype p -* Post) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && (tc_expr Delta (Ecast e2 (nested_field_type t_root gfs))) ->
    semax Delta
     (|> PROPx P (LOCALx Q (SEPx R)))
     (Sassign e1 e2)
     (normal_ret_assert
        (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros.
  eapply semax_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  eapply RAMIF_PLAIN.trans; [exact H7 |].
  apply mapsto_field_at_ramify; auto.
  apply JMeq_sym; apply by_value_default_val; auto.
Qed.

(* TODO: delete it *)
Lemma semax_max_path_field_store_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh P Q R (e1 e2 : expr) Pre Post
      (t_root: type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)) lr,
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      writable_share sh ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- field_at_ sh t_root gfs p *
        (field_at sh t_root gfs v' p -* Post) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v) (eval_expr (Ecast e2 (typeof (nested_efield e1 efs tts))))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        local (efield_denote efs gfs) &&
        (tc_expr Delta (Ecast e2 (typeof (nested_efield e1 efs tts)))) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R Post))))).
Proof.
  intros.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs).
  {
    eapply derives_trans; [exact H9 |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    apply prop_right.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  assert_PROP (field_compatible t_root gfs p).
  {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2; apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H6 |].
    unfold field_at_; rewrite (field_at_compatible' _ _ _ (default_val _)).
    normalize.
  }
  rewrite H10 in H.
  eapply semax_store_nth_ram; eauto.
  4: apply andp_right.
  + rewrite (add_andp _ _ H7), (add_andp _ _ H9).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; eassumption].
    solve_andp.
  + rewrite <- H10; exact H8.
  + eapply RAMIF_PLAIN.trans; [exact H6 |].
    apply mapsto_field_at_ramify; [auto | rewrite <- H10; auto | | auto].
    apply JMeq_sym; apply by_value_default_val; auto.
  + rewrite (add_andp _ _ H7), (add_andp _ _ H9).
    eapply derives_trans; [| eapply tc_lvalue_nested_efield; eassumption].
    solve_andp.
  + eapply derives_trans; [exact H9 |].
    rewrite H10; solve_andp.
Qed.

(* TODO: delete it *)
Lemma semax_partial_path_field_store_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh P Q R (e1 e2 : expr) Pre Post
      (t_root: type) (efs: list efield) (gfsA gfsB: list gfield) (tts: list type)
      (a v : val) (v' : reptype (nested_field_type t_root (gfsB ++ gfsA))) lr,
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      writable_share sh ->
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- field_at_ sh t_root (gfsB ++ gfsA) a *
        (field_at sh t_root (gfsB ++ gfsA) v' a -* Post) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfsA a)) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v) (eval_expr (Ecast e2 (typeof (nested_efield e1 efs tts))))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_LR Delta e1 lr) && 
        (tc_efield Delta efs) &&
        local (efield_denote efs gfsB) &&
        (tc_expr Delta (Ecast e2 (typeof (nested_efield e1 efs tts)))) ->
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R Post))))).
Proof.
  intros until 0. intros ByVal Wsh LRo Volatile JM GetR F Evale1 Evale2 Tc Lnef.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root (gfsB ++ gfsA)) as EqT. {
    rewrite <- nested_field_type_nested_field_type.
    eapply derives_trans; [exact Tc |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    apply prop_right.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  rewrite EqT in ByVal.
  assert_PROP (field_compatible t_root (gfsB ++ gfsA) a) as Fc. {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2.
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply F |].
    apply derives_left_sepcon_right_corable; auto.
    unfold field_at_. rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_store_nth_ram with (p := (field_address t_root (gfsB ++ gfsA) a)).
  + exact EqT.
  + rewrite field_address_app.
    rewrite (add_andp _ _ Evale1), (add_andp _ _ Tc).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; try eassumption].
    - solve_andp.
    - apply field_compatible_app. exact Fc.
    - rewrite nested_field_type_nested_field_type. exact ByVal.
  + rewrite <- EqT. exact Evale2.
  + exact GetR.
  + exact Wsh.
  + eapply RAMIF_PLAIN.trans; [exact F |].
    apply mapsto_field_at_ramify; [auto | rewrite <- EqT; auto | | auto].
    apply JMeq_sym; apply by_value_default_val; auto.
  + apply andp_right.
    - rewrite (add_andp _ _ Evale1), (add_andp _ _ Tc).
      eapply derives_trans; [| eapply tc_lvalue_nested_efield].
      * solve_andp.
      * apply field_compatible_app. exact Fc.
      * exact LRo.
      * exact Lnef.
      * rewrite nested_field_type_nested_field_type. exact ByVal.
    - eapply derives_trans; [exact Tc |].
      rewrite EqT; solve_andp.
Qed.

(* TODO: delete it *)
Lemma semax_no_path_field_store_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh P Q R (e1 e2 : expr) Pre Post
      (t_root: type) (gfs: list gfield)
      (a v : val) (v' : reptype (nested_field_type t_root gfs)),
      type_is_by_value (typeof e1) = true ->
      writable_share sh ->
      type_is_volatile (typeof e1) = false ->
      typeof e1 = nested_field_type t_root gfs ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- field_at_ sh t_root gfs a *
        (field_at sh t_root gfs v' a -* Post) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfs a)) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v) (eval_expr (Ecast e2 (typeof e1)))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e1) && 
        (tc_expr Delta (Ecast e2 (typeof e1))) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R Post))))).
Proof.
  intros until 0. intros ByVal Wsh Volatile EqT JM GetR F Evale1 Evale2 Tc.
  rewrite EqT in ByVal.
  eapply semax_store_nth_ram with (p := (field_address t_root gfs a)).
  + exact EqT.
  + exact Evale1.
  + rewrite <- EqT. exact Evale2.
  + exact GetR.
  + exact Wsh.
  + eapply RAMIF_PLAIN.trans; [exact F |].
    apply mapsto_field_at_ramify; [auto | rewrite <- EqT; auto | | auto].
    apply JMeq_sym; apply by_value_default_val; auto.
  + rewrite <- EqT. exact Tc.
Qed.

End LOADSTORE_FIELD_AT.
