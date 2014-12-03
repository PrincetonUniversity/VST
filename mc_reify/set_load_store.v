Require Import floyd.proofauto.
Require Import JMeq.
Require Import mc_reify.bool_funcs.
Local Open Scope logic.

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

Definition msubst_eval_LR T1 T2 e lr :=
  match lr with
  | LLLL => msubst_eval_lvalue T1 T2 e
  | RRRR => msubst_eval_expr T1 T2 e
  end.

Fixpoint msubst_efield_denote T1 T2 (efs: list efield) : option (list gfield) :=
  match efs with
  | nil => Some nil
  | eArraySubsc ei :: efs' =>
    match typeof ei, msubst_eval_expr T1 T2 ei with
    | Tint _ _ _, Some (Vint i) =>
      option_map (cons (ArraySubsc (Int.unsigned i))) (msubst_efield_denote T1 T2 efs')
    | _, _ => None
    end
  | eStructField i :: efs' =>
    option_map (cons (StructField i)) (msubst_efield_denote T1 T2 efs')
  | eUnionField i :: efs' =>
    option_map (cons (UnionField i)) (msubst_efield_denote T1 T2 efs')
  end.

Lemma msubst_efield_denote_equiv: forall Delta P T1 T2 R efs gfs,
  msubst_efield_denote T1 T2 efs = Some gfs ->
  (local (tc_environ Delta)) && assertD P (localD T1 T2) R |-- efield_denote efs gfs.
Proof.
  intros.
  revert gfs H; induction efs; intros.
  + simpl in H.
    inversion H.
    apply prop_right.
    auto.
Opaque andp.
  + destruct a;
    simpl in H;
    simpl efield_denote.
Transparent andp.
    - destruct (typeof i); try solve [inversion H].
      destruct (msubst_eval_expr T1 T2 i) eqn:?H; [| inversion H].
      destruct v; try solve [inversion H].
      apply msubst_eval_expr_eq with (P := P) (Q := nil) (R := map liftx R) in H0.
      destruct (msubst_efield_denote T1 T2 efs) eqn:?H; [| inversion H].
      inversion H.
      rewrite (add_andp _ _ (IHefs l eq_refl)).
      unfold assertD, localD.
      rewrite (add_andp _ _ H0).
      apply andp_derives; [| auto].
      apply andp_left2.
      apply andp_left2.
      rewrite Int.repr_unsigned.
      repeat apply andp_right; auto.
      entailer!.
    - destruct (msubst_efield_denote T1 T2 efs) eqn:?H; [| inversion H].
      inversion H. 
      rewrite (add_andp _ _ (IHefs l eq_refl)).
      apply andp_derives; [| auto].
      entailer!.
    - destruct (msubst_efield_denote T1 T2 efs) eqn:?H; [| inversion H].
      inversion H. 
      rewrite (add_andp _ _ (IHefs l eq_refl)).
      apply andp_derives; [| auto].
      entailer!.
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

Fixpoint tc_efield_b_norho Delta efs :=
  match efs with
  | nil => true
  | eArraySubsc ei :: efs' =>
      (tc_expr_b_norho Delta ei && tc_efield_b_norho Delta efs')%bool
  | eStructField _ :: efs' => tc_efield_b_norho Delta efs'
  | eUnionField _ :: efs' => tc_efield_b_norho Delta efs'
  end.

Lemma tc_efield_b_sound: forall efs Delta rho,
  tc_efield_b_norho Delta efs = true -> tc_efield Delta efs rho.
Proof.
  intros.
  induction efs.
  + simpl; auto.
  + destruct a; simpl in H |- *.
    - apply andb_true_iff in H.
      destruct H.
      apply tc_expr_b_sound with (rho := rho) in H.
      tauto.
    - tauto.
    - tauto.
Qed.

