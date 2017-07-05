Require Import floyd.base2.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.reptype_lemmas.
Require Import floyd.proj_reptype_lemmas.
Require Import floyd.replace_refill_reptype_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_rec_lemmas.
Require Import floyd.field_at.
Require Import floyd.stronger.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import floyd.local2ptree_denote.
Require Import floyd.local2ptree_eval.

Local Open Scope logic.

Definition msubst_eval_LR {cs: compspecs} T1 T2 e (lr: LLRR) :=
  match lr with
  | LLLL => msubst_eval_lvalue T1 T2 e
  | RRRR => msubst_eval_expr T1 T2 e
  end.

Lemma msubst_eval_LR_eq: forall {cs: compspecs} P T1 T2 Q R e v lr,
  msubst_eval_LR T1 T2 e lr = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_LR e lr)).
Proof.
  intros.
  destruct lr.
  + apply msubst_eval_lvalue_eq; auto.
  + apply msubst_eval_expr_eq; auto.
Qed.

Fixpoint msubst_efield_denote {cs: compspecs} T1 T2 (efs: list efield) : option (list gfield) :=
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

Lemma msubst_efield_denote_equiv: forall {cs: compspecs} P T1 T2 R efs gfs,
  msubst_efield_denote T1 T2 efs = Some gfs ->
  assertD P (localD T1 T2) R |-- efield_denote efs gfs.
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
    - destruct (typeof i) eqn:?; try solve [inversion H].
      destruct (msubst_eval_expr T1 T2 i) eqn:?H; [| inversion H].
      destruct v; try solve [inversion H].
      apply msubst_eval_expr_eq with (P0 := P) (Q := nil) (R0 := R) in H0.
      destruct (msubst_efield_denote T1 T2 efs) eqn:?H; [| inversion H].
      inversion H.
      rewrite (add_andp _ _ (IHefs l eq_refl)).
      unfold assertD, localD.
      rewrite (add_andp _ _ H0).
      apply andp_derives; [| auto].
      rewrite Int.repr_unsigned.
      apply andp_left2.
      apply andp_right; auto.
      intros x; apply prop_True_right.
    - destruct (msubst_efield_denote T1 T2 efs) eqn:?H; [| inversion H].
      inversion H.
      rewrite (add_andp _ _ (IHefs l eq_refl)).
      apply andp_derives; [| auto].
      simpl; intros; normalize.
    - destruct (msubst_efield_denote T1 T2 efs) eqn:?H; [| inversion H].
      inversion H.
      rewrite (add_andp _ _ (IHefs l eq_refl)).
      apply andp_derives; [| auto].
      simpl; intros; normalize.
Qed.

Section SEMAX_SC.

Context {cs: compspecs}.

Lemma semax_SC_set:
  forall {Espec: OracleKind},
    forall Delta id P Q R (e2: expr) t v,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (implicit_deref (typeof e2)) t = true ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq v) (eval_expr e2)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_expr Delta e2) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_expr Delta e2) &&  (tc_temp_id id (typeof e2) Delta e2)).
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
      apply neutral_isCastResultType, H0.
  }
  eapply semax_pre_simple.
  {
    hoist_later_left.
    rewrite (add_andp _ _ H3).
    rewrite andp_comm.
    rewrite (add_andp _ _ H1).
    apply later_derives.
    apply andp_derives; [apply derives_refl |].
    apply andp_derives; [| apply derives_refl].
    apply andp_left2.
    apply derives_refl.
  }
  eapply semax_post'; [| apply semax_set_forward].
  apply andp_left2; 
  rewrite <- insert_local.
  eapply derives_trans; [| apply andp_derives; [apply derives_refl | apply remove_localdef_temp_PROP]].
  normalize.
  apply (exp_right old).
  autorewrite with subst.
  rewrite andp_comm, andp_assoc, andp_comm.
  apply andp_derives; auto.
  simpl; unfold local, lift1; unfold_lift; intro rho; simpl.
  normalize.
Qed.

Lemma semax_SC_field_load:
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      readable_share sh ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        efield_denote efs gfs ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros until 7; pose proof I; intros.
  eapply semax_extract_later_prop'; [exact H12 | clear H12; intro H12].
  eapply semax_extract_later_prop';
   [eapply derives_trans; [exact H9 | eapply typeof_nested_efield; eauto] | intro].
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v)
    by (apply valinject_JMeq; apply is_neutral_cast_by_value with t; rewrite H13; auto).
  eapply semax_max_path_field_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ H9), (add_andp _ _ H11); solve_andp.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply H10 |].
    rewrite H4 in H14.
    apply @JMeq_sym, H14.
  + rewrite <- H4; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H4.
    apply derives_refl.
Qed.

Lemma semax_SC_field_load':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e: expr)
      (t t_root: type) (gfs0 gfs1 gfs: list gfield)
      (p q: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      type_is_volatile (typeof e) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq q) (eval_lvalue e)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (q = field_address t_root gfs p) ->
      typeof e = nested_field_type t_root gfs ->
      gfs = gfs1 ++ gfs0 ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      readable_share sh ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros.
  eapply semax_extract_later_prop'; [exact H10 | clear H10; intro H10].
  eapply semax_extract_later_prop'; [exact H3 | clear H3; intro H3]. subst q.
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v) as A. {
    apply valinject_JMeq. apply is_neutral_cast_by_value with t. rewrite <- H4. assumption.
  }
  eapply semax_max_path_field_load_nth_ram'.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  exact A.
  eassumption.
  2: eassumption.
  2: eassumption.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply H8 |].
    rewrite H5 in A.
    apply @JMeq_sym, A.
  + rewrite <- H5; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H5.
    apply derives_refl.
Qed.

(*
a is the "base pointer" of the SEP clause to be used, and the path to the value can be split in 2 ways:
- a.gfsA.gfsB :  a.gfsA corresponds to e1, and gfsB corresponds to efs
- a.gfs0.gfs1 :  a.gfs0 is what we have a field_at clause for, and gfs1 goes from there to final value
*)
Lemma semax_SC_field_load'':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfsA gfsB: list gfield) (tts: list type)
      (p a : val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfsB ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (p = field_address t_root gfsA a) ->
      nth_error R n = Some (field_at sh t_root gfs0 v' a) ->
      readable_share sh ->
      gfsB ++ gfsA = gfs1 ++ gfs0 ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
         local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root (gfsB ++ gfsA)) ->
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros until 0. intros TypeOf Cast Volatile Ugly Edenote Nice GetR Rsh Split Dig Tc Lnf EqLr Lnef.
  eapply semax_extract_later_prop'; [exact Lnf | clear Lnf; intro Lnf].
  eapply semax_extract_later_prop'; [exact Nice | clear Nice; intro Nice]. subst p.
  eapply semax_extract_later_prop';
   [eapply derives_trans; [exact Edenote | eapply typeof_nested_efield; eauto] | intro EqT].
  assert (JMeq (valinject (nested_field_type t_root (gfsB ++ gfsA)) v) v) as JM. {
    apply valinject_JMeq. apply is_neutral_cast_by_value with t.
    rewrite <- nested_field_type_nested_field_type. rewrite EqT. assumption.
  }
  eapply semax_max_path_field_load_nth_ram''.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ Edenote), (add_andp _ _ Tc); solve_andp.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply Dig |].
    rewrite Split in JM.
    apply @JMeq_sym, JM.
  + rewrite <- Split. exact Lnf.
  + apply sepcon_derives; [| auto].
    rewrite <- Split.
    apply derives_refl.
Qed.

Lemma nth_error_SEP_sepcon_TT': forall D P Q R n Rn S,
  ENTAIL D, PROPx P (LOCALx Q (SEPx (Rn :: nil))) |-- S ->
  nth_error R n = Some Rn ->
  ENTAIL D, (PROPx P (LOCALx Q (SEPx R))) |-- S * TT.
Proof.
  intros.
  erewrite SEP_nth_isolate by eauto.
  unfold PROPx, LOCALx, SEPx in *.
  unfold local, lift1 in H |- *.
  unfold_lift in H.
  unfold_lift.
  simpl in H |- *.
  intros rho.
  specialize (H rho).
  rewrite <- !andp_assoc in H |- *.
  rewrite <- !prop_and in H |- *.
  rewrite sepcon_emp in H.
  rewrite <- sepcon_andp_prop'.
  apply sepcon_derives.
  exact H.
  apply prop_right.
  auto.
Qed.

Lemma semax_SC_field_cast_load:
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      classify_cast (typeof (nested_efield e1 efs tts)) t <> cast_case_p2bool ->
      readable_share sh ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        efield_denote efs gfs ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v))) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id (eval_cast (typeof (nested_efield e1 efs tts)) t v) :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros until 2. intro H6. intros.
  eapply semax_extract_later_prop'; [exact H12 | clear H12; intro H12].
  eapply semax_extract_later_prop';
   [eapply derives_trans; [exact H9 | eapply typeof_nested_efield; eauto] | intro].
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v)
    by (apply valinject_JMeq; rewrite H13; auto).
  eapply semax_max_path_field_cast_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ H9), (add_andp _ _ H11); solve_andp.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply H10 |].
    rewrite H4 in H14.
    apply @JMeq_sym, H14.
  + rewrite <- H4; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H4.
    apply derives_refl.
Qed.

Lemma semax_SC_field_store:
  forall {Espec: OracleKind},
    forall Delta sh n (p: val) P Q R (e1 e2 : expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (v0: val) (v v_new: reptype (nested_field_type t_root gfs0)) lr,
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t = true ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some (field_at sh t_root gfs0 v p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        efield_denote efs gfs ->
      writable_share sh ->
      data_equal (upd_reptype (nested_field_type t_root gfs0) gfs1 v (valinject _ v0)) v_new ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
         (tc_expr Delta (Ecast e2 t)) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (field_at sh t_root gfs0 v_new p)))))).
Proof.
  intros until 6; pose proof I; intros.
  subst t.
  erewrite field_at_data_equal by (symmetry; apply H11).
  clear H11 v_new.
  eapply semax_extract_later_prop'; [exact H13 | clear H13; intro H13].
  eapply semax_extract_later_prop';
   [eapply derives_trans; [exact H9 | eapply typeof_nested_efield; eauto] | intro].
  eapply semax_max_path_field_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: apply @JMeq_sym.
     apply valinject_JMeq; rewrite H; auto.
  1: eassumption.
  2: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ H9), (add_andp _ _ H12); solve_andp.
  assert ({v0': reptype (nested_field_type t_root (gfs1 ++ gfs0)) | JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v) v0'}).
  Focus 1. {
    apply JMeq_sigT.
    rewrite nested_field_type_nested_field_type; auto.
  } Unfocus.
  destruct X as [v0' ?H].
  pose proof nested_field_ramif' sh t_root gfs0 gfs1 v v0' p H11.
  rewrite H3 in H13; spec H14; [auto |].
  eapply derives_trans; [apply H14 |].
  rewrite H3.
  apply sepcon_derives; [apply field_at_field_at_ |].
  clear v0' H11 H14.
  apply (allp_left _ (valinject (nested_field_type t_root (gfs1 ++ gfs0)) v0)).
  apply (allp_left _ (valinject (nested_field_type (nested_field_type t_root gfs0) gfs1) v0)).
  rewrite prop_imp; [apply derives_refl |].
  eapply JMeq_trans; [apply valinject_JMeq; rewrite <- H3, H; auto |].
  apply @JMeq_sym, valinject_JMeq.
  rewrite nested_field_type_nested_field_type.
  rewrite <- H3, H; auto.
Qed.

Lemma semax_SC_field_store_without_nested_efield:
  forall {Espec: OracleKind},
    forall Delta sh n (a p: val) P Q R (e1 e2 : expr)
      (t t_root: type) (gfs0 gfs1 gfs: list gfield)
      (v0: val) (v v_new: reptype (nested_field_type t_root gfs0)),
      typeof e1 = t ->
      nested_field_type t_root gfs = t ->
      type_is_by_value t = true ->
      type_is_volatile t = false ->
      gfs = gfs1 ++ gfs0 ->
      nth_error R n = Some (field_at sh t_root gfs0 v a) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (p = field_address t_root gfs a) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      writable_share sh ->
      data_equal (upd_reptype (nested_field_type t_root gfs0) gfs1 v (valinject _ v0)) v_new ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_lvalue Delta e1) && 
         (tc_expr Delta (Ecast e2 t)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (field_at sh t_root gfs0 v_new a)))))).
Proof.
  intros until 0.
  intros TypeOf EqT ByVal Volatile EqGfs GetR Ugly Nice EvalRhs Wsh DEq Tc Lnf.
  eapply semax_extract_later_prop'; [exact Lnf | clear Lnf; intro Lnf].
  eapply semax_extract_later_prop'; [exact Nice | clear Nice; intro Nice]. subst p.
  erewrite field_at_data_equal by (symmetry; apply DEq).
  clear DEq v_new.
  subst t.
  eapply semax_no_path_field_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: symmetry; eassumption.
  1: apply @JMeq_sym.
     apply valinject_JMeq. rewrite EqT. exact ByVal.
  1: eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  assert ({v0': reptype (nested_field_type t_root (gfs1 ++ gfs0)) | JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v) v0'}).
  {
    apply JMeq_sigT.
    rewrite nested_field_type_nested_field_type; auto.
  }
  destruct X as [v0' JM].
  pose proof nested_field_ramif' sh t_root gfs0 gfs1 v v0' a JM as A.
  rewrite EqGfs in Lnf; spec A; [auto |].
  eapply derives_trans; [apply A |].
  rewrite EqGfs.
  apply sepcon_derives; [apply field_at_field_at_ |].
  clear v0' A JM.
  apply (allp_left _ (valinject (nested_field_type t_root (gfs1 ++ gfs0)) v0)).
  apply (allp_left _ (valinject (nested_field_type (nested_field_type t_root gfs0) gfs1) v0)).
  rewrite prop_imp; [apply derives_refl |].
  rewrite <- EqT, EqGfs in ByVal.
  eapply JMeq_trans; [apply valinject_JMeq; exact ByVal |].
  apply @JMeq_sym, valinject_JMeq.
  rewrite nested_field_type_nested_field_type. exact ByVal.
Qed.

Lemma semax_SC_field_store_with_nested_field_partial:
  forall {Espec: OracleKind},
    forall Delta sh n (a p: val) P Q R (e1 e2 : expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfsA gfsB: list gfield) (tts: list type)
      (v0: val) (v v_new: reptype (nested_field_type t_root gfs0)) lr,
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t = true ->
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      gfsB ++ gfsA = gfs1 ++ gfs0 ->
      nth_error R n = Some (field_at sh t_root gfs0 v a) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (p = field_address t_root gfsA a) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfsB ->
      writable_share sh ->
      data_equal (upd_reptype (nested_field_type t_root gfs0) gfs1 v (valinject _ v0)) v_new ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) && 
         (tc_expr Delta (Ecast e2 t)) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root (gfsB ++ gfsA)) ->
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (field_at sh t_root gfs0 v_new a)))))).
Proof.
  intros until 0.
  intros TypeOf ByVal LRo Volatile EqGfs GetR Ugly Nice EvalRhs Edenote Wsh DEq Tc Lnf Lnef.
  eapply semax_extract_later_prop'; [exact Lnf | clear Lnf; intro Lnf].
  eapply semax_extract_later_prop'; [exact Nice | clear Nice; intro Nice]. subst p.
  eapply semax_extract_later_prop'; 
   [eapply derives_trans; [exact Edenote | eapply typeof_nested_efield; eauto] | intro EqT].
  erewrite field_at_data_equal by (symmetry; apply DEq).
  clear DEq v_new.
  subst t.
  eapply semax_partial_path_field_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: apply @JMeq_sym.
     apply valinject_JMeq. rewrite <- nested_field_type_nested_field_type. rewrite EqT. exact ByVal.
  1: eassumption.
  2: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ Edenote), (add_andp _ _ Tc); solve_andp.
  2: eassumption.
  assert ({v0': reptype (nested_field_type t_root (gfs1 ++ gfs0)) | JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v) v0'}).
  {
    apply JMeq_sigT.
    rewrite nested_field_type_nested_field_type; auto.
  }
  destruct X as [v0' JM].
  pose proof nested_field_ramif' sh t_root gfs0 gfs1 v v0' a JM as A.
  rewrite EqGfs in Lnf; spec A; [auto |].
  eapply derives_trans; [apply A |].
  rewrite EqGfs.
  apply sepcon_derives; [apply field_at_field_at_ |].
  clear v0' A JM.
  apply (allp_left _ (valinject (nested_field_type t_root (gfs1 ++ gfs0)) v0)).
  apply (allp_left _ (valinject (nested_field_type (nested_field_type t_root gfs0) gfs1) v0)).
  rewrite prop_imp; [apply derives_refl |].
  rewrite <- EqT, nested_field_type_nested_field_type, EqGfs in ByVal.
  eapply JMeq_trans; [apply valinject_JMeq; exact ByVal |].
  apply @JMeq_sym, valinject_JMeq.
  rewrite nested_field_type_nested_field_type. exact ByVal.
Qed.


(************************************************

The set, load, cast-load and store rules will be used in the future.

************************************************)

(* TODO: This was broken because semax_SC_field_load's specification is changed. *)
(*
Lemma semax_PTree_set:
  forall {Espec: OracleKind},
    forall Delta id P T1 T2 R (e2: Clight.expr) t v,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (implicit_deref (typeof e2)) t = true ->
      msubst_eval_expr T1 T2 e2 = Some v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
         (tc_expr Delta e2) ->
      semax Delta (|> (assertD P (localD T1 T2) R))
        (Sset id e2)
          (normal_ret_assert
            (assertD P (localD (PTree.set id v T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_set; eauto.
    instantiate (1 := v).
    apply andp_left2.
    apply msubst_eval_expr_eq, H1.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.

Lemma semax_PTree_load:
  forall {Espec: OracleKind},
    forall Delta sh n id P T1 T2 R Rn (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_efield_denote T1 T2 efs = Some gfs ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) (Rn :: nil)) |--
        `(field_at sh t_root gfs0 v' p) ->
      readable_share sh ->
      repinject _ (proj_reptype (nested_field_type t_root gfs0) gfs1 v') = v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
         (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
         (tc_efield Delta efs) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>assertD P (localD T1 T2) R)
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (assertD P (localD (PTree.set id v T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_tce in H6, H9, H10.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_field_load with (n0 := n); eauto.
(*    + apply map_nth_error, H3.*)
    + rewrite <- insert_tce.
      apply andp_left2.
      destruct lr;
      unfold eval_LR;
      unfold msubst_eval_LR in H4.
      - apply msubst_eval_lvalue_eq, H4.
      - apply msubst_eval_expr_eq, H4.
    + rewrite <- insert_tce.
      apply andp_left2.
      apply msubst_efield_denote_equiv, H5.
    + apply subst_LocalD_ok.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.
*)

(* TODO: This was broken because semax_SC_field_cast_load's specification is changed. *)
(*
Lemma semax_PTree_cast_load:
  forall {Espec: OracleKind},
    forall Delta sh n id P T1 T2 R Rn (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_efield_denote T1 T2 efs = Some gfs ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) (Rn :: nil)) |--
        `(field_at sh t_root gfs0 v' p) ->
      readable_share sh ->
      repinject _ (proj_reptype (nested_field_type t_root gfs0) gfs1 v') = v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
         (tc_LR Delta e1 lr) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v))) &&
         (tc_efield Delta efs) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>assertD P (localD T1 T2) R)
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (assertD P (localD (PTree.set id (eval_cast (typeof (nested_efield e1 efs tts)) t v) T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_tce in H6, H9, H10.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_field_cast_load with (n0 := n); eauto.
(*    + apply map_nth_error, H3.*)
    + rewrite <- insert_local.
      apply andp_left2.
      destruct lr;
      unfold eval_LR;
      unfold msubst_eval_LR in H4.
      - apply msubst_eval_lvalue_eq, H4.
      - apply msubst_eval_expr_eq, H4.
    + rewrite <- insert_local. apply andp_left2.
      apply msubst_efield_denote_equiv, H5.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.
*)

(* TODO: This was broken because semax_SC_field_store's specification is changed. *)
(*
Lemma semax_PTree_store:
  forall {Espec: OracleKind},
    forall Delta sh n P T1 T2 R Rn (e1 e2 : expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (p: val) (v0: val) (v v_new: reptype (nested_field_type t_root gfs0)) lr,
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t = true ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_eval_expr T1 T2 (Ecast e2 t) = Some v0 ->
      msubst_efield_denote T1 T2 efs = Some gfs ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) (Rn :: nil))  |--
        `(field_at sh t_root gfs0 v p) ->
      writable_share sh ->
      data_equal (upd_reptype (nested_field_type t_root gfs0) gfs1 v (valinject _ v0)) v_new ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
         (tc_LR Delta e1 lr) &&
         (tc_expr Delta (Ecast e2 t)) &&
         (tc_efield Delta efs) ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>assertD P (localD T1 T2) R)
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (assertD P (localD T1 T2)
                  (replace_nth n R
                    (field_at sh t_root gfs0 v_new p)))).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_tce in H7, H10, H11.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_field_store with (n0 := n); eauto.
(*    + apply map_nth_error, H3.*)
    + rewrite <- insert_local.
      apply andp_left2.
      destruct lr;
      unfold eval_LR;
      unfold msubst_eval_LR in H4.
      - apply msubst_eval_lvalue_eq, H4.
      - apply msubst_eval_expr_eq, H4.
    + rewrite <- insert_local.
      apply andp_left2.
      apply msubst_eval_expr_eq, H5.
    + rewrite <- insert_local. apply andp_left2.
      apply msubst_efield_denote_equiv, H6.
  } Unfocus.
(*  rewrite map_replace_nth.*)
  auto.
Qed.
*)

Definition proj_val t_root gfs v :=
   repinject (nested_field_type t_root gfs) (proj_reptype t_root gfs v).

Definition upd_val t_root gfs v v0 :=
   upd_reptype t_root gfs v (valinject (nested_field_type t_root gfs) v0).

End SEMAX_SC.