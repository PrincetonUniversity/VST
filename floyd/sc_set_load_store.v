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
Require Import floyd.simpl_reptype.

Local Open Scope logic.

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

(* TODO: remove "to_use" from its name. *)
Lemma semax_SC_field_load_to_use:
  forall {Espec: OracleKind} n (Delta: tycontext) sh id P Q R e1
    t_id t_root gfs0 gfs1 gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs0)),
    typeof e1 = nested_field_type t_root gfs ->
    typeof_temp Delta id = Some t_id ->
    is_neutral_cast (nested_field_type t_root gfs) t_id = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    nth_error R n = Some (field_at sh t_root gfs0 v_reptype p) ->
    gfs = gfs1 ++ gfs0 ->
    readable_share sh ->
    JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v_reptype) v_val ->
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
  assert_PROP (field_compatible t_root gfs p).
  Focus 1. {
    rewrite (add_andp _ _ H8), (add_andp _ _ H3).
    apply derives_trans with (local (tc_environ Delta) && local (` (eq (field_address t_root gfs p)) (eval_lvalue e1)) && (tc_lvalue Delta e1)); [solve_andp |].
    unfold local, lift1; intros rho; simpl; unfold_lift.
    normalize.
    eapply derives_trans; [apply typecheck_lvalue_sound; auto |].
    rewrite <- H10; normalize.
  } Unfocus.
  subst gfs.
  pose proof nested_field_ramif_load sh _ _ _ _ _ _ H9 H7 as [v_reptype' [? ?]].
  eapply semax_load_nth_ram_field_at.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
Qed.

(* TODO: delete this *)
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
        local (efield_denote efs gfs) ->
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
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs). {
    eapply derives_trans; [exact H9 |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v)
    by (apply valinject_JMeq; apply is_neutral_cast_by_value with t; rewrite <- H13; auto).
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

(* TODO: delete this *)
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
(* TODO: delete this *)
Lemma semax_SC_field_load'':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfsA gfsB: list gfield) (tts: list type)
      (p a : val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (efield_denote efs gfsB) ->
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
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root (gfsB ++ gfsA)) as EqT. {
    rewrite <- nested_field_type_nested_field_type.
    eapply derives_trans; [exact Edenote |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  assert (JMeq (valinject (nested_field_type t_root (gfsB ++ gfsA)) v) v) as JM. {
    apply valinject_JMeq. apply is_neutral_cast_by_value with t.
    rewrite <- EqT. assumption.
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

(* TODO: remove "to_use" from its name. *)
Lemma semax_SC_field_cast_load_to_use:
  forall {Espec: OracleKind} n (Delta: tycontext) sh id P Q R e1 t
    t_root gfs0 gfs1 gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs0)),
    typeof e1 = nested_field_type t_root gfs ->
    typeof_temp Delta id = Some t ->
    type_is_by_value (nested_field_type t_root gfs) = true ->
    classify_cast (nested_field_type t_root gfs) t <> cast_case_p2bool ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    nth_error R n = Some (field_at sh t_root gfs0 v_reptype p) ->
    gfs = gfs1 ++ gfs0 ->
    readable_share sh ->
    JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v_reptype) v_val ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      (tc_lvalue Delta e1) && local (`(tc_val t (eval_cast (nested_field_type t_root gfs) t v_val))) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id (Ecast e1 t))
      (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast (nested_field_type t_root gfs) t v_val) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  assert_PROP (field_compatible t_root gfs p).
  Focus 1. {
    rewrite (add_andp _ _ H9), (add_andp _ _ H4).
    apply derives_trans with (local (tc_environ Delta) && local (` (eq (field_address t_root gfs p)) (eval_lvalue e1)) && (tc_lvalue Delta e1)); [solve_andp |].
    unfold local, lift1; intros rho; simpl; unfold_lift.
    normalize.
    eapply derives_trans; [apply typecheck_lvalue_sound; auto |].
    rewrite <- H11; normalize.
  } Unfocus.
  subst gfs.
  pose proof nested_field_ramif_load sh _ _ _ _ _ _ H10 H8 as [v_reptype' [? ?]].
  eapply semax_cast_load_nth_ram_field_at.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
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
        local (efield_denote efs gfs) ->
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
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs). {
    eapply derives_trans; [exact H9 |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v)
    by (apply valinject_JMeq; rewrite <- H13; auto).
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
        local (efield_denote efs gfs) ->
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
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root gfs). {
    eapply derives_trans; [exact H9 |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  eapply semax_max_path_field_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: apply @JMeq_sym.
     apply valinject_JMeq; rewrite <- H; auto.
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
  eapply JMeq_trans; [apply valinject_JMeq; rewrite <- H3, <- H; auto |].
  apply @JMeq_sym, valinject_JMeq.
  rewrite nested_field_type_nested_field_type.
  rewrite <- H3, <- H; auto.
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
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (efield_denote efs gfsB) ->
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
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root (gfsB ++ gfsA)) as EqT. {
    rewrite <- nested_field_type_nested_field_type.
    eapply derives_trans; [exact Edenote |].
    intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
    symmetry; eapply typeof_nested_efield; eauto.
  }
  erewrite field_at_data_equal by (symmetry; apply DEq).
  clear DEq v_new.
  subst t.
  eapply semax_partial_path_field_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: apply @JMeq_sym.
     apply valinject_JMeq. rewrite <- EqT. exact ByVal.
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
  rewrite EqT, EqGfs in ByVal.
  eapply JMeq_trans; [apply valinject_JMeq; exact ByVal |].
  apply @JMeq_sym, valinject_JMeq.
  rewrite nested_field_type_nested_field_type. exact ByVal.
Qed.

End SEMAX_SC.

(************************************************

The set, load, cast-load and store rules will be used in the future.

************************************************)

Inductive Int_eqm_unsigned: int -> Z -> Prop :=
| Int_eqm_unsigned_repr: forall z, Int_eqm_unsigned (Int.repr z) z.

Lemma Int_eqm_unsigned_spec: forall i z,
  Int_eqm_unsigned i z -> Int.eqm (Int.unsigned i) z.
Proof.
  intros.
  inv H.
  apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Ltac solve_Int_eqm_unsigned :=
  solve
  [ autorewrite with norm;
    match goal with
    | |- Int_eqm_unsigned ?V _ =>
      match V with
      | Int.repr _ => idtac
      | Int.sub _ _ => unfold Int.sub at 1
      | Int.add _ _ => unfold Int.add at 1
      | Int.mul _ _ => unfold Int.mul at 1
      | Int.and _ _ => unfold Int.and at 1
      | Int.or _ _ => unfold Int.or at 1
(*      | Int.shl _ _ => unfold Int.shl at 1
      | Int.shr _ _ => unfold Int.shr at 1*)
      | _ => rewrite <- (Int.repr_unsigned V) at 1
      end
    end;
    apply Int_eqm_unsigned_repr
  ].

Inductive msubst_efield_denote {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc): list efield -> list gfield -> Prop :=
| msubst_efield_denote_nil: msubst_efield_denote T1 T2 nil nil
| msubst_efield_denote_cons_array: forall ei i i' efs gfs,
    is_int_type (typeof ei) = true ->
    msubst_eval_expr T1 T2 ei = Some (Vint i) ->
    Int_eqm_unsigned i i' ->
    msubst_efield_denote T1 T2 efs gfs ->
    msubst_efield_denote T1 T2 (eArraySubsc ei :: efs) (ArraySubsc i' :: gfs)
| msubst_efield_denote_cons_struct: forall i efs gfs,
    msubst_efield_denote T1 T2 efs gfs ->
    msubst_efield_denote T1 T2 (eStructField i :: efs) (StructField i :: gfs)
| msubst_efield_denote_cons_union: forall i efs gfs,
    msubst_efield_denote T1 T2 efs gfs ->
    msubst_efield_denote T1 T2 (eUnionField i :: efs) (UnionField i :: gfs).

Lemma msubst_efield_denote_eq: forall {cs: compspecs} P T1 T2 Q R efs gfs,
  msubst_efield_denote T1 T2 efs gfs ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- local (efield_denote efs gfs).
Proof.
  intros ? ? ? ? ? ? ? ? MSUBST_EFIELD_DENOTE.
  induction MSUBST_EFIELD_DENOTE.
  + intro rho; apply prop_right; constructor.
  + eapply (msubst_eval_expr_eq P _ _ Q R) in H0.
    rewrite (add_andp _ _ H0), (add_andp _ _ IHMSUBST_EFIELD_DENOTE).
    clear H0 IHMSUBST_EFIELD_DENOTE.
    rewrite andp_assoc; apply andp_left2.
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
    constructor; auto.
    constructor.
    apply Int_eqm_unsigned_spec in H1.
    rewrite <- H2; symmetry.
    f_equal.
    rewrite <- (Int.repr_unsigned i).
    apply Int.eqm_samerepr; auto.
  + eapply derives_trans; [eassumption |].
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
    constructor; auto.
  + eapply derives_trans; [eassumption |].
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
    constructor; auto.
Qed.

Ltac solve_msubst_efield_denote :=
  solve 
  [ repeat first
    [ eapply msubst_efield_denote_cons_array;
      [ reflexivity
      | solve_msubst_eval_expr
      | solve_Int_eqm_unsigned
      | ]
    | apply msubst_efield_denote_cons_struct
    | apply msubst_efield_denote_cons_union
    | apply msubst_efield_denote_nil
    ]
  ].

Inductive field_address_gen {cs: compspecs}: type * list gfield * val -> type * list gfield * val -> Prop :=
| field_address_gen_nil: forall t1 t2 gfs p tgp,
    nested_field_type t2 gfs = t1 ->
    field_address_gen (t2, gfs, p) tgp ->
    field_address_gen (t1, nil, (field_address t2 gfs p)) tgp
| field_address_gen_app: forall t1 t2 gfs1 gfs2 p tgp,
    nested_field_type t2 gfs2 = t1 ->
    field_address_gen (t2, gfs1 ++ gfs2, p) tgp ->
    field_address_gen (t1, gfs1, (field_address t2 gfs2 p)) tgp
| field_address_gen_assu: forall t gfs p1 p2 tgp,
    p1 = p2 ->
    field_address_gen (t, gfs, p2) tgp ->
    field_address_gen (t, gfs, p1) tgp    
| field_address_gen_refl: forall tgp, field_address_gen tgp tgp.

Lemma field_address_gen_fact: forall {cs: compspecs} t1 gfs1 p1 t2 gfs2 p2,
  field_address_gen (t1, gfs1, p1) (t2, gfs2, p2) ->
  field_address t1 gfs1 p1 = field_address t2 gfs2 p2 /\
  nested_field_type t1 gfs1 = nested_field_type t2 gfs2 /\
  (field_compatible t2 gfs2 p2 -> field_compatible t1 gfs1 p1).
Proof.
  intros.
  remember (t1, gfs1, p1) eqn:?H ; remember (t2, gfs2, p2) eqn:?H.
  revert t1 gfs1 p1 t2 gfs2 p2 H0 H1; induction H; intros.
  + subst.
    specialize (IHfield_address_gen _ _ _ _ _ _ eq_refl eq_refl).
    inv H1.
    destruct IHfield_address_gen as [? [? ?]].
    rewrite <- field_address_app.
    simpl.
    rewrite nested_field_type_ind.
    split; [| split]; auto; intros.
    apply field_compatible_app; auto.
  + subst.
    specialize (IHfield_address_gen _ _ _ _ _ _ eq_refl eq_refl).
    inv H1.
    destruct IHfield_address_gen as [? [? ?]].
    rewrite <- field_address_app.
    rewrite nested_field_type_nested_field_type.
    split; [| split]; auto; intros.
    apply field_compatible_app; auto.
  + subst.
    inv H1.
    auto.
  + subst.
    inv H1.
    auto.
Qed.

Ltac solve_field_address_gen :=
  solve [
    repeat
      first
      [ simple apply field_address_gen_nil; [reflexivity |]
      | simple apply field_address_gen_app; [reflexivity |]
      | simple eapply field_address_gen_assu; [eassumption |]
      | simple apply field_address_gen_refl
      ]
  ].

Lemma hint_msg_lemma: forall {cs: compspecs} e goal Q T1 T2 e_root efs tts lr p_full_from_e p_root_from_e
  t gfs p,
  local2ptree Q = (T1, T2, nil, nil) ->
  compute_nested_efield e = (e_root, efs, tts, lr) ->
  msubst_eval_lvalue T1 T2 e = Some p_full_from_e ->
  msubst_eval_LR T1 T2 e_root lr = Some p_root_from_e ->
  p_full_from_e = field_address t gfs p /\
  p_root_from_e = field_address t gfs p /\
  False ->
  goal.
Proof.
  intros.
  destruct H3 as [? [? ?]].
  inv H5.
Qed.

Ltac hint_msg LOCAL2PTREE e :=
  eapply (hint_msg_lemma e);
  [ exact LOCAL2PTREE
  | reflexivity
  | solve_msubst_eval_lvalue
  | solve_msubst_eval_LR
  | ];
  match goal with
  | |- ?eq1 /\ ?eq2 /\ False =>
          fail 1000 "Please use assert_PROP to prove an equality of the form" eq1
                    "or if this does not hold, prove an equality of the form" eq2
  end.

Section SEMAX_PTREE.

Context {cs: compspecs}.

Lemma semax_PTree_set:
  forall {Espec: OracleKind},
    forall Delta id P Q R T1 T2 (e2: expr) t v,
      local2ptree Q = (T1, T2, nil, nil) ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (implicit_deref (typeof e2)) t = true ->
      msubst_eval_expr T1 T2 e2 = Some v ->
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
  eapply semax_SC_set.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  apply andp_left2.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_eval_expr_eq; auto.
Qed.

Lemma semax_PTree_field_load_no_hint:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) t
      T1 T2 e_root (efs: list efield) (tts: list type) lr
      t_root_from_e gfs_from_e p_from_e
      (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
      (v : val) (v' : reptype (nested_field_type t_root gfs0)),
      local2ptree Q = (T1, T2, nil, nil) ->
      compute_nested_efield e = (e_root, efs, tts, lr) ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      type_is_volatile (typeof e) = false ->
      msubst_eval_LR T1 T2 e_root lr = Some p_from_e ->
      msubst_efield_denote T1 T2 efs gfs_from_e ->
      compute_root_type (typeof e_root) lr t_root_from_e ->
      field_address_gen (t_root_from_e, gfs_from_e, p_from_e) (t_root, gfs, p) ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) /\
      gfs = gfs1 ++ gfs0 ->
      readable_share sh ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        !! (legal_nested_field (nested_field_type t_root gfs0) gfs1) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e_root lr) &&
        local `(tc_val (typeof e) v) &&
         (tc_efield Delta efs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id e)
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id v :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros ? ? ? ? ? ? ? ? ? ?
         ? ? ? ? ? ?
         ? ? ?
         ? ? ? ? ?
         ? ?
         LOCAL2PTREE COMPUTE_NESTED_EFIELD ? ? ? EVAL_ROOT EVAL_EFIELD ROOT_TYPE
         FIELD_ADD_GEN [NTH GFS] SH JMEQ LEGAL_NESTED_FIELD TC.
  pose proof is_neutral_cast_by_value _ _ H0 as BY_VALUE.
  assert_PROP (nested_efield e_root efs tts = e /\
               LR_of_type t_root_from_e = lr /\
               legal_nested_efield t_root_from_e e_root gfs_from_e tts lr = true /\
               nested_field_type t_root_from_e gfs_from_e = typeof e).
  Focus 1. {
    erewrite (local2ptree_soundness P Q R) by eauto.
    simpl app.
    apply (msubst_efield_denote_eq P _ _ nil R)  in EVAL_EFIELD.
    eapply derives_trans; [apply andp_left2, EVAL_EFIELD |].
    intro rho; simpl; unfold local, lift1; unfold_lift.
    apply prop_derives; intros.
    pose proof compute_nested_efield_lemma _ rho BY_VALUE.
    rewrite COMPUTE_NESTED_EFIELD in H3; apply H3; auto.
  } Unfocus.
  destruct H2 as [NESTED_EFIELD [LR [LEGAL_NESTED_EFIELD TYPEOF]]].
  rewrite <- TYPEOF in BY_VALUE.
  assert_PROP (field_compatible t_root gfs0 p).
  Focus 1. {
    rewrite <- (corable_sepcon_TT (prop _)) by auto.
    eapply nth_error_SEP_sepcon_TT'; [| eassumption].
    apply andp_left2.
    apply andp_left2.
    apply andp_left2.
    rewrite field_at_compatible'.
    go_lowerx.
    normalize.
  } Unfocus.
  rename H2 into FIELD_COMPATIBLE.
  assert_PROP (legal_nested_field (nested_field_type t_root gfs0) gfs1); auto.
  clear LEGAL_NESTED_FIELD; rename H2 into LEGAL_NESTED_FIELD.
  eapply field_compatible_app_inv' in FIELD_COMPATIBLE; [| exact LEGAL_NESTED_FIELD].
  rewrite <- GFS in FIELD_COMPATIBLE.
  rewrite <- NESTED_EFIELD.
  apply field_address_gen_fact in FIELD_ADD_GEN.
  destruct FIELD_ADD_GEN as [FIELD_ADD_EQ [TYPE_EQ FIELD_COMPATIBLE_E]].
  specialize (FIELD_COMPATIBLE_E FIELD_COMPATIBLE).
  pose proof nested_efield_facts Delta _ _ efs _ _ _ _ FIELD_COMPATIBLE_E LR LEGAL_NESTED_EFIELD BY_VALUE as DERIVES.
  apply (derives_trans (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)))) in DERIVES.
  Focus 2. {
    rewrite (andp_comm _ (local (efield_denote _ _))), <- !andp_assoc.
    rewrite (add_andp _ _ TC).
    rewrite LR.
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_left1.
    erewrite (local2ptree_soundness P Q R) by eauto.
    apply andp_left2.
    simpl app.
    apply andp_right.
    + apply (msubst_efield_denote_eq P _ _ nil R) in EVAL_EFIELD; auto.
    + apply (msubst_eval_LR_eq P _ _ nil R) in EVAL_ROOT; auto.
  } Unfocus.
  eapply semax_SC_field_load_to_use.
  1: rewrite NESTED_EFIELD, <- TYPEOF, TYPE_EQ; reflexivity.
  1: eassumption.
  1: rewrite <- TYPE_EQ, TYPEOF; eassumption.
  1: rewrite <- TYPE_EQ, TYPEOF; eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  + rewrite <- FIELD_ADD_EQ.
    eapply derives_trans; [exact DERIVES | solve_andp].
  + apply andp_right.
    - eapply derives_trans; [exact DERIVES | solve_andp].
    - rewrite <- TYPE_EQ, TYPEOF.
      rewrite (add_andp _ _ TC); solve_andp.
Qed.

Lemma semax_PTree_field_load_with_hint:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) t
      T1 T2 p_from_e
      (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
      (v_val : val) (v_reptype : reptype (nested_field_type t_root gfs0)),
      local2ptree Q = (T1, T2, nil, nil) ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      type_is_volatile (typeof e) = false ->
      msubst_eval_lvalue T1 T2 e = Some p_from_e ->
      p_from_e = field_address t_root gfs p ->
      typeof e = nested_field_type t_root gfs ->
      nth_error R n = Some (field_at sh t_root gfs0 v_reptype p) /\
      gfs = gfs1 ++ gfs0 ->
      readable_share sh ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v_reptype) v_val ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) && local (`(tc_val (typeof e) v_val)) ->
      @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id e)
        (normal_ret_assert
          (PROPx P
            (LOCALx (temp id v_val :: remove_localdef_temp id Q)
              (SEPx R)))).
Proof.
  intros ? ? ? ? ? ? ? ? ?
         ? ? ? ?
         ? ? ? ? ?
         ? ?
         LOCAL2PTREE ? ? ? EVAL_L FIELD_ADD TYPE_EQ [NTH GFS] SH JMEQ TC.
  eapply semax_SC_field_load_to_use.
  1: eassumption.
  1: eassumption.
  1: rewrite <- TYPE_EQ; eassumption.
  1: rewrite <- TYPE_EQ; eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  2: rewrite <- TYPE_EQ; eassumption.
  rewrite <- FIELD_ADD.
  erewrite (local2ptree_soundness P Q R) by eassumption.
  simpl app.
  apply andp_left2. apply msubst_eval_lvalue_eq; auto.
Qed.

Lemma semax_PTree_field_cast_load_no_hint:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) t
      T1 T2 e_root (efs: list efield) (tts: list type) lr
      t_root_from_e gfs_from_e p_from_e
      (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
      (v : val) (v' : reptype (nested_field_type t_root gfs0)),
      local2ptree Q = (T1, T2, nil, nil) ->
      compute_nested_efield e = (e_root, efs, tts, lr) ->
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof e) = true ->
      type_is_volatile (typeof e) = false ->
      classify_cast (typeof e) t <> cast_case_p2bool ->
      msubst_eval_LR T1 T2 e_root lr = Some p_from_e ->
      msubst_efield_denote T1 T2 efs gfs_from_e ->
      compute_root_type (typeof e_root) lr t_root_from_e ->
      field_address_gen (t_root_from_e, gfs_from_e, p_from_e) (t_root, gfs, p) ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) /\
      gfs = gfs1 ++ gfs0 ->
      readable_share sh ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        !! (legal_nested_field (nested_field_type t_root gfs0) gfs1) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e_root lr) &&
        local `(tc_val t (eval_cast (typeof e) t v)) &&
         (tc_efield Delta efs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast e t))
          (normal_ret_assert
            (PROPx P
              (LOCALx (temp id (eval_cast (typeof e) t v) :: remove_localdef_temp id Q)
                (SEPx R)))).
Proof.
  intros ? ? ? ? ? ? ? ? ? ?
         ? ? ? ? ? ?
         ? ? ?
         ? ? ? ? ?
         ? ?
         LOCAL2PTREE COMPUTE_NESTED_EFIELD ? BY_VALUE ? ? EVAL_ROOT EVAL_EFIELD ROOT_TYPE
         FIELD_ADD_GEN [NTH GFS] SH JMEQ LEGAL_NESTED_FIELD TC.
  assert_PROP (nested_efield e_root efs tts = e /\
               LR_of_type t_root_from_e = lr /\
               legal_nested_efield t_root_from_e e_root gfs_from_e tts lr = true /\
               nested_field_type t_root_from_e gfs_from_e = typeof e).
  Focus 1. {
    erewrite (local2ptree_soundness P Q R) by eauto.
    simpl app.
    apply (msubst_efield_denote_eq P _ _ nil R)  in EVAL_EFIELD.
    eapply derives_trans; [apply andp_left2, EVAL_EFIELD |].
    intro rho; simpl; unfold local, lift1; unfold_lift.
    apply prop_derives; intros.
    pose proof compute_nested_efield_lemma _ rho BY_VALUE.
    rewrite COMPUTE_NESTED_EFIELD in H3; apply H3; auto.
  } Unfocus.
  destruct H2 as [NESTED_EFIELD [LR [LEGAL_NESTED_EFIELD TYPEOF]]].
  rewrite <- TYPEOF in BY_VALUE.
  assert_PROP (field_compatible t_root gfs0 p).
  Focus 1. {
    rewrite <- (corable_sepcon_TT (prop _)) by auto.
    eapply nth_error_SEP_sepcon_TT'; [| eassumption].
    apply andp_left2.
    apply andp_left2.
    apply andp_left2.
    rewrite field_at_compatible'.
    go_lowerx.
    normalize.
  } Unfocus.
  rename H2 into FIELD_COMPATIBLE.
  assert_PROP (legal_nested_field (nested_field_type t_root gfs0) gfs1); auto.
  clear LEGAL_NESTED_FIELD; rename H2 into LEGAL_NESTED_FIELD.
  eapply field_compatible_app_inv' in FIELD_COMPATIBLE; [| exact LEGAL_NESTED_FIELD].
  rewrite <- GFS in FIELD_COMPATIBLE.
  rewrite <- NESTED_EFIELD.
  apply field_address_gen_fact in FIELD_ADD_GEN.
  destruct FIELD_ADD_GEN as [FIELD_ADD_EQ [TYPE_EQ FIELD_COMPATIBLE_E]].
  specialize (FIELD_COMPATIBLE_E FIELD_COMPATIBLE).
  pose proof nested_efield_facts Delta _ _ efs _ _ _ _ FIELD_COMPATIBLE_E LR LEGAL_NESTED_EFIELD BY_VALUE as DERIVES.
  apply (derives_trans (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)))) in DERIVES.
  Focus 2. {
    rewrite (andp_comm _ (local (efield_denote _ _))), <- !andp_assoc.
    rewrite (add_andp _ _ TC).
    rewrite LR.
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_left1.
    erewrite (local2ptree_soundness P Q R) by eauto.
    apply andp_left2.
    simpl app.
    apply andp_right.
    + apply (msubst_efield_denote_eq P _ _ nil R) in EVAL_EFIELD; auto.
    + apply (msubst_eval_LR_eq P _ _ nil R) in EVAL_ROOT; auto.
  } Unfocus.
  rewrite NESTED_EFIELD. rewrite <- TYPEOF, TYPE_EQ.
  eapply semax_SC_field_cast_load_to_use.
  1: rewrite <- TYPEOF, TYPE_EQ; reflexivity.
  1: eassumption.
  1: rewrite <- TYPE_EQ; eassumption.
  1: rewrite <- TYPE_EQ, TYPEOF; eassumption.
  1: rewrite <- TYPE_EQ, TYPEOF; eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  + rewrite <- FIELD_ADD_EQ.
    eapply derives_trans; [exact DERIVES | rewrite NESTED_EFIELD; solve_andp].
  + apply andp_right.
    - eapply derives_trans; [exact DERIVES | rewrite NESTED_EFIELD; solve_andp].
    - rewrite <- TYPE_EQ, TYPEOF.
      rewrite (add_andp _ _ TC); solve_andp.
Qed.

Lemma semax_PTree_field_cast_load_with_hint:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) t
      T1 T2 p_from_e
      (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
      (v_val : val) (v_reptype : reptype (nested_field_type t_root gfs0)),
      local2ptree Q = (T1, T2, nil, nil) ->
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof e) = true ->
      type_is_volatile (typeof e) = false ->
      classify_cast (typeof e) t <> cast_case_p2bool ->
      msubst_eval_lvalue T1 T2 e = Some p_from_e ->
      p_from_e = field_address t_root gfs p ->
      typeof e = nested_field_type t_root gfs ->
      nth_error R n = Some (field_at sh t_root gfs0 v_reptype p) /\
      gfs = gfs1 ++ gfs0 ->
      readable_share sh ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v_reptype) v_val ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) && local (`(tc_val t (eval_cast (typeof e) t v_val))) ->
      @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast e t))
        (normal_ret_assert
          (PROPx P
            (LOCALx (temp id (eval_cast (typeof e) t v_val) :: remove_localdef_temp id Q)
              (SEPx R)))).
Proof.
  intros ? ? ? ? ? ? ? ? ?
         ? ? ? ?
         ? ? ? ? ?
         ? ?
         LOCAL2PTREE ? ? ? ? EVAL_L FIELD_ADD TYPE_EQ [NTH GFS] SH JMEQ TC.
  rewrite TYPE_EQ.
  eapply semax_SC_field_cast_load_to_use.
  1: eassumption.
  1: eassumption.
  1: rewrite <- TYPE_EQ; eassumption.
  1: rewrite <- TYPE_EQ; eassumption.
  1: rewrite <- TYPE_EQ; eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  2: rewrite <- TYPE_EQ; eassumption.
  rewrite <- FIELD_ADD.
  erewrite (local2ptree_soundness P Q R) by eassumption.
  simpl app.
  apply andp_left2. apply msubst_eval_lvalue_eq; auto.
Qed.

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

End SEMAX_PTREE.

Ltac unify_var_or_evar name val :=
  let E := fresh "E" in assert (name = val) as E by (try subst name; reflexivity); clear E.

Ltac sc_try_instantiate P Q R R0 gfs a sh t_root gfs0 v n i H SH GFS TY V A :=
  let E := fresh "E" in
  assert (R0 = (field_at sh t_root gfs0 v a)) as E;
  [ unify_var_or_evar gfs0 GFS;
    unify_var_or_evar t_root TY;
    unify_var_or_evar sh SH;
    unify_var_or_evar v V;
    unify_var_or_evar a A;
    try unfold sh, t_root, gfs0, v, a;
    unfold data_at_;
    unfold data_at;
    unify GFS (skipn (length gfs - length GFS) gfs);
    simpl skipn; try subst gfs;
    try unfold field_at_;
    generalize V;
    intro;
    solve [ rewrite <- ?field_at_offset_zero; reflexivity ] (* TODO: this line may be problematic. Because the left side of E may be not same to R0 now (although equal) *)
  | (pose i as n || unify_var_or_evar i n);
    assert (nth_error R n = Some R0) as H by reflexivity;
    clear E ].

Ltac sc_new_instantiate P Q R Rnow gfs p sh t_root gfs0 v n i H :=
  match Rnow with
  | ?R0 :: ?Rnow' =>
    match R0 with
    | data_at ?SH ?TY ?V ?A => 
      sc_try_instantiate P Q R R0 gfs p sh t_root gfs0 v n i H SH (@nil gfield) TY V A
    | data_at_ ?SH ?TY ?A => 
      sc_try_instantiate P Q R R0 gfs p sh t_root gfs0 v n i H SH (@nil gfield) TY
      (default_val (nested_field_type TY nil)) A
    | field_at ?SH ?TY ?GFS ?V ?A =>
      sc_try_instantiate P Q R R0 gfs p sh t_root gfs0 v n i H SH GFS TY V A
    | field_at_ ?SH ?TY ?GFS ?A =>
      sc_try_instantiate P Q R R0 gfs p sh t_root gfs0 v n i H SH GFS TY
      (default_val (nested_field_type TY GFS)) A
    | _ => sc_new_instantiate P Q R Rnow' gfs p sh t_root gfs0 v n (S i) H
    end
  end.

(* simplifies a list expression into [e1; e2; ...] form without simplifying its elements *)
Ltac eval_list l :=
  let l' := eval hnf in l in lazymatch l' with
  | ?h :: ?tl => let tl' := eval_list tl in constr:(h :: tl')
  | (@nil ?T) => constr:(@nil T)
  end.

Ltac prove_gfs_suffix gfs gfs0 gfs1 :=
  let len := fresh "len" in
  let gfs1' := eval_list (firstn ((length gfs - length gfs0)%nat) gfs) in
  unify_var_or_evar gfs1 gfs1';
  reflexivity.

Ltac search_field_at_in_SEP :=
match goal with
| |- nth_error ?R ?n = Some (field_at ?sh ?t_root ?gfs0 ?v ?p) /\
     ?gfs = ?gfs1 ++ ?gfs0 =>
  let H := fresh "H" in
  sc_new_instantiate (@nil Prop) (@nil localdef) R R
                     gfs p sh t_root gfs0 v n 0%nat H;
  split; [exact H | prove_gfs_suffix gfs gfs0 gfs1]
end.

Lemma quick_derives_right:
  forall P Q : environ -> mpred,
   TT |-- Q -> P |-- Q.
Proof.
intros. eapply derives_trans; try eassumption; auto.
Qed.

Ltac quick_typecheck3 :=
 clear;
 repeat match goal with
 | H := _ |- _ => clear H
 | H : _ |- _ => clear H
 end;
 apply quick_derives_right; clear; go_lowerx; intros;
 clear; repeat apply andp_right; auto; fail.

Ltac default_entailer_for_load_tac :=
  repeat match goal with H := _ |- _ => clear H end;
  try quick_typecheck3;
  unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
  try solve [entailer!].

Ltac entailer_for_load_tac := default_entailer_for_load_tac.

Ltac load_tac_with_hint LOCAL2PTREE :=  
  eapply semax_PTree_field_load_with_hint;
  [ exact LOCAL2PTREE
  | reflexivity
  | reflexivity
  | reflexivity
  | solve_msubst_eval_lvalue
  | eassumption (* This line can fail. If it does not, the following should not fail. *)
  | (reflexivity                            || fail 1000 "unexpected failure in load_tac_with_hint."
                                                         "The hint does not type match")
  | (search_field_at_in_SEP                 || fail 1000 "unexpected failure in load_tac_with_hint."
                                                         "Required field_at does not exists in SEP")
  | (auto                                   || fail 1000 "unexpected failure in load_tac_with_hint."
                                                         "Cannot prove readable_share")
  | first [solve_load_rule_evaluation        | fail 1000 "unexpected failure in load_tac_with_hint."
                                                         "unexpected failure in generating loaded value"]
  | first [entailer_for_load_tac             | fail 1000 "unexpected failure in load_tac_with_hint."
                                                         "unexpected failure in entailer_for_load_tac"]
  ].

Ltac load_tac_no_hint LOCAL2PTREE :=
  eapply semax_PTree_field_load_no_hint;
  [ exact LOCAL2PTREE
  | reflexivity (* compute_nested_efield *)
  | reflexivity
  | reflexivity
  | reflexivity
  | solve_msubst_eval_LR
  | solve_msubst_efield_denote
  | econstructor
  | solve_field_address_gen
  | search_field_at_in_SEP (* This line can fail. If it does not, the following should not fail. *)
  | (auto                                   || fail 1000 "unexpected failure in load_tac_no_hint."
                                                         "Cannot prove readable_share")
  | first [solve_load_rule_evaluation        | fail 1000 "unexpected failure in load_tac_no_hint."
                                                         "unexpected failure in generating loaded value"]
  | first [solve_legal_nested_field_in_entailment
                                             | fail 1000 "unexpected failure in load_tac_no_hint."
                                                         "unexpected failure in solve_legal_nested_field_in_entailment"]
  | first [entailer_for_load_tac             | fail 1000 "unexpected failure in load_tac_no_hint."
                                                         "unexpected failure in entailer_for_load_tac"]
  ].

Ltac load_tac :=
  match goal with
  | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
    let T1 := fresh "T1" in evar (T1: PTree.t val);
    let T2 := fresh "T2" in evar (T2: PTree.t vardesc);
    let LOCAL2PTREE := fresh "LOCAL2PTREE" in
    assert (local2ptree Q = (T1, T2, nil, nil)) as LOCAL2PTREE;
    [subst T1 T2; prove_local2ptree |];
    first [ load_tac_with_hint LOCAL2PTREE | load_tac_no_hint LOCAL2PTREE | hint_msg LOCAL2PTREE e];
    clear T1 T2 LOCAL2PTREE
  end.

Ltac cast_load_tac_with_hint LOCAL2PTREE :=  
  eapply semax_PTree_field_cast_load_with_hint;
  [ exact LOCAL2PTREE
  | reflexivity
  | reflexivity
  | reflexivity
  | now (clear; let H := fresh in intro H; inversion H)
  | solve_msubst_eval_lvalue
  | eassumption (* This line can fail. If it does not, the following should not fail. *)
  | (reflexivity                            || fail 1000 "unexpected failure in cast_load_tac_with_hint."
                                                         "The hint does not type match")
  | (search_field_at_in_SEP                 || fail 1000 "unexpected failure in cast)load_tac_with_hint."
                                                         "Required field_at does not exists in SEP")
  | (auto                                   || fail 1000 "unexpected failure in load_tac_with_hint."
                                                         "Cannot prove readable_share")
  | first [solve_load_rule_evaluation        | fail 1000 "unexpected failure in cast_load_tac_with_hint."
                                                         "unexpected failure in generating loaded value"]
  | first [entailer_for_load_tac             | fail 1000 "unexpected failure in cast_load_tac_with_hint."
                                                         "unexpected failure in entailer_for_load_tac"]
  ].

Ltac cast_load_tac_no_hint LOCAL2PTREE :=
  eapply semax_PTree_field_cast_load_no_hint;
  [ exact LOCAL2PTREE
  | reflexivity (* compute_nested_efield *)
  | reflexivity
  | reflexivity
  | reflexivity
  | now (clear; let H := fresh in intro H; inversion H)
  | solve_msubst_eval_LR
  | solve_msubst_efield_denote
  | econstructor
  | solve_field_address_gen
  | search_field_at_in_SEP (* This line can fail. If it does not, the following should not fail. *)
  | (auto                                   || fail 1000 "unexpected failure in cast_load_tac_no_hint."
                                                         "Cannot prove readable_share")
  | first [solve_load_rule_evaluation        | fail 1000 "unexpected failure in cast_load_tac_no_hint."
                                                         "unexpected failure in generating loaded value"]
  | first [solve_legal_nested_field_in_entailment
                                             | fail 1000 "unexpected failure in cast_load_tac_no_hint."
                                                         "unexpected failure in solve_legal_nested_field_in_entailment"]
  | first [entailer_for_load_tac             | fail 1000 "unexpected failure in cast_load_tac_no_hint."
                                                         "unexpected failure in entailer_for_load_tac"]
  ].

Ltac cast_load_tac :=
  match goal with
  | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ (Ecast ?e _)) _ =>
    let T1 := fresh "T1" in evar (T1: PTree.t val);
    let T2 := fresh "T2" in evar (T2: PTree.t vardesc);
    let LOCAL2PTREE := fresh "LOCAL2PTREE" in
    assert (local2ptree Q = (T1, T2, nil, nil)) as LOCAL2PTREE;
    [subst T1 T2; prove_local2ptree |];
    first [ cast_load_tac_with_hint LOCAL2PTREE | cast_load_tac_no_hint LOCAL2PTREE | hint_msg LOCAL2PTREE e];
    clear T1 T2 LOCAL2PTREE
  end.

