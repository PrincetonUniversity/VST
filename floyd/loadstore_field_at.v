Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.loadstore_mapsto.

Import LiftNotation.
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

Lemma access_mode_by_value':
  forall t ch, access_mode t = By_value ch -> type_is_by_value t = true.
Proof.
intros.
destruct t; inv H; auto.
Qed.

Lemma semax_store_nth_ram_field_at_union_hack:
  forall {Espec: OracleKind} {cs: compspecs} n Delta sh P Q R e1 e2 Pre Post
    t_root gfs gfs' ch ch' (p v_val v_val': val) (v_reptype: reptype (nested_field_type t_root gfs')),
    typeof e1 = nested_field_type t_root gfs ->
    access_mode (nested_field_type t_root gfs) = By_value ch ->
    access_mode (nested_field_type t_root gfs') = By_value ch' ->
    (numeric_type (nested_field_type t_root gfs) && numeric_type (nested_field_type t_root gfs'))%bool = true ->
    decode_encode_val_ok ch ch' ->
    field_address t_root gfs p = field_address t_root gfs' p ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    type_is_volatile (nested_field_type t_root gfs') = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq v_val) (eval_expr (Ecast e2 (nested_field_type t_root gfs)))) ->
    decode_encode_val v_val ch ch' v_val' ->
    JMeq v_val' v_reptype ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    Pre |-- (field_at_ sh t_root gfs p) * (field_at sh t_root gfs' v_reptype p -* Post) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && (tc_expr Delta (Ecast e2 (nested_field_type t_root gfs))) ->
    semax Delta
     (|> PROPx P (LOCALx Q (SEPx R)))
     (Sassign e1 e2)
     (normal_ret_assert
        (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros.
  assert (H15: sizeof (nested_field_type t_root gfs) = sizeof (nested_field_type t_root gfs')). {
    clear - H0 H1 H3.
    apply semax_straight.decode_encode_val_size in H3.
    unfold sizeof; erewrite !size_chunk_sizeof; eauto.
  }
  eapply semax_store_nth_ram_union_hack.
  eassumption. eassumption.  eassumption. eassumption. eassumption.
  eassumption. eassumption. eassumption. eassumption. eassumption. 2: auto.
  eapply RAMIF_PLAIN.trans; [exact H13 |].
  eapply derives_trans.
  apply prop_and_same_derives; apply field_at__local_facts.
  apply derives_extract_prop; intro FC.
  assert (FC1: field_compatible  (nested_field_type t_root gfs) nil (offset_val (nested_field_offset t_root gfs) p)).
    apply field_compatible_nested_field; auto.
  assert (FC1': field_compatible  (nested_field_type t_root gfs') nil (offset_val (nested_field_offset t_root gfs') p)).
    apply field_compatible_nested_field.
    clear - H4 FC. unfold field_address in *. rewrite if_true in H4 by auto.
    if_tac in H4; auto.
    destruct FC as [? _]. destruct p; try contradiction. inv H4.
  replace  (offset_val (nested_field_offset t_root gfs) p) with (field_address t_root gfs p) in FC1
      by (unfold field_address; rewrite if_true; auto).
  replace  (offset_val (nested_field_offset t_root gfs') p) with (field_address t_root gfs' p) in FC1'.
  2:{ clear - H4 FC. unfold field_address in *. rewrite if_true in H4 by auto.
       if_tac in H4; auto. destruct FC as [? _]. destruct p; try contradiction. inv H4.
   }
  rewrite <- memory_block_mapsto_; auto.
  2: eapply access_mode_by_value'; eassumption.
  2: destruct FC1 as [_ [_ [? _]]]; auto. 
  2: destruct FC1 as [_ [_ [_ [? _]]]]; auto. 
  rewrite H15. rewrite H4. rewrite memory_block_mapsto_; auto.
  2: eapply access_mode_by_value'; eassumption.
  2: destruct FC1' as [_ [_ [? _]]]; auto.   
  2: destruct FC1' as [_ [_ [_ [? _]]]]; auto. 
  rewrite field_at__memory_block.
  rewrite H4.
  rewrite H15.
  rewrite <- field_at__memory_block.
 eapply derives_trans.
  apply mapsto_field_at_ramify; try eassumption; auto.
  eapply access_mode_by_value'; eassumption.
  apply JMeq_sym; apply by_value_default_val; auto.
  eapply access_mode_by_value'; eassumption.
 apply sepcon_derives; auto.
  apply andp_right; auto.
  apply derives_refl.
  apply derives_refl.
Qed.


End LOADSTORE_FIELD_AT.
