Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.mapsto_memory_block.

Local Open Scope logic.

(***************************************

Load/store lemmas about mapsto:
  semax_load_37
  semax_load_37'
  semax_cast_load_37
  semax_cast_load_37'

***************************************)


Definition semax_load_37 := @semax_load.

Lemma semax_load_37' :
  forall {Espec: OracleKind}{cs: compspecs} ,
forall (Delta: tycontext) sh id P Q R e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
          (tc_lvalue Delta e1) &&
         local (`(tc_val (typeof e1) v2)) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `(v2) * TT) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id e1)
       (normal_ret_assert
         (PROPx P
           (LOCALx (temp id v2 :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  rename H1 into H_READABLE; rename H2 into H1.
  eapply semax_pre_post'; [ | | apply semax_load with sh t2; auto].
  + instantiate (1:= PROPx (tc_val (typeof e1) v2 :: P) (LOCALx Q (SEPx R))).
    apply later_left2.
    match goal with |- ?A |-- _ => rewrite <- (andp_dup A) end.
    eapply derives_trans.
    apply andp_derives; [apply derives_refl | apply H1].
    clear H.
    go_lowerx.
    autorewrite with gather_prop.
    apply derives_extract_prop; intro.
    apply andp_right.
    apply prop_right; repeat split; try eassumption.
    apply andp_right.
    apply andp_left2. apply andp_left1; auto.
    apply andp_left1; auto.
  + intros. apply andp_left2.
    eapply derives_trans.
    - apply andp_right.
      * apply exp_left; intros.
        apply andp_left2.
        rewrite <- insert_prop.
        autorewrite with subst.
        apply andp_left1, derives_refl.
      * apply exp_derives; intro old.
        rewrite <- insert_prop.
        autorewrite with subst.
        apply andp_derives; [| apply andp_left2, derives_refl].
        autorewrite with subst.
        apply derives_refl.
    - apply derives_extract_prop; intro.
      rewrite <- exp_andp2.
      rewrite <- insert_local.
      apply andp_derives; auto.
      * simpl; unfold local, lift1; unfold_lift.
        intros; apply prop_derives.
        intros; split; [congruence |].
        intro; clear H3; subst; revert H2. apply tc_val_Vundef.
      * apply remove_localdef_temp_PROP.
  + eapply derives_trans; [eapply derives_trans; [| apply H1] | clear H1].
    - apply andp_derives; auto.
      rewrite <- insert_prop.
      apply andp_left2; auto.
    - apply andp_left2. auto.
Qed.

Definition semax_cast_load_37 := @semax_cast_load.

Lemma semax_cast_load_37' :
  forall {Espec: OracleKind}{cs: compspecs} ,
forall (Delta: tycontext) sh id P Q R e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
     cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
          (tc_lvalue Delta e1) &&
         local (`(tc_val t1 (eval_cast (typeof e1) t1 v2))) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `(v2) * TT) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast (typeof e1) t1 v2) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros until 1. intros HCAST H_READABLE H1. pose proof I.
  eapply semax_pre_post'; [ | | apply semax_cast_load with (sh0:=sh)(v3:= v2); auto].
  + instantiate (1:= PROPx (tc_val t1 (force_val (sem_cast (typeof e1) t1 v2)) :: P) (LOCALx Q (SEPx R))).
    apply later_left2.
    match goal with |- ?A |-- _ => rewrite <- (andp_dup A) end.
    eapply derives_trans.
    apply andp_derives; [apply derives_refl | apply H1].
    clear H1.
    go_lowerx.
    autorewrite with gather_prop.
    apply derives_extract_prop; intro.
    apply andp_right.
    apply prop_right; repeat split; eassumption.
    apply andp_right.
    apply andp_left2. apply andp_left1; auto.
    apply andp_left1; auto.
  + intros. apply andp_left2.
    eapply derives_trans.
    - apply andp_right.
      * apply exp_left; intros.
        apply andp_left2.
        rewrite <- insert_prop.
        autorewrite with subst.
        apply andp_left1, derives_refl.
      * apply exp_derives; intro old.
        rewrite <- insert_prop.
        autorewrite with subst.
        apply andp_derives; [| apply andp_left2, derives_refl].
        autorewrite with subst.
        apply derives_refl.
    - apply derives_extract_prop; intro.
      rewrite <- exp_andp2.
      rewrite <- insert_local.
      apply andp_derives; auto.
      * simpl; unfold local, lift1; unfold_lift.
        intros; apply prop_derives.
        unfold force_val1 in *.
        intros; split; [congruence |].
        intro; clear H3; revert H2; rewrite H4. apply tc_val_Vundef.
      * apply remove_localdef_temp_PROP.
  + eapply derives_trans; [eapply derives_trans; [| apply H1] | clear H1].
    - apply andp_derives; auto.
      rewrite <- insert_prop.
      apply andp_left2; auto.
    - apply andp_left2. auto.
Qed.

(***************************************

Load/store lemmas about mapsto:
  semax_load_nth_ram.
  semax_cast_load_nth_ram.
  semax_store_nth_ram.

***************************************)

Lemma semax_load_nth_ram :
  forall {Espec: OracleKind}{cs: compspecs} n (Delta: tycontext) sh id P Q R e1 Pre t1 t2 v p,
    typeof e1 = t1 ->
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq p) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
    readable_share sh ->
    Pre |-- mapsto sh t1 p v * TT ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      (tc_lvalue Delta e1) && local (`(tc_val t1 v)) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id e1)
      (normal_ret_assert
         (PROPx P
           (LOCALx (temp id v :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  subst; eapply semax_load_37'; eauto.
  apply andp_right; auto.
  rewrite (add_andp _ _ H2).
  rewrite andp_comm. rewrite <- andp_assoc.
  erewrite SEP_nth_isolate, <- insert_SEP by eauto.
  rewrite <- local_lift2_and.
  rewrite <- local_sepcon_assoc1.
  eapply derives_trans.
  + apply sepcon_derives; [| apply derives_refl].
    instantiate (1 := `(mapsto sh (typeof e1)) (eval_lvalue e1) `(v) * `TT).
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
  + rewrite sepcon_assoc.
    apply sepcon_derives; auto.
Qed.

Lemma semax_cast_load_nth_ram :
  forall {Espec: OracleKind}{cs: compspecs} n (Delta: tycontext) sh id P Q R e1 Pre t1 t2 v p,
    typeof e1 = t1 ->
    typeof_temp Delta id = Some t2 ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      local (`(eq p) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
    cast_pointer_to_bool t1 t2 = false ->
    readable_share sh ->
    Pre |-- mapsto sh t1 p v * TT ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && local (`(tc_val t2 (eval_cast t1 t2 v))) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
     (Sset id (Ecast e1 t2))
     (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast t1 t2 v) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  subst; eapply semax_cast_load_37'; eauto.
  apply andp_right; auto.
  rewrite (add_andp _ _ H1).
  rewrite andp_comm. rewrite <- andp_assoc.
  erewrite SEP_nth_isolate, <- insert_SEP by eauto.
  rewrite <- local_lift2_and.
  rewrite <- local_sepcon_assoc1.
  eapply derives_trans.
  + apply sepcon_derives; [| apply derives_refl].
    instantiate (1 := `(mapsto sh (typeof e1)) (eval_lvalue e1) `(v) * `TT).
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
  + rewrite sepcon_assoc.
    apply sepcon_derives; auto.
Qed.

Lemma semax_store_nth_ram:
  forall {Espec: OracleKind} {cs: compspecs} n Delta P Q R e1 e2 Pre Post p v sh t1,
    typeof e1 = t1 ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq p) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq v) (eval_expr (Ecast e2 t1))) ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    Pre |-- mapsto_ sh t1 p * (mapsto sh t1 p v -* Post) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && (tc_expr Delta (Ecast e2 t1)) ->
    semax Delta
     (|> PROPx P (LOCALx Q (SEPx R)))
     (Sassign e1 e2)
     (normal_ret_assert
        (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros.
  eapply semax_pre_simple; [| eapply semax_post'; [| apply semax_store; eauto]].
  + apply later_left2.
    apply andp_right;  [subst; auto |].
    simpl lifted.
    change  (@LiftNatDed environ mpred Nveric)
      with (@LiftNatDed' mpred Nveric).
    rewrite (add_andp _ _ H0).
    rewrite (add_andp _ _ H1).
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    rewrite !(andp_comm _ (local _)).
    rewrite <- (andp_dup (local (`(eq p) (eval_lvalue e1)))), andp_assoc.
    do 3 rewrite <- local_sepcon_assoc2.  rewrite <- local_sepcon_assoc1.
    eapply derives_trans.
    - apply sepcon_derives; [| apply derives_refl].
      instantiate (1 := `(mapsto_ sh (typeof e1)) (eval_lvalue e1) * `(mapsto sh t1 p v -* Post)).
      unfold local, lift1; unfold_lift; intro rho; simpl.
      subst t1.
      normalize.
    - rewrite sepcon_assoc.
      apply derives_refl.
  + rewrite <- sepcon_assoc.
    rewrite !local_sepcon_assoc2, <- !local_sepcon_assoc1.
    erewrite SEP_replace_nth_isolate with (Rn' := Post), <- insert_SEP by eauto.
    apply sepcon_derives; auto.
    change (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))
      with (eval_expr (Ecast e2 (typeof e1))).
    Opaque eval_lvalue eval_expr.
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
    Transparent eval_lvalue eval_expr.
    subst t1.
    apply modus_ponens_wand.
Qed.

