Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.

Local Open Scope logic.

Lemma mapsto_force_ptr: forall sh t v v', 
  mapsto sh t (force_ptr v) v' = mapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Lemma isptr_force_ptr: forall v, isptr v -> force_ptr v = v.
Proof. intros. destruct v; inv H; auto. Qed.

Lemma local_andp_lemma:
  forall P Q, P |-- local Q -> P = local Q && P.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
apply andp_left2; auto.
Qed.

Lemma semax_load'':
  forall Espec (Delta : tycontext) (sh : Share.t) (id : positive) (n: nat)
         P Q R (e1 : expr) t1 i2 (v1 v2 : environ -> val),
   typeof e1 = Tpointer t1 noattr ->
   (temp_types Delta) ! id = Some (t1,i2) ->
   type_is_volatile t1 = false ->
   classify_cast t1 t1 = cast_case_neutral ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_expr e1)) ->
    nth_error R n = Some (`(mapsto sh t1) v1 v2) ->
 @semax Espec Delta  
    (|> PROPx P (LOCALx Q (SEPx R)))
    (Sset id (Ederef e1 t1))
    (normal_ret_assert
       (EX old: val, 
        PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) ::
                         map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (replace_nth n R (`(mapsto sh t1) (eval_expr e1) v2))))))).
Proof.
 intros. rename H2 into CLASSIFY.
 eapply semax_pre_post;
  [ | |  apply (semax_load Delta sh id (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) (Ederef e1 t1)
   v2)]; auto.
assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`isptr (eval_expr e1))).
 {clear - H4 H5.
  rewrite (local_andp_lemma _ _ H4).
  clear H4.
  unfold_lift.
  change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local,lift1; intro rho; simpl in *.
  apply derives_extract_prop; intro. unfold_lift in H. rewrite <- H. clear e1 H.
  apply andp_left2. apply andp_left2.
  unfold_lift in H5.
  revert R H5; induction n; destruct R; intros; inv H5; simpl in *; auto.
  rewrite mapsto_isptr.  normalize.
  apply derives_trans with (TT * (!!isptr (v1 rho) && TT)).
  apply sepcon_derives; auto. rewrite andp_TT. auto.
  normalize.
 }
eapply derives_trans; [apply andp_derives; [ apply now_later | apply derives_refl] | ].
rewrite <- later_andp.
apply later_derives.
rewrite insert_local.
repeat apply andp_right.
rewrite (local_andp_lemma _ _ H4).
rewrite (local_andp_lemma _ _ H3).
rewrite (local_andp_lemma _ _ H2).
repeat rewrite <- andp_assoc. apply andp_left1.
{go_lowerx. intro. apply prop_right. unfold tc_lvalue; simpl.
 rewrite H,H1.
 repeat rewrite denote_tc_assert_andp; repeat split; auto.
}
unfold tc_temp_id_load. rewrite H0.
go_lowerx. apply prop_right.
do 2 eexists; split; try reflexivity.
unfold allowedValCast; simpl. rewrite CLASSIFY.
destruct t1; simpl; auto.
rewrite (local_andp_lemma _ _ H4).
simpl typeof; simpl eval_lvalue.
apply derives_trans with 
 (local (`eq v1 (eval_expr e1)) && (`(mapsto sh t1) v1 v2 *
       PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))).
rewrite <- insert_local.
apply andp_derives; auto.
apply andp_left2.
clear - H5.
go_lowerx.
clear - H5; revert R H5; induction n; destruct R; simpl; intros; inv H5.
rewrite emp_sepcon; apply sepcon_derives; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (mapsto _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
go_lowerx.
rewrite mapsto_force_ptr.
rewrite H6; auto.

intros ek vl.
unfold normal_ret_assert.
repeat rewrite exp_andp2.
apply exp_derives; intro old.
simpl typeof; unfold eval_lvalue; fold eval_expr.
autorewrite with subst.
rewrite insert_SEP.
apply andp_left2.
go_lowerx. apply andp_right; try apply prop_right; auto.
rewrite mapsto_force_ptr.
clear - H5.
revert R H5; induction n; destruct R; simpl; intros; auto; inv H5.
apply sepcon_derives; simpl; auto.
rewrite closed_wrt_subst by (auto with closed).
rewrite emp_sepcon; auto.
specialize (IHn _ H0).
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (mapsto _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma semax_store'':
forall Espec (Delta: tycontext) sh t1 n P Q R e1 v1 e2
    (WS: writable_share sh)
    (NONVOL: type_is_volatile t1 = false)
    (TC: typecheck_store (Ederef e1 t1)),
    typeof e1 = Tpointer t1 noattr ->
    nth_error R n = Some (`(mapsto_ sh t1) v1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- local (`eq v1 (eval_expr e1)) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta (Ecast e2 t1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(mapsto sh t1) v1 (`(eval_cast (typeof e2) t1) (eval_expr e2)))))))).
Proof.
intros.
pose proof semax_store.
unfold_lift; unfold_lift in H0.
eapply semax_pre_post; [ | | eapply (H4 Delta (Ederef e1 t1) e2 sh)]; try eassumption.
instantiate (1:=(PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))).
assert (H1': PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_expr e1))).
 {  eapply derives_trans; [ | apply H1].
  apply andp_derives; auto. apply andp_derives; auto. change SEPx with SEPx'; unfold SEPx'.
  unfold fold_right at 2. rewrite sepcon_emp. apply TT_right.
 }
assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`isptr (eval_expr e1))).
  {clear - H1' H0. rename H1' into H4; rename H0 into H5.
   rewrite (local_andp_lemma _ _ H4).
   clear H4.
   go_lowerx. rewrite <- H. clear e1 H.
   unfold_lift in H5.
   revert R H5; induction n; destruct R; intros; inv H5; simpl in *; auto.
   rewrite mapsto__isptr. normalize.
   apply derives_trans with (TT * (!!isptr (v1 rho) && TT)).
   apply sepcon_derives; auto. rewrite andp_TT. auto.
   normalize.
  }
eapply derives_trans; [apply andp_derives; [ apply now_later | apply derives_refl] | ].
rewrite <- later_andp.
apply later_derives.
rewrite insert_local.
rewrite (local_andp_lemma _ _ H1').
rewrite (local_andp_lemma _ _ H2).
rewrite (local_andp_lemma _ _ H3).
rewrite (local_andp_lemma _ _ H5).
go_lowerx.
repeat apply andp_right; try apply prop_right; auto. 
destruct H11.
unfold tc_lvalue. simpl typecheck_lvalue.
repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite H; apply I. rewrite NONVOL; apply I.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
unfold_lift. rewrite isptr_force_ptr by auto. rewrite <- H6.
clear - H0.
revert R H0; induction n; destruct R; simpl; intros; inv H0; auto.
rewrite emp_sepcon; auto. f_equal.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (mapsto_ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.

intros ek vl; unfold normal_ret_assert.
match goal with |- ?A |-- _ => 
  apply derives_trans with (local (`eq v1 (eval_expr e1)) && A) 
end.
apply andp_right; auto. eapply derives_trans; [| apply H1].
rewrite <- insert_local.
rewrite andp_comm.
rewrite insert_SEP.
go_lowerx. subst. rewrite sepcon_emp.
repeat apply andp_right; try apply prop_right; auto.
rewrite insert_SEP.
go_lowerx. subst. unfold_lift. rewrite mapsto_force_ptr.
rewrite <- H5. 
clear - H0. revert R H0; induction n; destruct R; simpl; intros; inv H0.
rewrite emp_sepcon; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (mapsto _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma semax_load_field:
forall Espec (Delta: tycontext) sh id t1 fld P e1 v2 t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
    @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) &&
          (`(field_mapsto sh t1 fld) (eval_lvalue e1) v2 * P)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                  (subst id (`old) 
                    (`(field_mapsto sh t1 fld) (eval_lvalue e1) v2 * P)))).
Proof.
Transparent field_mapsto.
pose proof I.
pose proof I.
intros. rename H5 into CLASSIFY.
rename H3 into TC0; rename H4 into TC2.
subst t1.
rename H2 into TE1.
apply (semax_pre_post
            (|>(local (tc_lvalue Delta (Efield e1 fld t2)) &&
                 local (tc_temp_id_load id (typeof (Efield e1 fld t2)) Delta v2) && 
               (`(mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2 * 
                        ( !!(type_is_volatile t2 = false) &&  P))))
            (normal_ret_assert 
              (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
              (subst id (`old) (`(mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2  * 
                (!!(type_is_volatile t2 = false) && P))))));
  [ | | apply semax_load].

(* PRECONDITION *)
go_lowerx.
apply later_derives.
apply derives_extract_prop; intro.
unfold field_mapsto; unfold_lift. 
case_eq (eval_lvalue e1 rho); intros; 
 try (rewrite FF_sepcon; apply FF_left).
rewrite H1.
rewrite field_offset_unroll. rewrite <- TC2.
case_eq (field_offset fld fields); intros; 
 try (rewrite FF_sepcon; apply FF_left).
case_eq (access_mode t2); intros;
 try (rewrite FF_sepcon; apply FF_left).
rewrite andp_assoc.
repeat rewrite sepcon_andp_prop'.
  repeat (apply derives_extract_prop; intro).
repeat apply andp_right; try apply prop_right.
unfold tc_lvalue. 
unfold typecheck_lvalue; fold typecheck_lvalue. rewrite H1.
rewrite H8; simpl tc_bool.
rewrite H5. repeat rewrite tc_andp_TT2.
apply H3.
exists t2; exists i2; split; auto.
unfold allowedValCast. rewrite CLASSIFY.
destruct t2; simpl; auto. auto.
unfold mapsto.
repeat rewrite prop_true_andp by auto.
unfold umapsto.
rewrite H6.
unfold eval_field. rewrite H5.
simpl. apply sepcon_derives; auto. apply orp_right1. auto.

(* POSTCONDITION *)
intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives. intro old.
apply andp_derives; auto.
unfold subst. go_lowerx.
rewrite sepcon_andp_prop. apply derives_extract_prop. intro.
unfold mapsto, field_mapsto, umapsto.
rewrite sepcon_andp_prop'. apply derives_extract_prop. intro.
rewrite H1. rewrite <- TC2.
destruct (access_mode t2) eqn:?; 
 try (rewrite FF_sepcon; apply FF_left).
simpl eval_field. unfold always.
rewrite field_offset_unroll. unfold offset_val.
unfold_lift.
destruct (field_offset fld fields);  try (rewrite FF_sepcon; apply FF_left).
destruct (eval_lvalue e1 (env_set rho id old)); try (rewrite FF_sepcon; apply FF_left).
apply sepcon_derives; auto.
repeat apply andp_right; try apply prop_right; auto.
apply orp_left; auto.
apply derives_extract_prop; intro.
rewrite H4 in H3; inv H3.
Qed.

Lemma semax_store_field: 
forall Espec (Delta: tycontext) sh e1 fld P t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (`(field_mapsto_ sh (typeof e1) fld) (eval_lvalue e1) * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (`(field_mapsto sh (typeof e1) fld) (eval_lvalue e1) 
                  (`(eval_cast (typeof e2) t2) (eval_expr e2)) * P)).
Proof.
Transparent field_mapsto.
pose proof I. intros until fields. intro WS.
intros.
rename H0 into TE1.
rename H2 into TCS.
unfold field_mapsto_.

apply semax_pre0 with
 (EX v2: val,
   ((|>(local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
      (lift1(fun v1 : val =>
         match v1 with
         | Vundef => FF
         | Vint _ => FF
         | Vlong _ => FF
         | Vfloat _ => FF
         | Vptr l ofs =>
             match typeof e1 with
             | Tstruct id fList _ =>
                 match
                   field_offset fld
                     (unroll_composite_fields id (typeof e1) fList)
                 with
                 | Errors.OK delta =>
                     match
                       access_mode
                         (type_of_field
                            (unroll_composite_fields id (typeof e1) fList)
                            fld)
                     with
                     | By_value ch =>
                         !!(type_is_volatile
                              (type_of_field
                                 (unroll_composite_fields id (typeof e1)
                                    fList) fld) = false) &&
                         (address_mapsto ch v2 (Share.unrel Share.Lsh sh)
                            (Share.unrel Share.Rsh sh)
                            (l, Int.unsigned (Int.add ofs (Int.repr delta))))
                     | _ => FF
                     end
                 | _ => FF
                 end
             | _ => FF
             end
         end) (eval_lvalue e1) * P))))).
rewrite <- later_exp' by apply Vundef.
apply later_derives.
rewrite <- exp_andp2.
apply andp_derives; auto.
unfold lift1; intro rho; unfold_lift.
simpl sepcon. cbv beta.
case_eq (eval_lvalue e1 rho); intros; try rewrite FF_sepcon; try apply FF_left.
destruct (typeof e1);  try rewrite FF_sepcon; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i0 (Tstruct i0 f a) f));
   try (rewrite FF_sepcon; apply FF_left).
destruct ( access_mode
    (type_of_field (unroll_composite_fields i0 (Tstruct i0 f a) f) fld));
   try (rewrite FF_sepcon; apply FF_left).
rewrite sepcon_andp_prop'. apply derives_extract_prop; intro.
repeat rewrite exp_sepcon1.
simpl.
apply exp_derives; intro v2.
rewrite H0. rewrite prop_true_andp by auto. auto.

apply extract_exists_pre; intro v0.

pose proof (semax_store Delta (Efield e1 fld t2) e2 sh 
               (local (`(tc_val t2) (`(eval_cast (typeof e2) t2) (eval_expr e2))) &&
                 !! (type_is_volatile t2 = false) &&   P)).
simpl typeof in H0. 
eapply semax_pre_post ; [ | | apply H0; auto]; clear H0.
match goal with |- (?A && |> ?B |-- |> ?C) =>
  apply derives_trans with (|> (A && B));
    [rewrite (later_andp A B); apply andp_derives; auto; apply now_later 
    | apply later_derives]
end.

intro rho; unfold lift1; unfold_lift.
 simpl andp; simpl sepcon. cbv beta.
rewrite TE1.
normalize.
unfold mapsto_, umapsto.
case_eq (eval_lvalue e1 rho); intros; try (rewrite FF_sepcon; apply FF_left).
case_eq (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)); intros; try (rewrite FF_sepcon; apply FF_left).
rewrite <- H1.
case_eq (access_mode t2); intros; try (rewrite FF_sepcon; apply FF_left).
simpl eval_lvalue.
unfold lift1. unfold_lift. 
rewrite TE1. rewrite H4; simpl eval_field.
rewrite field_offset_unroll in H5. rewrite H5.
normalize.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl. rewrite TE1.
rewrite H5. rewrite tc_andp_TT2.
rewrite denote_tc_assert_andp.
split; auto. rewrite H7; auto.
apply sepcon_derives; auto.
simpl.
apply orp_right2. apply andp_right; try apply prop_right; auto.
apply exp_right with v0; auto.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl. hnf in H3. simpl in H3.
rewrite denote_tc_assert_andp in H3. destruct H3.
eapply expr_lemmas.typecheck_val_eval_cast; eassumption.

intros ek vl; unfold normal_ret_assert; go_lowerx.
normalize.
apply sepcon_derives; auto.
unfold mapsto, umapsto, field_mapsto.
rewrite TE1.
apply derives_extract_prop; intro.
destruct (access_mode t2) eqn:?; try apply FF_left.
unfold_lift.
unfold eval_field.
rewrite field_offset_unroll.
unfold offset_val, always.
case_eq (field_offset fld fields); intros; try apply FF_left.
case_eq (eval_lvalue e1 rho); intros; try apply FF_left.
rewrite <- H1. rewrite H4.
rewrite Heqm.
repeat apply andp_right; try apply prop_right; auto.
apply orp_left; auto.
apply derives_extract_prop; intro.
rewrite H9 in H4; inv H4.
Opaque field_mapsto.
Qed.

Lemma semax_store_field_mapsto: 
forall Espec (Delta: tycontext) sh e1 fld P v0 t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (`(field_mapsto sh (typeof e1) fld) (eval_lvalue e1) v0 * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (`(field_mapsto sh (typeof e1) fld) (eval_lvalue e1) 
                  (`(eval_cast (typeof e2) t2) (eval_expr e2)) * P)).
Proof.
intros.
eapply semax_pre0; [ | eapply semax_store_field; eassumption].
apply later_derives.
apply andp_derives; auto.
apply sepcon_derives; auto.
go_lowerx. apply field_mapsto_field_mapsto_.
Qed.

Definition force_eq ( x y: val) := force_ptr x = force_ptr y.


Lemma force_force_eq:
  forall v, force_ptr (force_ptr v) = force_ptr v.
Proof. intros. destruct v; reflexivity. Qed.

Lemma force_eq1: forall v w, force_eq v w -> force_eq (force_ptr v) w .
Proof. unfold force_eq; intros; rewrite force_force_eq; auto. Qed.

Lemma force_eq2: forall v w, force_eq v w -> force_eq v (force_ptr w).
Proof. unfold force_eq; intros; rewrite force_force_eq; auto. Qed.

Lemma force_eq0: forall v w, v=w -> force_eq v w.
Proof. intros. subst. reflexivity. Qed.

Ltac force_eq_tac := repeat first [simple apply force_eq1 | simple apply force_eq2];
                                 try apply force_eq0;
                                 first [assumption |  reflexivity].

Lemma semax_load_field''force:
forall Espec (Delta: tycontext) n sh id t1 fld P Q R e1 v1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
     Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
     PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                           |-- local (tc_lvalue Delta e1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`force_eq v1 (eval_lvalue e1)) ->
    nth_error R n = Some (`(field_mapsto sh t1 fld) v1 v2) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (replace_nth n R (`(field_mapsto sh t1 fld) (eval_lvalue e1) v2))))))).
intros. rename H3 into CC.
eapply semax_pre_post;
  [ | |  apply (semax_load_field Espec Delta sh id t1 fld (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) e1
   v2 t2 i2 sid fields)]; auto; try congruence.
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' )
end.
rewrite later_andp; apply andp_derives; auto; apply now_later.
apply later_derives.
rewrite insert_local.
assert (H3: PROPx P (LOCALx Q (SEPx R)) |-- local (`isptr v1)).
clear - H6.
go_lowerx.
unfold_lift in H6.
revert R H6; induction n; destruct R; simpl; intros; inv H6.
rewrite field_mapsto_isptr. clear; normalize.
apply derives_trans with (TT * (!!isptr (v1 rho) && TT)).
apply sepcon_derives; auto. rewrite andp_TT; auto. normalize.
assert (H4':  PROPx P
       (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_lvalue Delta e1)).
eapply derives_trans; [ | apply H4].
clear - H3 H5.
rewrite (local_andp_lemma _ _ H5).
repeat rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
go_lowerx. apply andp_right; auto. 
eapply derives_trans; [ apply H3 |].
unfold local, lift1. apply prop_derives.
unfold_lift;intros. unfold force_eq in H.
rewrite (isptr_force_ptr _ H1) in H. rewrite H in H1.
destruct (eval_lvalue e1 rho); inv H1; simpl; auto.
clear H4.
rewrite (local_andp_lemma _ _ H4').
rewrite (local_andp_lemma _ _ H5).
rewrite <- insert_local.
 rewrite (local_andp_lemma _ _ H3).
go_lowerx.
unfold force_eq in H8.
rewrite <- field_mapsto_force_ptr.
rewrite <- H7.
rewrite isptr_force_ptr by auto.
clear - H6. rename H6 into H5.
clear - H5; revert R H5; induction n; destruct R; simpl; intros; inv H5.
rewrite emp_sepcon; apply sepcon_derives; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (field_mapsto _ _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.

intros ek vl; unfold normal_ret_assert.
repeat rewrite exp_andp2. apply exp_derives; intro old.
autorewrite with subst.
rewrite insert_SEP. go_lowerx.
apply andp_right; try apply prop_right; auto.
clear - H6. rename H6 into H5.
clear - H5; revert R H5; induction n; destruct R; simpl; intros; inv H5.
apply sepcon_derives. apply derives_refl.
rewrite closed_wrt_subst by (auto with closed). rewrite emp_sepcon; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (field_mapsto _ _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.


Lemma semax_load_field'':
forall Espec (Delta: tycontext) n sh id t1 fld P Q R e1 v1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
     Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_lvalue Delta e1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_lvalue e1)) ->
    nth_error R n = Some (`(field_mapsto sh t1 fld) v1 v2) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (replace_nth n R (`(field_mapsto sh t1 fld) (eval_lvalue e1) v2))))))).
Proof.
intros; eapply semax_load_field''force; eauto.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _)). rewrite andp_assoc. rewrite insert_local.
apply andp_left2.
auto.
admit.  (* straightforward *)
Qed.

Lemma semax_load_field_deref'':
forall Espec (Delta: tycontext) n sh id t1 fld P Q R e1 v1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = tptr t1 ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
     Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_expr e1)) ->
    nth_error R n = Some (`(field_mapsto sh t1 fld) v1 v2) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (replace_nth n R (`(field_mapsto sh t1 fld) (eval_expr e1) v2))))))).
Proof.
intros; rename H3 into CC.
eapply semax_pre_post;
  [ | |  apply (semax_load_field Espec Delta sh id t1 fld (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) (Ederef e1 t1)
   v2 t2 i2 sid fields)]; auto; try congruence.
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' )
end.
rewrite later_andp; apply andp_derives; auto; apply now_later.
apply later_derives.
rewrite insert_local.
rewrite (local_andp_lemma _ _ H4).
rewrite (local_andp_lemma _ _ H5).
rewrite <- insert_local.
assert (PROPx P (LOCALx Q (SEPx R)) |-- local (`isptr v1)).
clear - H6.
go_lowerx.
unfold_lift in H6.
revert R H6; induction n; destruct R; simpl; intros; inv H6.
rewrite field_mapsto_isptr. normalize.
apply derives_trans with (TT * (!!isptr (v1 rho) && TT)).
apply sepcon_derives; auto. rewrite andp_TT; auto. normalize.
 rewrite (local_andp_lemma _ _ H3).
go_lowerx. 
repeat apply andp_right; try apply prop_right; auto.
unfold tc_lvalue; simpl.
repeat rewrite denote_tc_assert_andp.
rewrite H0, H. repeat split; simpl; auto.
unfold_lift; rewrite <- H8; apply H10.
repeat rewrite prop_true_andp by auto.
unfold_lift. rewrite field_mapsto_force_ptr.
rewrite <- H8.
clear - H6. rename H6 into H5.
clear - H5; revert R H5; induction n; destruct R; simpl; intros; inv H5.
rewrite emp_sepcon; apply sepcon_derives; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (field_mapsto _ _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.

intros ek vl.
unfold normal_ret_assert.
repeat rewrite exp_andp2; apply exp_derives; intro old.
simpl eval_lvalue.
autorewrite with subst.
rewrite insert_SEP.
go_lowerx.
apply andp_right. apply prop_right; auto.
rewrite field_mapsto_force_ptr.
clear - H6. rename H6 into H5.
clear - H5; revert R H5; induction n; destruct R; simpl; intros; inv H5.
apply sepcon_derives. apply derives_refl.
rewrite closed_wrt_subst by (auto with closed). rewrite emp_sepcon; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (field_mapsto _ _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma semax_store_field'':
forall Espec (Delta: tycontext) n sh t1 fld P Q R e1 v1 e2 t2 R1 sid fields 
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_lvalue Delta e1) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta (Ecast e2 t2)) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- local (`eq v1 (eval_lvalue e1)) ->
    nth_error R n = Some R1 ->
    R1 |-- `(field_mapsto_ sh t1 fld) v1 ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(field_mapsto sh t1 fld) v1 (`(eval_cast (typeof e2) t2) (eval_expr e2)))))))).
Proof.
intros. rename H7 into H6'.
assert (SF := semax_store_field). unfold_lift.
unfold_lift in SF.
subst t1.
specialize (SF Espec Delta sh e1 fld (PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))
   t2 e2 sid fields WS H0 H1 H2).
eapply semax_pre_post; [ | | eapply SF]; try eassumption; clear SF.
eapply derives_trans; [apply andp_derives; [ apply now_later | apply derives_refl] | ].
rewrite <- later_andp.
apply later_derives.
rewrite insert_local.
assert (H1': PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_lvalue e1))).
 {  eapply derives_trans; [ | apply H5].
  apply andp_derives; auto. apply andp_derives; auto. change SEPx with SEPx'; unfold SEPx'.
  unfold fold_right at 2. rewrite sepcon_emp. apply TT_right.
 }
assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`isptr (eval_lvalue e1))).
  {clear - H1' H6 H6'. rename H1' into H4.
  assert (H5: nth n R TT |-- local (`isptr v1)).
    clear - H6 H6'; revert R H6; induction n; destruct R; simpl; intros; inv H6.
   eapply derives_trans; [apply H6' |].
  unfold_lift; rewrite field_mapsto__isptr. normalize.
  apply IHn; auto.
   clear H6.
   rewrite (local_andp_lemma _ _ H4).
   clear H4.
   unfold_lift.
   change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local,lift1; intro rho; simpl in *.
   apply derives_extract_prop; intro. unfold_lift in H. rewrite <- H. clear e1 H.
   apply andp_left2. apply andp_left2.
   specialize (H5 rho). unfold local,lift1 in H5. unfold_lift in H5.
   revert R H5; induction n; destruct R; simpl; intros.
   eapply derives_trans; [ | apply H5]; apply prop_right; auto.
   apply derives_trans with ((!!isptr (v1 rho) && TT) * TT).
   apply sepcon_derives; auto. rewrite andp_TT. auto.
   normalize.
   eapply derives_trans; [ | apply H5]; apply prop_right; auto.
   apply derives_trans with (TT * (!!isptr (v1 rho) && TT)).
   apply sepcon_derives; auto. rewrite andp_TT. auto.
   normalize.
  }
rewrite (local_andp_lemma _ _ H1').
rewrite (local_andp_lemma _ _ H3).
rewrite (local_andp_lemma _ _ H4).
rewrite insert_SEP.
go_lowerx.
rewrite <- H7. rewrite <- H0 in H6'.
clear - H6 H6'. rename H6 into H0.
revert R H0; induction n; destruct R; intros; inv H0; auto.
 simpl.  rewrite emp_sepcon. apply sepcon_derives; auto.
 unfold_lift in H6'; apply H6'.
 simpl in *.
 rewrite <- sepcon_assoc.
rewrite (sepcon_comm (field_mapsto_ _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
repeat rewrite denote_tc_assert_andp.

intros ek vl; unfold normal_ret_assert.
rewrite insert_SEP.
rewrite H0.
match goal with |- ?A |-- _ => apply derives_trans with (local (`eq v1 (eval_lvalue e1)) && A) end.
apply andp_right.
eapply derives_trans; [ | apply H5].
rewrite <- insert_local.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
subst ek. apply H.
rewrite sepcon_emp; apply prop_right; auto.
apply andp_derives; auto.
go_lowerx. rewrite <- H.

clear - H6; revert R H6; induction n; destruct R; simpl; intros; inv H6.
rewrite emp_sepcon; auto.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm (field_mapsto _ _ _ _ _)).
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma semax_store_field_deref'':
forall Espec (Delta: tycontext) n sh t1 fld P Q R e1 v1 e2 t2 R1 sid fields
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = tptr t1 ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta (Ecast e2 t2)) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- local (`eq v1 (eval_expr e1)) ->
    nth_error R n = Some R1 ->
    R1 |-- `(field_mapsto_ sh t1 fld) v1 ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Efield (Ederef e1 t1) fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(field_mapsto sh t1 fld) v1 (`(eval_cast (typeof e2) t2) (eval_expr e2)))))))).
Proof.
intros. rename H7 into H6'.
assert (H1': PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_expr e1))).
 {  eapply derives_trans; [ | apply H5].
  apply andp_derives; auto. apply andp_derives; auto. change SEPx with SEPx'; unfold SEPx'.
  unfold fold_right at 2. rewrite sepcon_emp. apply TT_right.
 }
match goal with |- semax _ _ _ ?Post => 
apply semax_pre_post with
(P':= |>PROPx P (LOCALx (`isptr (eval_expr e1) :: Q) (SEPx R)))
(R' := Post)
end.
eapply derives_trans; [apply andp_derives; [ apply now_later | apply derives_refl] | ].
rewrite <- later_andp.
apply later_derives.
rewrite <- insert_local.
apply andp_right; auto.
rewrite insert_local.
rewrite (local_andp_lemma _ _ H1').
rewrite <- insert_local.
go_lowerx.
rewrite <- H7.
clear - H6 H6'.
eapply derives_trans with (R1 rho * TT).
Focus 2.
eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] |].
apply H6'. 
unfold_lift; rewrite field_mapsto__isptr. normalize.
clear - H6.
revert R H6; induction n; destruct R; simpl; intros; inv H6.
apply sepcon_derives; auto.
specialize (IHn _ H0).
rewrite sepcon_comm.
apply derives_trans with ((R1 rho * TT) * TT).
apply sepcon_derives; auto.
rewrite sepcon_assoc. apply sepcon_derives; auto.
apply andp_left2; auto.
intros ek vl. apply andp_left2; auto.
assert (SF := semax_store_field'' Espec Delta n sh t1 fld P (`isptr (eval_expr e1) :: Q) R
  (Ederef e1 t1) v1 e2 t2 R1 sid fields WS).
eapply semax_pre_post; [ | | eapply SF]; try eassumption; clear SF; auto.
apply andp_left2; auto.
intros; apply andp_left2.
apply normal_ret_assert_derives'. rewrite <- insert_local. apply andp_left2; auto.
do 2 rewrite <- insert_local.
 rewrite <- andp_assoc.
rewrite (andp_comm (local _) (local _)). rewrite andp_assoc.
rewrite insert_local. rewrite (local_andp_lemma _ _ H3).
rewrite <- andp_assoc. 
apply andp_left1.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue. simpl typecheck_lvalue.
rewrite H0,H. simpl tc_bool. repeat rewrite tc_andp_TT2.
rewrite denote_tc_assert_andp.
split; auto.
do 2 rewrite <- insert_local.
 rewrite <- andp_assoc.
rewrite (andp_comm (local _) (local _)). rewrite andp_assoc.
rewrite insert_local. apply andp_left2; auto.
simpl eval_lvalue.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _) (local _)). rewrite andp_assoc.
rewrite insert_local.
rewrite (local_andp_lemma _ _ H5).
go_lowerx. apply prop_right.
rewrite isptr_force_ptr by auto.
auto.
Qed.

(* ALL the rest of the lemmas in this file should (eventually) become obsolete, 
  in favor of the lemmas earlier in the file  *)

Lemma semax_load_field':
forall Espec (Delta: tycontext) sh id t1 fld P Q R e1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
     Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx (tc_lvalue Delta e1::Q) (SEPx (`(field_mapsto sh t1 fld) (eval_lvalue e1) v2::R))))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (`(field_mapsto sh t1 fld) (eval_lvalue e1) v2 :: R)))))).
Proof.
intros. rename H3 into CC.
eapply semax_pre_post;
  [ | |  apply (semax_load_field Espec Delta sh id t1 fld (PROPx P (LOCALx Q (SEPx R))) e1
   v2 t2 i2 sid fields)]; auto; try congruence.
+
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' )
end.
rewrite later_andp; apply andp_derives; auto; apply now_later.
apply later_derives.
go_lowerx.
+
intros ek vl.
unfold normal_ret_assert.
repeat rewrite exp_andp2.
apply exp_derives; intro old.
autorewrite with subst.
apply andp_left2.
rewrite insert_SEP.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
Qed.

Lemma semax_load_field_deref:
forall Espec (Delta: tycontext) sh id t1 fld P Q R e1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
     Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::Q) (SEPx (`(field_mapsto sh t1 fld) (eval_expr e1) v2::R))))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (`(field_mapsto sh t1 fld) (eval_expr e1) v2 :: R)))))).
Proof.
intros.
eapply semax_pre_post; [ | | 
    apply (semax_load_field' Espec Delta sh id t1 fld P Q R (Ederef e1 t1) v2 t2 i2 sid fields); auto].
eapply derives_trans.
apply andp_derives. apply now_later. apply derives_refl.
rewrite <- later_andp. apply later_derives.
apply go_lower_lem9.
go_lowerx.
rewrite field_mapsto_isptr. normalize.
rewrite field_mapsto_nonvolatile. normalize.
unfold_lift. 
repeat apply andp_right; try apply prop_right;  auto.
hnf; simpl. rewrite H0. rewrite H9.
repeat rewrite denote_tc_assert_andp; repeat split; auto.

intros ek vl. apply andp_left2.
apply normal_ret_assert_derives'.
apply exp_derives; intro old.
simpl.
autorewrite with subst.
go_lowerx.
rewrite field_mapsto_force_ptr.
repeat apply andp_right; try apply prop_right; auto.
Qed.

Lemma semax_store_field':
forall Espec (Delta: tycontext) sh t1 fld P Q R e1 e2 t2 sid fields
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx (tc_lvalue Delta e1::tc_expr Delta (Ecast e2 t2)::Q)
                             (SEPx (`(field_mapsto_ sh t1 fld) (eval_lvalue e1)::R))))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(field_mapsto sh t1 fld) (eval_lvalue e1) 
                  (`(eval_cast (typeof e2) t2) (eval_expr e2)) :: R))))).
Proof.
intros.
pose proof semax_store_field. unfold_lift.
unfold_lift in H3.
subst t1.
specialize (H3 Espec Delta sh e1 fld (PROPx P (LOCALx Q (SEPx R)))
   t2 e2 sid fields WS H0 H1 H2).
eapply semax_pre_post; [ | | eapply H3]; try eassumption.
apply andp_left2. apply later_derives.
go_lowerx. rewrite H0; auto. 

intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
rewrite insert_SEP.
rewrite H0.
go_lowerx.
Qed.

Lemma semax_store_field_deref:
forall Espec (Delta: tycontext) sh t1 fld P Q R e1 e2 t2 sid fields
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield (Ederef e1 t1) fld t2) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t2)::Q)
                             (SEPx (`(field_mapsto_ sh t1 fld) (eval_expr e1)::R))))
       (Sassign (Efield (Ederef e1 t1) fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(field_mapsto sh t1 fld) (eval_expr e1) 
                  (`(eval_cast (typeof e2) t2) (eval_expr e2)) :: R))))).
Proof.
intros.
pose proof (semax_store_field' Espec Delta sh t1 fld P Q R (Ederef e1 t1) e2 t2 sid fields WS H (eq_refl _) H1 H2).
unfold_lift. unfold_lift in H3.
eapply semax_pre_post; [  | | eapply H3].
apply andp_left2; apply later_derives.
go_lowerx.
rewrite field_mapsto__isptr.
rewrite field_mapsto__nonvolatile. normalize.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl. repeat rewrite denote_tc_assert_andp.
repeat split; auto. rewrite H0; apply I. rewrite H. apply I.

intros ek vl. apply andp_left2; auto.
apply normal_ret_assert_derives'.
go_lowerx.
normalize.
Qed.

Lemma semax_store_PQR:
forall Espec (Delta: tycontext) sh t1 P Q R e1 e2
    (WS: writable_share sh)
    (NONVOL: type_is_volatile t1 = false)
    (TC: typecheck_store (Ederef e1 t1)),
    typeof e1 = Tpointer t1 noattr ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t1)::Q)
                             (SEPx (`(mapsto_ sh t1) (eval_expr e1)::R))))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(mapsto sh t1) (eval_expr e1) 
                  (`(eval_cast (typeof e2) t1) (eval_expr e2)) :: R))))).
Proof.
intros.
pose proof semax_store.
unfold_lift; unfold_lift in H0.
eapply semax_pre_post; [ | | eapply (H0 Delta (Ederef e1 t1) e2 sh)]; try eassumption.
instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
apply andp_left2. apply later_derives.
go_lowerx.
rewrite mapsto__isptr at 1. normalize.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl. rewrite H; simpl.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite NONVOL; hnf; unfold_lift; hnf; auto.
replace (force_ptr (eval_expr e1 rho)) with (eval_expr e1 rho); auto.
clear - H5; hnf in H5. destruct (eval_expr e1 rho); try contradiction; simpl; auto.

intros ek vl; unfold normal_ret_assert.
rewrite insert_SEP. go_lowerx.
unfold_lift.
rewrite mapsto_force_ptr.
auto.
Qed.

Lemma semax_load':
  forall Espec (Delta : tycontext) (sh : Share.t) (id : positive) 
         P Q R (e1 : expr) t1 i2 (v2 : environ -> val),
   typeof e1 = Tpointer t1 noattr ->
   (temp_types Delta) ! id = Some (t1,i2) ->
   type_is_volatile t1 = false ->
   classify_cast t1 t1 = cast_case_neutral ->
 @semax Espec Delta
     (|> PROPx P (LOCALx (tc_expr Delta e1 ::  Q)
            (SEPx (`(mapsto sh t1) (eval_expr e1) v2 :: R))))
    (Sset id (Ederef e1 t1))
    (normal_ret_assert
       (EX old: val, 
        PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) v2) ::
                         map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old))
                    (`(mapsto sh t1) (eval_expr e1) v2 :: R)))))).
Proof.
 intros. rename H2 into CLASSIFY.
 eapply semax_pre_post;
  [ | |  apply (semax_load Delta sh id (PROPx P (LOCALx Q (SEPx R))) (Ederef e1 t1)
   v2)]; auto.
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' )
end.
rewrite later_andp; apply andp_derives; auto; apply now_later.
apply later_derives.
rewrite insert_SEP.
go_lowerx.
rewrite mapsto_isptr.
normalize.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl; repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite H; apply I.
rewrite H1; apply I.
hnf. exists t1, i2. split; auto.
unfold allowedValCast. rewrite CLASSIFY.
destruct t1; simpl; auto.
unfold_lift; rewrite mapsto_force_ptr; auto.

intros ek vl.
apply andp_left2.
unfold normal_ret_assert.
repeat rewrite exp_andp2.
apply exp_derives; intro old.
simpl eval_lvalue.
autorewrite with subst.
repeat rewrite insert_SEP.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
unfold_lift; rewrite mapsto_force_ptr.
auto.
Qed.


