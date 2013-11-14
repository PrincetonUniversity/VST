Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.

Local Open Scope logic.

Lemma later_left2 {T}{ND: NatDed T}{IT: Indir T}:  (* MOVE THIS TO ANOTHER FILE *)
 forall A B C : T, A && B |-- C -> A && |> B |-- |>C.
Proof.
intros.
apply derives_trans with (|> (A && B)).
rewrite later_andp.
apply andp_derives; auto.
apply now_later.
apply later_derives; assumption.
Qed.

Lemma SEP_nth_isolate:
  forall n R Rn, nth_error R n = Some Rn ->
      SEPx R = SEPx (Rn :: replace_nth n R emp).
Proof.
 unfold SEPx.
 induction n; destruct R; intros; inv H; extensionality rho.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m rho * fold_right sepcon emp R rho).
 reflexivity.
 rewrite (IHn R Rn H1).
 simpl.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn rho)).
 simpl.
 repeat rewrite sepcon_assoc.
 f_equal. rewrite sepcon_comm; reflexivity.
Qed.


Lemma SEP_replace_nth_isolate:
  forall n R Rn Rn', 
       nth_error R n = Some Rn ->
      SEPx (replace_nth n R Rn') = SEPx (Rn' :: replace_nth n R emp).
Proof.
 unfold SEPx.
 intros.
 revert R H.
 induction n; destruct R; intros; inv H; intros; extensionality rho.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m rho * fold_right sepcon emp (replace_nth n R Rn') rho).
 reflexivity.
 rewrite (IHn R H1). clear IHn.
 simpl.
 repeat rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn' rho)).
 rewrite sepcon_assoc.
 reflexivity.
Qed.

Lemma semax_store_nth:
forall {Espec: OracleKind} n Delta P Q R e1 e2 Rn sh t1,
   typeof e1 = t1 ->
   nth_error R n = Some Rn ->
   Rn |-- `(mapsto_ sh t1) (eval_lvalue e1) ->
   forall (WS: writable_share sh),
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
                 local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign e1 e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q (SEPx (replace_nth n R
              (`(mapsto sh t1) (eval_lvalue e1) 
                  (`force_val (`(sem_cast (typeof e2) t1) (eval_expr e2))))))))).
Proof.
intros.
subst t1.
eapply semax_pre_post ; [ | | 
 apply  (semax_store Delta e1 e2 sh 
       (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) WS)].
apply later_left2.
repeat rewrite insert_local.
apply andp_right. auto.
rewrite <- insert_local.
apply andp_left2.
rewrite insert_SEP.
apply andp_derives; auto.
apply andp_derives; auto.
rewrite (SEP_nth_isolate _ _ _ H0).
go_lowerx; apply sepcon_derives; auto.
apply H1.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
rewrite insert_SEP.
apply andp_derives; auto.
apply andp_derives; auto.
rewrite (SEP_replace_nth_isolate _ _ _ _ H0).
auto.
Qed.

Lemma mapsto_force_ptr: forall sh t v v', 
  mapsto sh t (force_ptr v) v' = mapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Lemma local_andp_lemma:
  forall P Q, P |-- local Q -> P = local Q && P.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
apply andp_left2; auto.
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
rewrite tc_val_eq in H3.
rewrite H4 in H3; inv H3.
Qed.

(*TODO move to expr_lemmas.v*)
Lemma typecheck_val_sem_cast: 
  forall t2 e2 rho Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2 t2 e2) rho ->
      typecheck_val (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))) t2 = true.
Admitted.

Lemma semax_store_field: 
forall Espec (Delta: tycontext) sh e1 fld P t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (`(field_mapsto_ sh (typeof e1) fld) (eval_lvalue e1) * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (`(field_mapsto sh (typeof e1) fld) (eval_lvalue e1) 
                  (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2))) * P)).
Proof.
Transparent field_mapsto.
pose proof I. intros until fields. intro WS.
intros.
rename H0 into TE1.
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
               (local (`(tc_val t2) (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2)))) &&
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
repeat apply andp_right; try apply prop_right; 
  repeat simple apply conj; auto.
hnf; simpl. rewrite TE1.
rewrite H5. rewrite tc_andp_TT2.
rewrite denote_tc_assert_andp.
split; auto. rewrite H7; auto.
hnf in H3. simpl in H3.
rewrite denote_tc_assert_andp in H3. destruct H3.
rewrite tc_val_eq;
eapply typecheck_val_sem_cast; eassumption.
apply sepcon_derives; auto.
simpl.
apply orp_right2. apply andp_right; try apply prop_right; auto.
apply exp_right with v0; auto.

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
rewrite <- H1.
rewrite Heqm.
repeat apply andp_right; try apply prop_right; auto.
apply orp_left; auto.
apply derives_extract_prop; intro.
rewrite H9 in H4. destruct t2; inv H4.
Opaque field_mapsto.
Qed.

Lemma semax_store_PQR:
forall Espec (Delta: tycontext) sh t1 P Q R e1 e2
    (WS: writable_share sh)
    (NONVOL: type_is_volatile t1 = false),
    typeof e1 = Tpointer t1 noattr ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t1)::Q)
                             (SEPx (`(mapsto_ sh t1) (eval_expr e1)::R))))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(mapsto sh t1) (eval_expr e1) 
                  (`force_val (`(sem_cast (typeof e2) t1) (eval_expr e2))) :: R))))).
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
repeat split; simpl; auto.
hnf. simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite H; simpl; auto.
rewrite NONVOL; hnf; unfold_lift; hnf; auto.

intros ek vl; unfold normal_ret_assert.
rewrite insert_SEP. go_lowerx.
unfold_lift.
rewrite mapsto_force_ptr.
auto.
Qed.


Lemma semax_store_field'':
forall Espec (Delta: tycontext) n sh t1 fld P Q R e1 v1 e2 t2 R1 sid fields 
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
  (*  typecheck_store (Efield e1 fld t2) -> *)
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
                    (`(field_mapsto sh t1 fld) v1 (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2))))))))).
Proof.
pose (H2:=True).
intros. rename H7 into H6'.
assert (SF := semax_store_field). unfold_lift.
unfold_lift in SF.
subst t1.
specialize (SF Espec Delta sh e1 fld (PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))
   t2 e2 sid fields WS H0 H1).
eapply semax_pre_post; [ | | eapply SF]; try eassumption; clear SF.
eapply derives_trans; [apply andp_derives; [ apply now_later | apply derives_refl] | ].
rewrite <- later_andp.
apply later_derives.
rewrite insert_local.
assert (H1': PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`eq v1 (eval_lvalue e1))).
 {  eapply derives_trans; [ | apply H5].
  apply andp_derives; auto. apply andp_derives; auto. unfold SEPx.
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
   unfold PROPx,LOCALx,SEPx,local,lift1; intro rho; simpl in *.
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

(* This lemma is almost obsolete, but still used in verif_message.v *)
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

Lemma semax_load_37 : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 (v2: environ -> val),
      local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && 
       local (tc_temp_id_load id (typeof e1) Delta v2) && 
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                                          (subst id (`old) P))).
Proof.
intros.
assert (EQ: local (tc_environ Delta) && P = `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * 
                  (ewand (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2) (local (tc_environ Delta) && P))).
extensionality rho.
simpl.
apply res_predicates.superprecise_ewand_lem1.
unfold_lift.
apply superprecise_mapsto.
apply H. clear H.

eapply semax_pre_post; [ | | apply (semax_load Delta sh id
   (ewand (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2) (local (tc_environ Delta) && P) )
   e1 v2)].
* 
intros.
apply later_left2.
apply derives_trans with 
  (local (tc_lvalue Delta e1) &&
 (local (tc_temp_id_load id (typeof e1) Delta v2) && (local (tc_environ Delta) &&P))).
repeat apply andp_right. apply andp_left2; apply andp_left1; auto.
 apply andp_left1; auto. apply andp_left2; apply andp_left1; apply andp_left2; auto.
apply andp_left1; auto.
repeat apply andp_left2; auto.
repeat rewrite andp_assoc.
apply andp_derives; auto.
apply andp_derives; auto.
apply derives_refl'; auto.
*
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
apply exp_derives; intro old.
apply andp_derives; auto.
apply subst_derives.
rewrite <- EQ.
apply andp_left2; auto.
Qed.

Lemma semax_load_37' : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P Q R e1 (v2: val),
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         local (tc_lvalue Delta e1) && local (tc_temp_id_load id (typeof e1) Delta `v2)
         && (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id e1)
       (normal_ret_assert (EX old:val, 
             PROPx P 
   (LOCALx (`eq (eval_id id) `v2 :: map (subst id (`old)) Q)
     (SEPx (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_pre_post; [ | | apply semax_load_37 with sh].
instantiate (1:= PROPx P (LOCALx Q (SEPx R))).
apply later_left2.
rewrite insert_local.
rewrite <- (andp_dup (PROPx P (LOCALx (_ :: _) _))).
eapply derives_trans.
apply andp_derives; [apply derives_refl | apply H].
clear H.
go_lowerx.
autorewrite with gather_prop.
apply derives_extract_prop; intros [? ?].
apply andp_right.
apply prop_right; repeat split; eassumption.
apply andp_left1; auto.
intros. apply andp_left2; auto.
apply normal_ret_assert_derives'.
apply exp_derives; intro old.
autorewrite with subst.
rewrite insert_local.
apply andp_derives; auto.
rewrite insert_local.
eapply derives_trans; [apply H | clear H].
apply andp_left2. auto.
Qed.

Lemma semax_load_field'':
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                           |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  `(field_mapsto sh t1 fld) (eval_lvalue e1) `v * TT ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, PROPx P 
                     (LOCALx (`(eq v) (eval_id id) :: map (subst id (`old)) Q)
                     (SEPx (map (subst id (`old)) R))))).
Proof.
Transparent field_mapsto.
pose proof I.
pose proof I.
intros. rename H5 into CLASSIFY.
rename H3 into TC0; rename H4 into TC2.
subst t1.
rename H2 into TE1.
rename H6 into TC3; rename H7 into H6.
repeat rewrite <- insert_local in H6.
repeat rewrite <- insert_local in TC3.
replace  (EX  old : val,
      PROPx P
        (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))
  with  (EX  old : val, local (`(eq v) (eval_id id)) && 
                   subst id `old (PROPx P (LOCALx Q (SEPx R))))
  by (f_equal; extensionality old; autorewrite with subst; rewrite insert_local; auto).
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
eapply semax_pre_post; [ | | apply (semax_load_37 Delta sh id ((*local (tc_environ Delta) && *)PQR) _ (`v))].
* (* PRECONDITION *)
apply later_left2.
apply andp_right; [ | apply andp_left2; auto].
apply derives_trans with 
 (local (tc_lvalue Delta e1)  && (`(field_mapsto sh (typeof e1) fld) (eval_lvalue e1) `v * TT)).
apply andp_right.
eapply derives_trans; [ | apply TC3].
apply andp_right. apply andp_left1; auto. apply andp_right; [ |  apply andp_left2; auto].
eapply derives_trans; [apply H6 | ].
go_lowerx. unfold field_mapsto.
destruct (eval_lvalue e1 rho);  try (rewrite FF_sepcon; apply FF_left).
rewrite H1. rewrite field_offset_unroll. 
destruct (field_offset fld fields);   try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
destruct (access_mode t2);   try (rewrite FF_sepcon; apply FF_left).
apply TT_right.
eapply derives_trans; [apply H6 | ].
apply sepcon_derives; auto.
go_lowerx.
unfold field_mapsto, tc_lvalue, tc_temp_id_load.
simpl.
destruct (eval_lvalue e1 rho);  try (rewrite FF_sepcon; apply FF_left).
rewrite H1. rewrite field_offset_unroll. 
destruct (field_offset fld fields);   try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
destruct (access_mode t2);   try (rewrite FF_sepcon; apply FF_left).
normalize.
apply prop_right; repeat split; auto.
rewrite denote_tc_assert_andp; split.
apply H2. rewrite H4. apply I.
exists t2,i2. split; auto.
unfold allowedValCast. rewrite CLASSIFY.
destruct t2; simpl; auto.
* (* POSTCONDITION *)
intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives; intro old.
apply andp_derives; auto.
clear; intro; unfold_lift; apply prop_derives; auto.
*
 eapply derives_trans; [ apply H6 | ].
apply sepcon_derives; auto.
unfold field_mapsto, mapsto, umapsto.
go_lowerx.
unfold_lift.
destruct (eval_lvalue e1 rho); try apply FF_left.
rewrite H1.
rewrite field_offset_unroll.
simpl.
destruct (field_offset fld fields);   try apply FF_left.
rewrite <- TC2.
destruct (access_mode t2);   try apply FF_left.
simpl offset_val. cbv iota.
normalize.
apply orp_right1.
auto.
Qed.

Lemma semax_load_field_38:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 i2 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                           |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  `(field_mapsto sh t1 fld) (eval_lvalue e1) `v * TT ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_post';[ | eapply semax_load_field''; eauto].
apply exp_left; intro old.
autorewrite with subst. auto.
Qed.

Lemma semax_load_field_40:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 i2 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    t1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   typeof e1 = tptr t1 ->
   Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  local (tc_expr Delta e1) && (`(field_mapsto sh t1 fld) (eval_expr e1) `v * TT) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_load_field_38; eauto.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local.
apply derives_trans with (local (tc_expr Delta e1) && local (`isptr (eval_expr e1))).
apply andp_right; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left1; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
clear; go_lowerx. rewrite field_mapsto_isptr; normalize.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue; simpl denote_tc_assert.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite H4. apply I.
rewrite H1; apply I.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
apply sepcon_derives; auto.
go_lowerx. unfold_lift. rewrite field_mapsto_force_ptr; eapply derives_refl.
Qed.

Lemma semax_load_field_39:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 i2 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    t1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   typeof e1 = tptr t1 ->
   Cop.classify_cast t2 t2 = Cop.cast_case_neutral ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  local (tc_expr Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  `(field_mapsto sh t1 fld) (eval_expr e1) `v * TT ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_load_field_38; eauto.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local.
apply derives_trans with (local (tc_expr Delta e1) && local (`isptr (eval_expr e1))).
apply andp_right; auto.
eapply derives_trans; [ apply H7 | ].
clear; go_lowerx. rewrite field_mapsto_isptr; normalize.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue; simpl denote_tc_assert.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite H4. apply I.
rewrite H1; apply I.
eapply derives_trans; [ apply H7 | ].
apply sepcon_derives; auto.
go_lowerx. unfold_lift. rewrite field_mapsto_force_ptr; eapply derives_refl.
Qed.

