Load loadpath.
Require Import Coqlib compositional_compcert.Coqlib2.
Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.

Local Open Scope logic.

Lemma forward_setx_closed_now':
  forall Delta (Q: list (environ -> Prop)) (R: list assert) id e,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx nil (LOCALx Q (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  semax Delta (PROPx nil (LOCALx Q (SEPx R))) (Sset id e) 
        (normal_ret_assert (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R)))).
Proof.
intros.
eapply semax_pre; [ | apply semax_set].
eapply derives_trans; [ | apply now_later].
apply andp_left2.
apply andp_right; auto.
apply andp_right; auto.
autorewrite with subst.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local,lift1; simpl.
apply prop_derives; simpl; intro; split; auto.
hnf; auto.
Qed.

Lemma forward_setx_closed_now:
  forall Delta (Q: list (environ -> Prop)) (R: list assert) id e PQR,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx nil (LOCALx Q (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  normal_ret_assert (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R))) |-- PQR ->
  semax Delta (PROPx nil (LOCALx Q (SEPx R))) (Sset id e) PQR.
Proof.
intros.
eapply semax_post.
intros ek vl. apply andp_left2. apply H4.
apply forward_setx_closed_now'; auto.
Qed.

Lemma forward_setx_closed_now_seq:
  forall Delta (Q: list (environ -> Prop)) (R: list assert) id e c PQR,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx nil (LOCALx Q (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  semax (update_tycon Delta (Sset id e))
           (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R))) c PQR ->
  semax Delta (PROPx nil (LOCALx Q (SEPx R))) (Ssequence (Sset id e) c) PQR.
Proof.
 intros.
 eapply semax_seq.
 apply sequential'.
 apply forward_setx_closed_now; auto.
 apply H4.
Qed.

Lemma semax_load_field:
forall (Delta: tycontext) sh id t1 fld P e1 v2 t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    semax Delta 
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
intros.
rename H3 into TC0; rename H4 into TC2.
subst t1.
rename H2 into TE1.
(*(Delta : tycontext) (sh : Share.t) (id : positive)
         (P : environ -> mpred) (e1 : expr) (v2 : environ -> val),*)
apply (semax_pre_post
            (|>(local (tc_lvalue Delta (Efield e1 fld t2)) &&
                 local (tc_temp_id_load id (typeof (Efield e1 fld t2)) Delta v2) && 
                 local (`(tc_val t2) v2) &&
               (`(mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2 * 
                        (local (`(tc_val t2) v2) &&  !!(type_is_volatile t2 = false) &&  P))))
            (normal_ret_assert 
              (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
              (subst id (`old) (`(mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2  * 
                ( local (`(tc_val t2) v2) && !!(type_is_volatile t2 = false) && P))))));
  [ | | apply semax_load].

(* PRECONDITION *)
intro rho.
unfold tc_temp_id_load, local; unfold_coerce.
simpl. unfold_coerce.
apply derives_extract_prop; intro.
apply later_derives.
apply derives_extract_prop; intro.
unfold field_mapsto; unfold_coerce. 
case_eq (eval_lvalue e1 rho); intros; 
 try (rewrite FF_sepcon; apply FF_left).
rewrite H1.
rewrite field_offset_unroll. rewrite <- TC2.
case_eq (field_offset fld fields); intros; 
 try (rewrite FF_sepcon; apply FF_left).
case_eq (access_mode t2); intros; 
 try (rewrite FF_sepcon; apply FF_left).
normalize.
repeat apply andp_right; try apply prop_right.
unfold tc_lvalue. 
unfold typecheck_lvalue; fold typecheck_lvalue. rewrite H1.
rewrite H8; simpl tc_bool.
rewrite H5. repeat rewrite tc_andp_TT2.
apply H3.
exists t2; exists i2; split; auto.
admit. (* typechecking proof; check with Joey *)
apply H7.
unfold mapsto.
rewrite H6.
unfold eval_field. rewrite H5. unfold eval_struct_field.
 rewrite H8.
unfold tc_val; rewrite H7.
normalize.

(* POSTCONDITION *)
intros ek vl.
apply andp_left2.
intro rho. apply normal_ret_assert_derives.
unfold local; unfold_coerce; simpl.
apply exp_derives. intro old.
apply andp_derives; auto.
unfold subst.
unfold mapsto, field_mapsto.
case_eq (access_mode t2); intros; 
 try (rewrite FF_sepcon; apply FF_left).
rewrite H1. unfold_coerce.
simpl eval_field.
rewrite field_offset_unroll.
destruct (field_offset fld fields);  try (rewrite FF_sepcon; apply FF_left).
unfold eval_struct_field.
destruct (eval_lvalue e1 (env_set rho id old)); try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2; rewrite H2.
unfold local, lift1.
normalize.
Qed.

Lemma writable_share_top: writable_share Share.top.
Admitted.
Hint Resolve writable_share_top.

Lemma denote_tc_assert_andp:
  forall a b rho, denote_tc_assert (tc_andp a b) rho =
             (denote_tc_assert a rho /\ denote_tc_assert b rho).
Proof.
 intros. apply prop_ext.
 unfold denote_tc_assert, tc_andp; unfold_coerce.
 destruct a,b; simpl; intuition; try contradiction.
Qed.


Lemma semax_store_field: 
forall (Delta: tycontext) sh e1 fld P t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   semax Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (`(field_storable sh (typeof e1) fld) (eval_lvalue e1) * P)))
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
unfold field_storable.

apply semax_pre0 with
 (EX v2: val,
   ((|>(local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
      (`(fun v1 : val =>
         match v1 with
         | Vundef => FF
         | Vint _ => FF
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
unfold coerce, lift1_C, lift1; intro rho.
simpl sepcon. cbv beta.
case_eq (eval_lvalue e1 rho); intros; try rewrite FF_sepcon; try apply FF_left.
destruct (typeof e1);  try rewrite FF_sepcon; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i0 (Tstruct i0 f a) f));
   try (rewrite FF_sepcon; apply FF_left).
destruct ( access_mode
    (type_of_field (unroll_composite_fields i0 (Tstruct i0 f a) f) fld));
   try (rewrite FF_sepcon; apply FF_left).
normalize.
apply exp_right with v2. rewrite H0. normalize.
apply extract_exists_pre; intro v0.

pose proof (semax_store Delta (Efield e1 fld t2) e2 (lift0 v0) sh 
               (local (`(tc_val t2) (`(eval_cast (typeof e2) t2) (eval_expr e2))) &&
                 !! (type_is_volatile t2 = false) &&   P)).
simpl typeof in H0. 
eapply semax_pre_post ; [ | | apply H0; auto]; clear H0.
match goal with |- (?A && |> ?B |-- |> ?C) =>
  apply derives_trans with (|> (A && B));
    [rewrite (later_andp A B); apply andp_derives; auto; apply now_later 
    | apply later_derives]
end.
intro rho; unfold coerce, local,lift2_C, lift1_C, lift2, lift1.
 simpl andp; simpl sepcon. cbv beta.
rewrite TE1.
normalize.
unfold mapsto.
case_eq (eval_lvalue e1 rho); intros; try (rewrite FF_sepcon; apply FF_left).
case_eq (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)); intros; try (rewrite FF_sepcon; apply FF_left).
rewrite <- H1.
case_eq (access_mode t2); intros; try (rewrite FF_sepcon; apply FF_left).
simpl eval_lvalue.
unfold coerce, lift1_C, lift1.
rewrite TE1. rewrite H4; simpl eval_field.
rewrite field_offset_unroll in H5. rewrite H5.
normalize.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl. rewrite TE1.
rewrite H5. rewrite tc_andp_TT2.
rewrite denote_tc_assert_andp.
split; auto. rewrite H7; auto.
apply sepcon_derives; auto.
repeat apply andp_right; try apply prop_right; auto.
hnf.
hnf; simpl. hnf in H3. simpl in H3.
rewrite denote_tc_assert_andp in H3. destruct H3.
eapply expr_lemmas.typecheck_val_eval_cast; eassumption.

intros ek vl rho; unfold local; unfold_coerce; unfold normal_ret_assert; simpl.
normalize.
apply sepcon_derives; auto.
unfold mapsto, field_mapsto.
rewrite TE1.
case_eq (access_mode t2); intros; normalize.
unfold eval_field.
rewrite field_offset_unroll.
unfold eval_struct_field.
case_eq (field_offset fld fields); intros; normalize.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite <- H1. rewrite H4.
normalize.
Opaque field_mapsto.
Qed.

Lemma semax_store_field_mapsto: 
forall (Delta: tycontext) sh e1 fld P v0 t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   semax Delta 
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
intro rho; simpl.
apply sepcon_derives; auto.
unfold coerce, lift2_C, lift2, lift1_C, lift1.
apply field_mapsto_storable.
Qed.

Lemma semax_load_field':
forall (Delta: tycontext) sh id t1 fld P Q R e1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    semax Delta 
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
eapply semax_pre_post;
  [ | |  apply (semax_load_field Delta sh id t1 fld (PROPx P (LOCALx Q (SEPx R))) (Ederef e1 t1)
   v2 t2 i2 sid fields)]; auto.
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' )
end.
rewrite later_andp; apply andp_derives; auto; apply now_later.
apply later_derives.
normalize.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue; unfold_coerce; simpl.
 rewrite field_mapsto_nonnull.
repeat rewrite denote_tc_assert_andp.
 normalize.
rewrite H0. rewrite H. simpl. normalize.
apply andp_right; [ | cancel].
destruct (eval_expr e1 rho); inv H7; normalize.
apply prop_right; apply I.

intros ek vl rho; normalize.
intros x ?; apply exp_right with x.
normalize.
Qed.

Lemma field_mapsto_storable_at1:
  forall Delta P Q sh ty fld e v R c Post,
    semax Delta (PROPx P (LOCALx Q (SEPx (`(field_storable sh ty fld) e :: R)))) c Post ->
    semax Delta (PROPx P (LOCALx Q (SEPx (`(field_mapsto sh ty fld) e v :: R)))) c Post.
Proof.
intros.
 eapply semax_pre0; [ | apply H].
 change SEPx with SEPx'.
 intro rho; unfold PROPx, LOCALx, SEPx'.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 apply field_mapsto_storable.
Qed.

Lemma later_field_mapsto_storable_at1:
  forall Delta P Q sh ty fld e v R c Post,
    semax Delta (PROPx P (LOCALx Q (SEPx (|>`(field_storable sh ty fld) e :: R)))) c Post ->
    semax Delta (PROPx P (LOCALx Q (SEPx (|> `(field_mapsto sh ty fld) e v :: R)))) c Post.
Proof.
intros.
 eapply semax_pre0; [ | apply H].
 change SEPx with SEPx'.
 intro rho; unfold PROPx, LOCALx, SEPx'.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 apply later_derives; auto.
 apply field_mapsto_storable.
Qed.

Lemma semax_store_field':
forall (Delta: tycontext) sh t1 fld P Q R e1 e2 t2 sid fields
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield (Ederef e1 t1) fld t2) ->
    semax Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t2)::Q)
                             (SEPx (`(field_storable sh t1 fld) (eval_expr e1)::R))))
       (Sassign (Efield (Ederef e1 t1) fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(field_mapsto sh t1 fld) (eval_expr e1) 
                  (`(eval_cast (typeof e2) t2) (eval_expr e2)) :: R))))).
Proof.
intros.
pose proof semax_store_field.
unfold coerce, lift2_C in *.
eapply semax_pre_post; [ | | eapply H3]; try eassumption.
instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
apply andp_left2. apply later_derives.
intro rho; normalize. 
subst t1.
unfold tc_lvalue. simpl typecheck_lvalue.
repeat rewrite denote_tc_assert_andp.
rewrite H0. simpl is_pointer_type. simpl tc_bool.
rewrite field_storable_nonnull.
normalize.
unfold Cop.bool_val in H.
simpl in H.
revert H; case_eq (eval_expr e1 rho); intros; try discriminate; normalize.
repeat apply andp_right.
apply prop_right; hnf. rewrite H; auto.
apply prop_right; auto.
simpl typeof. simpl force_ptr. auto.

intros ek vl rho; unfold normal_ret_assert, local; unfold_coerce; simpl.
normalize.
Qed.

Lemma semax_store_PQR:
forall (Delta: tycontext) sh t1 P Q R e1 e2 x
    (WS: writable_share sh)
    (NONVOL: type_is_volatile t1 = false)
    (TC: typecheck_store (Ederef e1 t1)),
    typeof e1 = Tpointer t1 noattr ->
    semax Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t1)::Q)
                             (SEPx (`(mapsto sh t1) (eval_expr e1) x::R))))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(mapsto sh t1) (eval_expr e1) 
                  (`(eval_cast (typeof e2) t1) (eval_expr e2)) :: R))))).
Proof.
intros.
pose proof semax_store.
unfold coerce, lift2_C, lift1_C in *.
eapply semax_pre_post; [ | | eapply H0]; try eassumption.
instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
instantiate (1:= x (*lift1 (eval_cast (typeof e2) (typeof e1)) (eval_expr e2) *)).
apply andp_left2. apply later_derives. change SEPx with SEPx'.
intro rho; unfold PROPx, LOCALx, SEPx', local, lift1,lift2.
simpl.
normalize.
unfold tc_lvalue. simpl typecheck_lvalue.
rewrite H; simpl.
rewrite mapsto_isptr at 1. normalize.
repeat apply andp_right; try apply prop_right; auto.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite NONVOL; hnf; auto.
replace (force_ptr (eval_expr e1 rho)) with (eval_expr e1 rho); auto.
clear - H5; hnf in H5. destruct (eval_expr e1 rho); try contradiction; simpl; auto.

intros ek vl rho; unfold normal_ret_assert, local; unfold_coerce; simpl.
normalize.
cancel.
clear.
rewrite mapsto_isptr at 1. normalize.
replace (force_ptr (eval_expr e1 rho)) with (eval_expr e1 rho); auto.
destruct (eval_expr e1 rho); simpl in *; try contradiction; auto.
Qed.


Lemma forward_setx':
  forall Delta P id e,
  (P |-- local (tc_expr Delta e) && local (tc_temp_id id (typeof e) Delta e) ) ->
  semax Delta
             P
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_set_forward Delta P id e); auto].
eapply derives_trans ; [ | apply now_later].
intro rho; normalize.
apply andp_right; auto.
eapply derives_trans; [apply H | ].
normalize.
intros ek vl rho; unfold normal_ret_assert. simpl; normalize.
apply exp_right with x.
normalize.
Qed.

Lemma forward_setx:
  forall Delta P Q R id e,
  (PROPx P (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e) && local (tc_temp_id id (typeof e) Delta e) ) ->
  semax Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  
                    PROPx P
                     (LOCALx (`eq (eval_id id) (subst id (`old) (eval_expr e)) ::
                                     map (subst id (`old)) Q)
                      (SEPx (map (subst id (`old)) R))))).
Proof.
 intros.
 eapply semax_post; [ | apply forward_setx'; auto].
 intros.
 intro rho. simpl. normalize.
 intros old ?; apply exp_right with old. normalize.
Qed.

Lemma normal_ret_assert_derives':
  forall ek vl P Q, 
      P |-- Q ->
      normal_ret_assert P ek vl |-- normal_ret_assert Q ek vl.
Proof. intros; intro rho. apply normal_ret_assert_derives. auto.
Qed.

Lemma normal_ret_assert_derives'':
  forall (P: assert) (Q: ret_assert), 
      (P |-- Q EK_normal None) ->
      normal_ret_assert P |-- Q.
Proof. intros; intros ek vl rho. 
    unfold normal_ret_assert; destruct ek; simpl; normalize.
   inv H0. inv H0. inv H0.
Qed.

Lemma after_set_special1:
  forall (A: Type) id e Delta Post  P Q R,
    EX x:A, PROPx (P x) (LOCALx (tc_environ(initialized id Delta) :: Q x) (SEPx (R x))) |-- Post ->
 forall ek vl,
   local (tc_environ (exit_tycon (Sset id e) Delta ek)) && 
    normal_ret_assert (EX  x : A, PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) ek vl 
   |-- normal_ret_assert Post ek vl.
Proof.
 intros.
 intro rho; unfold local,lift1. simpl.
 apply derives_extract_prop. intro.
 unfold normal_ret_assert.
 simpl. apply derives_extract_prop. intro.
 simpl. subst. apply andp_right. apply prop_right; auto.
 apply andp_derives; auto.
 eapply derives_trans; [ | apply H]; clear H.
 simpl. apply exp_derives; intro x.
 unfold PROPx. simpl. apply andp_derives; auto.
 unfold LOCALx; simpl; apply andp_derives; auto.
 unfold local; unfold_coerce.
 apply prop_derives.
 intro; split; auto.
Qed.


Lemma elim_redundant_Delta:
  forall Delta P Q R c Post,
  semax Delta (PROPx P (LOCALx Q R)) c Post ->
  semax Delta (PROPx P (LOCALx (tc_environ Delta:: Q) R)) c Post.
Proof.
 intros.
 eapply semax_pre; try apply H.
  apply andp_left2.
 intro rho; simpl.
 unfold PROPx; simpl; apply andp_derives; auto.
  unfold LOCALx; simpl; apply andp_derives; auto.
  unfold local; unfold_coerce; simpl.
 apply prop_derives; intros [? ?]; auto.
Qed.

Lemma semax_load_assist1:
  forall B P Q1 Q R,
  (forall rho, Q1 rho = True) ->
  B && PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (Q1::Q) (SEPx R)).
Proof. intros; intro rho;  normalize.
 apply andp_left2.
  apply andp_right; auto. apply andp_right; apply prop_right; auto.
 rewrite H; auto.
Qed.

Lemma snd_split_map {A B}:
  forall l: list (A*B), map (@snd _ _) l = snd (split l).
Proof.
  induction l; simpl; auto. destruct a. rewrite IHl.
destruct (split l); f_equal; auto.
Qed.

Lemma semax_ifthenelse_PQR : 
   forall Delta P Q R (b: expr) c d Post,
      bool_type (typeof b) = true ->
     semax Delta (PROPx P (LOCALx (`(typed_true (typeof b)) (eval_expr b) :: Q) (SEPx R)))
                        c Post -> 
     semax Delta (PROPx P (LOCALx (`(typed_false (typeof b)) (eval_expr b) :: Q) (SEPx R)))
                        d Post -> 
     semax Delta (PROPx P (LOCALx (tc_expr Delta b :: Q) (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply semax_pre0; [ | apply semax_ifthenelse]; auto.
 instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
 unfold PROPx, LOCALx; intro rho; normalize.
 eapply semax_pre0; [ | eassumption].
 unfold PROPx, LOCALx; intro rho; normalize.
 eapply semax_pre0; [ | eassumption].
 unfold PROPx, LOCALx; intro rho; normalize.
Qed.
