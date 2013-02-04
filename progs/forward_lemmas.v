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

Lemma field_storable_nonnull:  forall t fld sh x, 
     field_storable sh t fld x = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_storable sh t fld x.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_storable.
unfold Cop.bool_val.
destruct x; normalize.
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

Lemma semax_post_flipped:
  forall (R' : ret_assert) (Delta : tycontext) (R : ret_assert)
         (P : assert) (c : statement),
        semax Delta P c R' -> 
       (forall (ek : exitkind) (vl : option val),
        local (tc_environ (exit_tycon c Delta ek)) && R' ek vl |-- R ek vl) ->
       semax Delta P c R.
Proof. intros; eapply semax_post; eassumption. Qed.

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

Lemma semax_call': forall Delta A (Pre Post: A -> assert) (x: A) ret fsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig) ->
   match fsig, ret with
   | (_, Tvoid), None => True
   | (_, Tvoid), Some _ => False
   | _, Some _ => True
   | _, _ => False
   end ->
  semax Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
            (SEPx (`(Pre x) ( (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl))) ::
                      `(fun_assert_emp fsig A Pre Post) (eval_expr a) :: R))))
          (Scall ret a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (substopt ret (`old)) Q) 
                (SEPx (`(Post x) (get_result ret) :: map (substopt ret (`old)) R))))).
Proof.
 intros.
eapply semax_pre_post ; [ | | 
   apply (semax_call Delta A Pre Post x (PROPx P (LOCALx Q (SEPx R))) ret fsig a bl H)].
 Focus 3.
 clear - H0.
 destruct fsig. destruct t; destruct ret; simpl in *; try contradiction; split; intros; congruence.
 intro rho; normalize.
unfold fun_assert_emp.
repeat rewrite corable_andp_sepcon2 by apply corable_fun_assert.
normalize.
rewrite corable_sepcon_andp1 by apply corable_fun_assert.
rewrite sepcon_comm; auto. 
intros.
normalize.
intro old.
apply exp_right with old; destruct ret; normalize.
intro rho; normalize.
rewrite sepcon_comm; auto.
intro rho; normalize.
rewrite sepcon_comm; auto.
unfold substopt.
repeat rewrite list_map_identity.
normalize.
Qed.

Lemma semax_call1: forall Delta A (Pre Post: A -> assert) (x: A) id fsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig) ->
   match fsig with
   | (_, Tvoid) => False
   | _ => True
   end ->
  semax Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
            (SEPx (`(Pre x) ( (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl))) ::
                      `(fun_assert_emp fsig A Pre Post) (eval_expr a) :: R))))
          (Scall (Some id) a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (subst id (`old)) Q) 
                (SEPx (`(Post x) (get_result1 id) :: map (subst id (`old)) R))))).
Proof.
intros.
apply semax_call'; auto.
Qed.

Lemma semax_fun_id':
      forall id fsig (A : Type) (Pre Post : A -> assert)
              Delta P Q R PostCond c
            (GLBL: (var_types Delta) ! id = None),
            (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A Pre Post)) ->
       semax Delta 
        (PROPx P (LOCALx Q (SEPx (`(fun_assert_emp fsig A Pre Post)
                         (eval_lvalue (Evar id (type_of_funsig fsig))) :: R))))
                              c PostCond ->
       semax Delta (PROPx P (LOCALx Q (SEPx R))) c PostCond.
Proof.
intros. 
apply (semax_fun_id id fsig A Pre Post Delta); auto.
eapply semax_pre; [ | apply H0].
forget (eval_lvalue (Evar id (type_of_funsig fsig))) as f.
intro rho; normalize.
rewrite andp_comm.
unfold fun_assert_emp.
rewrite corable_andp_sepcon2 by apply corable_fun_assert.
rewrite emp_sepcon; auto.
Qed.

Lemma eqb_typelist_refl: forall tl, eqb_typelist tl tl = true.
Proof.
induction tl; simpl; auto.
apply andb_true_iff.
split; auto.
apply eqb_type_refl.
Qed.


Lemma semax_call_id1:
 forall Delta P Q R ret id argtys retty bl fsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A Pre Post)) ->
   match fsig with
   | (_, Tvoid) => False
   | _ => True
   end ->
   argtys = type_of_params (fst fsig) ->
   retty = snd fsig ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (`(Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction argtys retty))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Evar id (Tfunction argtys retty)))=
               Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig)).
subst; reflexivity.
apply semax_fun_id' with id fsig A Pre Post; auto.
subst. 
eapply semax_pre; [ | apply (semax_call1 Delta A Pre Post x ret fsig  _ bl P Q R H3 H0)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
autorewrite with normalize.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. split; hnf; auto.
auto.
change SEPx with SEPx'.
simpl.
intro rho.
rewrite sepcon_comm.
rewrite sepcon_assoc.
autorewrite with normalize.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
Qed.


Lemma semax_call_id1':
 forall Delta P Q R ret id argtys retty bl fsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A Pre Post)) ->
   match fsig with
   | (_, Tvoid) => False
   | _ => True
   end ->
   argtys = type_of_params (fst fsig) ->
   retty = snd fsig ->
  forall 
   (CLOSQ: Forall (closed_wrt_vars (eq ret)) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret)) R),
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (`(Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction argtys retty))
             bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q   (SEPx (`(Post x) (get_result1 ret) ::  R))))).
Proof.
intros.
eapply semax_post;
  [ | apply (semax_call_id1 Delta P Q R ret id argtys retty bl fsig A x Pre Post 
     GLBL H H0 H1 H2)].
intros ek vl.
apply andp_left2.
unfold normal_ret_assert.
apply andp_derives; auto.
apply andp_derives; auto.
apply exp_left; intro v.
apply andp_derives; auto.
apply andp_derives.
unfold local, lift1 ;intro rho.
clear - CLOSQ.
apply prop_left. intro.
apply prop_right.
induction Q; simpl; auto.
inv CLOSQ.
destruct H.
split.
rewrite closed_wrt_subst in H; auto.
auto.
clear - CLOSR.
change SEPx with SEPx'.
unfold SEPx'. intro rho.
simpl.
apply sepcon_derives; auto.
induction R; simpl; auto.
inv CLOSR.
apply sepcon_derives.
rewrite closed_wrt_subst; auto.
apply IHR; auto.
Qed.

Lemma semax_call_id1_Eaddrof:
 forall Delta P Q R ret id argtys retty bl fsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A Pre Post)) ->
   match fsig with
   | (_, Tvoid) => False
   | _ => True
   end ->
   argtys = type_of_params (fst fsig) ->
   retty = snd fsig ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (`(Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Scall (Some ret)
             (Eaddrof (Evar id (Tfunction argtys retty)) (Tpointer (Tfunction argtys retty) noattr))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Eaddrof (Evar id (Tfunction argtys retty)) (Tpointer (Tfunction argtys retty) noattr)))=
               Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig)).
subst; reflexivity.
apply semax_fun_id' with id fsig A Pre Post; auto.
subst. 
eapply semax_pre; [ | apply (semax_call1 Delta A Pre Post x ret fsig  _ bl P Q R H3 H0)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
autorewrite with normalize.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. apply I.
auto.
change SEPx with SEPx'.
simpl.
intro rho.
cancel.
Qed.


Lemma semax_call_id_aux1: forall P Q1 Q R S,
     PROPx P (LOCALx (Q1::Q) R) |-- S -> local Q1 && PROPx P (LOCALx Q R) |-- S.
Proof. intros. eapply derives_trans; try apply H.
  intro rho; normalize.
 unfold PROPx. simpl.
 apply andp_derives; auto.
 unfold LOCALx. simpl.
 unfold local,lift2,lift1.
 apply derives_extract_prop; intro.
 apply andp_right; auto.
 apply prop_right; split; auto.
Qed.

(* BEGIN HORRIBLE1.
  The following lemma is needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
 See also BEGIN HORRIBLE1 in forward.v
*)


Lemma semax_call_id1_x:
 forall Delta P Q R ret ret' id argtys retty bl fsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A Pre Post)) ->
   match fsig with
   | (_, Tvoid) => False
   | _ => True
   end ->
   argtys = type_of_params (fst fsig) ->
   retty = snd fsig ->
  forall
   (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret')) R),
   type_is_volatile retty = false -> 
   (temp_types Delta) ! ret' = Some (retty, false) ->
   is_neutral_cast retty retty = true ->
   match (temp_types Delta) ! ret with Some (t,_) => eqb_type t retty | None => false end = true ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (`(Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction argtys retty))
             bl)
      (Sset ret (Etempvar ret' retty)))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
 intros. rename H3 into NONVOL.
 eapply semax_seq'.
 apply (semax_call_id1' _ P Q R ret' _ _ _ bl _ _ x _ _ GLBL H H0 H1 H2 CLOSQ CLOSR).
match goal with |- semax ?D (PROPx ?P ?QR) ?c ?Post =>
   assert ( (fold_right and True P) -> semax D (PROPx nil QR) c Post)
 end.
Focus 2.
 clear - H3.
 unfold PROPx. 
 unfold PROPx at 1 in H3.
 normalize in H3.
 apply semax_extract_prop. apply H3.
 (* End Focus 2 *)
 intro.
 apply semax_post_flipped
 with (normal_ret_assert (EX  x0 : val,
PROP  ()
(LOCALx
   (tc_environ
      (initialized ret
         (update_tycon Delta
            (Scall (Some ret') (Evar id (Tfunction argtys retty)) bl)))
    :: `eq (eval_id ret)
         (subst ret (`x0) (eval_expr (Etempvar ret' retty)))
       :: map (subst ret (`x0)) Q)
   (SEPx
      (map (subst ret (`x0)) (`(Post x) (get_result1 ret') :: R)))))).
  make_sequential;
          eapply semax_post_flipped;
          [ apply forward_setx; 
            try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ]
           | intros ?ek ?vl; apply after_set_special1 ].
 apply andp_right.
 intro rho; unfold tc_expr; simpl.
 rewrite NONVOL. simpl.
 replace ( (temp_types (initialized ret' Delta)) ! ret' ) 
     with (Some (retty, true)).
Focus 2.
 unfold initialized;  simpl. rewrite H4.
 unfold temp_types; simpl.
 rewrite PTree.gss. auto.
 (* End Focus 2 *)
 unfold local; apply prop_right.
 simpl. rewrite eqb_type_refl. apply I.
 intro rho; apply prop_right; unfold tc_temp_id; simpl.
 unfold typecheck_temp_id.
 destruct (eq_dec ret' ret).
 subst ret'.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gss.
 rewrite H5.
 simpl.
 unfold isCastResultType. unfold is_neutral_cast in H5.
 destruct (Cop.classify_cast retty retty); try discriminate.
 rewrite eqb_type_refl. apply I.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gso by auto. 
 destruct ((temp_types Delta) ! ret); try discriminate.
 destruct p. apply eqb_type_true in H6.
 subst t. rewrite H5.
 simpl.
 unfold isCastResultType. unfold is_neutral_cast in H5.
 destruct (Cop.classify_cast retty retty); try discriminate.
 rewrite eqb_type_refl. apply I.
 auto.
 intros.
 apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 apply andp_derives.
 apply prop_right; auto.
 intro rho; unfold LOCALx, local.
change SEPx with SEPx'.
 simpl. 
  normalize.
 unfold coerce, lift1_C, lift0_C.
 apply sepcon_derives; auto.
 normalize.
 replace (subst ret (lift0 old) (get_result1 ret') rho)
   with (get_result1 ret rho); auto.
 destruct (eq_dec ret ret').
 subst.
 unfold get_result1.
 unfold subst. f_equal.
 normalize in H8.
 normalize. f_equal. auto.
 clear - H6 H8 H7.
 unfold tc_environ in H7.
 unfold env_set. destruct rho; simpl in *; f_equal.
 unfold eval_id in H8; simpl in H8. unfold subst in H8.
 simpl in *. rewrite Map.gss in H8. simpl in H8.
 unfold_coerce. subst.
 unfold Map.set. extensionality i. 
 destruct (ident_eq i ret'); auto.  subst i.
 unfold typecheck_environ in H7.
 repeat rewrite andb_true_iff in H7.
 destruct H7 as [[[? _] _] _].
 simpl te_of in H.
 apply environ_lemmas.typecheck_te_eqv in H.
 hnf in H.
 specialize (H ret').
 revert H6; case_eq ((temp_types Delta)!ret'); intros; try discriminate.
 destruct p.
 unfold temp_types, initialized in H; simpl in H.
 rewrite H0 in H. unfold temp_types in *. simpl in H. rewrite PTree.gss in H.
 simpl in H. rewrite PTree.gss in H.
 specialize (H true t (eq_refl _)). 
 destruct H as [v [? ?]]. rewrite H.
 apply H.
  rewrite closed_wrt_subst; auto with closed.
 unfold get_result1.
 f_equal. f_equal.
 rewrite H8.
  rewrite closed_wrt_subst; auto with closed.
Qed.

(* END HORRIBLE1 *)

