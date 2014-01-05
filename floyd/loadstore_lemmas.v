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
              local (`(tc_val t2) v2) &&
          (`(field_at sh t1 fld) v2 (eval_lvalue e1) * P)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                  (subst id (`old) 
                    (`(field_at sh t1 fld) v2 (eval_lvalue e1) * P)))).
Proof.
pose proof I.
pose proof I.
intros. rename H5 into CLASSIFY.
rename H3 into TC0; rename H4 into TC2.
subst t1.
rename H2 into TE1.
apply (semax_pre_post
            (|>(local (tc_lvalue Delta (Efield e1 fld t2)) &&
                 local (tc_temp_id_load id (typeof (Efield e1 fld t2)) Delta v2) && 
                 local (`(tc_val (typeof (Efield e1 fld t2))) v2) &&
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
unfold field_at; unfold_lift. 
rewrite H1.
rewrite field_offset_unroll. rewrite <- TC2.
normalize.
case_eq (field_offset fld fields); intros; 
 try (rewrite FF_sepcon; apply FF_left).
unfold mapsto.
rewrite sepcon_andp_prop'.
  apply derives_extract_prop; intro.
repeat apply andp_right; try apply prop_right.
unfold tc_lvalue. 
unfold typecheck_lvalue; fold typecheck_lvalue. rewrite H1.
rewrite H6; simpl tc_bool.
rewrite H5. repeat rewrite tc_andp_TT2.
repeat split; auto.
exists t2; exists i2; split; auto.
unfold allowedValCast. rewrite CLASSIFY.
destruct t2; simpl; auto.
unfold mapsto.
case_eq (access_mode t2); intros;
 try (rewrite FF_sepcon; apply FF_left).
simpl. rewrite H5.
destruct (offset_val (Int.repr z) (eval_lvalue e1 rho)); 
 try (rewrite FF_sepcon; apply FF_left).
apply sepcon_derives; auto.

(* POSTCONDITION *)
intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives. intro old.
apply andp_derives; auto.
unfold subst. go_lowerx.
rewrite sepcon_andp_prop. apply derives_extract_prop. intro.
unfold mapsto, field_at, field_at.
rewrite H1. 
 rewrite field_offset_unroll.
simpl. unfold_lift.
apply sepcon_derives; auto. 
unfold always.
destruct (field_offset fld fields);  simpl; try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
repeat apply andp_right; try apply prop_right; auto.
destruct (access_mode t2); auto.
Qed.

Lemma semax_store_field: 
forall Espec (Delta: tycontext) sh e1 fld P t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (`(field_at_ sh (typeof e1) fld) (eval_lvalue e1) * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (`(field_at sh (typeof e1) fld) 
                  (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2))) (eval_lvalue e1)  * P)).
Proof.
pose proof I. intros until fields. intro WS.
intros.
rename H0 into TE1.
unfold field_at_, field_at.

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
rewrite TE1. rewrite <- H1. rewrite field_offset_unroll.
destruct (field_offset fld fields);
   try (rewrite FF_sepcon; apply FF_left).
normalize.
unfold mapsto.
destruct (access_mode t2);    try (rewrite FF_sepcon; apply FF_left).
case_eq (eval_lvalue e1 rho); simpl; intros; try rewrite FF_sepcon; try apply FF_left.
rewrite distrib_orp_sepcon.
apply orp_left.
normalize. elimtype False; clear - H3; destruct t2; contradiction.
normalize. apply exp_right with v2'. normalize.
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
unfold mapsto_, mapsto.
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
eapply expr_lemmas.typecheck_val_sem_cast; eassumption.
apply sepcon_derives; auto.
simpl.
apply orp_right2. apply andp_right; try apply prop_right; auto.
apply exp_right with v0; auto.

intros ek vl; unfold normal_ret_assert; go_lowerx.
normalize.
apply sepcon_derives; auto.
unfold mapsto, field_at.
rewrite TE1.
rewrite field_offset_unroll.
simpl.
case_eq (field_offset fld fields); simpl; intros; try apply FF_left.
rewrite <- H1.
destruct (access_mode t2); try apply FF_left.
rewrite prop_true_andp by auto.
auto.
destruct (access_mode t2); try apply FF_left.
Qed.

Lemma SEP_TT_right:
  forall R, R |-- SEP(TT).
Proof. intros. go_lowerx. rewrite sepcon_emp. apply TT_right.
Qed.

Lemma semax_store_field_nth:
forall Espec (Delta: tycontext) n sh t1 fld P Q R e1 e2 t2 R1 sid fields, 
    nth_error R n = Some R1 ->
    writable_share sh ->
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    R1 |-- `(field_at_ sh t1 fld) (eval_lvalue e1) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  
              local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(field_at sh t1 fld)
                       (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2)))
                         (eval_lvalue e1) )))))).
Proof.
intros.
subst t1.
eapply semax_pre_post ; [ | |
 apply (semax_store_field Espec Delta sh e1 fld
       (PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))
    t2 e2 sid fields H0); auto].
*
apply later_left2.
repeat rewrite insert_local.
apply andp_right; auto.
rewrite insert_SEP.
rewrite H2.
match goal with |- ?A |-- _ => rewrite <- (andp_dup A) end.
eapply derives_trans; [apply andp_derives; [| apply derives_refl ] | ].
apply H5.
rewrite (SEP_nth_isolate _ _ _ H).
go_lowerx.  apply sepcon_derives; auto.
apply H4.
*
intros ek vl; unfold normal_ret_assert.
normalize. rewrite insert_SEP.
apply andp_left2.
rewrite (SEP_replace_nth_isolate _ _ _ _ H).
unfold exit_tycon.
rewrite <- H2. auto.
Qed.


(* move this to client_lemmas *)
Lemma subst_ewand: forall i v (P Q: environ->mpred),
  subst i v (ewand P Q) = ewand (subst i v P) (subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_ewand : subst.

Lemma semax_load_37 : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 (v2: environ -> val),
      local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && 
       local (tc_temp_id_load id (typeof e1) Delta v2) && 
       local (`(tc_val (typeof e1)) v2) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                                          (subst id (`old) P))).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_load Delta sh id
   (local (tc_environ Delta) && local (`(tc_val (typeof e1)) v2)  
     && ewand (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2) P)
   e1 v2)].
* 
intros.
apply later_left2.
go_lowerx.
eapply derives_refl'; apply res_predicates.superprecise_ewand_lem1.
apply superprecise_mapsto.
intro Hx; rewrite Hx in H3; apply tc_val_Vundef in H3; auto.
change (P rho |-- (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT) rho). 
eapply derives_trans; [ | apply H].
normalize.
*
intros.
go_lowerx.
apply normal_ret_assert_derives.
apply exp_derives; intro old.
apply andp_derives; auto.
unfold subst.
normalize.
apply derives_refl'; symmetry; 
 apply res_predicates.superprecise_ewand_lem1.
apply superprecise_mapsto.
intro Hx; rewrite Hx in H2; apply tc_val_Vundef in H2; auto.
change (P (env_set rho id old) |-- (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT) (env_set rho id old)).
eapply derives_trans; [ | apply H].
normalize.
Qed.

Lemma semax_cast_load_37 : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t1 (v2: environ -> val),
      local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && 
       local (tc_temp_id_load id t1 Delta (`(eval_cast (typeof e1) t1) v2)) && 
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1) v2)) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1) v2))) &&
                                          (subst id (`old) P))).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_cast_load Delta sh id
   (local (tc_environ Delta) && local (`(tc_val t1) (`(eval_cast (typeof e1) t1) v2))  
     && ewand (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2) P)
   e1 t1 v2)].
* 
intros.
apply later_left2.
go_lowerx.
eapply derives_refl'; apply res_predicates.superprecise_ewand_lem1.
apply superprecise_mapsto.
change (tc_val t1 (eval_cast (typeof e1) t1 (v2 rho))) in H3.
intro Hx; rewrite Hx, semax_straight.eval_cast_Vundef in H3; apply tc_val_Vundef in H3; auto.
change (P rho |-- (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT) rho). 
eapply derives_trans; [ | apply H].
normalize.
*
intros.
go_lowerx.
apply normal_ret_assert_derives.
apply exp_derives; intro old.
apply andp_derives; auto.
unfold subst.
normalize.
apply derives_refl'; symmetry; 
 apply res_predicates.superprecise_ewand_lem1.
apply superprecise_mapsto.
change (tc_val t1(eval_cast (typeof e1) t1 (v2 (env_set rho id old)))) in H2.
intro Hx; rewrite Hx, semax_straight.eval_cast_Vundef in H2; apply tc_val_Vundef in H2; auto.
change (P (env_set rho id old) |-- (`(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT) (env_set rho id old)).
eapply derives_trans; [ | apply H].
normalize.
Qed.

Lemma semax_load_37' : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P Q R e1 (v2: val),
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         local (tc_lvalue Delta e1) &&
         local (tc_temp_id_load id (typeof e1) Delta `v2) &&
         local (`(tc_val (typeof e1) v2)) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id e1)
       (normal_ret_assert (EX old:val, 
             PROPx P 
   (LOCALx (`eq (eval_id id) `v2 :: map (subst id (`old)) Q)
     (SEPx (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_pre_post; [ | | apply semax_load_37 with sh].
* instantiate (1:= PROPx P (LOCALx Q (SEPx R))).
  apply later_left2.
  rewrite insert_local.
  rewrite <- (andp_dup (PROPx P (LOCALx (_ :: _) _))).
  eapply derives_trans.
  apply andp_derives; [apply derives_refl | apply H].
  clear H.
  go_lowerx.
  autorewrite with gather_prop.
  apply derives_extract_prop; intros [? [? ?]].
  apply andp_right.
  apply prop_right; repeat split; eassumption.
  apply andp_left1; auto.
* intros. apply andp_left2; auto.
  apply normal_ret_assert_derives'.
  apply exp_derives; intro old.
  autorewrite with subst.
  rewrite insert_local.
  apply andp_derives; auto.
* rewrite insert_local.
  eapply derives_trans; [apply H | clear H].
  apply andp_left2. auto.
Qed.

Lemma semax_cast_load_37' : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P Q R e1 t1 (v2: val),
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         local (tc_lvalue Delta e1) &&
         local (tc_temp_id_load id t1 Delta `(eval_cast (typeof e1) t1 v2)) &&
         local (`(tc_val t1 (eval_cast (typeof e1) t1 v2))) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, 
             PROPx P 
   (LOCALx (`eq (eval_id id) `(eval_cast (typeof e1) t1 v2) :: map (subst id (`old)) Q)
     (SEPx (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_pre_post; [ | | apply semax_cast_load_37 with (sh0:=sh)(v3:= `v2)].
* instantiate (1:= PROPx P (LOCALx Q (SEPx R))).
  apply later_left2.
  rewrite insert_local.
  rewrite <- (andp_dup (PROPx P (LOCALx (_ :: _) _))).
  eapply derives_trans.
  apply andp_derives; [apply derives_refl | apply H].
  clear H.
  go_lowerx.
  autorewrite with gather_prop.
  apply derives_extract_prop; intros [? [? ?]].
  apply andp_right.
  apply prop_right; repeat split; eassumption.
  apply andp_left1; auto.
* intros. apply andp_left2; auto.
  apply normal_ret_assert_derives'.
  apply exp_derives; intro old.
  autorewrite with subst.
  rewrite insert_local.
  apply andp_derives; auto.
* rewrite insert_local.
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
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
        |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t2 v ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, PROPx P 
                     (LOCALx (`(eq v) (eval_id id) :: map (subst id (`old)) Q)
                     (SEPx (map (subst id (`old)) R))))).
Proof.
pose proof I.
pose proof I.
intros until fields; intros H1 H2 TE1 TC2 CLASSIFY TC3 H6 TC4.
subst t1.
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
 (local (tc_lvalue Delta e1)  && (`(field_at sh (typeof e1) fld v) (eval_lvalue e1) * TT)).
apply andp_right.
eapply derives_trans; [ | apply TC3].
apply andp_right. apply andp_left1; auto. apply andp_right; [ |  apply andp_left2; auto].
eapply derives_trans; [apply H6 | ].
go_lowerx. rewrite field_at_isptr. clear; normalize.
auto.
go_lowerx.
unfold field_at, tc_lvalue, tc_temp_id_load.
simpl. rewrite H1. rewrite field_offset_unroll.
destruct (field_offset fld fields);   try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
normalize.
apply prop_right; repeat split; auto.
rewrite denote_tc_assert_andp; split.
apply H3. rewrite H4. apply I.
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
unfold field_at.
go_lowerx.
unfold_lift.
rewrite H1.
rewrite field_offset_unroll.
simpl.
destruct (field_offset fld fields);   try apply FF_left.
rewrite <- TC2.
normalize.
Qed.


Lemma semax_cast_load_field'':
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t1' t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t1',i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    Cop.classify_cast t1' t1' = Cop.cast_case_neutral -> 
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                           |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
        |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t1' (eval_cast t2 t1' v) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Efield e1 fld t2) t1'))
       (normal_ret_assert (
         EX old:val, PROPx P 
                     (LOCALx (`(eq (eval_cast t2 t1' v)) (eval_id id) :: map (subst id (`old)) Q)
                     (SEPx (map (subst id (`old)) R))))).
Proof.
pose proof I.
pose proof I.
intros until fields; intros H1 H2 TE1 TC2 CLASSIFY TC3 H6 TC4.
subst t1. rename t1' into t1.
repeat rewrite <- insert_local in H6.
repeat rewrite <- insert_local in TC3.
replace  (EX  old : val,
      PROPx P
        (LOCALx (`(eq (eval_cast t2 t1 v)) (eval_id id) :: map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))
  with  (EX  old : val, local (`(eq (eval_cast t2 t1 v)) (eval_id id)) && 
                   subst id `old (PROPx P (LOCALx Q (SEPx R))))
  by (f_equal; extensionality old; autorewrite with subst; rewrite insert_local; auto).
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
eapply semax_pre_post; [ | | 
   apply (semax_cast_load_37 Delta sh id PQR _ _ `v)].
* (* PRECONDITION *)
apply later_left2.
apply andp_right; [ | apply andp_left2; auto].
apply derives_trans with 
 (local (tc_lvalue Delta e1)  && (`(field_at sh (typeof e1) fld v) (eval_lvalue e1) * TT)).
apply andp_right.
eapply derives_trans; [ | apply TC3].
apply andp_right. apply andp_left1; auto. apply andp_right; [ |  apply andp_left2; auto].
eapply derives_trans; [apply H6 | ].
go_lowerx. rewrite field_at_isptr. clear; normalize.
auto.
go_lowerx.
unfold field_at, tc_lvalue, tc_temp_id_load.
simpl. rewrite H1. rewrite field_offset_unroll.
destruct (field_offset fld fields);   try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
normalize.
apply prop_right; repeat split; auto.
rewrite denote_tc_assert_andp; split.
apply H3. rewrite H4. apply I.
exists t1,i2. split; auto.
unfold allowedValCast. rewrite CLASSIFY.
change (force_val (sem_cast t2 t1 v)) with (eval_cast t2 t1 v).
rewrite eqb_reflx.
clear.
destruct t1; try reflexivity.
* (* POSTCONDITION *)
intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives; intro old.
apply andp_derives; auto.
clear; intro; unfold_lift; apply prop_derives; auto.
*
 eapply derives_trans; [ apply H6 | ].
apply sepcon_derives; auto.
unfold field_at.
go_lowerx.
unfold_lift.
rewrite H1.
rewrite field_offset_unroll.
simpl.
destruct (field_offset fld fields);   try apply FF_left.
rewrite <- TC2.
normalize.
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
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
                     |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t2 v ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_post';[ | eapply semax_load_field''; eauto].
apply exp_left; intro old.
autorewrite with subst. auto.
Qed.

Lemma semax_cast_load_field_38:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t1' t2 i2 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t1',i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    Cop.classify_cast t1' t1' = Cop.cast_case_neutral -> 
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                     |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
                     |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t1' (eval_cast t2 t1' v) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Efield e1 fld t2) t1'))
       (normal_ret_assert (PROPx P (LOCALx (`(eq (eval_cast t2 t1' v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_post';[ | eapply semax_cast_load_field''; eauto].
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
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
         |--  local (tc_expr Delta e1) && (`(field_at sh t1 fld v) (eval_expr e1) * TT) ->
   tc_val t2 v ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros. rename H7 into TC4.
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
clear; go_lowerx. rewrite field_at_isptr; normalize.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue; simpl denote_tc_assert.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite H4. apply I.
rewrite H1; apply I.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
apply sepcon_derives; auto.
go_lowerx.
unfold_lift. rewrite field_at_force_ptr.
apply derives_refl.
Qed.

Lemma semax_cast_load_field_40:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t1' t2 i2 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    t1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t1',i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   typeof e1 = tptr t1 ->
    Cop.classify_cast t1' t1' = Cop.cast_case_neutral -> 
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
         |--  local (tc_expr Delta e1) && (`(field_at sh t1 fld v) (eval_expr e1) * TT) ->
   tc_val t1' (eval_cast t2 t1' v) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Efield (Ederef e1 t1) fld t2) t1'))
       (normal_ret_assert (PROPx P (LOCALx (`(eq (eval_cast t2 t1' v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros. rename H7 into TC4.
eapply semax_cast_load_field_38; eauto.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local.
apply derives_trans with (local (tc_expr Delta e1) && local (`isptr (eval_expr e1))).
apply andp_right; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left1; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
clear; go_lowerx. rewrite field_at_isptr; normalize.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue; simpl denote_tc_assert.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite H4. apply I.
rewrite H1; apply I.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
apply sepcon_derives; auto.
go_lowerx.
unfold_lift. rewrite field_at_force_ptr.
apply derives_refl.
Qed.

