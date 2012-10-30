Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.

Local Open Scope logic.


Lemma semax_load_field:
forall (Delta: tycontext) sh id t1 fld P e1 v2 t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
  forall (TC0: t1 = typeof e1) 
          (TC2: t2 =
           type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld),
    semax Delta 
       (|> (local (tc_lvalue Delta e1) &&
          (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) v2 * P)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, local (lift2 eq (eval_id id) (subst id (lift0 old) v2)) &&
                  (subst id (lift0 old) 
                    (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) v2 * P)))).
Proof with normalize.
Transparent field_mapsto.
pose proof I.
pose proof I.
intros.
subst t1.
rename H2 into TE1.
apply (semax_pre_post
            (|>(local (tc_lvalue Delta (Efield e1 fld t2)) &&
               (lift2 (mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2 * 
                  (local (lift1 (tc_val t2) v2) && !!(type_is_volatile t2 = false) &&  P))))
            (normal_ret_assert 
              (EX old:val, local (lift2 eq (eval_id id) (subst id (lift0 old) v2)) &&
              (subst id (lift0 old) (lift2 (mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2  * 
                (local (lift1 (tc_val t2) v2) && !!(type_is_volatile t2 = false) && P))))));
  [ | | apply semax_load].

Focus 3. hnf. unfold typecheck_temp_id; rewrite TE1. apply eqb_type_refl.

(* PRECONDITION *)
intro rho.
unfold tc_temp, typecheck_temp_id, local, lift1, lift0.
simpl.
normalize.
apply later_derives.
normalize.
apply derives_trans with ((!!(eqb_type t2 t2 = true) && !!tc_lvalue Delta (Efield e1 fld t2) rho &&
    (!!(typecheck_val (v2 rho) t2 = true) && !!(type_is_volatile t2 = false) && 
     (lift2 (mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2 rho))) * P rho).
apply sepcon_derives; auto.
unfold lift2.
rewrite eqb_type_refl. normalize.
unfold mapsto.
unfold tc_lvalue; simpl. unfold lift2.
unfold tc_lvalue in H3. rewrite H1.
unfold field_mapsto.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite <- TC2.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
case_eq (access_mode t2); intros; normalize.
rewrite H8. 
normalize.
simpl. rewrite H5. rewrite H4. simpl. auto.
normalize.

(* POSTCONDITION *)
intros ek vl. go_lower.
intros old ?.
apply exp_right with old; normalize.
unfold subst. normalize. apply sepcon_derives; auto.
unfold mapsto, field_mapsto.
simpl typeof.
case_eq (access_mode t2); intros; normalize.
unfold eval_field.
rewrite H1; simpl. 
rewrite field_offset_unroll.
destruct (field_offset fld fields); normalize.
unfold eval_struct_field.
destruct (eval_lvalue e1 (env_set rho id old)); normalize.
rewrite <- TC2.
rewrite H4. rewrite H5.
normalize. rewrite H6. normalize.
Opaque field_mapsto.
Qed.

Lemma writable_share_top: writable_share Share.top.
Admitted.

Lemma semax_store_field: 
forall (Delta: tycontext) e1 fld P v0 t2 e2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   semax Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) v0 * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) 
                  (lift1 (eval_cast (typeof e2) t2) (eval_expr e2)) * P)).
Proof.
Transparent field_mapsto.
pose proof I.
intros.
rename H0 into TE1.
rename H2 into TCS.
(*
apply semax_pre with 
  (EX v':val, 
    (|>(local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
      (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) (lift0 v') * P)))).
apply andp_left2.
intro rho. simpl. apply exp_right with (v0 rho). auto.
apply extract_exists_pre; intro v'.
clear v0. rename v' into v0.
*)

pose proof (semax_store Delta (Efield e1 fld t2) e2 v0 Share.top 
               (local (lift1 (tc_val t2) (lift1 (eval_cast (typeof e2) t2) (eval_expr e2))) &&
                 !! (type_is_volatile t2 = false) &&   P)).
simpl typeof in H0. (* rewrite splice_top_top in H0. *)
eapply semax_pre_post ; [ | | apply H0; auto].
3: apply writable_share_top.
apply derives_trans with(|> (local (tc_environ Delta) &&
  (local (tc_lvalue Delta e1) &&
   local (tc_expr Delta (Ecast e2 t2)) &&
   (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) v0 * P)))).
rewrite (later_andp (local (tc_environ Delta))). apply andp_derives; auto.
apply now_later.
apply later_derives.
intro rho; unfold local,lift0,lift1,lift2. simpl.
normalize.
unfold field_mapsto, mapsto.
simpl.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite TE1.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- H1. destruct (access_mode t2); normalize.
apply derives_trans with ((!!tc_lvalue Delta (Efield e1 fld t2) rho &&
    !!tc_expr Delta (Ecast e2 t2) rho &&
     (!!tc_val t2 (eval_cast (typeof e2) t2 (eval_expr e2 rho)) &&
      !!(type_is_volatile t2 = false)) &&
     address_mapsto m (v0 rho) (Share.unrel Share.Lsh Share.top)
       (Share.unrel Share.Rsh Share.top)
       (b, Int.unsigned (Int.add i (Int.repr z)))) * P rho).
apply sepcon_derives; auto. 
apply andp_right; normalize.
unfold tc_lvalue; simpl.
unfold lift2. rewrite TE1.
repeat apply andp_right; apply prop_right; auto.
split; auto. split; auto. rewrite H6; auto.
rewrite H8; simpl; auto.
eapply expr_lemmas.typecheck_val_eval_cast; eauto.
hnf in H4.
destruct H4; auto.
unfold tc_expr in H4.
simpl in H4.
destruct H4; auto.
simpl; 
normalize. rewrite H6; normalize. unfold eval_struct_field.

intros ek vl rho; unfold local, lift1, normal_ret_assert, lift2; simpl.
normalize.
apply sepcon_derives; auto.
unfold mapsto, field_mapsto.
simpl. unfold lift1. rewrite TE1. simpl.
case_eq (access_mode t2); intros; normalize.
rewrite field_offset_unroll.
unfold eval_struct_field.
case_eq (field_offset fld fields); intros; normalize.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite <- H1. rewrite H5.
normalize.
Opaque field_mapsto.
Qed.

Lemma semax_load_field':
forall (Delta: tycontext) sh id t1 fld P Q R e1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
        (temp_types Delta) ! id = Some (t2,i2) ->
  forall 
          (TC2: t2 =
           type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld),
    semax Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::Q) (SEPx (lift2 (field_mapsto sh t1 fld) (eval_expr e1) v2::R))))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (lift2 eq (eval_id id) (subst id (lift0 old) v2) :: map (subst id (lift0 old)) Q)
                (SEPx 
                  (map (subst id (lift0 old))
                    (lift2 (field_mapsto sh t1 fld) (eval_expr e1) v2 :: R)))))).
Proof.
intros.
eapply semax_pre_post;
  [ | |  apply (semax_load_field Delta sh id t1 fld (PROPx P (LOCALx Q (SEPx R))) (Ederef e1 t1)
   v2 t2 i2 sid fields)]; auto.
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' ); [auto 50 with derives | ]
end.
apply later_derives.
go_lower.
rewrite field_mapsto_nonnull.
unfold tc_expr, tc_lvalue.
simpl typecheck_lvalue.
simpl denote_tc_assert.
rewrite H0. rewrite H.
simpl.
normalize.
destruct (eval_expr e1 rho); inv H6; normalize.

normalize.
intro x; apply exp_right with x.
go_lower.
Qed.


Lemma semax_store_field':
forall (Delta: tycontext) t1 fld P Q R e1 e2 v0 t2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield (Ederef e1 t1) fld t2) ->
    semax Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t2)::Q)
                             (SEPx (lift2 (field_mapsto Share.top t1 fld) (eval_expr e1) v0::R))))
       (Sassign (Efield (Ederef e1 t1) fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (lift2 (field_mapsto Share.top t1 fld) (eval_expr e1) 
                  (lift1 (eval_cast (typeof e2) t2) (eval_expr e2)) :: R))))).
Proof.
intros.
eapply semax_pre_post; [ | | eapply (semax_store_field)].
3: subst t1; reflexivity.
3: assumption.
3: assumption.
instantiate (2:=v0).
instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
go_lower. apply later_derives.
normalize.
subst t1.
unfold tc_lvalue.
rewrite field_mapsto_nonnull.
normalize.
unfold bool_val in H.
revert H; case_eq (eval_expr e1 rho); intros; try discriminate; normalize.
repeat apply andp_right; normalize.
simpl.
unfold lift1, denote_tc_isptr.
unfold lift2.
rewrite H.
normalize.
rewrite H0; simpl; normalize.

intros ek vl rho; unfold normal_ret_assert, local, lift1, lift2; simpl.
normalize.
unfold PROPx, LOCALx; simpl.
normalize.
Qed.

Lemma forward_setx:
  forall Delta P id e,
  tc_temp Delta id (typeof e)  ->
  (P |-- local (tc_expr Delta e)) ->
  semax Delta
             P
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  local (lift2 eq (eval_id id) (subst id (lift0 old) (eval_expr e))) &&
                            subst id (lift0 old) P)).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_set_forward Delta P id e); auto].
eapply derives_trans ; [ | apply now_later].
go_lower.
apply andp_right; auto.
apply H0.
intros ek vl rho; unfold normal_ret_assert. simpl; normalize.
apply exp_right with x.
normalize.
Qed.

Lemma normal_ret_assert_derives':
  forall ek vl P Q, 
      P |-- Q ->
      normal_ret_assert P ek vl |-- normal_ret_assert Q ek vl.
Proof. intros; intro rho. apply normal_ret_assert_derives. auto.
Qed.

Lemma normal_ret_assert_derives'':
  forall (P: assert) (Q: ret_assert), 
      (P |-- Q EK_normal nil) ->
      normal_ret_assert P |-- Q.
Proof. intros; intros ek vl rho. 
    unfold normal_ret_assert; destruct ek; simpl; normalize.
   inv H0. inv H0. inv H0.
Qed.


Ltac normalizex :=
  normalize;
  repeat 
  (first [ apply normal_ret_assert_derives
         | apply normal_ret_assert_derives'
         | apply normal_ret_assert_derives''
         | simpl_tc_expr
         | flatten_sepcon_in_SEP
          | apply semax_extract_PROP_True; [solve [auto] | ]
          | apply semax_extract_PROP; intro
         | extract_prop_in_LOCAL
         | extract_exists_in_SEP
         ]; cbv beta; normalize).

Ltac forward_setx := 
  first [eapply semax_seq; 
            [ apply sequential' ; apply forward_setx; [reflexivity | normalizex]
              | apply extract_exists_pre; normalize; try (intros _) ]
         | eapply semax_post;  [ | apply forward_setx; [reflexivity | normalizex]];
            cbv beta; normalize
        ].

Ltac semax_field_tac1 := 
   eapply semax_load_field'; 
     [ reflexivity 
     | reflexivity 
     | simpl; reflexivity 
     | type_of_field_tac ].

Ltac isolate_field_tac e fld R := 
  match R with 
     | context [|> lift2 (field_mapsto ?sh ?struct fld) ?e' ?v :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth; normalize;
                replace e' with (eval_expr e) by auto
     | context [ lift2 (field_mapsto ?sh ?struct fld) ?e' ?v  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth; normalize;
                replace e' with (eval_expr e) by auto
     end.

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end.


Ltac semax_field_tac :=
match goal with
 | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                  (Ssequence (Sset _ (Efield (Ederef ?e _) ?fld _)) _) _ =>
  apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
   [ go_lower 
   | isolate_field_tac e fld R; hoist_later_in_pre;
     eapply semax_seq; [ apply sequential'; semax_field_tac1  
                                          | simpl update_tycon; apply extract_exists_pre
                                          ]
    ]
 | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset _ (Efield (Ederef ?e _) ?fld _)) _ =>
     apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
     [ go_lower 
     | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post; [ | semax_field_tac1]
     ]
end; normalizex.


Ltac store_field_tac1 := 
  eapply semax_store_field'; [ reflexivity | reflexivity | type_of_field_tac |
               try solve [hnf; intuition] ].

Ltac store_field_tac :=
  match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Ssequence (Sassign (Efield (Ederef ?e _) ?fld ?t2) ?e2) _) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ unfold tc_expr; go_lower 
   | isolate_field_tac e fld R; hoist_later_in_pre;
      eapply semax_seq; [ apply sequential'; store_field_tac1   |  ]
   ]
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Efield (Ederef ?e _) ?fld ?t2) ?e2) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ unfold tc_expr; go_lower 
   | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post; [ | store_field_tac1]
   ]
  end.

Ltac check_sequential s :=
 match s with
 | Sskip => idtac
 | Sassign _ _ => idtac
 | Sset _ _ => idtac
 | Scall _ _ _ => idtac
 | Ssequence ?s1 ?s2 => check_sequential s1; check_sequential s2
 | _ => fail
 end.

Ltac sequential := 
 match goal with
 |  |- semax _ _ _ (normal_ret_assert _) => fail 2
 |  |- semax _ _ ?s _ =>  check_sequential s; apply sequential
 end.

Ltac is_canonical P :=
 match P with 
 | PROPx _ (LOCALx _ (SEPx _)) => idtac
 | _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
 end.

Ltac forward := 
  match goal with
  | |- semax _ ?P (Ssequence (Sassign (Efield _ _ _) _) _) _ => 
                  is_canonical P; store_field_tac
  | |- semax _ ?P (Sassign (Efield _ _ _) _) _ => 
                  is_canonical P; store_field_tac
  | |- semax _ ?P (Ssequence (Sset _ (Efield _ _ _)) _) _ => 
                  is_canonical P; semax_field_tac
  | |- semax _ ?P (Sset _ (Efield _ _ _)) _ => 
                  is_canonical P; semax_field_tac
  | |- semax _ ?P (Ssequence (Sset _ ?e) _) _ => 
               is_canonical P; match e with (Efield _ _ _) => fail 2 | _ => forward_setx end
  | |- semax _ ?P (Sset _ ?e) _ => 
               is_canonical P; match e with (Efield _ _ _) => fail 2 | _ => forward_setx end
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
          apply semax_seq with FF; [eapply semax_pre; [ | apply semax_return ]
                                | apply semax_ff]
  | |- semax _ _ (Sreturn _) _ =>
          eapply semax_pre; [ | apply semax_return ]
  end.

