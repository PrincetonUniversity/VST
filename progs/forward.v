Load loadpath.
Require Import Coqlib veric.Coqlib2.
Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.

Local Open Scope logic.

Lemma prop_derives {A}{ND: NatDed A}: 
 forall (P Q: Prop), (P -> Q) -> prop P |-- prop Q.
Proof.
intros; apply prop_left; intro; apply prop_right; auto.
Qed.

Lemma forward_setx_closed_now':
  forall Delta (Q: list (environ -> Prop)) (R: list assert) id e,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx nil (LOCALx Q (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  semax Delta (PROPx nil (LOCALx Q (SEPx R))) (Sset id e) 
        (normal_ret_assert (PROPx nil (LOCALx (lift2 eq (eval_id id) (eval_expr e)::Q) (SEPx R)))).
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
  normal_ret_assert (PROPx nil (LOCALx (lift2 eq (eval_id id) (eval_expr e)::Q) (SEPx R))) |-- PQR ->
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
           (PROPx nil (LOCALx (lift2 eq (eval_id id) (eval_expr e)::Q) (SEPx R))) c PQR ->
  semax Delta (PROPx nil (LOCALx Q (SEPx R))) (Ssequence (Sset id e) c) PQR.
Proof.
 intros.
 eapply semax_seq.
 apply sequential'.
 apply forward_setx_closed_now; auto.
 apply H4.
Qed.

(* Admitted: move these next two to assert_lemmas *)
Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : normalize.

Lemma semax_load_field:
forall (Delta: tycontext) sh id t1 fld P e1 v2 t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    semax Delta 
       (|> (local (tc_lvalue Delta e1) &&
          (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) v2 * P)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, local (lift2 eq (eval_id id) (subst id (lift0 old) v2)) &&
                  (subst id (lift0 old) 
                    (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) v2 * P)))).
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
                 local (lift1 (tc_val t2) v2) &&
               (lift2 (mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2 * 
                        (local (lift1 (tc_val t2) v2) &&  !!(type_is_volatile t2 = false) &&  P))))
            (normal_ret_assert 
              (EX old:val, local (lift2 eq (eval_id id) (subst id (lift0 old) v2)) &&
              (subst id (lift0 old) (lift2 (mapsto sh t2) (eval_lvalue (Efield e1 fld t2)) v2  * 
                ( local (lift1 (tc_val t2) v2) && !!(type_is_volatile t2 = false) && P))))));
  [ | | apply semax_load].

(* PRECONDITION *)
intro rho.
unfold tc_temp_id_load, local, lift1, lift0.
simpl.
apply derives_extract_prop; intro.
apply later_derives.
apply derives_extract_prop; intro.
unfold field_mapsto, lift2. 
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
unfold eval_field. rewrite H5. unfold eval_struct_field. rewrite H4.
 rewrite H8.
unfold tc_val; rewrite H7.
normalize.

(* POSTCONDITION *)
intros ek vl.
apply andp_left2.
intro rho. apply normal_ret_assert_derives.
simpl.
apply exp_derives. intro old.
apply andp_derives; auto.
unfold subst.
unfold lift2.
unfold mapsto, field_mapsto.
case_eq (access_mode t2); intros; 
 try (rewrite FF_sepcon; apply FF_left).
unfold lift1.
rewrite H1.
simpl eval_field.
rewrite field_offset_unroll.
destruct (field_offset fld fields);  try (rewrite FF_sepcon; apply FF_left).
unfold eval_struct_field.
unfold lift0.
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
 unfold denote_tc_assert, tc_andp, lift2,lift1,lift0.
 destruct a,b; simpl; intuition; try contradiction.
Qed.

Lemma semax_store_field: 
forall (Delta: tycontext) sh e1 fld P v0 t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   semax Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (lift2 (field_mapsto sh (typeof e1) fld) (eval_lvalue e1) v0 * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (lift2 (field_mapsto sh (typeof e1) fld) (eval_lvalue e1) 
                  (lift1 (eval_cast (typeof e2) t2) (eval_expr e2)) * P)).
Proof.
Transparent field_mapsto.
pose proof I. intros until fields. intro WS.
intros.
rename H0 into TE1.
rename H2 into TCS.

pose proof (semax_store Delta (Efield e1 fld t2) e2 v0 sh 
               (local (lift1 (tc_val t2) (lift1 (eval_cast (typeof e2) t2) (eval_expr e2))) &&
                 !! (type_is_volatile t2 = false) &&   P)).
simpl typeof in H0. 
eapply semax_pre_post ; [ | | apply H0; auto].
apply derives_trans with(|> (local (tc_environ Delta) &&
  (local (tc_lvalue Delta e1) &&
   local (tc_expr Delta (Ecast e2 t2)) &&
   (lift2 (field_mapsto sh (typeof e1) fld) (eval_lvalue e1) v0 * P)))).
rewrite (later_andp (local (tc_environ Delta))). apply andp_derives; auto.
apply now_later.
apply later_derives.
intro rho; unfold local,lift0,lift1,lift2. simpl.
normalize.
unfold field_mapsto, mapsto.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite TE1.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- H1. destruct (access_mode t2); normalize.
apply derives_trans with ((!!tc_lvalue Delta (Efield e1 fld t2) rho &&
    !!tc_expr Delta (Ecast e2 t2) rho &&
     (!!tc_val t2 (eval_cast (typeof e2) t2 (eval_expr e2 rho)) &&
      !!(type_is_volatile t2 = false)) &&
     address_mapsto m (v0 rho) (Share.unrel Share.Lsh sh)
       (Share.unrel Share.Rsh sh)
       (b, Int.unsigned (Int.add i (Int.repr z)))) * P rho).
apply sepcon_derives; auto. 
apply andp_right; normalize.
unfold tc_lvalue, tc_expr, tc_andp in *; simpl typecheck_lvalue in *.
rewrite TE1.
rewrite H6; auto.
rewrite H8.
simpl tc_bool.
normalize.
apply andp_right; apply prop_right; auto.
eapply expr_lemmas.typecheck_val_eval_cast; eauto.
simpl in H4.
clear - H4.

rewrite denote_tc_assert_andp in H4.
destruct H4; auto.
simpl in H4.
rewrite denote_tc_assert_andp in H4.
destruct H4; auto.
normalize. 
unfold eval_field.
rewrite H6; normalize.

intros ek vl rho; unfold local, lift1, normal_ret_assert, lift2; simpl.
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
rewrite <- H1. rewrite H5.
normalize.
Opaque field_mapsto.
Qed.

Lemma semax_load_field':
forall (Delta: tycontext) sh id t1 fld P Q R e1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
        (temp_types Delta) ! id = Some (t2,i2) ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
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
normalize.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
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

Lemma semax_store_field':
forall (Delta: tycontext) sh t1 fld P Q R e1 e2 v0 t2 sid fields
    (WS: writable_share sh) ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield (Ederef e1 t1) fld t2) ->
    semax Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t2)::Q)
                             (SEPx (lift2 (field_mapsto sh t1 fld) (eval_expr e1) v0::R))))
       (Sassign (Efield (Ederef e1 t1) fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (lift2 (field_mapsto sh t1 fld) (eval_expr e1) 
                  (lift1 (eval_cast (typeof e2) t2) (eval_expr e2)) :: R))))).
Proof.
intros.
eapply semax_pre_post; [ | | eapply (semax_store_field)]; try eassumption.
instantiate (2:=v0).
instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
apply andp_left2. apply later_derives.
intro rho; normalize. 
subst t1.
unfold tc_lvalue. simpl typecheck_lvalue.
repeat rewrite denote_tc_assert_andp.
rewrite H0. simpl is_pointer_type. simpl tc_bool.
rewrite field_mapsto_nonnull.
repeat apply andp_right.
normalize.
unfold Cop.bool_val in H.
simpl in H.
revert H; case_eq (eval_expr e1 rho); intros; try discriminate; normalize.
apply prop_right; hnf. rewrite H; auto.
apply prop_right; auto.
apply prop_right; auto.
apply prop_right; auto.
normalize.

intros ek vl rho; unfold normal_ret_assert, local, lift1, lift2; simpl.
normalize.
Qed.

Lemma forward_setx':
  forall Delta P id e,
  (P |-- local (tc_expr Delta e) && local (tc_temp_id id (typeof e) Delta e) ) ->
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
                     (LOCALx (lift2 eq (eval_id id) (subst id (lift0 old) (eval_expr e)) ::
                                     map (subst id (lift0 old)) Q)
                      (SEPx (map (subst id (lift0 old)) R))))).
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
 unfold local,lift2,lift1,lift0.
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
  unfold local,lift2,lift1,lift0; simpl.
 apply prop_derives; intros [? ?]; auto.
Qed.

Ltac forward_setx_aux1 :=
      apply forward_setx; 
      try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ].

Lemma semax_post_flipped:
  forall (R' : ret_assert) (Delta : tycontext) (R : ret_assert)
         (P : assert) (c : statement),
        semax Delta P c R' -> 
       (forall (ek : exitkind) (vl : option val),
        local (tc_environ (exit_tycon c Delta ek)) && R' ek vl |-- R ek vl) ->
       semax Delta P c R.
Proof. intros; eapply semax_post; eassumption. Qed.

Ltac forward_setx_aux2 id :=
           match goal with 
           | Name: name id |- _ => 
                let x:= fresh Name in intro x; simpl eval_expr; autorewrite with subst; try clear x
           | |- _ => let x:= fresh in intro x; simpl eval_expr; autorewrite with subst; try clear x
           end.

Ltac forward_setx :=
first [apply forward_setx_closed_now;
            [solve [auto 50 with closed] | solve [auto 50 with closed] | solve [auto 50 with closed]
            | try solve [intro rho; apply prop_right; repeat split]
            | try solve [intro rho; apply prop_right; repeat split]
            |  ]
        | make_sequential;
          eapply semax_post_flipped;
          [ apply forward_setx; 
            try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ]
           | intros ?ek ?vl; apply after_set_special1 ]
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


Lemma semax_load_assist1:
  forall B P Q1 Q R,
  (forall rho, Q1 rho = True) ->
  B && PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (Q1::Q) (SEPx R)).
Proof. intros; intro rho;  normalize.
 apply andp_left2.
  apply andp_right; auto. apply andp_right; apply prop_right; auto.
 rewrite H; auto.
Qed.

Ltac semax_field_tac :=
match goal with |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset ?id (Efield (Ederef ?e _) ?fld _)) _ =>
     apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
     [ apply semax_load_assist1; [reflexivity]
     | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post'; [ | semax_field_tac1 ]
     ]
end.

Ltac store_field_tac1 := 
  eapply semax_store_field'; [ auto | reflexivity | reflexivity | type_of_field_tac |
               try solve [hnf; intuition] ].

Ltac store_field_tac :=
  match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Ssequence (Sassign (Efield (Ederef ?e _) ?fld ?t2) ?e2) _) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ normalize; go_lower; normalize
   | isolate_field_tac e fld R; hoist_later_in_pre;
      eapply semax_seq; [ apply sequential'; store_field_tac1   |  ]
   ]
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Efield (Ederef ?e _) ?fld ?t2) ?e2) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ normalize; go_lower; normalize
   | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post'; [ | store_field_tac1]
   ]
  end.

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
            (SEPx (lift1 (Pre x) ( (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl))) ::
                      lift1 (fun_assert_emp fsig A Pre Post) (eval_expr a) :: R))))
          (Scall ret a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (substopt ret (lift0 old)) Q) 
                (SEPx (lift1 (Post x) (get_result ret) :: map (substopt ret (lift0 old)) R))))).
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
apply exp_right with old; normalizex.
destruct ret; normalizex.
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
            (SEPx (lift1 (Pre x) ( (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl))) ::
                      lift1 (fun_assert_emp fsig A Pre Post) (eval_expr a) :: R))))
          (Scall (Some id) a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (subst id (lift0 old)) Q) 
                (SEPx (lift1 (Post x) (get_result1 id) :: map (subst id (lift0 old)) R))))).
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
        (PROPx P (LOCALx Q (SEPx (lift1 (fun_assert_emp fsig A Pre Post)
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
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (lift1 (Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction argtys retty))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (lift0 old)) Q) 
             (SEPx (lift1 (Post x) (get_result1 ret) :: map (subst ret (lift0 old)) R))))).
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
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (lift1 (Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction argtys retty))
             bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q   (SEPx (lift1 (Post x) (get_result1 ret) ::  R))))).
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
unfold SEPx. intro rho.
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
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (lift1 (Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Scall (Some ret)
             (Eaddrof (Evar id (Tfunction argtys retty)) (Tpointer (Tfunction argtys retty) noattr))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (lift0 old)) Q) 
             (SEPx (lift1 (Post x) (get_result1 ret) :: map (subst ret (lift0 old)) R))))).
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


Ltac intro_old_var' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x; simpl eval_expr; autorewrite with subst; try clear x
  | |- _ => let x := fresh "x" in 
        intro x; simpl eval_expr; autorewrite with subst; try clear x  
  end.

Ltac intro_old_var c :=
  match c with 
  | Sset ?id _ => intro_old_var' id
  | Scall (Some ?id) _ _ => intro_old_var' id
  | _ => intro x; simpl eval_expr; autorewrite with subst; try clear x
  end.


Ltac intro_old_var'' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x
  | |- _ => let x := fresh "x" in 
        intro x
  end.

Ltac semax_call_id_tac_aux Delta P Q R id f bl :=
   let VT := fresh "VT" in let GT := fresh "GT" in 
         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> assert); evar (Post: A -> assert);
      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);
 let SCI := fresh "SCI" in
    let H := fresh in let x := fresh "x" in let F := fresh "F" in
      evar (x:A); evar (F: list assert); 
      assert (SCI := semax_call_id1 Delta P Q F id f 
                (type_of_params (fst fsig)) (snd fsig) bl fsig A x Pre Post 
                      (eq_refl _) (eq_refl _) I (eq_refl _) (eq_refl _));
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (lift1 (Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre with (PROPx P
                (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
                 (SEPx (lift1 (Pre x)  (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) ::
                            F))));
       [apply (semax_call_id_aux1 _ _ _ _ _ H)
       | eapply semax_post'; [ unfold  x,F | unfold F in *; apply SCI] 
               ]];
  clear SCI VT GT; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.

(* BEGIN HORRIBLE.
  The following lemma and tactic are needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
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
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q) (SEPx (lift1 (Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: R))))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction argtys retty))
             bl)
      (Sset ret (Etempvar ret' retty)))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (lift0 old)) Q) 
             (SEPx (lift1 (Post x) (get_result1 ret) :: map (subst ret (lift0 old)) R))))).
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
    :: lift2 eq (eval_id ret)
         (subst ret (lift0 x0) (eval_expr (Etempvar ret' retty)))
       :: map (subst ret (lift0 x0)) Q)
   (SEPx
      (map (subst ret (lift0 x0)) (lift1 (Post x) (get_result1 ret') :: R)))))).
forward_setx.
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
 simpl. 
  normalize.
 apply sepcon_derives; auto.
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
 unfold lift0 in *. subst.
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

Ltac semax_call_id_tac_aux_x Delta P Q R id id' f bl :=
   let VT := fresh "VT" in let GT := fresh "GT" in 
         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> assert); evar (Post: A -> assert);

      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);

 let SCI := fresh "SCI" in
    let H := fresh in let x := fresh "x" in let F := fresh "F" in
      evar (x:A); evar (F: list assert); 

      assert (SCI := semax_call_id1_x Delta P Q F id id' f 
                (type_of_params (fst fsig)) (snd fsig) bl fsig A x Pre Post 
                      (eq_refl _) (eq_refl _) I (eq_refl _) (eq_refl _));
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (lift1 (Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre with (PROPx P
                (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
                 (SEPx (lift1 (Pre x)  (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) ::
                            F))));
       [apply (semax_call_id_aux1 _ _ _ _ _ H)
       | eapply semax_post'; [ unfold  x,F | unfold F in *; 
              ( apply SCI ; [ solve[simpl; auto with closed] |solve[simpl; auto with closed] 
                                 | reflexivity | reflexivity | reflexivity | reflexivity ] ) ]
               ]];
  clear SCI VT GT; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.

(* END HORRIBLE.  *)


Ltac semax_call_id_tac :=
match goal with 
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx 
          (?R))))
         (Ssequence (Scall (Some ?id) (Evar ?f _) ?bl) _)
        _ =>
      semax_call_id_tac_aux Delta P Q R id f bl
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx 
          (?R))))
         (Scall (Some ?id) (Evar ?f _) ?bl)
        _ =>
      semax_call_id_tac_aux Delta P Q R id f bl
end.

Ltac semax_call_tac1 :=
match goal with 
 |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx 
          (lift1 (fun_assert_emp ?fs ?A ?Pre ?Post) ?f :: ?R))))
        (Ssequence (Scall (Some ?id) ?a ?bl) _)
        _ =>
 let H := fresh in let x := fresh "x" in let F := fresh "F" in
      evar (x:A); evar (F: list assert); 
       let PR := fresh "Pre" in pose (PR := Pre);
     assert (H: lift1 (PR x)  (make_args' fs (eval_exprlist (snd (split (fst fs))) bl)) * SEPx F |-- SEPx R);
     [ | 
            apply semax_pre with (PROPx P
                (LOCALx (tc_expr Delta a :: tc_exprlist Delta (snd (split (fst fs))) bl :: Q)
                 (SEPx (lift1 (PR x)  (make_args' fs (eval_exprlist (snd (split (fst fs))) bl)) ::
                           lift1 (fun_assert_emp fs A Pre Post) f  :: F))));
              unfold F in *; clear F H
      ];
 idtac
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

Ltac forward1 :=   
   match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx _))) _ _ => idtac 
       | |- _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
  end;
  match goal with 
  | |- semax _ _ (Sassign (Efield _ _ _) _) _ =>      store_field_tac
  | |- semax _ _ (Sset _ (Efield _ _ _)) _ => semax_field_tac || fail 2
  | |- semax _ _ (Sset ?id ?e) _ => forward_setx
  | |- semax _ _ (Sreturn _) _ => 
                    eapply semax_pre; [ go_lower1 | apply semax_return ]
(* see comment HACK below, in forward tactic...
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl)  _ =>
                   semax_call_id_tac_aux Delta P Q R id f bl
*)
  end.

(*
Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with 
  | |- semax _ ?PQR (Ssequence ?c1 ?c2) ?PQR' => 
           let Post := fresh "Post" in
              evar (Post : assert);
              apply semax_seq' with Post;
               [ 
               | unfold exit_tycon, update_tycon, Post; clear Post ]
  end.
*)

Ltac forward :=
match goal with
 (* BEGIN HORRIBLE2.  (see BEGIN HORRIBLE, above)  *)
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
               (Ssequence (Ssequence (Scall (Some ?id') (Evar ?f _) ?bl)
                       (Sset ?id (Etempvar ?id' _))) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [  semax_call_id_tac_aux_x Delta P Q R id id' f bl;
        [ | apply derives_refl  ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon;
            try (apply extract_exists_pre; intro_old_var'' id)
           ]
 (* END HORRIBLE2 *)
  | |- semax _ _ (Ssequence (Ssequence _ _) _) _ =>
          apply seq_assoc; forward
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Scall (Some ?id) (Evar ?f _) ?bl) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [ semax_call_id_tac_aux Delta P Q R id f bl  ; [ | apply derives_refl  ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon;
            try (apply extract_exists_pre; intro_old_var'' id)
            ]
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
               eapply semax_post_flipped';
               [ semax_call_id_tac_aux Delta P Q R id f bl  ; [ | apply derives_refl ] 
               | try (apply exp_left; intro_old_var'' id)
               ]
  | |- semax _ _ (Ssequence ?c1 ?c2) _ => 
           let Post := fresh "Post" in
              evar (Post : assert);
              apply semax_seq' with Post;
               [ forward1; unfold Post; 
                 try apply normal_ret_assert_derives';
                 apply derives_refl
               | try unfold exit_tycon; 
                   simpl update_tycon;
                   try (unfold Post; clear Post);
                    try (apply extract_exists_pre; intro_old_var c1);
                    try apply elim_redundant_Delta                
               ]
  | |- semax _ _ ?c1 _ => forward1;
                  try unfold exit_tycon; 
                  simpl update_tycon;
                  try (apply exp_left; intro_old_var c1)
  end.

Ltac start_function :=
match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
  match Pre with fun i => _ => intro i end;
  simpl fn_body; simpl fn_params; simpl fn_return;
  canonicalize_pre
 end;
 match goal with |- semax (func_tycontext ?F ?V ?G) _ _ _ => 
   set (Delta := func_tycontext F V G)
 end;
  try match goal with |- context [stackframe_of ?F] =>
            change (stackframe_of F) with emp;
            rewrite frame_ret_assert_emp
         end;
  repeat (apply semax_extract_PROP; intro).

Opaque sepcon.
Opaque emp.
Opaque andp.