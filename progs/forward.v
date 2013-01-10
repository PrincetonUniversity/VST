Load loadpath.
Require Import Coqlib veric.Coqlib2.
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
Proof with normalize.
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
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
simpl eval_field. rewrite H5. rewrite H4.
simpl eval_struct_field.
forget (Int.add i (Int.repr z)) as N.
 simpl. auto.
normalize.
apply andp_right.
apply andp_right; apply prop_right; auto.
exists t2; exists i2; split; auto.
admit.  (* consult with Joey *)
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
rewrite H5.  rewrite H4.
change ((Int.unsigned i + z mod Int.modulus) mod Int.modulus)
    with (Int.unsigned (Int.add i (Int.repr z))). rewrite H6. normalize.
Opaque field_mapsto.
Qed.

Lemma writable_share_top: writable_share Share.top.
Admitted.

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
     address_mapsto m (v0 rho) (Share.unrel Share.Lsh sh)
       (Share.unrel Share.Rsh sh)
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
go_lower.
rewrite field_mapsto_nonnull.
unfold tc_expr, tc_lvalue.
simpl typecheck_lvalue.
simpl denote_tc_assert.
rewrite H0. rewrite H.
simpl.
normalize.
destruct (eval_expr e1 rho); inv H7; normalize.

normalize.
intro x; apply exp_right with x.
go_lower.
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
go_lower. apply later_derives.
normalize.
subst t1.
unfold tc_lvalue.
rewrite field_mapsto_nonnull.
normalize.
unfold Cop.bool_val in H.
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
Qed.

Lemma forward_setx:
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
go_lower.
apply andp_right; auto.
eapply derives_trans; [apply H | ].
normalize.
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
  forall A P (Q: A -> assert) ek vl R,
  (ek = EK_normal -> vl=None -> forall x, P && Q x |-- R) ->
    P && normal_ret_assert (exp Q) ek vl |-- R.
Proof. intros. normalize.
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

Ltac forward_setx_aux2 :=
            let x:= fresh"x" in intro; autorewrite with normalize; (clear x || revert x).

Ltac forward_setx := 
  first [eapply semax_seq; 
             [apply sequential'; forward_setx_aux1 | apply extract_exists_pre; forward_setx_aux2]
         | eapply semax_post_flipped;  
             [forward_setx_aux1
             | intros ?ek ?vl; apply after_set_special1; intros ? ?; subst ek vl;
               forward_setx_aux2 ]].

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
Proof. intros; go_lower.
 apply andp_left2.
  apply andp_right; auto. apply andp_right; apply prop_right; auto.
 rewrite H; auto.
Qed.

Ltac semax_field_tac :=
match goal with
 | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                  (Ssequence (Sset _ (Efield (Ederef ?e _) ?fld _)) _) _ =>
  apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
   [ try (apply semax_load_assist1; [reflexivity])
   | isolate_field_tac e fld R; hoist_later_in_pre;
     eapply semax_seq; [ apply sequential'; semax_field_tac1
                                          | simpl update_tycon; apply extract_exists_pre
                                          ]
    ]
 | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset _ (Efield (Ederef ?e _) ?fld _)) _ =>
     apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
     [ try (apply semax_load_assist1; [reflexivity])
     | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post; [ | semax_field_tac1  ]
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
go_lower.
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
go_lower.
rewrite sepcon_comm; auto.
go_lower.
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
go_lower.
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
split; [ | apply I].
simpl typecheck_lvalue.
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


Lemma semax_call_id_aux1: forall P Q1 Q R S,
     PROPx P (LOCALx (Q1::Q) R) |-- S -> local Q1 && PROPx P (LOCALx Q R) |-- S.
Proof. intros. eapply derives_trans; try apply H. go_lower.
Qed.

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
       | ((eapply semax_seq; [apply sequential'; unfold F in *; apply SCI | ]) ||
            (eapply semax_post; [ | unfold F in *; apply SCI ])) ]];
  clear SCI VT GT; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.


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

Ltac forward := 
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx _))) _ _ => idtac 
                          | |- _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
  end;
  match goal with
  | |- semax _ _ (Ssequence (Sassign (Efield _ _ _) _) _) _ => store_field_tac
  | |- semax _ _ (Sassign (Efield _ _ _) _) _ =>      store_field_tac
  | |- semax _ _ (Ssequence (Sset _ (Efield _ _ _)) _) _ => semax_field_tac
  | |- semax _ _ (Sset _ (Efield _ _ _)) _ => semax_field_tac || fail 2
  | |- semax _ _ (Ssequence (Sset _ ?e) _) _ =>  forward_setx
  | |- semax _ _ (Sset _ ?e) _ => forward_setx
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
          apply semax_seq with FF; [eapply semax_pre; [ | apply semax_return ]
                                | apply semax_ff]
  | |- semax _ _ (Sreturn _) _ => eapply semax_pre; [ | apply semax_return ]
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
            (Ssequence (Scall (Some ?id) (Evar ?f _) ?bl) _) _ =>
                                          semax_call_id_tac_aux Delta P Q R id f bl
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                              (Scall (Some ?id) (Evar ?f _) ?bl)  _ =>
                                         semax_call_id_tac_aux Delta P Q R id f bl
  end.
