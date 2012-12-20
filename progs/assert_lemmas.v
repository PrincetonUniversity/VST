Load loadpath.
Require Import veric.SeparationLogic.
Require veric.SequentialClight.

(* no "semax" in this file, just assertions.
 Thus, no need to import SequentialClight.SeqC.CSL.
*)

Local Open Scope logic.

Hint Rewrite eval_id_other using solve [auto; clear; intro Hx; inversion Hx] : normalize.

Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.

Lemma type_eq_refl:
 forall t, proj_sumbool (type_eq t t) = true.
Proof.
intros.
apply proj_sumbool_is_true.
auto.
Qed.

Lemma overridePost_normal:
  forall P R, overridePost P R EK_normal None = P.
Proof.
 intros. unfold overridePost. rewrite if_true by auto.
 apply prop_true_andp. auto.
Qed.
Hint Rewrite overridePost_normal : normalize.

Lemma eval_expr_Etempvar: 
  forall i t, eval_expr (Etempvar i t) = eval_id i.
Proof. reflexivity.
Qed.
Hint Rewrite eval_expr_Etempvar : normalize.

Lemma eval_expr_binop: forall op a1 a2 t, eval_expr (Ebinop op a1 a2 t) = 
          lift2 (eval_binop op (typeof a1) (typeof a2)) (eval_expr a1)  (eval_expr a2).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_binop : normalize.

Lemma eval_expr_unop: forall op a1 t, eval_expr (Eunop op a1 t) = 
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_unop : normalize.

Definition tc_val (t: type) (v: val) : Prop := typecheck_val v t = true.
Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B) 
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3):  environ -> B := 
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Lemma bool_val_int_eq_e: 
  forall i j, Cop.bool_val (Val.of_bool (Int.eq i j)) type_bool = Some true -> i=j.
Proof.
 intros.
 revert H; case_eq (Val.of_bool (Int.eq i j)); simpl; intros; inv H0.
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. rewrite Int.eq_true in H2. inv H2.
Qed.

Lemma closed_wrt_local: forall S P, closed_wrt_vars S P -> closed_wrt_vars S (local P).
Proof.
intros.
hnf in H|-*; intros.
specialize (H _ _ H0).
unfold local,lift1.
f_equal; auto.
Qed.
Hint Resolve closed_wrt_local : closed.

Lemma closed_wrt_lift1: forall {A}{B} S (f: A -> B) P, 
        closed_wrt_vars S P -> 
        closed_wrt_vars S (lift1 f P).
Proof.
intros.
intros ? ? ?. specialize (H _ _ H0).
unfold lift1; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift1 : closed.

Lemma closed_wrt_lift2: forall {A1 A2}{B} S (f: A1 -> A2 -> B) P1 P2, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S (lift2 f P1 P2).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H1).
specialize (H0 _ _ H1).
unfold lift2; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift2 : closed.

Lemma closed_wrt_eval_expr: forall S e,
  expr_closed_wrt_vars S e -> 
  closed_wrt_vars S (eval_expr e).
Proof.
intros. apply H.
Qed.
Hint Resolve closed_wrt_eval_expr : closed.

Lemma closed_wrt_eval_id: forall S i,
    ~ S i -> closed_wrt_vars S (eval_id i).
Proof.
intros.
intros ? ? ?.
unfold eval_id, force_val.
simpl.
destruct (H0 i).
contradiction.
rewrite H1; auto.
Qed.
Hint Resolve closed_wrt_eval_id : closed.

Lemma closed_wrt_andp: forall S (P Q: assert),
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P && Q).
Admitted.

Lemma closed_wrt_sepcon: forall S P Q,
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P * Q).
Admitted.

Fixpoint temp_free_in (id: ident) (e: expr) := 
 match e with
 | Econst_int _ _ => false
 | Econst_float _ _ => false
 | Evar _ _ => false
 | Etempvar i _ => eqb_ident id i
 | Ederef e1 _ => temp_free_in id e1
 | Eaddrof e1 _ => temp_free_in id e1
 | Eunop _ e1 _ => temp_free_in id e1
 | Ebinop _ e1 e2 _ => orb (temp_free_in id e1) (temp_free_in id e2) 
 | Ecast e1 _ => temp_free_in id e1
 | Efield e1 _ _ => temp_free_in id e1
end.

Lemma closed_wrt_ideq: forall a b e,
  a <> b ->
  temp_free_in a e = false ->
  closed_wrt_vars (modified1 a) (fun rho => !! (eval_id b rho = eval_expr e rho)).
Proof.
Admitted.

Hint Resolve closed_wrt_andp closed_wrt_sepcon : closed.

Hint Extern 2 (closed_wrt_vars (modified1 _) _) => 
      (apply closed_wrt_ideq; [solve [let Hx := fresh in (intro Hx; inv Hx)] | reflexivity]) : closed.

Hint Resolve @Forall_cons @Forall_nil : closed.

Lemma closed_wrt_lift0: forall {A} S (Q: A), closed_wrt_vars S (lift0 Q).
Proof.
intros.
intros ? ? ?.
unfold lift0; auto.
Qed.
Hint Resolve @closed_wrt_lift0: closed.

Lemma closed_wrt_tc_formals:
  forall (S: ident -> Prop) (L: list (ident*type)), 
    Forall (fun q => not (S q)) (map (@fst _ _) L) ->
    closed_wrt_vars S (tc_formals L).
Admitted.
Hint Resolve closed_wrt_tc_formals.

Lemma closed_wrt_not1:
  forall (i j: ident), 
   i<>j ->
   not (modified1 i j).
Proof.
intros.
hnf. unfold modified1.
intros; subst; congruence.
Qed.
Hint Resolve closed_wrt_not1 : closed.


Lemma closed_wrt_tc_expr:
  forall Delta S e, expr_closed_wrt_vars S e ->
             closed_wrt_vars S (tc_expr Delta e).
Proof.
intros.
Admitted.
Hint Resolve closed_wrt_tc_expr : closed.

Lemma expr_closed_tempvar:
 forall S i t, ~ S i -> expr_closed_wrt_vars S (Etempvar i t).
Admitted.
Hint Resolve expr_closed_tempvar : closed.

Hint Extern 1 (not (@eq ident _ _)) => (let Hx := fresh in intro Hx; inversion Hx) : closed.

Definition nullval : val := Vint Int.zero.

Lemma bool_val_notbool_ptr:
    forall v t,
   match t with Tpointer _ _ => True | _ => False end ->
   (Cop.bool_val (force_val (Cop.sem_notbool v t)) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.

Hint Rewrite bool_val_notbool_ptr using (solve [simpl; auto]) : normalize.
Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : normalize.


Lemma closed_wrt_subst:
  forall {A} id e (P: environ -> A), closed_wrt_vars (eq id) P -> subst id e P = P.
Proof.
intros.
unfold subst, closed_wrt_vars in *.
extensionality rho.
symmetry.
apply H.
intros.
destruct (eq_dec id i); auto.
right.
rewrite Map.gso; auto.
Qed.


Lemma lvalue_closed_tempvar:
 forall S i t, ~ S i -> lvalue_closed_wrt_vars S (Etempvar i t).
Admitted.
Hint Resolve lvalue_closed_tempvar : closed.


Hint Resolve  eval_expr_Etempvar.

Lemma eval_expr_Etempvar' : forall i t, eval_id i = eval_expr (Etempvar i t).
Proof. intros. symmetry; auto.
Qed.
Hint Resolve  eval_expr_Etempvar'.


Lemma subst_eval_id_eq:
 forall id v, subst id v (eval_id id) = v.
Proof. unfold subst, eval_id; intros. extensionality rho.
    unfold force_val, env_set; simpl. rewrite Map.gss; auto.
Qed.

Lemma subst_eval_id_neq:
  forall id v j, id<>j -> subst id v (eval_id j) = eval_id j.
Proof.
    unfold subst, eval_id; intros. extensionality rho.
    unfold force_val, env_set; simpl. rewrite Map.gso; auto.
Qed.

Hint Rewrite subst_eval_id_eq : normalize.
Hint Rewrite subst_eval_id_neq using (solve [auto with closed]) : normalize.


Lemma typed_false_ptr: 
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct v; try discriminate.
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H.
Qed.

Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @lift1_lift0 : normalize.
(*
Lemma subst_eval_expr_const:
  forall i v n t, subst i v (eval_expr (Econst_int n t)) = eval_expr (Econst_int n t).
Proof.
intros. reflexivity.
Qed.
Hint Rewrite subst_eval_expr_const : normalize.
*)
Lemma tc_formals_cons:
  forall i t rest, tc_formals ((i,t) :: rest) =
         lift2 and (lift1 (tc_val t) (eval_id i)) (tc_formals rest).
Proof.
intros.
extensionality rho; simpl.
unfold tc_formals; fold tc_formals.
unfold lift2. simpl.
apply prop_ext.
rewrite andb_true_iff.
intuition.
Qed.

Lemma tc_formals_nil : tc_formals nil = lift0 True.
Proof. intros; extensionality rho.  unfold tc_formals.  simpl. 
apply prop_ext; intuition.  hnf; auto. 
Qed.

Hint Rewrite tc_formals_cons tc_formals_nil: normalize.


Lemma tc_eval_gvar_i:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some (Global_var t) ->
             tc_val (Tpointer t noattr) (eval_var i t rho).
Proof.
 intros. unfold tc_val, eval_var; simpl.
 hnf in H. unfold typecheck_environ in H.
 repeat rewrite andb_true_iff in H.
  destruct H as [[[_ ?] ?] ?].
  apply environ_lemmas.typecheck_mode_eqv in H3.
  apply environ_lemmas.typecheck_ge_eqv in H2.
  apply environ_lemmas.typecheck_ve_eqv in H.
  destruct (H3 _ _ H1).
  unfold Map.get; rewrite H4.
  destruct (H2 _ _ H1) as [b [i' [? ?]]].
   rewrite H5. simpl. rewrite eqb_type_refl.
   simpl globtype in H6.
   auto. 
  destruct H4; congruence.
Qed.

Lemma local_lift2_and: forall P Q, local (lift2 and P Q) = 
        local P && local Q.
Proof. intros; extensionality rho. unfold local, lift1,lift2.   
simpl.
 apply pred_ext; normalize. destruct H; normalize.
Qed.
Hint Rewrite local_lift2_and : normalize.

Lemma subst_TT {A}{NA: NatDed A}: forall i v, subst i v TT = TT.
Admitted.
Lemma subst_FF {A}{NA: NatDed A}: forall i v, subst i v FF = FF.
Admitted.
Hint Rewrite @subst_TT @subst_FF: normalize.
Hint Rewrite (@subst_TT mpred Nveric) (@subst_FF mpred Nveric): normalize.


Lemma eval_expr_Econst_int: forall i t, eval_expr (Econst_int i t) = lift0 (Vint i).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_Econst_int : normalize.

Lemma eval_expr_Ecast: 
  forall e t, eval_expr (Ecast e t) = lift1 (eval_cast (typeof e) t) (eval_expr e).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_Ecast : normalize.


Lemma subst_local: forall id v P,
  subst id v (local P) = local (subst id v P).
Proof. reflexivity. Qed.
Hint Rewrite subst_local : normalize.
Lemma eval_lvalue_Ederef:
  forall e t, eval_lvalue (Ederef e t) = lift1 force_ptr (eval_expr e).
Proof. reflexivity. Qed.
Hint Rewrite eval_lvalue_Ederef : normalize.


Lemma tc_eval_id_i:
  forall Delta t i rho, 
               tc_environ Delta rho -> 
              (temp_types Delta)!i = Some (t,true) ->
              tc_val t (eval_id i rho).
Proof.
intros.
unfold tc_environ in H.
destruct rho; apply environ_lemmas.typecheck_environ_sound in H.
destruct H as [? _].
destruct (H i true t H0) as [v [? ?]].
unfold eval_id. simpl. rewrite H1. simpl; auto.
destruct H2. inv H2. auto.
Qed.

Lemma local_lift0_True:     local (lift0 True) = TT.
Proof. reflexivity. Qed.
Hint Rewrite local_lift0_True : normalize.

Lemma overridePost_EK_return: 
  forall Q P, overridePost Q P EK_return = P EK_return.
Proof. unfold overridePost; intros. 
  extensionality vl rho; rewrite if_false by congruence. auto.
Qed.
Hint Rewrite overridePost_EK_return : normalize.

Lemma frame_ret_assert_EK_return:
 forall P Q vl, frame_ret_assert P Q EK_return vl =  P EK_return vl * Q.
Proof. reflexivity. Qed.
Hint Rewrite frame_ret_assert_EK_return : normalize.

Lemma function_body_ret_assert_EK_return:
  forall t P vl, function_body_ret_assert t P EK_return vl = bind_ret vl t P.
Proof. reflexivity. Qed.
Hint Rewrite function_body_ret_assert_EK_return : normalize.

Lemma bind_ret1_unfold:
  forall v t Q, bind_ret (Some v) t Q = !!tc_val t v && lift1 Q (make_args (ret_temp :: nil)(v::nil)).
Proof. reflexivity. Qed.
Hint Rewrite bind_ret1_unfold : normalize.

Lemma tc_val_extract_int:
 forall v sign ch attr, tc_val (Tint ch sign attr) v -> exists n, v = Vint n.
Proof.
intros. destruct v; inv H; eauto.
Qed.


Lemma normal_ret_assert_eq:
  forall P ek vl, normal_ret_assert P ek vl =
             (!! (ek=EK_normal) && (!! (vl=None) && P)).
Proof. reflexivity. Qed.
Hint Rewrite normal_ret_assert_eq: normalize. 

Lemma for1_ret_assert_normal:
  forall P Q, for1_ret_assert P Q EK_normal None = P.
Proof. reflexivity. Qed.
Hint Rewrite for1_ret_assert_normal: normalize.

Definition retval : environ -> val := eval_id ret_temp.

Lemma retval_get_result1: 
   forall i rho, retval (get_result1 i rho) = (eval_id i rho).
Proof. intros. unfold retval, get_result1. simpl. normalize. Qed.
Hint Rewrite retval_get_result1 : normalize.


Lemma unfold_make_args': forall fsig args rho,
    make_args' fsig args rho = make_args (map (@fst _ _) (fst fsig)) (args rho) rho.
Proof. reflexivity. Qed.
Hint Rewrite unfold_make_args' : normalize.
Lemma unfold_make_args_cons: forall i il v vl rho,
   make_args (i::il) (v::vl) rho = env_set (make_args il vl rho) i v.
Proof. reflexivity. Qed.
Lemma unfold_make_args_nil: make_args nil nil = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite unfold_make_args_cons unfold_make_args_nil : normalize.


Definition fun_assert_emp fsig A P Q v := emp && fun_assert fsig A P Q v.

Lemma substopt_unfold {A}: forall id v, @substopt A (Some id) v = @subst A id v.
Proof. reflexivity. Qed.
Lemma substopt_unfold_nil {A}: forall v (P:  environ -> A), substopt None v P = P.
Proof. reflexivity. Qed.
Hint Rewrite @substopt_unfold @substopt_unfold_nil : normalize.


Lemma get_result_unfold: forall id, get_result (Some id) = get_result1 id.
Proof. reflexivity. Qed.
Lemma get_result_None: get_result None = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite get_result_unfold get_result_None : normalize.

Lemma eval_expropt_Some: forall e, eval_expropt (Some e) = lift1 Some (eval_expr e).
Proof. reflexivity. Qed.
Lemma eval_expropt_None: eval_expropt None = lift0 None.
Proof. reflexivity. Qed.
Hint Rewrite eval_expropt_Some eval_expropt_None : normalize.


Definition Ews (* extern_write_share *) := Share.splice extern_retainer Share.top.

Lemma globvar_eval_var:
  forall (ge: Genv.t fundef type) Delta rho id t,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  (Global_var t) ->
     exists b, exists z,  eval_var id t rho = Vptr b z /\ ge_of rho id = Some (Vptr b z, t).
Proof.
intros.
unfold tc_environ, typecheck_environ in H.
repeat rewrite andb_true_iff in H. destruct H as [[[Ha Hb] Hc] Hd].
apply environ_lemmas.typecheck_ge_eqv in Hc. 
hnf in Hc.
specialize (Hc _ _ H1). destruct Hc as [b [i [Hc Hc']]].
exists b; exists i.
unfold eval_var; simpl.
apply environ_lemmas.typecheck_mode_eqv in Hd.
apply Hd in H1. 
destruct H1 as [? | [? ?]]; [ | congruence].
unfold Map.get; rewrite H. rewrite Hc.
rewrite eqb_type_refl; auto.
Qed.

Lemma globvars2pred_unfold: forall ge vl rho, 
    globvars2pred ge vl rho = 
    fold_right sepcon emp (map (fun idv => globvar2pred ge idv rho) vl).
Proof. intros. unfold globvars2pred.
   induction vl; simpl; auto. normalize; f_equal; auto.
Qed.
Hint Rewrite globvars2pred_unfold : normalize.

Lemma writable_Ews: writable_share Ews.
Admitted.
Hint Resolve writable_Ews.


 Lemma offset_offset_val:
  forall v i j, offset_val (offset_val v i) j = offset_val v (Int.add i j).
Proof. intros; unfold offset_val.
 destruct v; auto. rewrite Int.add_assoc; auto.
Qed.
Hint Rewrite offset_offset_val: normalize.

Lemma add_repr: forall i j, Int.add (Int.repr i) (Int.repr j) = Int.repr (i+j).
Proof. intros.
  rewrite Int.add_unsigned.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.
Hint Rewrite add_repr : normalize.

Lemma int_add_assoc1:
  forall z i j, Int.add (Int.add z (Int.repr i)) (Int.repr j) = Int.add z (Int.repr (i+j)).
Admitted.
Hint Rewrite int_add_assoc1 : normalize.

Lemma align_0: forall z, 
    z > 0 -> align 0 z = 0.
Proof. unfold align; intros. rewrite Zdiv_small; omega.
Qed.
Hint Rewrite align_0 using omega : normalize.

Lemma eval_cast_pointer2: 
  forall v t1 t2 t3 t1' t2',
   t1' = Tpointer t1 noattr ->
   t2' = Tpointer t2 noattr ->
   tc_val (Tpointer t3 noattr) v ->
   eval_cast t1' t2' v = v.
Proof.
intros.
subst.
hnf in H1. destruct v; inv H1; reflexivity.
Qed.

Lemma eval_cast_var:
  forall Delta rho,
      tc_environ Delta rho ->
  forall t1 t2 t3 id,
  Cop.classify_cast t1 t3 = Cop.cast_case_neutral ->
  tc_lvalue Delta (Evar id t2) rho ->
  eval_cast t1 t3 (eval_var id t2 rho) = eval_var id t2 rho.
Proof.
intros.
 pose proof (expr_lemmas.typecheck_lvalue_sound _ _ _ H H1 (Tpointer t2 noattr) (eq_refl _)).
 unfold typecheck_val in H2. simpl in H2.
 destruct (eval_var id t2 rho); inv H2.
 pose proof (Int.eq_spec i Int.zero). rewrite H4 in H2. subst. clear H4.
 destruct t1; destruct t3; inv H0; 
  try (destruct i; inv H3); try (destruct i0; inv H2); try reflexivity.
 destruct t1; destruct t3; inv H0; 
  try (destruct i0; inv H3); try (destruct i1; inv H2); try reflexivity.
Qed.

Lemma eval_cast_id:
  forall Delta rho,
      tc_environ Delta rho ->
  forall t1 t3 id,
  Cop.classify_cast t1 t3 = Cop.cast_case_neutral ->
  match (temp_types Delta)!id with Some (Tpointer _ _, true) => true | _ => false end = true ->
  eval_cast t1 t3 (eval_id id rho) = eval_id id rho.
Proof.
intros.
 revert H1; case_eq ((temp_types Delta) ! id); intros; try discriminate.
 destruct p as [t2 ?].
 destruct t2; inv H2.
 destruct b; inv H4.
 pose proof (tc_eval_id_i _ _ _ _ H H1).
 hnf in H2.
 unfold typecheck_val in H2.
 destruct (eval_id id  rho); inv H2.
 pose proof (Int.eq_spec i Int.zero). rewrite H4 in H2. subst. clear H4.
 destruct t1; destruct t3; inv H0; 
  try (destruct i; inv H3); try (destruct i0; inv H2); try reflexivity.
 destruct t1; destruct t3; inv H0; 
  try (destruct i0; inv H3); try (destruct i1; inv H2); try reflexivity.
Qed.

Ltac eval_cast_simpl :=
     match goal with H: tc_environ ?Delta ?rho |- _ =>
       first [rewrite (eval_cast_var Delta rho H); [ | reflexivity | hnf; simpl; normalize ]
               | rewrite (eval_cast_id Delta rho H); [ | reflexivity | reflexivity ]
               ]
     end.
