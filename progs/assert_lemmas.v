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
  forall P R, overridePost P R EK_normal nil = P.
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

Definition tc_val (t: type) (v: val) : Prop := typecheck_val v t = true.
Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B) 
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3):  environ -> B := 
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Lemma bool_val_int_eq_e: 
  forall i j, bool_val (Val.of_bool (Int.eq i j)) type_bool = Some true -> i=j.
Proof.
 intros.
 apply Clight_lemmas.of_bool_Int_eq_e'.
 forget (Val.of_bool (Int.eq i j)) as v.
 destruct v; simpl in *; try discriminate; auto.
 inv H. intro. subst. rewrite Int.eq_true in H1. inv H1.
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
 | Econdition e0 e1 e2 _ => orb (temp_free_in id e0) (orb (temp_free_in id e1) (temp_free_in id e2)) 
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
   (bool_val (force_val (sem_notbool v t)) type_bool = Some true) = (v = nullval).
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

Lemma local_lift2_and: forall P Q, local (lift2 and P Q) = 
        local P && local Q.
Proof. intros; extensionality rho. unfold local, lift1,lift2.   
simpl.
 apply pred_ext; normalize. destruct H; normalize.
Qed.
Hint Rewrite local_lift2_and : normalize.

Lemma subst_TT: forall i v, subst i v TT = TT.
Admitted.
Lemma subst_FF: forall i v, subst i v FF = FF.
Admitted.
Hint Rewrite subst_TT subst_FF: normalize.


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
apply expr_lemmas.typecheck_environ_sound in H.
destruct H as [? _].
destruct (H i t true H0) as [v [? ?]].
unfold eval_id. rewrite H1. simpl; auto.
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
  forall v t Q, bind_ret (v::nil) t Q = !!tc_val t v && lift1 Q (make_args (ret_temp :: nil)(v::nil)).
Proof. reflexivity. Qed.
Hint Rewrite bind_ret1_unfold : normalize.

Lemma tc_val_extract_int:
 forall v sign ch attr, tc_val (Tint ch sign attr) v -> exists n, v = Vint n.
Proof.
intros. destruct v; inv H; eauto.
Qed.


Lemma normal_ret_assert_eq:
  forall P ek vl, normal_ret_assert P ek vl =
             (!! (ek=EK_normal) && (!! (vl=nil) && P)).
Proof. reflexivity. Qed.
Hint Rewrite normal_ret_assert_eq: normalize. 

Lemma for1_ret_assert_normal:
  forall P Q, for1_ret_assert P Q EK_normal nil = P.
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

