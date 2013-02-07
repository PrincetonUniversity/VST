Load loadpath.
Require Import veric.SeparationLogic.
Require Import Coqlib compositional_compcert.Coqlib2.
Require Import Clightdefs.
(* no "semax" in this file, just assertions.
 Thus, no need to import SequentialClight.SeqC.CSL.
*)

Local Open Scope logic.

Hint Resolve @TT_right.

Hint Rewrite Int.sub_idem Int.sub_zero_l  Int.add_neg_zero : normalize.
Hint Rewrite Int.add_zero_l Int.add_zero : normalize.
Hint Rewrite eval_id_other using solve [auto; clear; intro Hx; inversion Hx] : normalize.



Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.

Lemma force_Vint:  forall i, force_int (Vint i) = i.
Proof.  reflexivity. Qed.
Hint Rewrite force_Vint : normalize.

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
          `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1)  (eval_expr a2).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_binop : normalize.

Lemma eval_expr_unop: forall op a1 t, eval_expr (Eunop op a1 t) = 
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_unop : normalize.

Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B) 
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3):  environ -> B := 
     fun rho => P (f1 rho) (f2 rho) (f3 rho).


Lemma closed_wrt_local: forall S P, closed_wrt_vars S P -> closed_wrt_vars S (local P).
Proof.
intros.
hnf in H|-*; intros.
specialize (H _ _ H0).
unfold local, lift1.
f_equal; auto.
Qed.
Hint Resolve closed_wrt_local : closed.

Lemma closed_wrt_lift0: forall {A} S (Q: A), closed_wrt_vars S (lift0 Q).
Proof.
intros.
intros ? ? ?.
unfold lift0; auto.
Qed.
Hint Resolve @closed_wrt_lift0: closed.

Lemma closed_wrt_lift0C: forall {B} S (Q: B), 
   closed_wrt_vars S (@coerce B (environ -> B) (lift0_C B)  Q).
Proof.
intros.
intros ? ? ?.
unfold_coerce; auto.
Qed.
Hint Resolve @closed_wrt_lift0C: closed.

Lemma closed_wrt_lift0Cassert: forall  S (Q: mpred), 
   closed_wrt_vars S (@coerce mpred assert (lift0_C mpred)  Q).
Proof. apply closed_wrt_lift0C. Qed.
Hint Resolve @closed_wrt_lift0Cassert: closed.

Lemma closed_wrt_lift1: forall {A}{B} S (f: A -> B) P, 
        closed_wrt_vars S P -> 
        closed_wrt_vars S (lift1 f P).
Proof.
intros.
intros ? ? ?. specialize (H _ _ H0).
unfold lift1; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift1 : closed.

Lemma closed_wrt_lift1C: forall {A}{B} S (f: A -> B) P, 
        closed_wrt_vars S P -> 
        closed_wrt_vars S (@coerce (A -> B) ((environ -> A) -> environ -> B) (lift1_C A B) f P).
Proof.
intros.
intros ? ? ?. specialize (H _ _ H0).
unfold_coerce; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift1C : closed.

Lemma closed_wrt_lift1Cassert: forall {A} S (f: A -> mpred) P, 
        closed_wrt_vars S P -> 
        closed_wrt_vars S (@coerce (A -> mpred) ((environ -> A) -> assert) (lift1_C A mpred) f P).
Proof. intro; apply closed_wrt_lift1C. Qed.
Hint Resolve @closed_wrt_lift1Cassert : closed.

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

Lemma closed_wrt_lift2C: forall {A1 A2}{B} S (f: A1 -> A2 -> B) P1 P2, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S (@coerce (A1 -> A2 -> B) ((environ -> A1) -> (environ -> A2) -> environ -> B)
                  (lift2_C A1 A2 B) f P1 P2).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H1).
specialize (H0 _ _ H1).
unfold_coerce; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift2C : closed.


Lemma closed_wrt_lift2C_assert: forall {A1 A2} 
                  S (f: A1 -> A2 -> mpred) P1 P2, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S (@coerce (A1 -> A2 -> mpred) ((environ -> A1) -> (environ -> A2) -> assert)
                  (lift2_C A1 A2 mpred) f P1 P2).
Proof. intros ? ?; apply closed_wrt_lift2C. Qed.
Hint Resolve @closed_wrt_lift2C_assert : closed.


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

Lemma closed_wrt_get_result1 :
  forall (S: ident -> Prop) i , ~ S i -> closed_wrt_vars S (get_result1 i).
Proof.
intros. unfold get_result1. simpl.
 hnf; intros.
 simpl. f_equal.
apply (closed_wrt_eval_id _ _ H); auto.
Qed.
Hint Resolve closed_wrt_get_result1 : closed.


Lemma closed_wrt_andp: forall S (P Q: assert),
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P && Q).
Admitted.

Lemma closed_wrt_sepcon: forall S (P Q: assert),
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P * Q).
Admitted.

Lemma closed_wrt_emp {A} {ND: NatDed A} {SL: SepLog A}:
  forall S, closed_wrt_vars S emp.
Proof. repeat intro. reflexivity. Qed.
Hint Resolve (@closed_wrt_emp mpred Nveric Sveric) : closed.


Lemma closed_wrt_main_pre:
  forall prog u S, closed_wrt_vars S (main_pre prog u).
Admitted.
Lemma closed_wrt_globvars:
  forall S v, closed_wrt_vars S (globvars2pred v).
Admitted.
Hint Resolve closed_wrt_main_pre closed_wrt_globvars: closed.


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

Lemma expr_closed_const_int:
  forall S i t, expr_closed_wrt_vars S (Econst_int i t).
Proof.
intros. unfold expr_closed_wrt_vars. simpl; intros.
unfold_coerce. auto.
Qed.
Hint Resolve expr_closed_const_int : closed.

Lemma expr_closed_cast: forall S e t, 
     expr_closed_wrt_vars S e -> 
     expr_closed_wrt_vars S (Ecast e t).
Proof.
 unfold expr_closed_wrt_vars; intros.
 simpl.
 unfold_coerce.
 destruct (H rho te' H0); auto.
Qed.
Hint Resolve expr_closed_cast : closed.


Lemma expr_closed_binop: forall S op e1 e2 t, 
     expr_closed_wrt_vars S e1 -> 
     expr_closed_wrt_vars S e2 -> 
     expr_closed_wrt_vars S (Ebinop op e1 e2 t).
Proof.
 unfold expr_closed_wrt_vars; intros.
 simpl.
 unfold_coerce. f_equal; auto.
Qed.
Hint Resolve expr_closed_binop : closed.


Lemma expr_closed_unop: forall S op e t, 
     expr_closed_wrt_vars S e -> 
     expr_closed_wrt_vars S (Eunop op e t).
Proof.
 unfold expr_closed_wrt_vars; intros.
 simpl.
 unfold_coerce. f_equal; auto.
Qed.
Hint Resolve expr_closed_unop : closed.

Lemma closed_wrt_tc_formals_cons:
  forall S id t rest,
    ~ S id ->
    closed_wrt_vars S (tc_formals rest) ->
    closed_wrt_vars S (tc_formals ((id,t)::rest)).
Admitted.
Lemma closed_wrt_tc_formals_nil:
  forall S, closed_wrt_vars S (tc_formals nil).
Admitted.
Hint Resolve closed_wrt_tc_formals_cons closed_wrt_tc_formals_nil : closed.

Lemma closed_wrt_stackframe_of:
  forall S f, closed_wrt_vars S (stackframe_of f).
Admitted.
Hint Resolve closed_wrt_stackframe_of : closed.

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

Lemma closed_wrt_map_subst:
   forall {A: Type} id e (Q: list (environ -> A)),
         Forall (closed_wrt_vars (eq id)) Q ->
         map (subst id e) Q = Q.
Proof.
induction Q; intros.
simpl; auto.
inv H.
simpl; f_equal; auto.
apply closed_wrt_subst; auto.
Qed.
Hint Rewrite @closed_wrt_map_subst using solve [auto with closed] : normalize.
Hint Rewrite @closed_wrt_map_subst using solve [auto with closed] : subst.
Hint Rewrite @closed_wrt_subst using solve [auto with closed] : normalize.
Hint Rewrite @closed_wrt_subst using solve [auto with closed] : subst.

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
Hint Rewrite subst_eval_id_eq : subst.
Hint Rewrite subst_eval_id_neq using (solve [auto with closed]) : normalize.
Hint Rewrite subst_eval_id_neq using (solve [auto with closed]) : subst.

Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @lift1_lift0 : normalize.

Lemma tc_formals_cons:
  forall i t rest, tc_formals ((i,t) :: rest) =
         `and (`(tc_val t) (eval_id i)) (tc_formals rest).
Proof.
intros.
extensionality rho; simpl.
unfold tc_formals; fold tc_formals.
unfold_coerce. simpl.
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

Lemma local_lift2_and: forall P Q, local (`and P Q) = 
        local P && local Q.
Proof. intros; extensionality rho. unfold local; unfold_coerce.   
simpl.
 apply pred_ext; normalize. destruct H; normalize.
Qed.
Hint Rewrite local_lift2_and : normalize.

Lemma subst_TT {A}{NA: NatDed A}: forall i v, subst i v TT = TT.
Admitted.
Lemma subst_FF {A}{NA: NatDed A}: forall i v, subst i v FF = FF.
Admitted.
Hint Rewrite @subst_TT @subst_FF: normalize.
Hint Rewrite @subst_TT @subst_FF: subst.
Hint Rewrite (@subst_TT mpred Nveric) (@subst_FF mpred Nveric): normalize.
Hint Rewrite (@subst_TT mpred Nveric) (@subst_FF mpred Nveric): subst.

Lemma eval_expr_Econst_int: forall i t, eval_expr (Econst_int i t) = `(Vint i).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_Econst_int : normalize.

Lemma eval_expr_Ecast: 
  forall e t, eval_expr (Ecast e t) = `(eval_cast (typeof e) t) (eval_expr e).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_Ecast : normalize.

Lemma subst_local: forall id v P,
  subst id v (local P) = local (subst id v P).
Proof. reflexivity. Qed.
Hint Rewrite subst_local : normalize.
Hint Rewrite subst_local : subst.
Lemma eval_lvalue_Ederef:
  forall e t, eval_lvalue (Ederef e t) = `force_ptr (eval_expr e).
Proof. reflexivity. Qed.
Hint Rewrite eval_lvalue_Ederef : normalize.

Lemma local_lift0_True:     local (`True) = TT.
Proof. reflexivity. Qed.
Hint Rewrite local_lift0_True : normalize.

Lemma overridePost_EK_return: 
  forall Q P, overridePost Q P EK_return = P EK_return.
Proof. unfold overridePost; intros. 
  extensionality vl rho; rewrite if_false by congruence. auto.
Qed.
Hint Rewrite overridePost_EK_return : normalize.

Lemma frame_ret_assert_emp:
  forall P, frame_ret_assert P emp = P.
Proof. intros.
 extensionality ek. extensionality vl. extensionality rho.
 unfold frame_ret_assert.
 rewrite sepcon_emp. auto.
Qed.

Hint Rewrite frame_ret_assert_emp : normalize.

Lemma frame_ret_assert_EK_return:
 forall P Q vl, frame_ret_assert P Q EK_return vl =  P EK_return vl * Q.
Proof. reflexivity. Qed.
Hint Rewrite frame_ret_assert_EK_return : normalize.

Lemma function_body_ret_assert_EK_return:
  forall t P vl, function_body_ret_assert t P EK_return vl = bind_ret vl t P.
Proof. reflexivity. Qed.
Hint Rewrite function_body_ret_assert_EK_return : normalize.

Lemma bind_ret1_unfold:
  forall v t Q, bind_ret (Some v) t Q = !!tc_val t v && `Q (make_args (ret_temp :: nil)(v::nil)).
Proof. reflexivity. Qed.
Hint Rewrite bind_ret1_unfold : normalize.

Lemma bind_ret1_unfold':
  forall v t Q rho, 
  bind_ret (Some v) t Q rho = !!(tc_val t v) && Q (make_args (ret_temp::nil)(v::nil) rho).
Proof.
 intros. reflexivity.
Qed.
Hint Rewrite bind_ret1_unfold' : normalize.  (* put this in AFTER the unprimed version, for higher priority *)

Lemma normal_ret_assert_derives': 
  forall P Q, P |-- Q -> normal_ret_assert P |-- normal_ret_assert Q.
Proof. 
  intros. intros ek vl rho. apply normal_ret_assert_derives. apply H.
Qed.

Lemma normal_ret_assert_eq:
  forall P ek vl, normal_ret_assert P ek vl =
             (!! (ek=EK_normal) && (!! (vl=None) && P)).
Proof. reflexivity. Qed.
Hint Rewrite normal_ret_assert_eq: normalize. 

Lemma loop1_ret_assert_normal:
  forall P Q, loop1_ret_assert P Q EK_normal None = P.
Proof. reflexivity. Qed.
Hint Rewrite loop1_ret_assert_normal: normalize.

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
Hint Rewrite @substopt_unfold @substopt_unfold_nil : subst.

Lemma get_result_unfold: forall id, get_result (Some id) = get_result1 id.
Proof. reflexivity. Qed.
Lemma get_result_None: get_result None = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite get_result_unfold get_result_None : normalize.

Lemma eval_expropt_Some: forall e, eval_expropt (Some e) = `Some (eval_expr e).
Proof. reflexivity. Qed.
Lemma eval_expropt_None: eval_expropt None = `None.
Proof. reflexivity. Qed.
Hint Rewrite eval_expropt_Some eval_expropt_None : normalize.

Definition Ews (* extern_write_share *) := Share.splice extern_retainer Share.top.

Lemma globvar_eval_var:
  forall Delta rho id t,
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

Lemma globvars2pred_unfold: forall vl rho, 
    globvars2pred vl rho = 
    fold_right sepcon emp (map (fun idv => globvar2pred idv rho) vl).
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

Lemma deref_noload_tarray:
  forall ty n, deref_noload (tarray ty n) = (fun v => v).
Proof. 
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_tarray : normalize.

Lemma deref_noload_Tarray:
  forall ty n a, deref_noload (Tarray ty n a) = (fun v => v).
Proof. 
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_Tarray : normalize.


Lemma TT_sepcon {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
   forall (P: A), P |-- (TT * P).
Proof. intros. rewrite sepcon_comm; apply sepcon_TT.
Qed.

Ltac find_change P Q :=
 match Q with
  | ?Q1 * ?Q2 => first [change Q2 with P | find_change P Q1]
  | _ => change Q with P
 end.

Ltac find_change_later P Q :=
 match Q with
  | ?Q1 * later ?Q2 => first [change Q2 with P | find_change_later P Q1]
  | later ?Q2 => change Q2 with P
 end.

Ltac lift1 a e1 rho  :=
 match e1 with
 | lift0 rho => constr:(a)
 | lift0 ?a1 => constr: (lift0 (a a1))
 | _ => constr:(lift1 a e1)
 end.

Ltac lift2 a e1 e2 rho :=
 match e1 with
 |  lift0 ?a1 => lift1 (a a1) e2 rho
 | _ => constr:(lift2 a e1 e2)
 end.

Ltac lift3 a e1 e2 e3 rho :=
 match e1 with
 |  lift0 ?a1 => lift2 (a a1) e2 e3 rho
 | _ => constr:(lift3 a e1 e2 e3)
 end.

Ltac abstract_env rho P :=
  match P with
   | @emp mpred _ _ => constr:(@emp assert _ _)
   | @sepcon mpred _ _ ?e1 ?e2 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
       in constr:(@sepcon assert _ _ e1' e2')
   | ?a0 ?a1 ?a2 ?e1 ?e2 ?e3 => 
      let e1' := abstract_env rho e1  in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3
      in lift3 (a0 a1 a2) e1' e2' e3' rho
   | ?a0 ?a1 ?e1 ?e2 ?e3 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3
      in lift3 (a0 a1) e1' e2' e3' rho
   | ?a0 ?e1 ?e2 ?e3 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3
      in lift3 a0 e1' e2' e3' rho
   | ?a0 ?e1 ?e2 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
      in lift2 a0 e1' e2' rho
   | ?a0 ?e1 => let e1' := abstract_env rho e1 in lift1 a0 e1' rho
   | rho => constr: (lift1)
   | ?a => constr:(lift0 a)
   end.

Lemma cancel_frame0{A}{ND: NatDed A}{SL: SepLog A}:
  forall rho: environ, emp rho |-- fold_right sepcon emp nil rho.
Proof. intro; apply derives_refl. Qed.

Lemma cancel_frame2: forall (P Q: assert) F (rho: environ),
     Q rho |-- 	fold_right sepcon emp F rho ->
    (P * Q) rho |-- fold_right sepcon emp (P::F) rho.
Proof. intros. simpl. apply sepcon_derives; auto.
Qed.

Lemma cancel_frame1: forall P (rho: environ), 
         P rho |-- fold_right sepcon emp (P::nil) rho.
Proof. intros. unfold fold_right. rewrite sepcon_emp; apply derives_refl.
Qed.

Ltac cancel_frame := 
match goal with |- ?P |-- fold_right sepcon emp ?F ?rho  =>
     let P' := abstract_env rho P in  
       change ( P' rho |-- fold_right sepcon emp F rho);
    repeat rewrite sepcon_assoc;
    repeat apply cancel_frame2; 
    try apply cancel_frame1;
    try (instantiate (1:=nil) in (Value of F); unfold F; apply cancel_frame0)
 end.

Ltac cancel :=
repeat first [rewrite emp_sepcon | rewrite sepcon_emp];
match goal with |- ?P |-- ?Q =>
  (* The "emp" is a marker to notice when one complete pass has been made *)
   apply derives_trans with (emp * P) ; [ rewrite (emp_sepcon P); apply derives_refl | ]
 end;
repeat rewrite <- sepcon_assoc;
repeat
match goal with 
   | |- sepcon _ emp |-- _ => fail 1
   | |- sepcon _ TT |-- _ => pull_left (@TT mpred _)
   | |- sepcon ?P ?P' |-- ?Q =>
      first [find_change P' Q; pull_right P'; 
               apply sepcon_derives; [  | apply derives_refl ]
             | find_change_later P' Q; pull_right (later P'); 
               apply sepcon_derives; [  | apply now_later ]
             | pull_left P'
             ]
 end;
  repeat first [rewrite emp_sepcon | rewrite sepcon_emp];
  pull_left (@TT mpred _);
  first [apply derives_refl
          | apply TT_right
          | apply sepcon_TT 
          | apply TT_sepcon
          | cancel_frame
          | idtac
          ].

Lemma exp_trivial {A}{NA: NatDed A}:
  forall {T: Type} (any: T) (P: A), exp (fun x:T => P) = P.
Proof.
 intros. apply pred_ext. apply exp_left; auto.
 apply exp_right with any; auto.
Qed.

Hint Rewrite (exp_trivial Vundef) (exp_trivial O) (exp_trivial 0%Z) (exp_trivial Int.zero) : normalize.

(* Admitted: move these next two to assert_lemmas *)
Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : normalize.

Lemma prop_derives {A}{ND: NatDed A}: 
 forall (P Q: Prop), (P -> Q) -> prop P |-- prop Q.
Proof.
intros; apply prop_left; intro; apply prop_right; auto.
Qed.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 => Int.cmpu Ceq n1 n2 = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Int.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

Lemma ptr_eq_e: forall v1 v2, ptr_eq v1 v2 -> v1=v2.
Proof.
intros. destruct v1; destruct v2; simpl in H; try contradiction.
pose proof (Int.eq_spec i i0). rewrite H in H0. subst; auto.
destruct H; subst.
f_equal.
pose proof (Int.eq_spec i i0). rewrite H0 in H; auto.
Qed.

