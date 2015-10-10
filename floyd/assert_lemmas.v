Require Import floyd.base.
Local Open Scope logic.

Lemma proj_sumbool_is_false:
  forall (P: Prop) (a: {P}+{~P}), ~P -> proj_sumbool a = false.
Proof.
intros. destruct a; auto; contradiction.
Qed.

Hint Rewrite proj_sumbool_is_true using (solve [auto 3]) : norm.
Hint Rewrite proj_sumbool_is_false using (solve [auto 3]) : norm.

Lemma neutral_isCastResultType:
  forall {cs: compspecs}  P t t' v rho,
   is_neutral_cast t' t = true ->
   P |-- denote_tc_assert (isCastResultType t' t v) rho.
Proof.
intros.
  unfold isCastResultType;
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |], t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
     inv H; simpl; try apply @TT_right;
    simpl; if_tac; apply @TT_right.
Qed.

Lemma exp_uncurry:
  forall {T} {ND: NatDed T} A B F, (@exp T ND A (fun a => @exp T ND B (fun b => F a b)))
   = @exp T ND (A*B) (fun ab => F (fst ab) (snd ab)).
Proof.
intros.
apply pred_ext.
apply exp_left; intro a. apply exp_left; intro b. apply exp_right with (a,b).
apply derives_refl.
apply exp_left; intro ab. apply exp_right with (fst ab). apply exp_right with (snd ab).
apply derives_refl.
Qed.

Lemma isptr_offset_val':
 forall i p, isptr p -> isptr (offset_val i p).
Proof. intros. destruct p; try contradiction; apply Coq.Init.Logic.I. Qed.
Hint Resolve isptr_offset_val': norm.

Lemma sem_add_pi_ptr:
   forall {cs: compspecs}  t p i, 
    isptr p ->
    sem_add_pi t p (Vint i) = Some (offset_val (Int.mul (Int.repr (sizeof cenv_cs t)) i) p).
Proof. intros. destruct p; try contradiction. reflexivity. Qed.
Hint Rewrite @sem_add_pi_ptr using (solve [auto with norm]) : norm.

Lemma sem_cast_i2i_correct_range: forall sz s v,
  is_int sz s v -> sem_cast_i2i sz s v = Some v.
Proof.
  intros.
  destruct sz, s, v; try solve [inversion H]; simpl;
  f_equal; f_equal; try apply sign_ext_inrange; try apply zero_ext_inrange; eauto.
  + simpl in H; destruct H; subst; reflexivity.
  + simpl in H; destruct H; subst; reflexivity.
Qed.
Hint Rewrite sem_cast_i2i_correct_range using (solve [auto with norm]) : norm.

Lemma force_val_e:
 forall v, force_val (Some v) = v. 
Proof. reflexivity. Qed.
Hint Rewrite force_val_e: norm.

Lemma sem_cast_neutral_ptr:
  forall p, isptr p -> sem_cast_neutral p = Some p.
Proof. intros. destruct p; try contradiction; reflexivity. Qed.
Hint Rewrite sem_cast_neutral_ptr using (solve [auto with norm]): norm.

Lemma sem_cast_neutral_int: forall v,
  (exists sz s, is_int sz s v) -> sem_cast_neutral v = Some v.
Proof.
  intros.
  destruct H as [? [? ?]].
  destruct v; try inversion H.
  reflexivity.
Qed.
Hint Rewrite sem_cast_neutral_int using (solve [eauto with norm]) : norm.

Lemma sizeof_tuchar: forall cenv, sizeof cenv tuchar = 1%Z.
Proof. reflexivity. Qed.
Hint Rewrite sizeof_tuchar: norm.

Hint Rewrite Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r : norm.

Definition nullval : val := Vint Int.zero.

Lemma subst_derives:
  forall id e P Q, P |-- Q -> subst id e P |-- subst id e Q.
Proof.
 intros. intro rho. unfold subst. apply H.
Qed.

(* no "semax" in this file, just assertions. *)
Global Transparent Int.repr.

Lemma liftTrue: forall rho, `True rho.
Proof. intro. unfold_lift; apply Coq.Init.Logic.I. Qed.
Hint Resolve liftTrue.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
extensionality ek vl.
if_tac; normalize.
subst ek.
rewrite (prop_true_andp (EK_normal = _)) by auto.
auto.
apply pred_ext; normalize.
Qed.

Lemma normal_ret_assert_derives:
 forall (P Q: environ->mpred) rho,
  P rho |-- Q rho ->
  forall ek vl, normal_ret_assert P ek vl rho |-- normal_ret_assert Q ek vl rho.
Proof.
 intros.
 unfold normal_ret_assert; intros; normalize.
 simpl.
 apply andp_derives.
 apply derives_refl.
 apply andp_derives.
 apply derives_refl.
 auto.
Qed.
Hint Resolve normal_ret_assert_derives : norm.

Lemma normal_ret_assert_FF:
  forall ek vl, normal_ret_assert FF ek vl = FF.
Proof.
unfold normal_ret_assert. intros. normalize.
Qed.

Lemma frame_normal:
  forall P F, 
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (P * F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, normal_ret_assert.
normalize.
Qed.

Lemma frame_for1:
  forall Q R F, 
   frame_ret_assert (loop1_ret_assert Q R) F = 
   loop1_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, loop1_ret_assert.
destruct ek; normalize.
Qed.

Lemma frame_loop1:
  forall Q R F, 
   frame_ret_assert (loop2_ret_assert Q R) F = 
   loop2_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, loop2_ret_assert.
destruct ek; normalize.
Qed.


Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_loop1 
                 overridePost_normal: ret_assert.

Hint Rewrite eval_id_same : norm.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.

Hint Resolve @TT_right.

Hint Rewrite Int.sub_idem Int.sub_zero_l  Int.add_neg_zero : norm.

Lemma type_eq_refl:
 forall t, proj_sumbool (type_eq t t) = true.
Proof.
intros.
apply proj_sumbool_is_true.
auto.
Qed.

Lemma overridePost_overridePost:
 forall P Q R, overridePost P (overridePost Q R) = overridePost P R.
Proof.
intros.
unfold overridePost.
extensionality ek vl; simpl.
if_tac; auto.
Qed.
Hint Rewrite overridePost_overridePost : ret_assert.

Lemma overridePost_normal':
  forall P R, overridePost P R EK_normal None = P.
Proof.
 intros. unfold overridePost. rewrite if_true by auto.
 apply prop_true_andp. auto.
Qed.
Hint Rewrite overridePost_normal' : ret_assert.

Lemma eval_expr_Etempvar: 
  forall {cs: compspecs}  i t, eval_expr (Etempvar i t) = eval_id i.
Proof. reflexivity.
Qed.
Hint Rewrite @eval_expr_Etempvar : eval.

Lemma eval_expr_binop: forall {cs: compspecs}  op a1 a2 t, eval_expr (Ebinop op a1 a2 t) = 
          `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2).
Proof. reflexivity. Qed.
Hint Rewrite @eval_expr_binop : eval.

Lemma eval_expr_unop: forall {cs: compspecs} op a1 t, eval_expr (Eunop op a1 t) = 
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
Hint Rewrite @eval_expr_unop : eval.

Hint Resolve  eval_expr_Etempvar.

Lemma eval_expr_Etempvar' : forall {cs: compspecs}  i t, eval_id i = eval_expr (Etempvar i t).
Proof. intros. symmetry; auto.
Qed.
Hint Resolve  @eval_expr_Etempvar'.

Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : norm.

Lemma liftx_id:
    forall {T} e, @liftx (Tarrow T (LiftEnviron T)) (fun v => v) e = e.
Proof.
 intros. extensionality rho; simpl; auto.
Qed.
Hint Rewrite @liftx_id : norm2.

Lemma liftx3_liftx2:
 forall {A1 A2 A3 B} f (x: A1),
  @liftx (Tarrow A1 (Tarrow A2 (Tarrow A3 (LiftEnviron B)))) f (@liftx (LiftEnviron A1) x) =
  @liftx (Tarrow A2 (Tarrow A3 (LiftEnviron B))) (f x).
Proof. reflexivity. Qed.

Lemma liftx2_liftx1:
 forall {A1 A2 B} f (x: A1),
  @liftx (Tarrow A1 (Tarrow A2 (LiftEnviron B))) f (@liftx (LiftEnviron A1) x) =
  @liftx (Tarrow A2 (LiftEnviron B)) (f x).
Proof. reflexivity. Qed.

Lemma liftx1_liftx0:
  forall {A1 B} f (x: A1),
  @liftx (Tarrow A1 (LiftEnviron B)) f (@liftx (LiftEnviron A1) x) =
  @liftx (LiftEnviron B) (f x).
Proof. reflexivity. Qed.

Hint Rewrite @liftx3_liftx2 @liftx2_liftx1 @liftx1_liftx0 : norm2.

Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @lift1_lift0 : norm2.

Lemma const_liftx0:
  forall B (P: B), (fun _ : environ => P) = `P.
Proof. reflexivity. Qed.
Hint Rewrite const_liftx0 : norm2.

Lemma lift_identity:
  forall A f, `(fun v: A => v) f = f.
Proof. intros. reflexivity. Qed.
Hint Rewrite lift_identity : norm2.

Lemma tc_eval_gvar_zero:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some t ->
            exists b, eval_var i t rho = Vptr b Int.zero.
Proof.
 intros. unfold eval_var; simpl.
 hnf in H. unfold typecheck_environ in H.
  destruct H as [_ [? [? ?]]].
  unfold typecheck_var_environ in  *. 
  unfold typecheck_glob_environ in *. 
  unfold same_env in *. 
  destruct (H3 _ _ H1).
  unfold Map.get; rewrite H4.
  destruct (H2 _ _ H1) as [b [? ?]].
   rewrite H5. simpl.
  eauto.
  destruct H4; congruence.
Qed.

Lemma tc_eval_gvar_i:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some t ->
             tc_val (Tpointer t noattr) (eval_var i t rho).
Proof.
 intros.
 destruct (tc_eval_gvar_zero _ _ _ _ H H0 H1) as [b ?].
 rewrite H2; apply Coq.Init.Logic.I.
Qed.

Lemma local_lift2_and: forall P Q, local (`and P Q) = 
        local P && local Q.
Proof. intros; extensionality rho. unfold local; super_unfold_lift.   
simpl.
 apply pred_ext; normalize. destruct H; normalize.
Qed.
Hint Rewrite local_lift2_and : norm2.

Lemma subst_TT {A}{NA: NatDed A}: forall i v, subst i v TT = TT.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_FF {A}{NA: NatDed A}: forall i v, subst i v FF = FF.
Proof. 
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @subst_TT @subst_FF: subst.
Hint Rewrite (@subst_TT mpred Nveric) (@subst_FF mpred Nveric): subst.

Lemma eval_expr_Econst_int: forall {cs: compspecs}  i t, eval_expr (Econst_int i t) = `(Vint i).
Proof. reflexivity. Qed.
Hint Rewrite @eval_expr_Econst_int : eval.

Lemma subst_eval_var:
  forall id v id' t, subst id v (eval_var id' t) = eval_var id' t.
Proof.
intros. unfold subst, eval_var. extensionality rho.
simpl. auto.
Qed.
Hint Rewrite subst_eval_var : subst.

Lemma subst_local: forall id v P,
  subst id v (local P) = local (subst id v P).
Proof. reflexivity. Qed.
Hint Rewrite subst_local : subst.

Lemma eval_lvalue_Ederef:
  forall {cs: compspecs}  e t, eval_lvalue (Ederef e t) = `force_ptr (eval_expr e).
Proof. reflexivity. Qed.
Hint Rewrite @eval_lvalue_Ederef : eval.

Lemma local_lift0_True:     local (`True) = TT.
Proof. reflexivity. Qed.
Hint Rewrite local_lift0_True : norm2.

Lemma overridePost_EK_return: 
  forall Q P, overridePost Q P EK_return = P EK_return.
Proof. unfold overridePost; intros. 
  extensionality vl rho; rewrite if_false by congruence. auto.
Qed.
Hint Rewrite overridePost_EK_return : ret_assert.

Lemma frame_ret_assert_emp:
  forall P, frame_ret_assert P emp = P.
Proof. intros.
 extensionality ek. extensionality vl. extensionality rho.
 unfold frame_ret_assert.
 rewrite sepcon_emp. auto.
Qed.

Hint Rewrite frame_ret_assert_emp : ret_assert.

Lemma frame_ret_assert_EK_return:
 forall P Q vl, frame_ret_assert P Q EK_return vl =  P EK_return vl * Q.
Proof. reflexivity. Qed.
Hint Rewrite frame_ret_assert_EK_return : ret_assert.

Lemma function_body_ret_assert_EK_return:
  forall t P vl, function_body_ret_assert t P EK_return vl = bind_ret vl t P.
Proof. reflexivity. Qed.
Hint Rewrite function_body_ret_assert_EK_return : ret_assert.

Lemma bind_ret1_unfold:
  forall v t Q, bind_ret (Some v) t Q = !!tc_val t v && `Q (make_args (ret_temp :: nil)(v::nil)).
Proof. reflexivity. Qed.
Hint Rewrite bind_ret1_unfold : norm2.

Lemma bind_ret1_unfold':
  forall v t Q rho, 
  bind_ret (Some v) t Q rho = !!(tc_val t v) && Q (make_args (ret_temp::nil)(v::nil) rho).
Proof.
 intros. reflexivity.
Qed.
Hint Rewrite bind_ret1_unfold' : norm2.  (* put this in AFTER the unprimed version, for higher priority *)

Lemma normal_ret_assert_derives': 
  forall P Q, P |-- Q -> normal_ret_assert P |-- normal_ret_assert Q.
Proof. 
  intros. intros ek vl rho. apply normal_ret_assert_derives. apply H.
Qed.

Lemma normal_ret_assert_eq:
  forall P ek vl, normal_ret_assert P ek vl =
             (!! (ek=EK_normal) && (!! (vl=None) && P)).
Proof. reflexivity. Qed.
(* Hint Rewrite normal_ret_assert_eq: ret_assert.  NO! *)

Lemma normal_ret_assert_elim:
 forall P, normal_ret_assert P EK_normal None = P.
Proof.
intros. unfold normal_ret_assert.
repeat rewrite prop_true_andp by auto.
auto.
Qed.

Lemma overridePost_EK_break:
 forall P Q, overridePost P Q EK_break None = Q EK_break None.
Proof. intros. unfold overridePost.
 rewrite if_false; congruence.
Qed.

Lemma loop1_ret_assert_EK_break:
 forall P Q, loop1_ret_assert P Q EK_break None = Q EK_normal None.
Proof. intros. reflexivity.
Qed.

Hint Rewrite overridePost_EK_break loop1_ret_assert_EK_break
  normal_ret_assert_elim : ret_assert.

Lemma loop1_ret_assert_normal:
  forall P Q, loop1_ret_assert P Q EK_normal None = P.
Proof. reflexivity. Qed.
Hint Rewrite loop1_ret_assert_normal: ret_assert.

Lemma unfold_make_args': forall fsig args rho,
    make_args' fsig args rho = make_args (map (@fst _ _) (fst fsig)) (args rho) rho.
Proof. reflexivity. Qed.
Hint Rewrite unfold_make_args' : norm2.
Lemma unfold_make_args_cons: forall i il v vl rho,
   make_args (i::il) (v::vl) rho = env_set (make_args il vl rho) i v.
Proof. reflexivity. Qed.
Lemma unfold_make_args_nil: make_args nil nil = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite unfold_make_args_cons unfold_make_args_nil : norm2.

Lemma clear_rhox:  (* replaces clear_make_args' *)
 forall (P: mpred) (f: environ -> environ),
    @liftx (Tarrow environ (LiftEnviron mpred))
                    (@liftx (LiftEnviron mpred) P) f
       = `P.
Proof. intros. reflexivity. Qed.
Hint Rewrite clear_rhox: norm2.

Lemma eval_make_args':
  forall (Q: val -> Prop) i fsig args,
  @liftx (Tarrow environ (LiftEnviron Prop))
      (@liftx (Tarrow val (LiftEnviron Prop)) Q (eval_id i))
   (make_args' fsig args) =
  `Q (`(eval_id i) (make_args' fsig args)).
Proof. reflexivity. Qed.
Hint Rewrite eval_make_args' : norm2.

Lemma eval_make_args_same:
 forall {cs: compspecs}  i t fsig t0 tl (e: expr) el,
 `(eval_id i) (make_args' ((i,t)::fsig, t0) (eval_exprlist (t::tl) (e::el))) = 
   `force_val (`(sem_cast (typeof e) t) (eval_expr e)).
Proof.
intros.
extensionality rho.
unfold make_args'.
unfold_lift.
simpl.
unfold eval_id.
simpl.
rewrite Map.gss.
simpl.
unfold_lift.
reflexivity.
Qed.

Lemma eval_make_args_other:
 forall {cs: compspecs}  i j fsig t0 t t' tl (e: expr) el,
   i<>j ->
  `(eval_id i) (make_args' ((j,t)::fsig, t0) (eval_exprlist (t'::tl) (e::el))) =
   `(eval_id i) (make_args' (fsig, t0) (eval_exprlist tl el)).
Proof.
intros. extensionality rho.
unfold make_args'.
unfold_lift.
simpl.
unfold eval_id.
simpl.
rewrite Map.gso; auto.
Qed.

Hint Rewrite @eval_make_args_same : norm2.
Hint Rewrite @eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

Infix "oo" := Basics.compose (at level 54, right associativity).
Arguments Basics.compose {A B C} g f x / .

Lemma compose_backtick:
  forall A B C (F: B -> C) (G: A -> B) (J: environ -> A),
   `F (`G  J) = `(Basics.compose F G) J.
Proof. reflexivity. Qed.
Hint Rewrite compose_backtick : norm.

Lemma compose_eval_make_args_same:
  forall {cs: compspecs}  (Q: val -> Prop) i t fsig t0 tl e el,
  @liftx (Tarrow environ (LiftEnviron Prop))
      (Q oo (eval_id i)) (make_args' ((i,t)::fsig,t0) (eval_exprlist (t::tl) (e::el))) =
  `Q (`force_val (`(sem_cast (typeof e) t) (eval_expr e))).
Proof. 
  intros.
  rewrite <- compose_backtick.
  f_equal. apply eval_make_args_same.
Qed.

Lemma compose_eval_make_args_other:
  forall {cs: compspecs}  Q i j fsig t0 t t' tl (e: expr) el,
   i<>j ->
    @liftx (Tarrow environ (LiftEnviron Prop))
     (Q oo (eval_id i)) (make_args' ((j,t)::fsig, t0) (eval_exprlist (t'::tl) (e::el))) =
     `Q (`(eval_id i) (make_args' (fsig, t0) (eval_exprlist tl el))).
Proof.
  intros.
  rewrite <- compose_backtick.
  f_equal. apply eval_make_args_other; auto.
Qed.

Hint Rewrite @compose_eval_make_args_same : norm.
Hint Rewrite @compose_eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

Lemma substopt_unfold {A}: forall id v, @substopt A (Some id) v = @subst A id v.
Proof. reflexivity. Qed.
Lemma substopt_unfold_nil {A}: forall v (P:  environ -> A), substopt None v P = P.
Proof. reflexivity. Qed.
Hint Rewrite @substopt_unfold @substopt_unfold_nil : subst.

Lemma get_result_unfold: forall id, get_result (Some id) = get_result1 id.
Proof. reflexivity. Qed.
Lemma get_result_None: get_result None = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite get_result_unfold get_result_None : norm.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (var_types Delta) ! i = None /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Proof.
intros. 
destruct H as [H [H8 H0]].
unfold eval_var, globals_only.
simpl. 
destruct H as [_ [? [? ?]]].
destruct (H2 i g H0).
unfold Map.get; rewrite H3; auto.
destruct H3.
congruence.
Qed.

Hint Rewrite elim_globals_only using (split3; [eassumption | reflexivity.. ]) : norm.

Lemma eval_var_env_set:
  forall i t j v (rho: environ), eval_var i t (env_set rho j v) = eval_var i t rho.
Proof. reflexivity. Qed.

Hint Rewrite eval_var_env_set : norm. (* MOVE elsewhere? *)

Lemma elim_globals_only': 
 forall a: mpred, 
 (@liftx (Tarrow environ (LiftEnviron mpred)) (`a) globals_only) = `a.
Proof. reflexivity. Qed.
Hint Rewrite elim_globals_only' : norm.

Lemma eval_expropt_Some: forall {cs: compspecs}  e, eval_expropt (Some e) = `Some (eval_expr e).
Proof. reflexivity. Qed.
Lemma eval_expropt_None: forall  {cs: compspecs} , eval_expropt None = `None.
Proof. reflexivity. Qed.
Hint Rewrite @eval_expropt_Some @eval_expropt_None : eval.
 
Lemma globvar_eval_var:
  forall Delta rho id t,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  t ->
     exists b,  eval_var id t rho = Vptr b Int.zero
            /\ ge_of rho id = Some b.
Proof.
intros.
unfold tc_environ, typecheck_environ in H.
destruct H as [Ha [Hb [Hc Hd]]].
hnf in Hc.
specialize (Hc _ _ H1). destruct Hc as [b [Hc Hc']].
exists b.
unfold eval_var; simpl.
apply Hd in H1. 
destruct H1 as [? | [? ?]]; [ | congruence].
unfold Map.get; rewrite H. rewrite Hc.
auto.
Qed.

Lemma globvars2pred_unfold: forall vl rho, 
    globvars2pred vl rho = 
    fold_right sepcon emp (map (fun idv => globvar2pred idv rho) vl).
Proof. intros. unfold globvars2pred.
   induction vl; simpl; auto. normalize; f_equal; auto.
Qed.
Hint Rewrite globvars2pred_unfold : norm.

Lemma offset_offset_val:
  forall v i j, offset_val j (offset_val i v) = offset_val (Int.add i j) v.
Proof. intros; unfold offset_val.
 destruct v; auto. rewrite Int.add_assoc; auto.
Qed.
Hint Rewrite offset_offset_val: norm.

Hint Rewrite add_repr : norm.
Hint Rewrite mul_repr : norm.
Hint Rewrite sub_repr : norm.
Hint Rewrite and_repr : norm.
Hint Rewrite or_repr : norm.

Lemma ltu_repr: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma ltu_repr_false: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = false -> i>=j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma int_add_assoc1:
  forall z i j, Int.add (Int.add z (Int.repr i)) (Int.repr j) = Int.add z (Int.repr (i+j)).
Proof.
intros.
rewrite Int.add_assoc. f_equal. apply add_repr.
Qed.
Hint Rewrite int_add_assoc1 : norm.

Lemma power_nat_divide: forall n m, two_power_nat n <= two_power_nat m -> Z.divide (two_power_nat n) (two_power_nat m).
Proof.
  intros.
  repeat rewrite two_power_nat_two_p in *.
  unfold Zdivide.
  exists (two_p (Z.of_nat m - Z.of_nat n)).
  assert ((Z.of_nat m) = (Z.of_nat m - Z.of_nat n) + Z.of_nat n) by omega.
  rewrite H0 at 1.
  assert (Z.of_nat m >= 0) by omega.
  assert (Z.of_nat n >= 0) by omega.
  assert (Z.of_nat n <= Z.of_nat m).
    destruct (Z_le_gt_dec (Z.of_nat n) (Z.of_nat m)).
    exact l.
    assert (Z.of_nat m < Z.of_nat n) by omega.
    assert (two_p (Z.of_nat m) < two_p (Z.of_nat n)) by (apply two_p_monotone_strict; omega).
    omega.  
  apply (two_p_is_exp (Z.of_nat m - Z.of_nat n) (Z.of_nat n)); omega.
Qed.

Lemma divide_add_align: forall a b c, Z.divide b a -> a + (align c b) = align (a + c) b.
Proof.
  intros.
  pose proof zeq b 0.
  destruct H0; unfold Z.divide in H; unfold align.
  + destruct H. subst. 
    repeat rewrite Zdiv_0_r.
    simpl.
    omega.
  + destruct H.
    subst.
    replace (x * b + c + b - 1) with (x * b + (c + b - 1)) by omega.
    rewrite Z_div_plus_full_l.
    rewrite Z.mul_add_distr_r.
    reflexivity.
    omega.
Qed.

Lemma deref_noload_tarray:
  forall ty n, deref_noload (tarray ty n) = (fun v => v).
Proof. 
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_tarray : norm.

Lemma deref_noload_Tarray:
  forall ty n a, deref_noload (Tarray ty n a) = (fun v => v).
Proof. 
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_Tarray : norm.


Lemma TT_sepcon {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
   forall (P: A), P |-- (TT * P).
Proof. intros. rewrite sepcon_comm; apply sepcon_TT.
Qed.

Hint Resolve (@derives_refl mpred _) : cancel.
Hint Resolve (@now_later mpred _ _) : cancel.

Lemma cancel1_start:
 forall P Q : mpred, 
   P |-- Q * emp ->
   P |-- Q.
Proof. intros. rewrite sepcon_emp in H; auto.
Qed.

Lemma cancel1_here:
  forall P P' Q1 Q2 Q3 : mpred, 
  P' |-- Q2 ->
  P |-- Q1 * Q3 ->
  P * P' |-- Q1 * Q2 * Q3.
Proof.
intros. rewrite (sepcon_comm Q1).
rewrite sepcon_assoc.  rewrite sepcon_comm. apply sepcon_derives; auto.
Qed.

Lemma cancel1_next:
  forall P Q1 Q2 Q3 : mpred,
   P |-- Q1 * (Q2 * Q3) ->
   P |-- Q1 * Q2 * Q3.
Proof. intros. rewrite sepcon_assoc; auto. Qed.

Lemma cancel1_last:
  forall P P' Q2 Q3 : mpred,
  P' |-- Q2 ->
  P |-- Q3 ->
  P * P' |-- Q2 * Q3.
Proof.
 intros. rewrite sepcon_comm; apply sepcon_derives; auto.
Qed.

Lemma cancel1_finish1:
  forall P Q1 Q2 Q3 : mpred,
   P |-- Q1 * Q2 * Q3 ->
   P |-- Q1 * (Q2 * Q3).
Proof.
 intros. rewrite <- sepcon_assoc. auto.
Qed.

Lemma cancel1_finish2:
  forall P Q : mpred, 
    P |-- Q ->
   P |-- Q * emp.
Proof. intros. rewrite sepcon_emp; auto.
Qed.

Ltac cancel1 := 
 first [
   simple apply cancel1_here; [
    try match goal with H := _ : list mpred |- _ => clear H end; (*
      this line is to work around Coq 8.4 bug,
      Anomaly: undefined_evars_of_term *) 
    solve [eauto with nocore cancel] 
   | ]
 | simple apply cancel1_next; cancel1
 | simple apply cancel1_last; [
    try match goal with H := _ : list mpred |- _ => clear H end; (*
      this line is to work around Coq 8.4 bug,
      Anomaly: undefined_evars_of_term *)  
    solve [eauto with nocore cancel] | ]
 ].

Ltac cancel2 := 
  simple apply cancel1_start;
  cancel1;
  repeat simple apply cancel1_finish1; 
  try simple apply cancel1_finish2.

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

Ltac lift4 a e1 e2 e3 e4 rho :=
 match e1 with
 |  lift0 ?a1 => lift3 (a a1) e2 e3 e4 rho
 | _ => constr:(lift4 a e1 e2 e3 e4)
 end.

Ltac abstract_env rho P :=
  match P with
   | @emp mpred _ _ => constr:(@emp (environ->mpred) _ _)
   | @sepcon mpred _ _ ?e1 ?e2 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
       in constr:(@sepcon (environ->mpred) _ _ e1' e2')
   | ?a0 ?a1 ?a2 ?e1 ?e2 ?e3 ?e4 => 
      let e1' := abstract_env rho e1  in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1 a2) e1' e2' e3' e4' rho
   | ?a0 ?a1 ?e1 ?e2 ?e3 ?e4 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1) e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 ?e4 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift4 a0 e1' e2' e3' e4' rho
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

Lemma cancel_frame0_low{A}{ND: NatDed A}{SL: SepLog A}:
  emp |-- fold_right sepcon emp nil.
Proof.  apply derives_refl. Qed.

Lemma cancel_frame2: forall (P Q: environ->mpred) F (rho: environ),
     Q rho |-- 	fold_right sepcon emp F rho ->
    (P * Q) rho |-- fold_right sepcon emp (P::F) rho.
Proof. intros. simpl. apply sepcon_derives; auto.
Qed.

Lemma cancel_frame2_low: forall (P Q: mpred) F,
     Q  |-- fold_right sepcon emp F  ->
    (P * Q) |-- fold_right sepcon emp (P::F).
Proof. intros. unfold fold_right; fold @fold_right. apply sepcon_derives; auto.
Qed.

Lemma cancel_frame1: forall (P: environ->mpred) (rho: environ), 
         P rho |-- fold_right sepcon emp (P::nil) rho.
Proof. intros. unfold fold_right. rewrite sepcon_emp; apply derives_refl.
Qed.

Lemma cancel_frame1_low: forall (P: mpred), 
         P |-- fold_right sepcon emp (P::nil).
Proof. intros. unfold fold_right. rewrite sepcon_emp; apply derives_refl.
Qed.


Ltac fixup_lifts := 
 repeat 
 match goal with
 | |- appcontext [@lift0 mpred] => change (@lift0 mpred) with (@liftx (LiftEnviron mpred))
 | |- appcontext [@lift1 ?A] => change (@lift1 A mpred) with (@liftx (Tarrow A (LiftEnviron mpred)))
 | |- appcontext [@lift2 ?A ?B] =>  change (@lift2 A B mpred) with (@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))))
 | |- appcontext [@lift3 ?A ?B ?C] => change (@lift3 A B C mpred) with (@liftx (Tarrow A (Tarrow B (Tarrow C (LiftEnviron mpred)))))
 | |- appcontext [@lift4 ?A ?B ?C ?D] => change (@lift4 A B C D mpred) with (@liftx (Tarrow A (Tarrow B (Tarrow C (Tarrow D (LiftEnviron mpred))))))
 end.

Ltac cancel_frame := 
match goal with
| |- ?P |-- fold_right _ _ ?F ?rho  =>
     let P' := abstract_env rho P in  
       change ( P' rho |-- fold_right sepcon emp F rho);
   fixup_lifts; cbv beta;
    repeat rewrite sepcon_assoc;
   repeat match goal with |- (_ * _) _ |-- _ =>
                   apply cancel_frame2
                    end; 
    try (unfold F; apply cancel_frame1);
    try (instantiate (1:=nil) in (Value of F); unfold F; apply cancel_frame0)
| |- _ |-- fold_right sepcon emp ?F  =>
   repeat rewrite sepcon_assoc;
   repeat apply cancel_frame2_low;
    try (unfold F; apply cancel_frame1_low);
    try (unfold F; apply cancel_frame0_low)
 end.

Ltac pull_left A :=
 (* For some reason in Coq 8.4pl3 and perhaps other versions,
  this works better than the version in log_normalize
  which is simply,
   repeat rewrite <- (pull_right A) || rewrite <- (pull_right0 A)
  and which sometimes fails when the terms get complicated.
 *)
  repeat match goal with
  | |- context [?Q * ?R * A] => rewrite <- (pull_right A Q R)
  | |- context [?Q * A] => rewrite <- (pull_right0 A Q)
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
   | |- sepcon _ ?P' |-- _ => first [ cancel2 | pull_left P' ]
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

Hint Rewrite @exp_trivial : norm.

Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : norm.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 =>  Int.cmpu Ceq n1 n2 = true  /\ Int.cmpu Ceq n1 (Int.repr 0) = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Int.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

Lemma ptr_eq_e: forall v1 v2, ptr_eq v1 v2 -> v1=v2.
Proof.
intros. destruct v1; destruct v2; simpl in H; try contradiction.
pose proof (Int.eq_spec i i0). destruct H. 
rewrite H in H0. subst; auto.
destruct H; subst.
f_equal.
pose proof (Int.eq_spec i i0). rewrite H0 in H; auto.
Qed.

Lemma ptr_eq_True':
   forall p, isptr p -> ptr_eq p p = True.
Proof. intros.
 apply prop_ext; intuition. destruct p; inv H; simpl; auto.
 rewrite Int.eq_true. auto.
Qed.
(* Hint Rewrite ptr_eq_True' using solve[auto] : norm. *)

Lemma ptr_eq_True:
   forall p, is_pointer_or_null p -> ptr_eq p p = True.
Proof. intros.
 apply prop_ext; intuition. destruct p; inv H; simpl; auto.
 rewrite Int.eq_true. auto.
Qed.
Hint Rewrite ptr_eq_True using solve[auto] : norm.

Lemma ptr_eq_is_pointer_or_null: forall x y, ptr_eq x y -> is_pointer_or_null x.
Proof.
  intros.
  unfold ptr_eq, is_pointer_or_null in *.
  destruct x; destruct y; try tauto.
  destruct H as [_ ?].
  unfold Int.cmpu in H.
  exact (binop_lemmas2.int_eq_true _ _ (eq_sym H)).
Qed.

Lemma ptr_eq_sym: forall x y, ptr_eq x y -> ptr_eq y x.
Proof.
   intros.
   pose proof ptr_eq_is_pointer_or_null _ _ H.
   apply ptr_eq_e in H.
   rewrite H in *.
   rewrite ptr_eq_True; tauto.
Qed.

Lemma ptr_eq_trans: forall x y z, ptr_eq x y -> ptr_eq y z -> ptr_eq x z.
Proof.
   intros.
   pose proof ptr_eq_is_pointer_or_null _ _ H.
   apply ptr_eq_e in H.
   apply ptr_eq_e in H0.
   subst.
   rewrite ptr_eq_True; tauto.
Qed.

Lemma flip_lifted_eq:
  forall (v1: environ -> val) (v2: val),
    `eq v1 `v2 = `(eq v2) v1.
Proof.
intros. unfold_lift. extensionality rho. apply prop_ext; split; intro; auto.
Qed.
Hint Rewrite flip_lifted_eq : norm.

Lemma isptr_is_pointer_or_null: 
  forall v, isptr v -> is_pointer_or_null v.
Proof. intros. destruct v; inv H; simpl; auto.
Qed.
Hint Resolve isptr_is_pointer_or_null.

Lemma eval_var_isptr:
  forall Delta t i rho, 
            tc_environ Delta rho ->
            ((var_types Delta) ! i = Some t \/ 
             (var_types Delta)!i = None /\
            (glob_types Delta) ! i = Some t) ->
            isptr (eval_var i t rho).
Proof.
 intros.
  unfold isptr, eval_var; simpl.
 hnf in H. unfold typecheck_environ in H.
 repeat rewrite andb_true_iff in H.
  destruct H as [_ [? [? ?]]].
  hnf in H,H1.
  destruct H0.
  specialize (H i t). destruct H as [H _]. specialize (H H0).
  destruct H; rewrite H.
  rewrite eqb_type_refl.
  simpl. auto.
  destruct H0. 
  destruct (H1 _ _ H3) as [b [? ?]].
  rewrite H4. simpl.
 destruct (H2 _ _ H3).
 unfold Map.get; rewrite H6.
 auto.
 destruct H6. congruence.
Qed.


Definition repable_signed (z: Z) :=
  Int.min_signed <= z <= Int.max_signed.

Definition repable_signed_dec (z: Z) : {repable_signed z}+{~repable_signed z}.
Proof.
 intros. unfold repable_signed.
 destruct (zlt z Int.min_signed).
 right; intros [? _]; unfold Int.min_signed; omega. 
 destruct (zlt Int.max_signed z).
 right; intros [_ ?]; unfold Int.max_signed; omega.
 left; split; omega. 
Defined.

Definition add_ptr_int'  {cs: compspecs}  (ty: type) (v: val) (i: Z) : val :=
  if repable_signed_dec (sizeof cenv_cs ty * i)
   then match v with
      | Vptr b ofs => 
           Vptr b (Int.add ofs (Int.repr (sizeof cenv_cs ty * i)))
      | _ => Vundef
      end
  else Vundef.

Definition add_ptr_int  {cs: compspecs}  (ty: type) (v: val) (i: Z) : val :=
           eval_binop Oadd (tptr ty) tint v (Vint (Int.repr i)).

Lemma repable_signed_mult2:
  forall i j, i<>0 -> (j <= Int.max_signed \/ i <> -1) ->
   repable_signed (i*j) -> repable_signed j.
Proof.
intros until 1. intro HACK. intros.
assert (MAX: 0 < Int.max_signed) by (compute; auto).
assert (MIN: Int.min_signed < 0) by (compute; auto).
hnf in H0|-*.
assert (0 < i \/ i < 0) by omega; clear H.
destruct H1.
replace i with ((i-1)+1) in H0 by omega.
rewrite Z.mul_add_distr_r in H0.
rewrite Z.mul_1_l in H0.
assert (j < 0 \/ 0 <= j) by omega. destruct H1.
assert ((i-1)*j <= 0) by (apply Z.mul_nonneg_nonpos; omega).
omega.
assert (0 <= (i-1)*j) by (apply Z.mul_nonneg_nonneg; omega).
omega.
replace i with ((i+1)-1) in H0 by omega.
rewrite Z.mul_sub_distr_r in H0.
rewrite Z.mul_1_l in H0.
assert (MINMAX: Int.min_signed = -Int.max_signed - 1) by reflexivity.
assert (j < 0 \/ 0 <= j) by omega. destruct H1.
assert (0 <= (i+1)*j) by (apply Z.mul_nonpos_nonpos; omega).
rewrite MINMAX in H0|-*.
omega.
assert ((i+1)*j <= 0) by (apply Z.mul_nonpos_nonneg; omega).
rewrite MINMAX in H0|-*.
split; try omega.
clear MIN MINMAX.
destruct H0 as [? _].
assert (- Int.max_signed <= 1 + (i+1)*j - j) by omega; clear H0.
assert (-1 - (i + 1) * j + j <= Int.max_signed) by omega; clear H3.
destruct HACK; auto.
assert (i < -1) by omega.
destruct (zlt 0 j); try omega.
assert ((i+1)*j < 0).
rewrite Z.mul_add_distr_r.
replace i with ((i+1)-1) by omega.
rewrite Z.mul_sub_distr_r.
assert ((i+1)*j<0); [ | omega].
apply Z.mul_neg_pos; auto. omega.
omega.
Qed.

Lemma repable_signed_mult1:
  forall i j, j<>0 ->  (i <= Int.max_signed \/ j <> -1) ->
              repable_signed (i*j) -> repable_signed i.
Proof.
intros.
 rewrite Zmult_comm in H1.
 apply repable_signed_mult2 in H0; auto.
Qed.

Lemma add_ptr_int_eq:
  forall  {cs: compspecs}  ty v i, 
       repable_signed (sizeof cenv_cs ty * i) ->
       add_ptr_int' ty v i = add_ptr_int ty v i.
Proof.
 intros.
 unfold add_ptr_int, add_ptr_int'.
 rewrite if_true by auto.
 destruct v; simpl; auto.
 rewrite mul_repr; auto.
Qed.

Lemma add_ptr_int_offset:
  forall  {cs: compspecs}  t v n, 
  repable_signed (sizeof cenv_cs t) ->
  repable_signed n ->
  add_ptr_int t v n = offset_val (Int.repr (sizeof cenv_cs t * n)) v.
Proof.
 unfold add_ptr_int; intros.
 unfold eval_binop, force_val2; destruct v; simpl; auto.
 rewrite Int.mul_signed.
 rewrite Int.signed_repr by auto.
  rewrite Int.signed_repr by auto.
 auto.
Qed.

Lemma add_ptr_int'_offset:
  forall  {cs: compspecs}  t v n, 
  repable_signed (sizeof cenv_cs t * n) ->
  add_ptr_int' t v n = offset_val (Int.repr (sizeof cenv_cs t * n)) v.
Proof.
 intros.
 unfold add_ptr_int'. 
 rewrite if_true by auto. destruct v; simpl; auto.
Qed.

Lemma typed_false_cmp:
  forall op i j , 
   typed_false tint (force_val (sem_cmp op tint tint true2 (Vint i) (Vint j))) ->
   Int.cmp (negate_comparison op) i j = true.
Proof.
intros.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
rewrite Int.negate_cmp.
destruct (Int.cmp op i j); auto. inv H.
Qed.

Lemma typed_true_cmp:
  forall op i j, 
   typed_true tint (force_val (sem_cmp op tint tint true2 (Vint i) (Vint j))) ->
   Int.cmp op i j = true.
Proof.
intros.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
destruct (Int.cmp op i j); auto. inv H.
Qed.

Definition Zcmp (op: comparison) : Z -> Z -> Prop :=
 match op with 
 | Ceq => eq
 | Cne => (fun i j => i<>j)
 | Clt => Zlt
 | Cle => Zle
 | Cgt => Zgt 
 | Cge => Zge
 end.

Lemma int_cmp_repr:
 forall op i j, repable_signed i -> repable_signed j ->
   Int.cmp op (Int.repr i) (Int.repr j) = true ->
   Zcmp op i j.
Proof.
intros.
unfold Int.cmp, Int.eq, Int.lt in H1.
replace (if zeq (Int.unsigned (Int.repr i)) (Int.unsigned (Int.repr j))
             then true else false)
 with (if zeq i j then true else false) in H1.
Focus 2.
destruct (zeq i j); destruct (zeq (Int.unsigned (Int.repr i)) (Int.unsigned (Int.repr j))); 
 auto.
subst. contradiction n; auto.
clear - H H0 e n.
apply Int.signed_repr in H. rewrite Int.signed_repr_eq in H.
apply Int.signed_repr in H0; rewrite Int.signed_repr_eq in H0.
contradiction n; clear n.
repeat rewrite Int.unsigned_repr_eq in e.
 match type of H with
           | context [if ?a then _ else _] => destruct a
           end;
 match type of H0 with
           | context [if ?a then _ else _] => destruct a
           end; omega.
unfold Zcmp.
rewrite (Int.signed_repr _ H) in H1; rewrite (Int.signed_repr _ H0) in H1.
repeat match type of H1 with
           | context [if ?a then _ else _] => destruct a
           end; try omegaContradiction;
 destruct op; auto; simpl in *; try discriminate; omega.
Qed.


Lemma typed_false_cmp_repr:
  forall op i j, 
   repable_signed i -> repable_signed j -> 
   typed_false tint (force_val (sem_cmp op tint tint true2
                              (Vint (Int.repr i)) 
                              (Vint (Int.repr j)) )) ->
   Zcmp (negate_comparison op) i j.
Proof.
 intros.
 apply typed_false_cmp in H1.
 apply int_cmp_repr; auto.
Qed.

Lemma typed_true_cmp_repr:
  forall op i j, 
   repable_signed i -> repable_signed j -> 
   typed_true tint (force_val (sem_cmp op tint tint true2
                              (Vint (Int.repr i)) 
                              (Vint (Int.repr j)) )) ->
   Zcmp op i j.
Proof.
 intros.
 apply typed_true_cmp in H1.
 apply int_cmp_repr; auto.
Qed.

Ltac intcompare H :=
 (apply typed_false_cmp_repr in H || apply typed_true_cmp_repr in H);
   [ simpl in H | auto; unfold repable_signed, Int.min_signed, Int.max_signed in *; omega .. ].


Lemma derives_refl' {A}{NA: NatDed A}: forall P Q: A, P=Q -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

Lemma derives_refl'' {A}{NA: NatDed A}: forall P Q: A, Q=P -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

Lemma isptr_deref_noload:
 forall t p, access_mode t = By_reference -> isptr (deref_noload t p) = isptr p.
Proof.
intros.
unfold deref_noload. rewrite H. reflexivity.
Qed.
Hint Rewrite isptr_deref_noload using reflexivity : norm.

Lemma isptr_offset_val_zero:
  forall v, isptr v -> offset_val Int.zero v = v.
Proof. intros. destruct v; inv H; subst; simpl.  rewrite Int.add_zero; reflexivity.
Qed.

Hint Rewrite isptr_offset_val_zero using solve [auto] : norm.

Lemma isptr_offset_val:
 forall i p, isptr (offset_val i p) = isptr p.
Proof.
intros.
unfold isptr.
destruct p; simpl; auto.
Qed.
Hint Rewrite isptr_offset_val : norm.

Lemma isptr_force_ptr: forall v, isptr v -> force_ptr v = v.
Proof. intros. destruct v; inv H; auto. Qed.
Hint Rewrite isptr_force_ptr using solve [auto] : norm.

Lemma isptr_force_ptr' : forall p, isptr (force_ptr p) =  isptr p.
Proof.
intros. destruct p; reflexivity.
Qed.
Hint Rewrite isptr_force_ptr' : norm.

Ltac no_evars P := (has_evar P; fail 1) || idtac.


Ltac putable x :=
 match x with 
 | O => idtac
 | S ?x => putable x
 | Z.lt ?x ?y => putable x; putable y
 | Z.le ?x ?y => putable x; putable y
 | Z.gt ?x ?y => putable x; putable y
 | eq?x ?y => putable x; putable y
 | ?x <> ?y => putable x; putable y
 | Zpos ?x => putable x
 | Zneg ?x => putable x
 | Z0 => idtac
 | xH => idtac
 | xI ?x => putable x
 | xO ?x => putable x
 | Z.add ?x ?y => putable x; putable y
 | Z.sub ?x ?y => putable x; putable y
 | Z.mul ?x ?y => putable x; putable y
 | Z.div ?x ?y => putable x; putable y
 | Zmod ?x ?y => putable x; putable y
 | Z.max ?x ?y => putable x; putable y
 | Z.opp ?x => putable x
 | Int.eq ?x ?y => putable x; putable y
 | Int.lt ?x ?y => putable x; putable y
 | Int.ltu ?x ?y => putable x; putable y
 | Int.add ?x ?y => putable x; putable y
 | Int.sub ?x ?y => putable x; putable y
 | Int.mul ?x ?y => putable x; putable y
 | Int.neg ?x => putable x
 | Ceq => idtac
 | Cne => idtac
 | Clt => idtac
 | Cle => idtac
 | Cgt => idtac
 | Cge => idtac
 | Int.cmp ?op ?x ?y => putable op; putable x; putable y
 | Int.cmpu ?op ?x ?y => putable op; putable x; putable y
 | Int.repr ?x => putable x
 | Int.signed ?x => putable x
 | Int.unsigned ?x => putable x
 | two_power_nat ?x => putable x
 | Int.max_unsigned => idtac
 | Int.max_signed => idtac
 | Int.modulus => idtac
 | ?x /\ ?y => putable x; putable y
 | Int.zwordsize => idtac
end.

Ltac computable := match goal with |- ?x =>
 no_evars x;
 putable x;
 compute; clear; repeat split; auto; congruence
end.

Lemma sign_ext_range2:
   forall lo n i hi,
      0 < n < Int.zwordsize ->
      lo = - two_p (n-1) ->
      hi = two_p (n-1) - 1 ->
      lo <= Int.signed (Int.sign_ext n i) <= hi.
Proof.
intros.
subst. apply expr_lemmas3.sign_ext_range'; auto.
Qed.

Lemma zero_ext_range2:
  forall n i lo hi,
      0 <= n < Int.zwordsize ->
      lo = 0 ->
      hi = two_p n - 1 ->
      lo <= Int.unsigned (Int.zero_ext n i) <= hi.
Proof.
intros; subst; apply expr_lemmas3.zero_ext_range'; auto.
Qed.

Hint Extern 3 (_ <= Int.signed (Int.sign_ext _ _) <= _) =>
    (apply sign_ext_range2; [computable | reflexivity | reflexivity]).

Hint Extern 3 (_ <= Int.unsigned (Int.zero_ext _ _) <= _) =>
    (apply zero_ext_range2; [computable | reflexivity | reflexivity]).

Hint Rewrite sign_ext_inrange using assumption : norm.
Hint Rewrite zero_ext_inrange using assumption : norm.

Lemma force_signed_int_e:
  forall i, force_signed_int (Vint i) = Int.signed i.
Proof. reflexivity. Qed.
Hint Rewrite force_signed_int_e : norm.

