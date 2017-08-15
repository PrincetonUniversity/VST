Require Import floyd.base.
Require Import floyd.val_lemmas.
Local Open Scope logic.

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
Hint Resolve @TT_right.

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
  forall {cs: compspecs}  e t, eval_lvalue (Ederef e t) = eval_expr e.
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

(*Hint Rewrite frame_ret_assert_emp : ret_assert.*)

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
Proof. 
  intros.
 unfold loop1_ret_assert. normalize.
Qed.
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

Lemma elim_globals_only':
 forall a: mpred,
 (@liftx (Tarrow environ (LiftEnviron mpred)) (`a) globals_only) = `a.
Proof. reflexivity. Qed.
Hint Rewrite elim_globals_only' : norm.

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

Hint Rewrite @exp_trivial : norm.

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

