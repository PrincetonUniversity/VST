From compcert Require Export Clightdefs.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Import VST.floyd.val_lemmas.
Local Open Scope logic.
Import LiftNotation.
Import compcert.lib.Maps.

Ltac _destruct_var_types i Heq_vt Heq_ve t b ::=
  let HH := fresh "H" in
  match goal with
  | H: typecheck_var_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_var_types___instead _ _ H i as HH
  | H: typecheck_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_var_types___instead _ _ (proj1 (proj2 H)) i as HH
  | H: tc_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_var_types___instead _ _ (proj1 (proj2 H)) i as HH
  end;
  match type of HH with
  | match ?o with _ => _ end =>
      match goal with
      | H: o = Some _ |- _ =>
          rewrite H in HH
      | H: Some _ = o |- _ =>
          rewrite <- H in HH
      | H: o = None |- _ =>
          rewrite H in HH
      | H: None = o |- _ =>
          rewrite <- H in HH
      | _ =>
          let HH' := fresh "H" in
          pose proof eq_refl o as HH';
          destruct o as [t |] in HH, HH' at 2;
          pose proof HH' as Heq_vt; clear HH'
      end
  end;
  match type of HH with
  | ex _ =>
      pose proof HH as [b Heq_ve]
  | _ =>
      pose proof HH as Heq_ve
  end;
  clear HH.

Ltac _destruct_glob_types i Heq_gt Heq_ge t b ::=
  let HH := fresh "H" in
  match goal with
  | H: typecheck_glob_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_glob_types___instead _ _ H i as HH
  | H: typecheck_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_glob_types___instead _ _ (proj2 (proj2 H)) i as HH
  | H: tc_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_glob_types___instead _ _ (proj2 (proj2 H)) i as HH
  end;
  match type of HH with
  | match ?o with _ => _ end =>
      match goal with
      | H: o = Some _ |- _ =>
          rewrite H in HH
      | H: Some _ = o |- _ =>
          rewrite <- H in HH
      | H: o = None |- _ =>
          rewrite H in HH
      | H: None = o |- _ =>
          rewrite <- H in HH
      | _ =>
          let HH' := fresh "H" in
          pose proof eq_refl o as HH';
          destruct o as [t |] in HH, HH' at 2;
          pose proof HH' as Heq_gt; clear HH'
      end
  end;
  match type of HH with
  | ex _ =>
      pose proof HH as [b Heq_ge]
  | _ =>
      idtac
  end;
  clear HH.

(* no "semax" in this file, just assertions. *)
Global Transparent Int.repr.
Global Transparent Int64.repr.
Global Transparent Ptrofs.repr.

Definition loop1x_ret_assert (Inv : environ -> mpred) (R : ret_assert) :=
  {| RA_normal := Inv; RA_break := FF; RA_continue := Inv; RA_return := R.(RA_return) |}.

Lemma loop1x_ret_assert_EK_normal:
 forall Inv R, RA_normal (loop1x_ret_assert Inv R) = Inv.
Proof. reflexivity. Qed.
#[export] Hint Rewrite loop1x_ret_assert_EK_normal: ret_assert.


Definition loop1y_ret_assert (Inv : environ -> mpred) :=
  {| RA_normal := Inv; RA_break := FF; RA_continue := Inv; RA_return := FF |}.

Definition for_ret_assert (I: environ->mpred) (Post: ret_assert) :=
 match Post with 
  {| RA_normal := _; RA_break := _; RA_continue := _; RA_return := r |} =>
  {| RA_normal := I; RA_break := FF; RA_continue := I; RA_return := r |}
 end.

Ltac simpl_ret_assert := 
 cbn [RA_normal RA_break RA_continue RA_return 
      normal_ret_assert overridePost loop1_ret_assert
      loop2_ret_assert function_body_ret_assert frame_ret_assert
      switch_ret_assert loop1x_ret_assert loop1y_ret_assert
      for_ret_assert loop_nocontinue_ret_assert];
     try change (bind_ret None tvoid ?P) with P.

Lemma RA_normal_loop2_ret_assert: (* MOVE TO assert_lemmas *)
  forall Inv R, RA_normal (loop2_ret_assert Inv R) = Inv.
Proof. destruct R; reflexivity. Qed.
#[export] Hint Rewrite RA_normal_loop2_ret_assert : ret_assert.

Lemma liftTrue: forall rho, `True rho.
Proof. intro. unfold_lift; apply Logic.I. Qed.
#[export] Hint Resolve liftTrue : core.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
reflexivity.
Qed.

Lemma frame_normal:
  forall P F,
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (P * F).
Proof.
intros.
unfold normal_ret_assert; simpl.
f_equal; try solve [extensionality rho; normalize].
extensionality vl rho; normalize.
Qed.

Lemma frame_for1:
  forall Q R F,
   frame_ret_assert (loop1_ret_assert Q R) F =
   loop1_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; normalize.
Qed.

Lemma frame_loop1:
  forall Q R F,
   frame_ret_assert (loop2_ret_assert Q R) F =
   loop2_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl.
f_equal; try solve [extensionality rho; normalize].
Qed.


#[export] Hint Rewrite frame_normal frame_for1 frame_loop1
                 overridePost_normal: ret_assert.
#[export] Hint Resolve TT_right : core.

Lemma overridePost_overridePost:
 forall P Q R, overridePost P (overridePost Q R) = overridePost P R.
Proof.
intros.
destruct R; reflexivity.
Qed.
#[export] Hint Rewrite overridePost_overridePost : ret_assert.

Lemma overridePost_normal':
  forall P R, RA_normal (overridePost P R) = P.
Proof.
 intros. destruct R; reflexivity. 
Qed.
#[export] Hint Rewrite overridePost_normal' : ret_assert.

Lemma liftx_id:
    forall {T} e, @liftx (Tarrow T (LiftEnviron T)) (fun v => v) e = e.
Proof.
 intros. extensionality rho; simpl; auto.
Qed.
#[export] Hint Rewrite @liftx_id : norm2.

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

#[export] Hint Rewrite @liftx3_liftx2 @liftx2_liftx1 @liftx1_liftx0 : norm2.

Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.
#[export] Hint Rewrite @lift1_lift0 : norm2.

Lemma const_liftx0:
  forall B (P: B), (fun _ : environ => P) = `P.
Proof. reflexivity. Qed.
#[export] Hint Rewrite const_liftx0 : norm2.

Lemma lift_identity:
  forall A f, `(fun v: A => v) f = f.
Proof. intros. reflexivity. Qed.
#[export] Hint Rewrite lift_identity : norm2.

Lemma tc_eval_gvar_zero:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some t ->
            exists b, eval_var i t rho = Vptr b Ptrofs.zero.
Proof.
 intros. unfold eval_var; simpl.
 destruct_var_types i.
 destruct_glob_types i.
 rewrite Heqo0, Heqo1.
 eauto.
Qed.

Lemma tc_eval_gvar_i:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some t ->
             tc_val (Tpointer t noattr) (eval_var i t rho).
Proof.
 intros.
 red.
 destruct (tc_eval_gvar_zero _ _ _ _ H H0 H1) as [b ?].
 rewrite H2.  destruct (eqb_type _ _); apply Logic.I.
Qed.

Lemma local_lift2_and: forall P Q, local (`and P Q) =
        local P && local Q.
Proof. intros; extensionality rho. unfold local; super_unfold_lift.
simpl.
 apply pred_ext; normalize. destruct H; normalize.
Qed.
#[export] Hint Rewrite local_lift2_and : norm2.

Lemma subst_TT {A}{NA: NatDed A}: forall i v, subst i v TT = TT.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_FF {A}{NA: NatDed A}: forall i v, subst i v FF = FF.
Proof.
intros. extensionality rho; reflexivity.
Qed.
#[export] Hint Rewrite @subst_TT @subst_FF: subst.
#[export] Hint Rewrite (@subst_TT mpred Nveric) (@subst_FF mpred Nveric): subst.

Lemma subst_sepcon: forall i v (P Q: environ->mpred),
  subst i v (P * Q) = (subst i v P * subst i v Q).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_sepcon : subst.

Lemma subst_wand: forall i v (P Q: environ->mpred),
  subst i v (P -* Q) = (subst i v P -* subst i v Q).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_wand : subst.

Lemma subst_exp:
  forall (A B: Type) (NA : NatDed A) (a : ident) (v : environ -> val) (P: B -> environ -> A),
    subst a v (EX b: B, P b) = EX b: B, subst a v (P b).
Proof. intros; reflexivity. Qed.

Lemma env_set_env_set: forall id v1 v2 rho, env_set (env_set rho id v1) id v2 = env_set rho id v2.
Proof.
  intros.
  unfold env_set.
  f_equal.
  apply Map.ext. intro j.
  destruct (eq_dec id j). subst. repeat rewrite Map.gss. f_equal.
  simpl.
  repeat rewrite Map.gso by auto. auto.
Qed.

Lemma env_set_eval_id: forall id rho Delta t,
  tc_environ Delta rho ->
  (temp_types Delta) ! id = Some t ->
  env_set rho id (eval_id id rho) = rho.
Proof.
  intros.
  destruct H as [? _].
  specialize (H _ _ H0).
  destruct H as [? [? ?]].
  unfold eval_id, env_set, force_val.
  destruct rho; simpl in *.
  f_equal.
  rewrite H.
  apply Map.ext.
  intros.
  destruct (Pos.eq_dec id x0).
  - subst.
    rewrite Map.gss; auto.
  - rewrite Map.gso; auto.
Qed.

Lemma resubst: forall {A} i (v v1: val) (e: environ -> A), subst i (`v1) (subst i `(v) e) = subst i `(v) e.
Proof.
 intros. extensionality rho. unfold subst.
 f_equal.
 unfold env_set.
 f_equal.
 apply Map.ext. intro j.
 destruct (eq_dec i j). subst. repeat rewrite Map.gss. f_equal.
 simpl.
 repeat rewrite Map.gso by auto. auto.
Qed.

#[export] Hint Rewrite @resubst : subst.

Lemma resubst_full: forall {A} i (v: environ -> val) v1 (e: environ -> A), subst i v1 (subst i v e) = subst i (subst i v1 v) e.
Proof.
  intros.
  extensionality rho. unfold subst.
 f_equal.
 unfold env_set.
 f_equal.
 apply Map.ext. intro j.
 destruct (eq_dec i j). subst. repeat rewrite Map.gss. f_equal.
 simpl.
 repeat rewrite Map.gso by auto. auto.
Qed.

Lemma subst_ewand: forall i v (P Q: environ->mpred),
  subst i v (ewand P Q) = ewand (subst i v P) (subst i v Q).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_ewand : subst.

Lemma subst_andp {A}{NA: NatDed A}:
  forall id v (P Q: environ-> A), subst id v (P && Q) = subst id v P && subst id v Q.
Proof.
intros.
extensionality rho; unfold subst; simpl.
auto.
Qed.

Lemma subst_prop {A}{NA: NatDed A}: forall i v P,
    subst i v (prop P) = prop P.
Proof.
intros; reflexivity.
Qed.
#[export] Hint Rewrite @subst_andp subst_prop : subst.

Lemma eval_expr_Econst_int: forall {cs: compspecs}  i t, eval_expr (Econst_int i t) = `(Vint i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @eval_expr_Econst_int : eval.

Lemma subst_eval_var:
  forall id v id' t, subst id v (eval_var id' t) = eval_var id' t.
Proof.
intros. unfold subst, eval_var. extensionality rho.
simpl. auto.
Qed.
#[export] Hint Rewrite subst_eval_var : subst.

Lemma subst_local: forall id v P,
  subst id v (local P) = local (subst id v P).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_local : subst.

Lemma eval_lvalue_Ederef:
  forall {cs: compspecs}  e t, eval_lvalue (Ederef e t) = eval_expr e.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @eval_lvalue_Ederef : eval.

Lemma local_lift0_True:     local (`True) = TT.
Proof. reflexivity. Qed.
#[export] Hint Rewrite local_lift0_True : norm2.

Lemma overridePost_EK_return:
  forall Q P, RA_return (overridePost Q P) = RA_return P.
Proof.
 destruct P; reflexivity.
Qed.
#[export] Hint Rewrite overridePost_EK_return : ret_assert.

Lemma frame_ret_assert_emp:
  forall P, frame_ret_assert P emp = P.
Proof. intros.
 destruct P; simpl; f_equal; extensionality; try extensionality; normalize.
Qed.

Lemma frame_ret_assert_EK_return:
 forall P Q vl, RA_return (frame_ret_assert P Q) vl =  RA_return P vl * Q.
Proof.
 destruct P; simpl; reflexivity.
Qed.
#[export] Hint Rewrite frame_ret_assert_EK_return : ret_assert.

Lemma function_body_ret_assert_EK_return:
  forall t P vl, RA_return (function_body_ret_assert t P) vl = bind_ret vl t P.
Proof. reflexivity. Qed.
#[export] Hint Rewrite function_body_ret_assert_EK_return : ret_assert.

Lemma bind_ret1_unfold:
  forall v t Q, bind_ret (Some v) t Q = !!tc_val t v && `Q (make_args (ret_temp :: nil)(v::nil)).
Proof. reflexivity. Qed.
#[export] Hint Rewrite bind_ret1_unfold : norm2.

Lemma bind_ret1_unfold':
  forall v t Q rho,
  bind_ret (Some v) t Q rho = !!(tc_val t v) && Q (make_args (ret_temp::nil)(v::nil) rho).
Proof.
 intros. reflexivity.
Qed.
#[export] Hint Rewrite bind_ret1_unfold' : norm2.  (* put this in AFTER the unprimed version, for higher priority *)

Lemma normal_ret_assert_elim:
 forall P, RA_normal (normal_ret_assert P) = P.
Proof.
reflexivity.
Qed.

Lemma overridePost_EK_break:
 forall P Q, RA_break (overridePost P Q) = RA_break Q.
Proof. destruct Q; reflexivity.
Qed.

Lemma loop1_ret_assert_EK_break:
 forall P Q, RA_break (loop1_ret_assert P Q) = RA_normal Q.
Proof. destruct Q;   reflexivity.
Qed.

#[export] Hint Rewrite overridePost_EK_break loop1_ret_assert_EK_break
  normal_ret_assert_elim : ret_assert.

Lemma loop1_ret_assert_normal:
  forall P Q, RA_normal (loop1_ret_assert P Q) = P.
Proof. 
  destruct Q; reflexivity.
Qed.
#[export] Hint Rewrite loop1_ret_assert_normal: ret_assert.

Lemma unfold_make_args': forall fsig args rho,
    make_args' fsig args rho = make_args (map (@fst _ _) (fst fsig)) (args rho) rho.
Proof. reflexivity. Qed.
#[export] Hint Rewrite unfold_make_args' : norm2.
Lemma unfold_make_args_cons: forall i il v vl rho,
   make_args (i::il) (v::vl) rho = env_set (make_args il vl rho) i v.
Proof. reflexivity. Qed.
Lemma unfold_make_args_nil: make_args nil nil = globals_only.
Proof. reflexivity. Qed.
#[export] Hint Rewrite unfold_make_args_cons unfold_make_args_nil : norm2.

Lemma clear_rhox:  (* replaces clear_make_args' *)
 forall (P: mpred) (f: environ -> environ),
    @liftx (Tarrow environ (LiftEnviron mpred))
                    (@liftx (LiftEnviron mpred) P) f
       = `P.
Proof. intros. reflexivity. Qed.
#[export] Hint Rewrite clear_rhox: norm2.

Lemma eval_make_args':
  forall (Q: val -> Prop) i fsig args,
  @liftx (Tarrow environ (LiftEnviron Prop))
      (@liftx (Tarrow val (LiftEnviron Prop)) Q (eval_id i))
   (make_args' fsig args) =
  `Q (`(eval_id i) (make_args' fsig args)).
Proof. reflexivity. Qed.
#[export] Hint Rewrite eval_make_args' : norm2.

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

#[export] Hint Rewrite @eval_make_args_same : norm2.
#[export] Hint Rewrite @eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

Infix "oo" := Basics.compose (at level 54, right associativity).
Arguments Basics.compose {A B C} g f x / .

Lemma compose_backtick:
  forall A B C (F: B -> C) (G: A -> B) (J: environ -> A),
   `F (`G  J) = `(Basics.compose F G) J.
Proof. reflexivity. Qed.
#[export] Hint Rewrite compose_backtick : norm.

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

#[export] Hint Rewrite @compose_eval_make_args_same : norm.
#[export] Hint Rewrite @compose_eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

Lemma substopt_unfold {A}: forall id v, @substopt A (Some id) v = @subst A id v.
Proof. reflexivity. Qed.
Lemma substopt_unfold_nil {A}: forall v (P:  environ -> A), substopt None v P = P.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @substopt_unfold @substopt_unfold_nil : subst.

Lemma get_result_unfold: forall id, get_result (Some id) = get_result1 id.
Proof. reflexivity. Qed.
Lemma get_result_None: get_result None = globals_only.
Proof. reflexivity. Qed.
#[export] Hint Rewrite get_result_unfold get_result_None : norm.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (var_types Delta) ! i = None /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Proof.
intros.
destruct H as [H [H8 H0]].
unfold eval_var, globals_only.
simpl.
destruct_var_types i.
destruct_glob_types i.
rewrite Heqo0, Heqo1.
auto.
Qed.
#[export] Hint Rewrite elim_globals_only using (split3; [eassumption | reflexivity.. ]) : norm.

Lemma elim_globals_only':
 forall a: mpred,
 (@liftx (Tarrow environ (LiftEnviron mpred)) (`a) globals_only) = `a.
Proof. reflexivity. Qed.
#[export] Hint Rewrite elim_globals_only' : norm.

Lemma globvar_eval_var:
  forall Delta rho id t,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  t ->
     exists b,  eval_var id t rho = Vptr b Ptrofs.zero
            /\ Map.get (ge_of rho) id = Some b.
Proof.
intros.
unfold eval_var; simpl.
destruct_var_types id.
destruct_glob_types id.
rewrite Heqo0, Heqo1.
eauto.
Qed.

Lemma globvars2pred_unfold: forall gv vl,
    globvars2pred gv vl = fold_right sepcon emp (map (globvar2pred gv) vl).
Proof. easy. Qed.
#[export] Hint Rewrite globvars2pred_unfold : norm.
#[export] Hint Rewrite @exp_trivial : norm.

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
 destruct H0 as [? | [? ?]].
 + destruct_var_types i.
   rewrite Heqo0.
   rewrite eqb_type_refl.
   auto.
 + destruct_var_types i.
   destruct_glob_types i.
   rewrite Heqo0, Heqo1.
   auto.
Qed.

Lemma ENTAIL_trans:
  forall Delta P Q R,
  (local (tc_environ Delta) && P |-- Q) ->
  (local (tc_environ Delta) && Q |-- R) ->
  local (tc_environ Delta) && P |-- R.
Proof.
intros.
eapply derives_trans.
apply andp_right; [ | apply H].
apply andp_left1; apply derives_refl.
auto.
Qed.

Lemma ENTAIL_refl:
  forall Delta P,
  local (tc_environ Delta) && P |-- P.
Proof. intros. apply andp_left2, derives_refl. Qed.

Lemma corable_andp_bupd: forall (P Q: environ -> mpred),
  corable P ->
  (P && |==> Q) |-- |==> P && Q.
Proof.
  intros.
  rewrite !(andp_comm P).
  apply bupd_andp2_corable; auto.
Qed.

Lemma corable_andp_fupd: forall E1 E2 (P Q: environ -> mpred),
  corable P ->
  (P && |={E1,E2}=> Q) |-- |={E1,E2}=> P && Q.
Proof.
  intros.
  rewrite !(andp_comm P).
  apply fupd_andp2_corable; auto.
Qed.

Lemma local_andp_fupd: forall E1 E2 P Q,
  (local P && |={E1,E2}=> Q) |-- |={E1,E2}=> (local P && Q).
Proof.
  intros.
  rewrite !(andp_comm (local P)).
  apply fupd_andp2_corable.
  intro; apply corable_prop.
Qed.

Lemma fupd_andp_local: forall E1 E2 P Q,
  (|={E1,E2}=> P) && local Q |-- |={E1,E2}=> (P && local Q).
Proof.
  intros.
  apply fupd_andp2_corable.
  intro; apply corable_prop.
Qed.

Lemma derives_fupd_trans: forall TC E1 E2 E3 P Q R,
  (local TC && P |-- (|={E1,E2}=> Q)) ->
  (local TC && Q |-- (|={E2,E3}=> R)) ->
  local TC && P |-- (|={E1,E3}=> R).
Proof.
  intros.
  rewrite (add_andp _ _ H).
  rewrite (andp_comm _ P), andp_assoc; apply andp_left2.
  eapply derives_trans; [apply local_andp_fupd |].
  rewrite (add_andp _ _ H0).
  rewrite (andp_comm _ Q), andp_assoc; eapply derives_trans; [apply fupd_mono, andp_left2, derives_refl |].
  eapply derives_trans; [apply fupd_mono,local_andp_fupd |].
  eapply derives_trans; [apply fupd_trans|].
  apply fupd_mono; solve_andp.
Qed.

Lemma derives_fupd_refl: forall TC E P,
  local TC && P |-- |={E}=> P.
Proof. intros. apply andp_left2, fupd_intro. Qed.

Lemma derives_full_refl: forall Delta E P,
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |={E}=> P.
Proof. intros. refine (derives_trans _ _ _ _ (derives_fupd_refl (tc_environ Delta) _ P)). solve_andp. Qed.

Lemma derives_full_trans: forall Delta E P Q R,
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- (|={E}=> (Q))) ->
  (local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- (|={E}=> (R))) ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- (|={E}=> (R)).
Proof.
  intros.
  eapply derives_fupd_trans; [| exact H0].
  rewrite (add_andp _ _ H).
  apply derives_trans with ((|={E}=> Q) && allp_fun_id Delta); [solve_andp |].
  eapply derives_trans; [apply fupd_andp2_corable; intro; apply corable_allp_fun_id |].
  rewrite andp_comm; auto.
Qed.

Lemma derives_ENTAIL: forall TC P Q,
  (P |-- Q) ->
  local TC && P |-- Q.
Proof. intros. apply andp_left2, H. Qed.

Lemma ENTAIL_derives_fupd: forall TC E P Q,
  (local TC && P |-- Q) ->
  local TC && P |-- |={E}=> Q.
Proof. intros. apply (derives_trans _ _ _ H), fupd_intro. Qed.

Lemma derives_fupd_derives_full: forall Delta E P Q,
  (local (tc_environ Delta) && P |-- (|={E}=> Q)) ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- (|={E}=> Q).
Proof. intros. refine (derives_trans _ _ _ _ H). solve_andp. Qed.

Lemma andp_ENTAIL: forall TC P P' Q Q',
  (local TC && P |-- P') ->
  (local TC && Q |-- Q') ->
  local TC && (P && Q) |-- P' && Q'.
Proof.
  intros.
  eapply derives_trans; [| apply andp_derives; [exact H | exact H0]].
  solve_andp.
Qed.

Lemma orp_ENTAIL: forall TC P P' Q Q',
  (local TC && P |-- P') ->
  (local TC && Q |-- Q') ->
  local TC && (P || Q) |-- P' || Q'.
Proof.
  intros.
  rewrite andp_comm, distrib_orp_andp.
  apply orp_derives; rewrite andp_comm; auto.
Qed.

Lemma sepcon_ENTAIL: forall TC P P' Q Q',
  (local TC && P |-- P') ->
  (local TC && Q |-- Q') ->
  local TC && (P * Q) |-- P' * Q'.
Proof.
  intros.
  eapply derives_trans; [| apply sepcon_derives; [exact H | exact H0]].
  rewrite corable_andp_sepcon1, corable_sepcon_andp1 by (intro; apply corable_prop).
  solve_andp.
Qed.

Lemma wand_ENTAIL: forall TC P P' Q Q',
  (local TC && P' |-- P) ->
  (local TC && Q |-- Q') ->
  local TC && (P -* Q) |-- P' -* Q'.
Proof.
  intros.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [| apply H0].
  rewrite corable_andp_sepcon1 by (intro; apply corable_prop).
  apply andp_right; [apply andp_left1, derives_refl |].
  rewrite <- corable_sepcon_andp1 by (intro; apply corable_prop).
  rewrite sepcon_comm, wand_sepcon_adjoint.
  eapply derives_trans; [apply H |].
  rewrite <- wand_sepcon_adjoint.
  apply modus_ponens_wand.
Qed.

Lemma exp_ENTAIL: forall Delta B (P Q: B -> environ -> mpred),
  (forall x: B, local (tc_environ Delta) && P x |-- Q x) ->
  local (tc_environ Delta) && exp P |-- exp Q.
Proof.
  intros.
  rewrite exp_andp2.
  apply exp_derives; auto.
Qed.

Lemma allp_ENTAIL: forall Delta B (P Q: B -> environ -> mpred),
  (forall x: B, local (tc_environ Delta) && P x |-- Q x) ->
  local (tc_environ Delta) && allp P |-- allp Q.
Proof.
  intros.
  apply allp_right; intro y.
  rewrite andp_comm.
  apply imp_andp_adjoint.
  apply allp_left with y.
  apply imp_andp_adjoint.
  rewrite andp_comm.
  apply H.
Qed.

Lemma later_ENTAIL: forall Delta P Q,
  (local (tc_environ Delta) && P |-- Q) ->
  local (tc_environ Delta) && |> P |-- |> Q.
Proof.
  intros.
  apply later_left2, H.
Qed.

Lemma andp_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P') ->
  (local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- Q') ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P && Q)) |-- P' && Q'.
Proof.
  intros.
  eapply derives_trans; [| apply andp_derives; [exact H | exact H0]].
  solve_andp.
Qed.

Lemma orp_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P') ->
  (local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- Q') ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P || Q)) |-- P' || Q'.
Proof.
  intros.
  rewrite <- andp_assoc in *.
  rewrite andp_comm, distrib_orp_andp.
  apply orp_derives; rewrite andp_comm; auto.
Qed.

Lemma imp_ENTAILL: forall Delta P P' Q Q',
  local (tc_environ Delta) && (allp_fun_id Delta && P') |-- P ->
  local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- Q' ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P -->Q)) |-- P' --> Q'.
Proof.
  intros.
  rewrite <- andp_assoc in *.
  rewrite <- imp_andp_adjoint.
  eapply derives_trans; [| apply H0].
  apply andp_right; [apply andp_left1, andp_left1, derives_refl |].
  rewrite !andp_assoc, (andp_comm _ P'), <- !andp_assoc.
  apply imp_andp_adjoint.
  eapply derives_trans; [apply H |].
  apply imp_andp_adjoint.
  apply modus_ponens.
Qed.

Lemma sepcon_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P') ->
  (local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- Q') ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P * Q)) |-- P' * Q'.
Proof.
  intros.
  rewrite <- andp_assoc in *.
  eapply derives_trans; [| apply sepcon_derives; [exact H | exact H0]].
  rewrite corable_andp_sepcon1, corable_sepcon_andp1 by (intro; simpl; apply corable_andp; [apply corable_prop | apply corable_allp_fun_id]).
  solve_andp.
Qed.

Lemma wand_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) && (allp_fun_id Delta && P') |-- P) ->
  (local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- Q') ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P -* Q)) |-- P' -* Q'.
Proof.
  intros.
  rewrite <- andp_assoc in *.
  rewrite <- wand_sepcon_adjoint.
  eapply derives_trans; [| apply H0].
  rewrite corable_andp_sepcon1 by (intro; simpl; apply corable_andp; [apply corable_prop | apply corable_allp_fun_id]).
  apply andp_right; [apply andp_left1, derives_refl |].
  rewrite <- corable_sepcon_andp1 by (intro; simpl; apply corable_andp; [apply corable_prop | apply corable_allp_fun_id]).
  rewrite sepcon_comm, wand_sepcon_adjoint.
  eapply derives_trans; [apply H |].
  rewrite <- wand_sepcon_adjoint.
  apply modus_ponens_wand.
Qed.

Lemma exp_ENTAILL: forall Delta B (P Q: B -> environ -> mpred),
  (forall x: B, local (tc_environ Delta) && (allp_fun_id Delta && P x) |-- Q x) ->
  local (tc_environ Delta) && (allp_fun_id Delta && exp P) |-- exp Q.
Proof.
  intros.
  rewrite !exp_andp2.
  apply exp_derives; auto.
Qed.

Lemma allp_ENTAILL: forall Delta B (P Q: B -> environ -> mpred),
  (forall x: B, local (tc_environ Delta) && (allp_fun_id Delta && P x) |-- Q x) ->
  local (tc_environ Delta) && (allp_fun_id Delta && allp P) |-- allp Q.
Proof.
  intros.
  apply allp_right; intro y.
  rewrite <- andp_assoc, andp_comm.
  apply imp_andp_adjoint.
  apply allp_left with y.
  apply imp_andp_adjoint.
  rewrite andp_comm, andp_assoc.
  apply H.
Qed.

Lemma later_ENTAILL: forall Delta P Q,
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) && (allp_fun_id Delta && |> P) |-- |> Q.
Proof.
  intros.
  rewrite <- andp_assoc in *.
  apply later_left2, H.
Qed.

Lemma andp_subst_ENTAILL: forall Delta P P' Q Q' i v t,
  (temp_types Delta) ! i = Some t ->
  (local (tc_environ Delta) && (allp_fun_id Delta && P') |-- local (`(tc_val' t) v)) ->
  (local (tc_environ Delta) && (allp_fun_id Delta && P') |-- Q') ->
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P' && subst i v P)) |-- Q' && subst i v Q.
Proof.
  intros.
  apply (subst_derives i v) in H2.
  autorewrite with subst in H2.
  eapply derives_trans; [| apply andp_derives; eassumption].
  repeat apply andp_right; try solve_andp.
  rewrite <- !andp_assoc; apply andp_left1; rewrite andp_assoc.
  rewrite (add_andp _ _ H0).
  unfold local, lift1; unfold_lift.
  intro rho; simpl; normalize; clear H0 H1 H2.
  apply prop_right.
  unfold subst, env_set.
  destruct rho; simpl in *.
  destruct H3; split; auto.
  clear H1; simpl in *.
  hnf; intros.
  specialize (H0 _ _ H1).
  destruct H0 as [? [? ?]].
  destruct (Pos.eq_dec i id).
  + subst.
    rewrite Map.gss.
    exists (v (mkEnviron ge ve te)); split; auto.
    rewrite H in H1.
    inv H1.
    auto.
  + exists x.
    rewrite Map.gso by auto.
    auto.
Qed.

Lemma derives_fupd_fupd_left: forall TC E P Q,
  (local TC && P |-- (|={E}=> Q)) ->
  (local TC && |={E}=> P) |-- |={E}=> Q.
Proof.
  intros.
  eapply derives_trans; [apply local_andp_fupd |].
  eapply derives_trans; [apply fupd_mono, H |].
  apply fupd_trans.
Qed.

Lemma derives_full_fupd_left: forall Delta E P Q,
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- (|={E}=> Q)) ->
  local (tc_environ Delta) && (allp_fun_id Delta && |={E}=> P) |-- |={E}=> Q.
Proof.
  intros.
  rewrite <- andp_assoc in H |- *.
  eapply derives_trans; [apply corable_andp_fupd; intro; simpl; apply corable_andp; [apply corable_prop | apply corable_allp_fun_id] |].
  eapply derives_trans; [apply fupd_mono | apply fupd_trans]; auto.
Qed.

Ltac lifted_derives_L2R H :=
  eapply ENTAIL_trans; [apply H |].

Ltac ENTAIL_L2R H :=
  match type of H with
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
      eapply ENTAIL_trans; [apply H |]
  | _ =>
      eapply ENTAIL_trans; [apply derives_ENTAIL, H |]
  end.

Ltac derives_fupd_L2R H :=
  match type of H with
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
      eapply derives_fupd_trans; [apply H |]
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
      eapply derives_fupd_trans; [apply ENTAIL_derives_fupd, H |]
  | _ =>
      eapply derives_fupd_trans; [apply ENTAIL_derives_fupd, derives_ENTAIL, H |]
  end.

Ltac derives_full_L2R H :=
  match type of H with
  | @derives (environ -> mpred) _ (local (tc_environ ?Delta) && (allp_fun_id ?Delta && _)) (|={_,_}=> _) =>
      eapply derives_full_trans; [apply H |]
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
      eapply derives_full_trans; [apply derives_fupd_derives_full, H |]
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
      eapply derives_full_trans; [apply derives_fupd_derives_full, ENTAIL_derives_fupd, H |]
  | _ =>
      eapply derives_full_trans; [apply derives_fupd_derives_full, ENTAIL_derives_fupd, derives_ENTAIL, H |]
  end.

Tactic Notation "derives_rewrite" "->" constr(H) :=
  match goal with
  | |- @derives (environ -> mpred) _ (local (tc_environ ?Delta) && (allp_fun_id ?Delta && _)) (|={_,_}=> _) =>
         derives_full_L2R H
  | |- @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
         derives_fupd_L2R H
  | |- @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
         ENTAIL_L2R H
  | |- _ =>
         lifted_derives_L2R H
  end.

Ltac lifted_derives_R2L H :=
  eapply derives_trans; [| apply H].

Ltac ENTAIL_R2L H :=
  match type of H with
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
      eapply ENTAIL_trans; [| apply H]
  | _ =>
      eapply ENTAIL_trans; [| apply derives_ENTAIL, H]
  end.

Ltac derives_fupd_R2L H :=
  match type of H with
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
      eapply derives_fupd_trans; [| apply H]
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
      eapply derives_fupd_trans; [| apply ENTAIL_derives_fupd, H]
  | _ =>
      eapply derives_fupd_trans; [| apply ENTAIL_derives_fupd, derives_ENTAIL, H]
  end.

Ltac derives_full_R2L H :=
  match type of H with
  | @derives (environ -> mpred) _ (local (tc_environ ?Delta) && (allp_fun_id ?Delta && _)) (|={_,_}=> _) =>
      eapply derives_fupd_trans; [| apply H]
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
      eapply derives_fupd_trans; [| apply derives_fupd_derives_full, H]
  | @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
      eapply derives_fupd_trans; [| apply derives_fupd_derives_full, ENTAIL_derives_fupd, H]
  | _ =>
      eapply derives_fupd_trans; [| apply derives_fupd_derives_full, ENTAIL_derives_fupd, derives_ENTAIL, H]
  end.

Tactic Notation "derives_rewrite" "<-" constr(H) :=
  match goal with
  | |- @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
         derives_fupd_R2L H
  | |- @derives (environ -> mpred) _ (local (tc_environ _) && _) (|={_,_}=> _) =>
         derives_fupd_R2L H
  | |- @derives (environ -> mpred) _ (local (tc_environ _) && _) _ =>
         ENTAIL_R2L H
  | |- _ =>
         lifted_derives_R2L H
  end.

Ltac solve_derives_trans :=
  first [simple apply derives_full_refl | eapply derives_full_trans; [eassumption | solve_derives_trans]].

(*Lemma aux1_reduceR: forall P Q: environ -> mpred,
  (P |-- (|==> Q)) ->
  P |-- |==> |> FF || Q.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply bupd_mono.
  apply orp_right2; auto.
Qed.*)

Lemma aux2_reduceR: forall E (P Q: environ -> mpred),
  (P |-- Q) ->
  P |-- |={E}=> Q.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply fupd_intro.
Qed.

Ltac reduceR :=
(*  match goal with
  | |- _ |-- |==> |> FF || _ => apply aux1_reduceR
  | _ => idtac
  end;*)
  match goal with
  | |- _ |-- |={_}=> _ => apply aux2_reduceR
  | _ => idtac
  end.

Lemma aux_reduceL: forall P Q R S: environ -> mpred,
  (P && R |-- S) ->
  P && (Q && R) |-- S.
Proof.
  intros.
  eapply derives_trans; [| exact H].
  solve_andp.
Qed.

Ltac reduceLL :=
  match goal with
  | |- local (tc_environ ?Delta) && (allp_fun_id ?Delta && _) |-- _ => apply aux_reduceL
  | _ => idtac
  end.

Ltac reduceL :=
  match goal with
  | |- local (tc_environ ?Delta) && (allp_fun_id ?Delta && _) |-- _ => apply aux_reduceL
  | _ => idtac
  end;
  match goal with
  | |- local (tc_environ _) && _ |-- _ => apply derives_ENTAIL
  | _ => idtac
  end.

Ltac reduce2derives :=
  reduceL; reduceR.

Ltac reduce2ENTAIL :=
  reduceLL; reduceR.
