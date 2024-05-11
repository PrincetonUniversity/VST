From compcert Require Export Clightdefs.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Import VST.floyd.val_lemmas.
Import LiftNotation.

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

(* up? *)
Lemma pure_and : forall {M} P Q, bi_pure(PROP := ouPredI M) (P /\ Q) = (⌜P⌝ ∧ ⌜Q⌝).
Proof.
  intros.
  ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext; tauto.
Qed.

(* up? *)
Lemma monPred_eq : forall {I B} a1 a2 b1 b2, a1 = a2 -> @MonPred I B a1 b1 = MonPred a2 b2.
Proof.
  intros; subst; f_equal; apply proof_irr.
Qed.

Section monPred.

Context {A : biIndex} {M : uora}.
Implicit Types (P Q : monPred A (ouPredI M)).

Lemma assert_ext : forall P Q, (forall rho, monPred_at P rho = monPred_at Q rho) -> P = Q.
Proof.
  intros.
  destruct P, Q; apply monPred_eq.
  extensionality; auto.
Qed.

Lemma False_sep' : forall P, (P ∗ False) = False.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply False_sep.
Qed.

Lemma sep_False' : forall P, (False ∗ P) = False.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply sep_False.
Qed.

Lemma True_and' : forall P, (True ∧ P) = P.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply log_normalize.True_and.
Qed.

Lemma and_True' : forall P, (P ∧ True) = P.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply log_normalize.and_True.
Qed.

Lemma emp_sep' : forall P, (emp ∗ P) = P.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply emp_sep.
Qed.

Lemma sep_emp' : forall P, (P ∗ emp) = P.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply sep_emp.
Qed.

Lemma and_comm' : forall P Q, (P ∧ Q) = (Q ∧ P).
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply log_normalize.and_comm.
Qed.

Lemma and_assoc' : forall P Q R, (P ∧ Q ∧ R) = ((P ∧ Q) ∧ R).
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply log_normalize.and_assoc.
Qed.

Lemma sep_comm' : forall P Q, (P ∗ Q) = (Q ∗ P).
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply sep_comm.
Qed.

Lemma sep_assoc' : forall P Q R, (P ∗ Q ∗ R) = ((P ∗ Q) ∗ R).
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply sep_assoc.
Qed.

Lemma pure_and' : forall (P Q : Prop), bi_pure(PROP := monPredI A (ouPredI M)) (P /\ Q) = (⌜P⌝ ∧ ⌜Q⌝).
Proof.
intros.
  intros; apply assert_ext; intros; monPred.unseal; apply pure_and.
Qed.

Lemma and_exist_l' : forall {A} P (Q : A -> _), (P ∧ (∃ a : A, Q a)) = ∃ a, P ∧ Q a.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply and_exist_l.
Qed.

Lemma and_exist_r' : forall {A} P (Q : A -> _), ((∃ a : A, Q a) ∧ P) = ∃ a, Q a ∧ P.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply and_exist_r.
Qed.

Lemma sep_exist_l' : forall {A} P (Q : A -> _), (P ∗ (∃ a : A, Q a)) = ∃ a, P ∗ Q a.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply sep_exist_l.
Qed.

Lemma sep_exist_r' : forall {A} P (Q : A -> _), ((∃ a : A, Q a) ∗ P) = ∃ a, Q a ∗ P.
Proof.
  intros; apply assert_ext; intros; monPred.unseal; apply sep_exist_r.
Qed.

End monPred.

#[export] Hint Rewrite @False_sep' @sep_False' @True_and' @and_True' : norm.

#[export] Hint Rewrite @sep_emp' @emp_sep'
             @sep_exist_l' @sep_exist_r'
               @and_exist_l' @and_exist_r'
     using (solve [auto with typeclass_instances])
        : norm.

Section mpred.

Context `{!heapGS Σ}.

Local Notation assert := (@assert Σ).

Implicit Types (P Q : assert).

Definition loop1x_ret_assert (Inv : assert) (R : ret_assert) :=
  {| RA_normal := Inv; RA_break := False; RA_continue := Inv; RA_return := R.(RA_return) |}.

Lemma loop1x_ret_assert_EK_normal:
 forall Inv R, RA_normal (loop1x_ret_assert Inv R) = Inv.
Proof. reflexivity. Qed.

Definition loop1y_ret_assert (Inv : assert) :=
  {| RA_normal := Inv; RA_break := False; RA_continue := Inv; RA_return _ := False |}.

Definition for_ret_assert (I: assert) (Post: ret_assert) :=
 match Post with 
  {| RA_normal := _; RA_break := _; RA_continue := _; RA_return := r |} =>
  {| RA_normal := I; RA_break := False; RA_continue := I; RA_return := r |}
 end.

Lemma RA_normal_loop2_ret_assert:
  forall Inv R, RA_normal (loop2_ret_assert Inv R) = Inv.
Proof. destruct R; reflexivity. Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
reflexivity.
Qed.

Lemma frame_normal:
  forall P F,
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (P ∗ F).
Proof.
intros.
unfold normal_ret_assert; simpl.
f_equal; last extensionality; apply sep_False'.
Qed.

Lemma frame_for1:
  forall Q R F,
   frame_ret_assert (loop1_ret_assert Q R) F =
   loop1_ret_assert (Q ∗ F) (frame_ret_assert R F).
Proof.
intros.
destruct R; reflexivity.
Qed.

Lemma frame_loop1:
  forall Q R F,
   frame_ret_assert (loop2_ret_assert Q R) F =
   loop2_ret_assert (Q ∗ F) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; f_equal.
apply sep_False'.
Qed.

Lemma overridePost_overridePost:
 forall P Q R, overridePost P (overridePost Q R) = overridePost P R.
Proof.
intros.
destruct R; reflexivity.
Qed.

Lemma overridePost_normal':
  forall P R, RA_normal (overridePost P R) = P.
Proof.
 intros. destruct R; reflexivity. 
Qed.

Lemma liftx_id:
    forall {T} e, @liftx (Tarrow T (LiftEnviron T)) (fun v => v) e = e.
Proof.
 intros. extensionality rho; simpl; auto.
Qed.

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

Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma const_liftx0:
  forall B (P: B), (fun _ : environ => P) = `P.
Proof. reflexivity. Qed.

Lemma lift_identity:
  forall A f, `(fun v: A => v) f = f.
Proof. intros. reflexivity. Qed.

Lemma tc_eval_gvar_zero:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) !! i = None ->
            (glob_types Delta) !! i = Some t ->
            exists b, eval_var i t rho = Vptr b Ptrofs.zero.
Proof.
 intros. unfold eval_var; simpl.
 destruct_var_types i.
 destruct_glob_types i.
 rewrite Heqo0 ?Heqo1.
 eauto.
Qed.

Lemma tc_eval_gvar_i:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) !! i = None ->
            (glob_types Delta) !! i = Some t ->
             tc_val (Tpointer t noattr) (eval_var i t rho).
Proof.
 intros.
 red.
 destruct (tc_eval_gvar_zero _ _ _ _ H H0 H1) as [b ?].
 rewrite H2. destruct (eqb_type _ _); apply Coq.Init.Logic.I.
Qed.

Lemma local_lift2_and: forall (P Q : environ -> Prop), (local (`and P Q) : assert) =
        (local P ∧ local Q).
Proof.
  intros.
  apply assert_ext; intros; monPred.unseal; super_unfold_lift.
  rewrite pure_and //.
Qed.

Lemma subst_True : forall i v, assert_of (subst i v (True : assert)) = True.
Proof.
  intros.
  apply assert_ext; intros; rewrite /subst /=; monPred.unseal; done.
Qed.

Lemma subst_False : forall i v, assert_of (subst i v (False : assert)) = False.
Proof.
  intros.
  apply assert_ext; intros; rewrite /subst /=; monPred.unseal; done.
Qed.

Lemma subst_sepcon: forall i v P Q,
  assert_of (subst i v (P ∗ Q)) = (assert_of (subst i v P) ∗ assert_of (subst i v Q)).
Proof.
  intros; rewrite /subst; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma subst_wand: forall i v P Q,
  (assert_of (subst i v (P -∗ Q)%I)) = (assert_of (subst i v P) -∗ assert_of (subst i v Q))%I.
Proof.
  intros; rewrite /subst; apply assert_ext; intros; monPred.unseal.
  ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split; intros ??????? [=]; subst; by apply H.
Qed.

Lemma subst_exp:
  forall (B: Type) (a : ident) (v : environ -> val) (P: B -> assert),
    assert_of (subst a v (∃ b: B, P b)) = ∃ b: B, assert_of (subst a v (P b)).
Proof.
  intros; rewrite /subst; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma env_set_env_set: forall id v1 v2 rho, env_set (env_set rho id v1) id v2 = env_set rho id v2.
Proof.
  intros.
  unfold env_set.
  f_equal.
  apply Map.ext. intro j.
  destruct (eq_dec id j). subst. repeat rewrite Map.gss. f_equal.
  simpl.
  repeat rewrite -> Map.gso by auto. auto.
Qed.

Lemma env_set_eval_id: forall id rho Delta t,
  tc_environ Delta rho ->
  (temp_types Delta) !! id = Some t ->
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
 repeat rewrite -> Map.gso by auto. auto.
Qed.

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
 repeat rewrite -> Map.gso by auto. auto.
Qed.

(*Lemma subst_ewand: forall i v (P Q: environ->mpred),
  subst i v (ewand P Q) = ewand (subst i v P) (subst i v Q).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_ewand : subst.*)

(* What's the best way to do this? *)
Lemma subst_proper: forall i v (P Q : assert), P ⊣⊢ Q -> assert_of (subst i v P) ⊣⊢ assert_of (subst i v Q).
Proof.
  intros; split => rho; rewrite /= /subst H //.
Qed.

Lemma subst_andp: forall id v P Q,
  assert_of (subst id v (P ∧ Q)) = (assert_of (subst id v P) ∧ assert_of (subst id v Q)).
Proof.
  intros; rewrite /subst; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma subst_prop: forall i v (P : Prop),
    assert_of (subst i v (⌜P⌝ : assert)) = ⌜P⌝.
Proof.
  intros; rewrite /subst; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma eval_expr_Econst_int: forall {cs: compspecs}  i t, eval_expr (Econst_int i t) = `(Vint i).
Proof. reflexivity. Qed.

Lemma subst_eval_var:
  forall id v id' t, subst id v (eval_var id' t) = eval_var id' t.
Proof.
intros. unfold subst, eval_var. extensionality rho.
simpl. auto.
Qed.

Lemma subst_local: forall id v (P : environ -> Prop),
  subst id v (local P) = local (subst id v P).
Proof. reflexivity. Qed.

Lemma eval_lvalue_Ederef:
  forall {cs: compspecs}  e t, eval_lvalue (Ederef e t) = eval_expr e.
Proof. reflexivity. Qed.

Lemma local_lift0_True:     local (`True%type) = True.
Proof.
  rewrite /local; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma overridePost_EK_return:
  forall Q (P : ret_assert), RA_return (overridePost Q P) = RA_return P.
Proof.
 destruct P; reflexivity.
Qed.

Lemma frame_ret_assert_emp:
  forall (P : ret_assert), frame_ret_assert P emp = P.
Proof. intros.
  destruct P; simpl; f_equal; last extensionality; apply sep_emp'.
Qed.

Lemma frame_ret_assert_EK_return:
 forall (P : ret_assert) Q vl, RA_return (frame_ret_assert P Q) vl = (RA_return P vl ∗ Q).
Proof.
 destruct P; simpl; reflexivity.
Qed.

Lemma function_body_ret_assert_EK_return:
  forall t P vl, RA_return (function_body_ret_assert t P) vl = bind_ret vl t P.
Proof. reflexivity. Qed.

Lemma bind_ret0_unfold:
  forall Q, bind_ret None tvoid Q = (assert_of (fun rho => Q (globals_only rho))).
Proof.
  intros; rewrite /bind_ret; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma bind_ret1_unfold:
  forall v t Q, bind_ret (Some v) t Q = (⌜tc_val t v⌝ ∧ assert_of (fun rho => Q (make_args (ret_temp :: nil)(v::nil) rho))).
Proof.
  intros; rewrite /bind_ret; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma bind_ret1_unfold':
  forall v t Q rho,
  bind_ret (Some v) t Q rho = (⌜tc_val t v⌝ ∧ Q (make_args (ret_temp::nil)(v::nil) rho)).
Proof.
 intros. rewrite /bind_ret; monPred.unseal. reflexivity.
Qed.

Lemma normal_ret_assert_elim:
 forall P, RA_normal (normal_ret_assert P) = P.
Proof.
reflexivity.
Qed.

Lemma overridePost_EK_break:
 forall P (Q : ret_assert), RA_break (overridePost P Q) = RA_break Q.
Proof. destruct Q; reflexivity.
Qed.

Lemma loop1_ret_assert_EK_break:
 forall P (Q : ret_assert), RA_break (loop1_ret_assert P Q) = RA_normal Q.
Proof. destruct Q; reflexivity.
Qed.

Lemma loop1_ret_assert_normal:
  forall P (Q : ret_assert), RA_normal (loop1_ret_assert P Q) = P.
Proof.
  destruct Q; reflexivity.
Qed.

Definition make_args' (fsig: funsig) args rho :=
   make_args (map (@fst _ _) (fst fsig)) (args rho) rho.
Lemma unfold_make_args': forall fsig args rho,
    make_args' fsig args rho = make_args (map (@fst _ _) (fst fsig)) (args rho) rho.
Proof. reflexivity. Qed.
Lemma unfold_make_args_cons: forall i il v vl rho,
   make_args (i::il) (v::vl) rho = env_set (make_args il vl rho) i v.
Proof. reflexivity. Qed.
Lemma unfold_make_args_nil: make_args nil nil = globals_only.
Proof. reflexivity. Qed.

Lemma clear_rhox:  (* replaces clear_make_args' *)
 forall (P: mpred) (f: environ -> environ),
    @liftx (Tarrow environ (LiftEnviron mpred))
                    (@liftx (LiftEnviron mpred) P) f
       = `P.
Proof. intros. reflexivity. Qed.

Lemma eval_make_args':
  forall (Q: val -> Prop) i fsig args,
  @liftx (Tarrow environ (LiftEnviron Prop))
      (@liftx (Tarrow val (LiftEnviron Prop)) Q (eval_id i))
   (make_args' fsig args) =
  `Q (`(eval_id i) (make_args' fsig args)).
Proof. reflexivity. Qed.

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

Infix "oo" := Basics.compose (at level 54, right associativity).
Arguments Basics.compose {A B C} g f x / .

Lemma compose_backtick:
  forall A B C (F: B -> C) (G: A -> B) (J: environ -> A),
   `F (`G  J) = `(Basics.compose F G) J.
Proof. reflexivity. Qed.

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
  forall {cs: compspecs}  (Q : val -> Prop) i j fsig t0 t t' tl (e: expr) el,
   i<>j ->
    @liftx (Tarrow environ (LiftEnviron Prop))
     (Q oo (eval_id i)) (make_args' ((j,t)::fsig, t0) (eval_exprlist (t'::tl) (e::el))) =
     `Q (`(eval_id i) (make_args' (fsig, t0) (eval_exprlist tl el))).
Proof.
  intros.
  rewrite <- compose_backtick.
  f_equal. apply eval_make_args_other; auto.
Qed.

Lemma substopt_unfold {A}: forall id v, @substopt A (Some id) v = @subst A id v.
Proof. reflexivity. Qed.
Lemma substopt_unfold_nil {A}: forall v (P:  environ -> A), substopt None v P = P.
Proof. reflexivity. Qed.

Lemma get_result_unfold: forall id, get_result (Some id) = get_result1 id.
Proof. reflexivity. Qed.
Lemma get_result_None: get_result None = globals_only.
Proof. reflexivity. Qed.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (var_types Delta) !! i = None /\ (glob_types Delta) !! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Proof.
intros.
destruct H as [H [H8 H0]].
unfold eval_var, globals_only.
simpl.
destruct_var_types i.
destruct_glob_types i.
rewrite Heqo0 Heqo1 //.
Qed.

Lemma elim_globals_only':
 forall a: mpred,
 (@liftx (Tarrow environ (LiftEnviron mpred)) (`a) globals_only) = `a.
Proof. reflexivity. Qed.

Lemma globvar_eval_var:
  forall Delta rho id t,
      tc_environ Delta rho ->
     (var_types Delta) !! id = None ->
     (glob_types Delta) !! id = Some  t ->
     exists b,  eval_var id t rho = Vptr b Ptrofs.zero
            /\ Map.get (ge_of rho) id = Some b.
Proof.
intros.
unfold eval_var; simpl.
destruct_var_types id.
destruct_glob_types id.
rewrite Heqo0 Heqo1.
eauto.
Qed.

Lemma globvars2pred_unfold: forall gv vl,
    globvars2pred gv vl = [∗] (map (globvar2pred gv) vl).
Proof. easy. Qed.

Lemma eval_var_isptr:
  forall Delta t i rho,
            tc_environ Delta rho ->
            ((var_types Delta) !! i = Some t \/
             (var_types Delta) !! i = None /\
            (glob_types Delta) !! i = Some t) ->
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
   rewrite Heqo0 Heqo1 //.
Qed.

Lemma ENTAIL_trans:
  forall Delta P Q R,
  (local (tc_environ Delta) ∧ P ⊢ Q) ->
  (local (tc_environ Delta) ∧ Q ⊢ R) ->
  local (tc_environ Delta) ∧ P ⊢ R.
Proof.
intros ????? <-; rewrite -H.
iIntros "(? & $)"; auto.
Qed.

Lemma ENTAIL_refl:
  forall Delta P,
  local (tc_environ Delta) ∧ P ⊢ P.
Proof.
  intros; apply bi.and_elim_r.
Qed.

Implicit Type (R : assert).

Lemma derives_fupd_trans: forall TC E1 E2 E3 P Q R,
  (local TC ∧ P ⊢ (|={E1,E2}=> Q)) ->
  (local TC ∧ Q ⊢ (|={E2,E3}=> R)) ->
  local TC ∧ P ⊢ (|={E1,E3}=> R).
Proof.
  intros.
  iIntros "(#? & ?)".
  iMod (H with "[$]"); iApply H0; iFrame; auto.
Qed.

Lemma derives_fupd_refl: forall TC E P,
  local TC ∧ P ⊢ |={E}=> P.
Proof. intros; by iIntros "(_ & $)". Qed.

Lemma derives_full_refl: forall Delta E P,
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> P.
Proof. intros; by iIntros "(_ & _ & $)". Qed.

Lemma derives_full_trans: forall Delta E P Q R,
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ (|={E}=> (Q))) ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q) ⊢ (|={E}=> (R))) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ (|={E}=> (R)).
Proof.
  intros.
  eapply derives_fupd_trans, H0.
  iIntros "(? & #$ & ?)".
  by iApply H; iFrame.
Qed.

Lemma derives_ENTAIL: forall TC P Q,
  (P ⊢ Q) ->
  local TC ∧ P ⊢ Q.
Proof. intros ??? ->; apply bi.and_elim_r. Qed.

Lemma ENTAIL_derives_fupd: forall TC E P Q,
  (local TC ∧ P ⊢ Q) ->
  local TC ∧ P ⊢ |={E}=> Q.
Proof. intros. rewrite H; apply fupd_intro. Qed.

Lemma derives_fupd_derives_full: forall Delta E P Q,
  (local (tc_environ Delta) ∧ P ⊢ (|={E}=> Q)) ->
  local (tc_environ Delta) ∧ (allp_fun_id Delta ∧ P) ⊢ (|={E}=> Q).
Proof.
  intros. rewrite -H. iIntros "(? & _ & $)"; auto.
Qed.

Lemma andp_ENTAIL: forall TC P P' Q Q',
  (local TC ∧ P ⊢ P') ->
  (local TC ∧ Q ⊢ Q') ->
  local TC ∧ (P ∧ Q) ⊢ P' ∧ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & ?)"; iSplit; [rewrite bi.and_elim_l | rewrite bi.and_elim_r]; auto.
Qed.

Lemma orp_ENTAIL: forall TC P P' Q Q',
  (local TC ∧ P ⊢ P') ->
  (local TC ∧ Q ⊢ Q') ->
  local TC ∧ (P ∨ Q) ⊢ P' ∨ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & [? | ?])"; auto.
Qed.

Lemma sepcon_ENTAIL: forall TC P P' Q Q',
  (local TC ∧ P ⊢ P') ->
  (local TC ∧ Q ⊢ Q') ->
  local TC ∧ (P ∗ Q) ⊢ P' ∗ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & $ & $)".
  iSplit; first iModIntro; iSplit; done.
Qed.

Lemma wand_ENTAIL: forall TC P P' Q Q',
  (local TC ∧ P' ⊢ P) ->
  (local TC ∧ Q ⊢ Q') ->
  local TC ∧ (P -∗ Q) ⊢ P' -∗ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & H) ?"; iSplit; first done.
  iApply "H"; iFrame.
Qed.

Lemma exp_ENTAIL: forall Delta B (P Q: B -> assert),
  (forall x: B, local (tc_environ Delta) ∧ P x ⊢ Q x) ->
  local (tc_environ Delta) ∧ (∃ y, P y) ⊢ ∃ y, Q y.
Proof.
  intros.
  iIntros "(? & %y & P)".
  iExists y; rewrite -H; iFrame.
Qed.

Lemma allp_ENTAIL: forall Delta B (P Q: B -> assert),
  (forall x: B, local (tc_environ Delta) ∧ P x ⊢ Q x) ->
  local (tc_environ Delta) ∧ (∀ y, P y) ⊢ ∀ y, Q y.
Proof.
  intros.
  iIntros "H" (?); rewrite -H.
  iApply (bi.and_mono with "H"); eauto.
Qed.

Lemma later_ENTAIL: forall Delta P Q,
  (local (tc_environ Delta) ∧ P ⊢ Q) ->
  local (tc_environ Delta) ∧ ▷ P ⊢ ▷ Q.
Proof.
  intros.
  iIntros "? !>"; by iApply H.
Qed.

Lemma andp_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ P') ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q) ⊢ Q') ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P ∧ Q)) ⊢ P' ∧ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & ? & ?)"; iSplit; [rewrite bi.and_elim_l | rewrite bi.and_elim_r]; auto.
Qed.

Lemma orp_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ P') ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q) ⊢ Q') ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P ∨ Q)) ⊢ P' ∨ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & ? & [? | ?])"; auto.
Qed.

Lemma imp_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P') ⊢ P) ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q) ⊢ Q') ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P → Q)) ⊢ P' → Q'.
Proof.
  intros ????? <- <-.
  iIntros "H"; iApply bi.impl_intro_r; last iApply "H".
  iIntros "H"; iSplit; first by iDestruct "H" as "((? & _ & _) & _)".
  iSplit; first by iDestruct "H" as "((_ & $ & _) & _)".
  iApply (bi.impl_elim with "H").
  - iIntros "((_ & _ & $) & _)".
  - rewrite -bi.and_assoc {1}(persistent (allp_fun_id _)).
    rewrite -bi.persistently_and_intuitionistically_sep_l -bi.and_assoc.
    iIntros "(? & ? & _ & $)"; iFrame.
    by iApply bi.intuitionistically_affinely.
Qed.

Lemma sepcon_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ P') ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q) ⊢ Q') ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P ∗ Q)) ⊢ P' ∗ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(#? & #? & $ & $)"; auto.
Qed.

Lemma wand_ENTAILL: forall Delta P P' Q Q',
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P') ⊢ P) ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q) ⊢ Q') ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P -∗ Q)) ⊢ P' -∗ Q'.
Proof.
  intros ????? <- <-.
  iIntros "(? & ? & H) ?"; iSplit; first done; iSplit; first done.
  iApply "H"; iFrame.
Qed.

Lemma exp_ENTAILL: forall Delta B (P Q: B -> assert),
  (forall x: B, local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P x) ⊢ Q x) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ ∃ y, P y) ⊢ ∃ y, Q y.
Proof.
  intros.
  iIntros "(? & ? & %y & P)".
  iExists y; rewrite -H; iFrame.
Qed.

Lemma allp_ENTAILL: forall Delta B (P Q: B -> assert),
  (forall x: B, local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P x) ⊢ Q x) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ ∀ y, P y) ⊢ ∀ y, Q y.
Proof.
  intros.
  iIntros "H" (?); rewrite -H.
  iApply (bi.and_mono with "H"); eauto.
  iIntros "($ & ?)"; eauto.
Qed.

Lemma later_ENTAILL: forall Delta P Q,
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ Q) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ ▷ P) ⊢ ▷ Q.
Proof.
  intros ??? <-.
  by iIntros "? !>".
Qed.

Lemma andp_subst_ENTAILL: forall Delta P P' Q Q' i v t,
  (temp_types Delta) !! i = Some t ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P') ⊢ local (`(tc_val' t) v)) ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P') ⊢ Q') ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ Q) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P' ∧ assert_of (subst i v P))) ⊢ Q' ∧ assert_of (subst i v Q).
Proof.
  intros ?????????? <- ?.
  iIntros "H".
  iAssert (local (`(tc_val' t) v)) as "#Hty".
  { iDestruct "H" as "(? & ? & ? & _)".
    iApply (H0 with "[$]"). }
  assert (local ((` (tc_val' t)) v) ∧ local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ assert_of (subst i v P) ⊢ assert_of (subst i v Q)) as <-.
  2: { iDestruct "H" as "(? & ? & ?)"; iSplit; iSplit; auto.
       * rewrite bi.and_elim_l; iFrame.
       * rewrite bi.and_elim_r; iFrame. }
  split => rho; rewrite /subst /= -H1; monPred.unseal.
  rewrite !monPred_at_affinely.
  iIntros "(% & %TC & $ & $)"; iPureIntro.
  split; auto; unfold tc_environ, typecheck_environ in *.
  destruct TC as (TC & ? & ?); split3; auto; simpl.
  intros ?? Ht.
  destruct (eq_dec id i).
  + subst; rewrite Map.gss.
    eexists; split; first done.
    assert (t = ty) as -> by congruence.
    apply TC in H as (? & ? & ?); eauto.
  + rewrite Map.gso; eauto.
Qed.

Lemma derives_fupd_fupd_left: forall TC E P Q,
  (local TC ∧ P ⊢ (|={E}=> Q)) ->
  (local TC ∧ |={E}=> P) ⊢ |={E}=> Q.
Proof.
  intros.
  iIntros "(? & >?)"; iApply H; iFrame.
Qed.

Lemma derives_full_fupd_left: forall Delta E P Q,
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ (|={E}=> Q)) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ |={E}=> P) ⊢ |={E}=> Q.
Proof.
  intros.
  iIntros "(? & ? & >?)"; iApply H; iFrame.
Qed.

Lemma aux2_reduceR: forall E P Q,
  (P ⊢ Q) ->
  P ⊢ |={E}=> Q.
Proof.
  intros ??? <-; apply fupd_intro.
Qed.

Lemma aux_reduceL: forall P Q R S,
  (P ∧ R ⊢ S) ->
  P ∧ (<affine> Q ∗ R) ⊢ S.
Proof.
  intros ???? <-.
  iIntros "H"; iSplit; [iDestruct "H" as "($ & _)" | iDestruct "H" as "(_ & _ & $)"].
Qed.

End mpred.

Infix "oo" := Basics.compose (at level 54, right associativity).
Arguments Basics.compose {A B C} g f x / .

#[export] Hint Rewrite @loop1x_ret_assert_EK_normal: ret_assert.
Ltac simpl_ret_assert :=
 cbn [RA_normal RA_break RA_continue RA_return 
      normal_ret_assert overridePost loop1_ret_assert
      loop2_ret_assert function_body_ret_assert frame_ret_assert
      switch_ret_assert loop1x_ret_assert loop1y_ret_assert
      for_ret_assert loop_nocontinue_ret_assert];
  try (match goal with
      | |- context[bind_ret None tvoid ?P] =>
        let H:= fresh in
          assert (bind_ret None tvoid P ⊣⊢ P) as -> by (raise_rho; try monPred.unseal; done)
      end).

#[export] Hint Rewrite @frame_normal @frame_for1 @frame_loop1
                 @overridePost_normal: ret_assert.
#[export] Hint Rewrite @RA_normal_loop2_ret_assert : ret_assert.
#[export] Hint Rewrite @overridePost_overridePost : ret_assert.
#[export] Hint Rewrite @overridePost_normal' : ret_assert.
#[export] Hint Rewrite @liftx_id : norm2.
#[export] Hint Rewrite @liftx3_liftx2 @liftx2_liftx1 @liftx1_liftx0 : norm2.
#[export] Hint Rewrite @lift1_lift0 : norm2.
#[export] Hint Rewrite const_liftx0 : norm2.
#[export] Hint Rewrite lift_identity : norm2.
#[export] Hint Rewrite @local_lift2_and : norm2.
#[export] Hint Rewrite @subst_True @subst_False: subst.
#[export] Hint Rewrite @subst_sepcon : subst.
#[export] Hint Rewrite @subst_wand : subst.
#[export] Hint Rewrite @resubst : subst.
#[export] Hint Rewrite @subst_andp @subst_prop : subst.
#[export] Hint Rewrite @eval_expr_Econst_int : eval.
#[export] Hint Rewrite subst_eval_var : subst.
#[export] Hint Rewrite @subst_local : subst.
#[export] Hint Rewrite @eval_lvalue_Ederef : eval.
#[export] Hint Rewrite @local_lift0_True : norm2.
#[export] Hint Rewrite @overridePost_EK_return : ret_assert.
#[export] Hint Rewrite @frame_ret_assert_EK_return : ret_assert.
#[export] Hint Rewrite @function_body_ret_assert_EK_return : ret_assert.
#[export] Hint Rewrite @bind_ret1_unfold : norm2.
#[export] Hint Rewrite @bind_ret1_unfold' : norm2.  (* put this in AFTER the unprimed version, for higher priority *)
#[export] Hint Rewrite @overridePost_EK_break @loop1_ret_assert_EK_break
  @normal_ret_assert_elim : ret_assert.
#[export] Hint Rewrite @loop1_ret_assert_normal: ret_assert.
#[export] Hint Rewrite unfold_make_args' : norm2.
#[export] Hint Rewrite unfold_make_args_cons unfold_make_args_nil : norm2.
#[export] Hint Rewrite @clear_rhox: norm2.
#[export] Hint Rewrite eval_make_args' : norm2.
#[export] Hint Rewrite @eval_make_args_same : norm2.
#[export] Hint Rewrite @eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

#[export] Hint Rewrite compose_backtick : norm.
#[export] Hint Rewrite @compose_eval_make_args_same : norm.
#[export] Hint Rewrite @compose_eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.
#[export] Hint Rewrite @substopt_unfold @substopt_unfold_nil : subst.
#[export] Hint Rewrite get_result_unfold get_result_None : norm.
#[export] Hint Rewrite @elim_globals_only using (split3; [eassumption | reflexivity.. ]) : norm.
#[export] Hint Rewrite @elim_globals_only' : norm.
#[export] Hint Rewrite @globvars2pred_unfold : norm.
#[export] Hint Rewrite @exp_trivial : norm.


Ltac lifted_derives_L2R H :=
  eapply ENTAIL_trans; [apply H |].

Ltac ENTAIL_L2R H :=
  match type of H with
  | (local (tc_environ _) ∧ _) ⊢ _ =>
      eapply ENTAIL_trans; [apply H |]
  | _ =>
      eapply ENTAIL_trans; [apply derives_ENTAIL, H |]
  end.

Ltac derives_fupd_L2R H :=
  match type of H with
  | (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
      eapply derives_fupd_trans; [apply H |]
  | (local (tc_environ _) ∧ _) ⊢ _ =>
      eapply derives_fupd_trans; [apply ENTAIL_derives_fupd, H |]
  | _ =>
      eapply derives_fupd_trans; [apply ENTAIL_derives_fupd, derives_ENTAIL, H |]
  end.

Ltac derives_full_L2R H :=
  match type of H with
  | (local (tc_environ ?Delta) ∧ (<affine> allp_fun_id ?Delta ∗ _)) ⊢ (|={_,_}=> _) =>
      eapply derives_full_trans; [apply H |]
  | (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
      eapply derives_full_trans; [apply derives_fupd_derives_full, H |]
  | (local (tc_environ _) ∧ _) ⊢ _ =>
      eapply derives_full_trans; [apply derives_fupd_derives_full, ENTAIL_derives_fupd, H |]
  | _ =>
      eapply derives_full_trans; [apply derives_fupd_derives_full, ENTAIL_derives_fupd, derives_ENTAIL, H |]
  end.

Tactic Notation "derives_rewrite" "->" constr(H) :=
  match goal with
  | |- (local (tc_environ ?Delta) ∧ (<affine> allp_fun_id ?Delta ∗ _)) ⊢ (|={_,_}=> _) =>
         derives_full_L2R H
  | |- (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
         derives_fupd_L2R H
  | |- (local (tc_environ _) ∧ _) ⊢ _ =>
         ENTAIL_L2R H
  | |- _ =>
         lifted_derives_L2R H
  end.

Ltac lifted_derives_R2L H :=
  etrans; [| apply H].

Ltac ENTAIL_R2L H :=
  match type of H with
  | (local (tc_environ _) ∧ _) ⊢ _ =>
      eapply ENTAIL_trans; [| apply H]
  | _ =>
      eapply ENTAIL_trans; [| apply derives_ENTAIL, H]
  end.

Ltac derives_fupd_R2L H :=
  match type of H with
  | (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
      eapply derives_fupd_trans; [| apply H]
  | (local (tc_environ _) ∧ _) ⊢ _ =>
      eapply derives_fupd_trans; [| apply ENTAIL_derives_fupd, H]
  | _ =>
      eapply derives_fupd_trans; [| apply ENTAIL_derives_fupd, derives_ENTAIL, H]
  end.

Ltac derives_full_R2L H :=
  match type of H with
  | (local (tc_environ ?Delta) ∧ (<affine> allp_fun_id ?Delta ∗ _)) ⊢ (|={_,_}=> _) =>
      eapply derives_fupd_trans; [| apply H]
  | (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
      eapply derives_fupd_trans; [| apply derives_fupd_derives_full, H]
  | (local (tc_environ _) ∧ _) ⊢ _ =>
      eapply derives_fupd_trans; [| apply derives_fupd_derives_full, ENTAIL_derives_fupd, H]
  | _ =>
      eapply derives_fupd_trans; [| apply derives_fupd_derives_full, ENTAIL_derives_fupd, derives_ENTAIL, H]
  end.

Tactic Notation "derives_rewrite" "<-" constr(H) :=
  match goal with
  | |- (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
         derives_fupd_R2L H
  | |- (local (tc_environ _) ∧ _) ⊢ (|={_,_}=> _) =>
         derives_fupd_R2L H
  | |- (local (tc_environ _) ∧ _) ⊢ _ =>
         ENTAIL_R2L H
  | |- _ =>
         lifted_derives_R2L H
  end.

Ltac solve_derives_trans :=
  first [simple apply derives_full_refl | eapply derives_full_trans; [eassumption | solve_derives_trans]].

(*Lemma aux1_reduceR: forall P Q: environ -> mpred,
  (P ⊢ (|==> Q)) ->
  P ⊢ |==> ▷ FF || Q.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply bupd_mono.
  apply orp_right2; auto.
Qed.*)

Ltac reduceR :=
(*  match goal with
  | |- _ ⊢ |==> ▷ FF || _ => apply aux1_reduceR
  | _ => idtac
  end;*)
  match goal with
  | |- _ ⊢ |={_}=> _ => apply aux2_reduceR
  | _ => idtac
  end.

Ltac reduceLL :=
  match goal with
  | |- local (tc_environ ?Delta) ∧ (<affine> allp_fun_id ?Delta ∗ _) ⊢ _ => apply aux_reduceL
  | _ => idtac
  end.

Ltac reduceL :=
  match goal with
  | |- local (tc_environ ?Delta) ∧ (<affine> allp_fun_id ?Delta ∗ _) ⊢ _ => apply aux_reduceL
  | _ => idtac
  end;
  match goal with
  | |- local (tc_environ _) ∧ _ ⊢ _ => apply derives_ENTAIL
  | _ => idtac
  end.

Ltac reduce2derives :=
  reduceL; reduceR.

Ltac reduce2ENTAIL :=
  reduceLL; reduceR.
