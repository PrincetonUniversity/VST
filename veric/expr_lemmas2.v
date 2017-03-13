Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Export veric.environ_lemmas.

Import Cop.
Import Cop2.

Opaque tc_andp. (* This is needed otherwise certain Qeds take
    forever in Coq 8.3.  *)

Lemma typecheck_var_environ_None: forall ve vt,
  typecheck_var_environ ve vt ->
  forall i,
  vt ! i = None <-> Map.get ve i = None.
Proof.
  intros.
  destruct (vt ! i) eqn:?H, (Map.get ve i) eqn:?H; try (split; congruence).
  + apply H in H0.
    destruct H0; congruence.
  + destruct p.
    assert (vt ! i = Some t) by (apply H; eauto).
    congruence.
Qed.

Lemma eval_lvalue_ptr : forall {CS: compspecs} rho m e (Delta: tycontext) te' te ve ge,
mkEnviron ge ve te = rho ->
typecheck_var_environ ve (var_types Delta) ->
typecheck_glob_environ ge (glob_types Delta) ->
denote_tc_assert (typecheck_lvalue Delta te' e) rho m ->
exists base, exists ofs, eval_lvalue e rho  = Vptr base ofs.
Proof.
intros.
induction e; eauto;
try now inversion H2.
*
simpl. unfold eval_var.
simpl in H2.
unfold get_var_type in H2.
subst rho; simpl ve_of; simpl ge_of.
destruct ((var_types Delta) ! i) eqn:?H;
 [| destruct ((glob_types Delta) ! i) eqn:?H].
+ apply tc_bool_e in H2.
  apply H0 in H.
  destruct H as [b ?].
  exists b, Int.zero.
  rewrite H, H2.
  auto.
+ apply tc_bool_e in H2.
  apply (typecheck_var_environ_None _ _ H0) in H.
  apply H1 in H3.
  destruct H3 as [b [? ?]].
  exists b, Int.zero.
  rewrite H, H3.
  auto.
+ inv H2.
*
simpl in H2.
rewrite !denote_tc_assert_andp in H2.
destruct H2 as [[? ?] ?].
simpl in H4.
simpl.
destruct (eval_expr e rho); simpl; try now inversion H4; eauto.
*
simpl in *. super_unfold_lift.
rewrite denote_tc_assert_andp in H2.
destruct H2.
spec IHe; auto. destruct IHe.
unfold eval_field.
destruct H4 as [ofs ?].
destruct (eval_lvalue e rho); try congruence.
inversion H4; subst x i0; clear H4.
destruct (typeof e); try now inversion H3.
+
destruct (cenv_cs ! i0) as [co |]; [| inv H3].
destruct (field_offset cenv_cs i (co_members co)); [| inv H3].
unfold offset_val; eauto.
+
destruct (cenv_cs ! i0) as [co |]; [| inv H3].
simpl.
eauto.
Qed.

Ltac unfold_tc_denote :=
unfold denote_tc_nonzero in *;
unfold isptr in *;
unfold denote_tc_igt in *;
unfold denote_tc_Zle in *;
unfold denote_tc_Zge in *;
unfold denote_tc_samebase in *;
unfold denote_tc_nodivover in *;
unfold denote_tc_initialized in *.


Lemma typecheck_lvalue_Evar:
  forall {CS: compspecs} i t pt Delta te rho m, typecheck_environ Delta rho ->
           denote_tc_assert (typecheck_lvalue Delta te (Evar i t)) rho m ->
           is_pointer_type pt = true ->
           typecheck_val (eval_lvalue (Evar i t) rho) pt = true.
Proof.
intros.
simpl in *. unfold eval_var.

unfold typecheck_environ in H.
intuition.
destruct rho.
unfold typecheck_var_environ in *. unfold get_var_type in *.

remember ((var_types Delta) ! i).
destruct o; try rewrite eqb_type_eq in *; simpl in *; intuition.
super_unfold_lift.
remember (type_eq t t0). destruct s; intuition.
subst.
simpl in *. super_unfold_lift.
symmetry in Heqo.
specialize (H i t0).
destruct H as [H _].
specialize (H Heqo).

{destruct H.
rewrite H in *. rewrite eqb_type_refl in *. destruct pt; auto.
}
{remember ((glob_types Delta) ! i). destruct o; try congruence.
simpl in *. super_unfold_lift.
remember (eqb_type t t0).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst.
unfold same_env in *.
symmetry in Heqo0.  specialize (H5 _ _ Heqo0).
destruct H5. simpl in *. unfold Map.get. rewrite H4.
unfold typecheck_glob_environ in *. destruct (H3 i _ Heqo0). destruct H5.
rewrite H5.
destruct pt; inv H1; reflexivity.
destruct H4; congruence. inv H0.
inv H0.
}
Qed.

Lemma typecheck_expr_sound_Efield:
  forall {CS: compspecs} Delta te0 rho e i t m
  (H: typecheck_environ Delta rho)
  (IHe: (denote_tc_assert (typecheck_expr Delta te0 e) rho m ->
          typecheck_val (eval_expr e rho) (typeof e) = true) /\
          (forall pt : type,
          denote_tc_assert (typecheck_lvalue Delta te0 e) rho m ->
          is_pointer_type pt = true ->
          typecheck_val (eval_lvalue e rho) pt = true))
  (H0: denote_tc_assert (typecheck_expr Delta te0 (Efield e i t)) rho m),
  typecheck_val (eval_expr (Efield e i t) rho) (typeof (Efield e i t)) = true.
Proof.
intros.
simpl in *. super_unfold_lift.
 unfold eval_field, offset_val, deref_noload in *.
assert (MODE: access_mode t = By_reference) by (destruct (access_mode t); auto; hnf in H0; try contradiction).
rewrite MODE in *.
destruct IHe.
destruct rho.
rewrite denote_tc_assert_andp in H0. destruct H0.
unfold typecheck_environ in H.
destruct H as [_ [Hve [Hge _]]].
assert (PTR := eval_lvalue_ptr _ _ e Delta te0 te ve ge (eq_refl _) Hve Hge H0).
specialize (H2 t H0).
spec H2. clear - MODE; destruct t; try destruct i; try destruct s; try destruct f; inv MODE; simpl; auto.
destruct PTR.
destruct (typeof e); try now inv H3.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H3.
  destruct (field_offset cenv_cs i (co_members co)); try now inv H3.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H3.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H.
Qed.

Lemma typecheck_lvalue_sound_Efield:
 forall {CS: compspecs} Delta rho te0 m e i t pt
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta te0 e) rho m ->
          typecheck_val (eval_expr e rho) (typeof e) = true) /\
        (forall pt0 : type, denote_tc_assert (typecheck_lvalue Delta te0 e) rho m ->
           is_pointer_type pt0 = true ->
         typecheck_val (eval_lvalue e rho) pt0 = true))
  (H0: denote_tc_assert (typecheck_lvalue Delta te0 (Efield e i t)) rho m)
  (H1: is_pointer_type pt = true),
  typecheck_val (eval_lvalue (Efield e i t) rho) pt = true.
Proof.
intros.
simpl in *.
rewrite denote_tc_assert_andp in H0. destruct H0.
super_unfold_lift.
 unfold eval_field,offset_val in *; intuition.
specialize  (H4 pt).
destruct rho.
unfold typecheck_environ in *. intuition.
assert (PTR := eval_lvalue_ptr _ m e _ te0 te _ _ (eq_refl _) H H6 H0).
simpl in *.
remember (eval_lvalue e (mkEnviron ge ve te)). unfold isptr in *.
subst v.
destruct PTR as [b [ofs ?]].
destruct (typeof e); try now inv H2.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H2.
  destruct (field_offset cenv_cs i (co_members co)); try now inv H2.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H7.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H2.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H7.
Qed.

Lemma typecheck_expr_sound_Evar:
  forall {CS: compspecs} Delta te0 rho m i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta te0 (Evar i t)) rho m ->
  typecheck_val (eval_expr (Evar i t) rho) (typeof (Evar i t)) = true.
Proof.
intros.
assert (MODE: access_mode t = By_reference)
 by (unfold typecheck_expr in H0; destruct (access_mode t); try (hnf in H0; contradiction); auto).
simpl. super_unfold_lift. unfold deref_noload.

 unfold typecheck_environ in H. intuition.
rename H4 into SM.
destruct rho.
unfold typecheck_var_environ, same_env in *.
simpl in H0. rewrite MODE in H0.
unfold get_var_type in *.

remember ((var_types Delta) ! i).
destruct o; try rewrite eqb_type_eq in *; simpl in *; intuition.
remember (type_eq t t0). destruct s; intuition.
subst. simpl in H0.
clear H0.
symmetry in Heqo.
specialize (H i t0).
destruct H as [H _]; specialize (H Heqo).
destruct H. unfold eval_var. simpl.
rewrite H in *. rewrite eqb_type_refl in *.
simpl. destruct t0; try destruct i0; try destruct s; try destruct f; inv MODE; auto.
remember ((glob_types Delta) ! i). destruct o; try congruence.
simpl in *.
unfold eval_var in *.
 super_unfold_lift. remember (eqb_type t t0).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst.
symmetry in Heqo0.  specialize (SM _ _ Heqo0).
destruct SM.
unfold Map.get. rewrite H3.
unfold typecheck_glob_environ in *.
destruct (H2 _ _ Heqo0). destruct H4.
rewrite H4. auto. destruct H3; congruence.
inv H0. inv H0.
Qed.

Definition unOp_result_type op t :=
match op with
  | Cop.Onotbool =>match t with
                                | Tint _ _ _ => Tint IBool Signed noattr
                                | Tlong _ _ => Tint IBool Signed noattr
                                | Tpointer _ _ => Tint I32 Signed noattr
                                | Tfloat _ _ => Tint IBool Signed noattr
                                | Tarray _ _ _ => Tint IBool Signed noattr
                                | Tfunction _ _ _ => Tint IBool Signed noattr
                                | _ => Tvoid
                                end
  | Cop.Onotint => match t with
                                | Tint _ _ _ => Tint I32 Signed noattr
                                | Tlong _ _ => Tlong Signed noattr
                                | _ => Tvoid
                                end
  | Cop.Oneg => match t with
                           | Tint _ _ _ => Tint I32 Signed noattr
                           | Tlong _ _ => Tlong Signed noattr
                           | Tfloat _ _ => t
                           | _ => Tvoid
                           end
  | Cop.Oabsfloat => t
end.


Lemma tc_bool_e: forall {CS: compspecs} b a rho m, (* copied from binop_lemmas.v *)
  app_pred (denote_tc_assert (tc_bool b a) rho) m ->
  b = true.
Proof.
intros.
destruct b; simpl in H; auto.
Qed.

Lemma typecheck_val_of_bool_int_type:
 forall b t, is_int_type t = true ->
  typecheck_val (Val.of_bool b) t = true.
Proof.
 intros.
 destruct t as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 try inv H; destruct b; reflexivity.
Qed.

Lemma typecheck_unop_sound:
 forall {CS: compspecs} Delta te0 rho m u e t
 (H: typecheck_environ Delta rho)
(* (Ht: t =unOp_result_type u (typeof e)) *)
 (IHe: (denote_tc_assert (typecheck_expr Delta te0 e) rho m ->
          typecheck_val (eval_expr e rho) (typeof e) = true) /\
          (forall pt : type,
           denote_tc_assert (typecheck_lvalue Delta te0 e) rho m ->
           is_pointer_type pt = true ->
           typecheck_val (eval_lvalue e rho) pt = true))
  (H0: denote_tc_assert (typecheck_expr Delta te0 (Eunop u e t)) rho m),
  typecheck_val (eval_expr (Eunop u e t) rho) t = true.
Proof.
intros.
simpl in H0. rewrite denote_tc_assert_andp in H0. destruct H0.
destruct IHe as [? _].
specialize (H2 H1).
simpl eval_expr.
unfold_lift.
clear - H2 H0.
unfold eval_unop, sem_unary_operation, force_val1.
destruct u; simpl in *;
unfold sem_notbool, sem_notint, sem_neg, sem_absfloat in *;
super_unfold_lift; simpl;
destruct (typeof e) as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 simpl in *; try contradiction;
 try (rewrite denote_tc_assert_andp in H0; destruct H0 as [H0 H0']);
 try contradiction H0;
 simple apply tc_bool_e in H0; try discriminate H0;
 destruct (eval_expr e rho) eqn:?; try discriminate H2;
 try solve [apply typecheck_val_of_bool_int_type; auto];
 unfold sem_notbool_p; simpl force_val; try reflexivity;
 destruct t as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; inv H0;
 try reflexivity.
Qed.

Lemma same_base_tc_val : forall v t1 t2,
same_base_type t1 t2 = true ->
typecheck_val v t1 = true ->
 typecheck_val v t2 = true.
Proof.
intros. destruct t1; destruct t2;
    try destruct f; try destruct f0; try destruct f1;
   try solve [inv H]; destruct v; auto.
Qed.

Lemma typecheck_temp_sound:
  forall {CS: compspecs} Delta rho m i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (te_of rho) (Etempvar i t)) rho m ->
  typecheck_val (eval_expr (Etempvar i t) rho) (typeof (Etempvar i t)) = true.
Proof.
intros.
simpl in *. destruct rho.
destruct H as [H1 _].
unfold typecheck_temp_environ in *.
unfold eval_id, force_val in *.

simpl.
destruct Delta; simpl in *.
unfold temp_types in *. simpl in *.
specialize (H1 i).
destruct (tyc_temps ! i); try (contradiction H0).
destruct (H1 _ (eq_refl _)) as [v [? ?]]. clear H1.
rewrite H.
simpl in H0.
destruct (is_neutral_cast t0 t) eqn:?.
rewrite tc_val_eq' in *.
intuition;
  try solve [symmetry in Heqb; eapply neutral_cast_subsumption; eauto].
simpl in H0. unfold Map.get in H. rewrite H in H0.
destruct (same_base_type t0 t) eqn:?; [ | inv H0].
simpl in H0.
intuition;
try solve [eapply same_base_tc_val; eauto].
Qed.

Lemma typecheck_deref_sound:
  forall {CS: compspecs} Delta te0 rho m e t pt,
   typecheck_environ Delta rho ->
   (denote_tc_assert (typecheck_expr Delta te0 e) rho m ->
    typecheck_val (eval_expr e rho) (typeof e) = true) /\
    (forall pt0 : type,
     denote_tc_assert (typecheck_lvalue Delta te0 e) rho m ->
     is_pointer_type pt0 = true -> typecheck_val (eval_lvalue e rho) pt0 = true) ->
     denote_tc_assert (typecheck_lvalue Delta te0 (Ederef e t)) rho m ->
    is_pointer_type pt = true ->
    typecheck_val (eval_lvalue (Ederef e t) rho) pt = true.
Proof.
intros until pt. intros H IHe H0 H1.
simpl. unfold lift.
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0 as [[? ?] ?].
destruct IHe as[ ? _].
specialize (H4 H0).
revert H2; case_eq (is_pointer_type (typeof e)); intros; hnf in H2; try contradiction.
clear H H5 H4.
hnf in H3. unfold_lift in H3; hnf in H3.
unfold_lift.
destruct (eval_expr e rho); try contradiction.
destruct pt; inv H1; reflexivity.
Qed.

