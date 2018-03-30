Require Import VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.

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

Lemma eval_lvalue_ptr : forall {CS: compspecs} rho m e (Delta: tycontext) te ve ge,
mkEnviron ge ve te = rho ->
typecheck_var_environ ve (var_types Delta) ->
typecheck_glob_environ ge (glob_types Delta) ->
denote_tc_assert (typecheck_lvalue Delta e) rho m ->
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
  exists b, Ptrofs.zero.
  rewrite H, H2.
  auto.
+ apply tc_bool_e in H2.
  apply (typecheck_var_environ_None _ _ H0) in H.
  apply H1 in H3.
  destruct H3 as [b ?].
  exists b, Ptrofs.zero.
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
  forall {CS: compspecs} i t pt Delta rho m, typecheck_environ Delta rho ->
           denote_tc_assert (typecheck_lvalue Delta (Evar i t)) rho m ->
           is_pointer_type pt = true ->
           tc_val pt (eval_lvalue (Evar i t) rho).
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
rewrite H in *. rewrite eqb_type_refl in *.
 unfold is_pointer_type in H1.
 destruct pt; try solve [inv H1; auto].
 unfold tc_val.
 simple_if_tac; apply I.
}
{remember ((glob_types Delta) ! i). destruct o; try congruence.
simpl in *. super_unfold_lift.
remember (eqb_type t t0).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst.
unfold same_env in *.
symmetry in Heqo0.  specialize (H5 _ _ Heqo0).
destruct H5. simpl in *. unfold Map.get. rewrite H4.
unfold typecheck_glob_environ in *. destruct (H3 i _ Heqo0).
rewrite H5.
unfold tc_val; unfold is_pointer_type in H1;
 destruct pt; try solve [inv H1; reflexivity].
 simple_if_tac; apply I.
destruct H4; congruence. inv H0.
inv H0.
}
Qed.

Lemma typecheck_expr_sound_Efield:
  forall {CS: compspecs} Delta rho e i t m
  (H: typecheck_environ Delta rho)
  (IHe: (denote_tc_assert (typecheck_expr Delta e) rho m ->
          tc_val (typeof e) (eval_expr e rho)) /\
          (forall pt : type,
          denote_tc_assert (typecheck_lvalue Delta e) rho m ->
          is_pointer_type pt = true ->
          tc_val pt (eval_lvalue e rho)))
  (H0: denote_tc_assert (typecheck_expr Delta (Efield e i t)) rho m),
  tc_val (typeof (Efield e i t)) (eval_expr (Efield e i t) rho).
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
assert (PTR := eval_lvalue_ptr _ _ e Delta te ve ge (eq_refl _) Hve Hge H0).
specialize (H2 t H0).
spec H2. clear - MODE; destruct t; try destruct i; try destruct s; try destruct f; inv MODE; simpl; auto.
destruct PTR.
destruct (typeof e); try now inv H3.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H3.
  destruct (field_offset cenv_cs i (co_members co)); try now inv H3.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H.
  destruct t; auto; try inversion H2.
  destruct f; inv H2.
  red. simple_if_tac; apply I.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H3.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H.
Qed.

Lemma typecheck_lvalue_sound_Efield:
 forall {CS: compspecs} Delta rho m e i t pt
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta e) rho m ->
          tc_val (typeof e) (eval_expr e rho)) /\
        (forall pt0 : type, denote_tc_assert (typecheck_lvalue Delta e) rho m ->
           is_pointer_type pt0 = true ->
         tc_val pt0 (eval_lvalue e rho)))
  (H0: denote_tc_assert (typecheck_lvalue Delta (Efield e i t)) rho m)
  (H1: is_pointer_type pt = true),
  tc_val pt (eval_lvalue (Efield e i t) rho).
Proof.
intros.
simpl in *.
rewrite denote_tc_assert_andp in H0. destruct H0.
super_unfold_lift.
 unfold eval_field,offset_val in *; intuition.
specialize  (H4 pt).
destruct rho.
unfold typecheck_environ in *. intuition.
assert (PTR := eval_lvalue_ptr _ m e _ te _ _ (eq_refl _) H H6 H0).
simpl in *.
remember (eval_lvalue e (mkEnviron ge ve te)). unfold isptr in *.
subst v.
destruct PTR as [b [ofs ?]].
destruct (typeof e); try now inv H2.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H2.
  destruct (field_offset cenv_cs i (co_members co)); try now inv H2.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H7.
  destruct pt; inv H1; auto.
  red; simple_if_tac; apply I.
+ destruct (cenv_cs ! i0) as [co |]; try now inv H2.
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H7.
Qed.

Lemma typecheck_expr_sound_Evar:
  forall {CS: compspecs} Delta rho m i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (Evar i t)) rho m ->
  tc_val (typeof (Evar i t)) (eval_expr (Evar i t) rho).
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
- remember (type_eq t t0). destruct s; intuition.
 subst. simpl in H0.
clear H0.
symmetry in Heqo.
specialize (H i t0).
destruct H as [H _]; specialize (H Heqo).
destruct H. unfold eval_var. simpl.
rewrite H in *. rewrite eqb_type_refl in *.
simpl. destruct t0; try destruct i0; try destruct s; try destruct f; inv MODE; simpl; auto.
- remember ((glob_types Delta) ! i). destruct o; [| inv H0].
simpl in *.
unfold eval_var in *.
super_unfold_lift. remember (eqb_type t t0).
symmetry in Heqb. destruct b; simpl in *; [| inv H0].
apply eqb_type_true in Heqb.
subst.
symmetry in Heqo0.  specialize (SM _ _ Heqo0).
destruct SM as [| [? ?]]; [| congruence].
unfold Map.get. rewrite H3.
unfold typecheck_glob_environ in *.
destruct (H2 _ _ Heqo0).
rewrite H4. destruct t0 as [| [| | |] [|] | | [|] | | | | |]; inv MODE; simpl; auto.
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

Lemma tc_val_of_bool_int_type:
 forall b t, is_int_type t = true ->
  tc_val t (Val.of_bool b).
Proof.
 intros.
 destruct t as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 try inv H; destruct b; simpl; try split; auto;
rewrite <- Z.leb_le; reflexivity.
Qed.

Lemma typecheck_unop_sound:
 forall {CS: compspecs} Delta rho m u e t
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta e) rho m ->
          tc_val (typeof e) (eval_expr e rho)) /\
          (forall pt : type,
           denote_tc_assert (typecheck_lvalue Delta e) rho m ->
           is_pointer_type pt = true ->
           tc_val pt (eval_lvalue e rho)))
  (H0: denote_tc_assert (typecheck_expr Delta (Eunop u e t)) rho m),
  tc_val t (eval_expr (Eunop u e t) rho).
Proof.
intros.
simpl in H0. rewrite denote_tc_assert_andp in H0. destruct H0.
destruct IHe as [? _].
specialize (H2 H1).
simpl eval_expr.
unfold_lift.
clear - H2 H0.
unfold eval_unop, sem_unary_operation, force_val1.
destruct u; unfold tc_val in H2; simpl in H0;
unfold sem_notbool, sem_notint, sem_neg, sem_absfloat, bool_val in *;
super_unfold_lift; simpl;
destruct (typeof e) as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 try contradiction;
 repeat match goal with
 | H:  app_pred (denote_tc_assert (tc_andp _ _) _) _ |- _ =>
        rewrite denote_tc_assert_andp in H; destruct H
 | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
      apply tc_bool_e in H
 | H: app_pred (denote_tc_assert (tc_int_or_ptr_type _) _) _ |- _ => 
      apply tc_bool_e in H
| H: (if eqb_type ?T1 ?T2 then _ else _) _ |- _ =>
   let J := fresh "J" in
   destruct (eqb_type T1 T2) eqn:J;
   [apply eqb_type_true in J | apply eqb_type_false in J]
end;
 destruct (eval_expr e rho) eqn:?; try contradiction;
 try discriminate;
 try solve [apply tc_val_of_bool_int_type; auto].
all: try solve [
  destruct t as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; 
  match goal with H: _ _ = true |- _ => inv H end;
            try reflexivity; auto;
             simpl tc_val; try split; auto;
             rewrite <- Z.leb_le; reflexivity].
Qed.

Lemma same_base_tc_val : forall v t1 t2,
same_base_type t1 t2 = true ->
tc_val t1 v ->
 tc_val t2 v.
Proof.
intros. destruct t1; destruct t2;
    try destruct f; try destruct f0; try destruct f1;
   unfold tc_val in *; 
 try match type of H0 with (if ?A then _ else _) _ => 
         destruct A eqn:?J;
         [apply  eqb_type_true in J | apply eqb_type_false in J]
    end;
   try solve [inv H]; destruct v; auto;
   try solve [inv H0];
   try solve [simple_if_tac; apply I].
   unfold same_base_type in H.
   destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type).
   apply I. inv H0. reflexivity.
   unfold same_base_type in H.
   destruct (eqb_type (Tpointer t2 a) int_or_ptr_type).
   apply I. inv H0. reflexivity.
Qed.

Lemma typecheck_temp_sound:
  forall {CS: compspecs} Delta rho m i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (Etempvar i t)) rho m ->
  tc_val (typeof (Etempvar i t)) (eval_expr (Etempvar i t) rho).
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
destruct p. destruct (H1 _ _ (eq_refl _)) as [v [? ?]]. clear H1.
rewrite H.
simpl in H0.
destruct (is_neutral_cast t0 t) eqn:?.
destruct b; inv H0;
intuition;
try solve [symmetry in Heqb0; eapply neutral_cast_subsumption; eauto].
simpl in H0. rewrite H in H0. inv H0.
auto.
destruct (same_base_type t0 t) eqn:?; [ | inv H0].
simpl in H0.
destruct b; inv H0;
intuition;
try solve [eapply same_base_tc_val; eauto].
simpl in H0. rewrite H in H0. inv H0.
auto.
Qed.

Lemma typecheck_deref_sound:
  forall {CS: compspecs} Delta rho m e t pt,
   typecheck_environ Delta rho ->
   (denote_tc_assert (typecheck_expr Delta e) rho m ->
    tc_val (typeof e) (eval_expr e rho)) /\
    (forall pt0 : type,
     denote_tc_assert (typecheck_lvalue Delta e) rho m ->
     is_pointer_type pt0 = true -> tc_val pt0 (eval_lvalue e rho)) ->
     denote_tc_assert (typecheck_lvalue Delta (Ederef e t)) rho m ->
    is_pointer_type pt = true ->
    tc_val pt (eval_lvalue (Ederef e t) rho).
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
destruct pt; try solve [inv H1; reflexivity].
unfold tc_val.
unfold is_pointer_type in H1.
destruct (eqb_type (Tpointer pt a) int_or_ptr_type); inv H1.
apply I.
Qed.

