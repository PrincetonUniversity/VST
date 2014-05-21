Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Require Export veric.environ_lemmas. 

Import Cop.
Import Cop2.

Opaque tc_andp. (* This is needed otherwise certain Qeds take
    forever in Coq 8.3.  *)

Lemma eval_lvalue_ptr : forall rho e (Delta: tycontext) te ve ge,
mkEnviron ge ve te = rho -> 
typecheck_var_environ ve (var_types Delta) -> 
typecheck_glob_environ ge (glob_types Delta) ->
denote_tc_assert (typecheck_lvalue Delta e) rho ->
eval_lvalue e rho = Vundef \/ exists base, exists ofs, eval_lvalue e rho  = Vptr base ofs.
Proof. 
intros.
induction e; eauto.
simpl. unfold eval_var. 
remember (Map.get (ve_of rho) i). destruct o; try rewrite eqb_type_eq; intuition;
try destruct p; try rewrite eqb_type_eq; simpl; try remember (type_eq t t0); try destruct s;
simpl; try remember (negb (type_is_volatile t0));try destruct b0; auto;
try solve[right; eauto].
remember (ge_of rho i); try rewrite eqb_type_eq; simpl.
destruct o; try rewrite eqb_type_eq; simpl; eauto.
destruct p; try rewrite eqb_type_eq; simpl; eauto.
if_tac; eauto.
unfold typecheck_var_environ in *. simpl in H2.
unfold get_var_type in *. 
remember ((var_types Delta) ! i).
destruct o. subst. simpl in H2.
super_unfold_lift.
try rewrite eqb_type_eq in *; simpl in *; intuition.
symmetry in Heqo1.
specialize (H0 i t1 Heqo1).
destruct H0. congruence.
remember ((glob_types Delta) ! i). destruct o; simpl in *; try congruence. 
super_unfold_lift. right. 
 unfold typecheck_glob_environ in H1.
symmetry in Heqo2. 
specialize (H1 _  _ Heqo2). destruct H1 as [b [? ?]].
rewrite <- H in *.  simpl ge_of in Heqo0. rewrite H1 in *.
inv Heqo0. eauto. inv H2. 



simpl in *. intuition. super_unfold_lift. unfold force_ptr in *. 
destruct (eval_expr e rho); eauto.

simpl in *. super_unfold_lift.
rewrite tc_andp_sound in *. simpl in *. 
super_unfold_lift. rewrite tc_andp_sound in *. 
simpl in *. super_unfold_lift.
destruct H2 as [[? ?] ?]. 
spec IHe; auto. destruct IHe. 
unfold eval_field.
destruct (eval_lvalue e rho); eauto;
destruct (typeof e); try congruence; auto.
destruct (field_offset i f); eauto.
unfold eval_field.
destruct (eval_lvalue e rho); eauto;
destruct (typeof e); try congruence; auto;
try destruct (field_offset i f); eauto.
destruct (field_offset i f0); eauto.
unfold offset_val; right; eauto.
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
  forall i t pt Delta rho, typecheck_environ Delta rho ->
           denote_tc_assert (typecheck_lvalue Delta (Evar i t)) rho ->
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
subst. remember (negb(type_is_volatile t0)).
rewrite tc_andp_sound in *. simpl in *. super_unfold_lift.
 destruct b; intuition. 
clear H3. symmetry in Heqo.
specialize (H i t0 Heqo).

{destruct H. 
rewrite H in *. rewrite <- Heqb. rewrite eqb_type_refl in *. destruct pt; auto.
}
{remember ((glob_types Delta) ! i). destruct o; try congruence.
rewrite tc_andp_sound in *.  simpl in *. 
simpl in *. super_unfold_lift. destruct H0. remember (eqb_type t (globtype g)).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst. 
unfold same_env in *. 
symmetry in Heqo0.  specialize (H5 _ _ Heqo0). 
destruct H5. simpl in *. unfold Map.get. rewrite H5. 
unfold typecheck_glob_environ in *. destruct (H3 i g); auto. destruct H6. 
rewrite H6. rewrite eqb_type_refl. auto.
destruct pt; inv H1; reflexivity.
destruct H5; congruence. inv H0.
inv H0.
} 
Qed.

Lemma typecheck_expr_sound_Efield:
  forall Delta rho e i t
  (H: typecheck_environ Delta rho)
  (IHe: (denote_tc_assert (typecheck_expr Delta e) rho ->
          typecheck_val (eval_expr e rho) (typeof e) = true) /\
          (forall pt : type,
          denote_tc_assert (typecheck_lvalue Delta e) rho ->
          is_pointer_type pt = true -> 
          typecheck_val (eval_lvalue e rho) pt = true))
  (H0: denote_tc_assert (typecheck_expr Delta (Efield e i t)) rho),
  typecheck_val (eval_expr (Efield e i t) rho) (typeof (Efield e i t)) = true.
Proof.
intros.
simpl in *. super_unfold_lift.
 unfold eval_field, offset_val, deref_noload in *.
assert (MODE: access_mode t = By_reference) by (destruct (access_mode t); auto; hnf in H0; try contradiction).
rewrite MODE in *.
destruct IHe.
destruct rho.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift). 
simpl in H0.
super_unfold_lift. destruct H0 as [[?  ]?].
revert H4; case_eq (type_is_volatile t); simpl; intros; try contradiction.
clear H5.
unfold typecheck_environ in H. 
destruct H as [_ [Hve [Hge _]]]. 
assert (PTR := eval_lvalue_ptr _ e Delta te ve ge (eq_refl _) Hve Hge H0).
specialize (H2 t H0).
spec H2. clear - MODE; destruct t; try destruct i; try destruct s; try destruct f; inv MODE; simpl; auto.
destruct PTR.
elimtype False; clear - H H2. rewrite H in H2; inv H2.
destruct H as [b [ofs ?]]. 
rewrite H in *.
destruct (typeof e); intuition. 
destruct (field_offset i f); intuition.
Qed.

Lemma typecheck_lvalue_sound_Efield:
 forall Delta rho e i t pt
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta e) rho ->
          typecheck_val (eval_expr e rho) (typeof e) = true) /\
        (forall pt0 : type, denote_tc_assert (typecheck_lvalue Delta e) rho ->
           is_pointer_type pt0 = true -> 
         typecheck_val (eval_lvalue e rho) pt0 = true))
  (H0: denote_tc_assert (typecheck_lvalue Delta (Efield e i t)) rho)
  (H1: is_pointer_type pt = true),
  typecheck_val (eval_lvalue (Efield e i t) rho) pt = true.
Proof.
intros.
simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift.
 unfold eval_field,offset_val in *; intuition. 
specialize  (H3 pt). intuition. remember rho.
destruct e0.
unfold typecheck_environ in *. intuition. clear H4 H9.
rewrite Heqe0 in H0.
assert (PTR := eval_lvalue_ptr _ e _ _ _ _ Heqe0 H H7).
rewrite Heqe0 in *. clear Heqe0.
intuition. 
remember (eval_lvalue e rho). unfold isptr in *.
destruct v; intuition; try congruence.
remember (eval_lvalue e rho). destruct H8. destruct H4.
destruct v; intuition; try congruence.
inv H4.
destruct (typeof e); intuition. 
destruct (field_offset i f); intuition.
Qed.

Lemma typecheck_expr_sound_Evar:
  forall Delta rho i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (Evar i t)) rho ->
  typecheck_val (eval_expr (Evar i t) rho) (typeof (Evar i t)) = true.
Proof.
intros.
assert (MODE: access_mode t = By_reference)
 by (unfold typecheck_expr in H0; destruct (access_mode t); try (hnf in H0; contradiction); auto).
simpl. super_unfold_lift. unfold deref_noload. rewrite MODE.

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
remember (negb(type_is_volatile t0)). destruct b; intuition. 
clear H0. 
symmetry in Heqo. 
specialize (H i t0 Heqo).
destruct H. unfold eval_var. simpl. 
rewrite H in *. rewrite <- Heqb. rewrite eqb_type_refl in *.
simpl. destruct t0; try destruct i0; try destruct s; try destruct f; inv MODE; auto.
remember ((glob_types Delta) ! i). destruct o; try congruence. 
simpl in *.
rewrite tc_andp_sound in *. simpl in *. 
unfold eval_var in *. 
 super_unfold_lift. destruct H0. remember (eqb_type t (globtype g)).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst. 
symmetry in Heqo0.  specialize (SM _ _ Heqo0). 
destruct SM. 
unfold Map.get. rewrite H4. 
unfold typecheck_glob_environ in *. 
destruct (H2 i g); auto. destruct H5. 
rewrite H5. rewrite eqb_type_refl. auto. destruct H4; congruence.
inv H0. inv H0. 
Qed.

Lemma typecheck_unop_sound:
 forall Delta rho u e t
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta e) rho ->
          typecheck_val (eval_expr e rho) (typeof e) = true) /\
          (forall pt : type,
           denote_tc_assert (typecheck_lvalue Delta e) rho ->
           is_pointer_type pt = true -> 
           typecheck_val (eval_lvalue e rho) pt = true))
  (H0: denote_tc_assert (typecheck_expr Delta (Eunop u e t)) rho),
  typecheck_val (eval_expr (Eunop u e t) rho) (typeof (Eunop u e t)) = true.
Proof.
intros.
simpl in H0. rewrite denote_tc_assert_andp in H0. destruct H0.
destruct IHe as [? _].
specialize (H2 H1).
simpl eval_expr.
unfold_lift.
clear - H2 H0.
revert H0; case_eq (isUnOpResultType u e t); intros; [ | inv H0].
clear H0.
simpl.
forget (eval_expr e rho) as v.
clear - H2 H.
assert (TV: forall b i s a, typecheck_val (Val.of_bool b) (Tint i s a) = true)
  by (destruct b; reflexivity).
unfold isUnOpResultType in H.
unfold eval_unop, sem_unary_operation, force_val1.
unfold classify_bool in H.
destruct u; try solve [inv H]; simpl.
(* notbool case *)
assert (is_int_type t = true) 
  by (destruct (typeof e); try destruct i,s; inv H; auto).
destruct t;  inv H0.
unfold sem_notbool.
destruct (typeof e), v; inv H2; try destruct i0,s0; simpl; inv H; try rewrite H1; auto.
(* notint case *)
unfold sem_notint.
destruct (typeof e), v; inv H; inv H2; simpl; auto.
destruct i,s; destruct t; inv H1; simpl; auto.
(* neg case *)
unfold sem_neg; simpl.
destruct (typeof e); inv H.
destruct v; inv H2.
destruct i,s; inv H1; simpl; destruct t; try inv H0; auto.
destruct v; inv H2.
destruct f; inv H1; simpl; destruct t; try inv H0; auto.
(* absfloat case *)
unfold sem_absfloat.
destruct (classify_neg (typeof e)) eqn:H3; try discriminate;
destruct t; inv H.
destruct (typeof e); inv H3; destruct v; inv H2; reflexivity.
destruct (typeof e); inv H3; destruct v; inv H2; try reflexivity.
destruct i; try destruct s; inv H0.
destruct (typeof e); inv H3; destruct v; inv H2; try reflexivity.
destruct i; try destruct s0; inv H0.
Qed.

Lemma same_base_tc_val : forall v t1 t2,
same_base_type t1 t2 = true ->
typecheck_val v t1 = typecheck_val v t2.
Proof.
intros. destruct v; destruct t1; destruct t2; try solve [inv H]; auto.
Qed.

Lemma typecheck_temp_sound:
  forall Delta rho i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (Etempvar i t)) rho ->
  typecheck_val (eval_expr (Etempvar i t) rho) (typeof (Etempvar i t)) = true.
Proof.
intros.
simpl in *. destruct rho. 
destruct H as [H1 _].
unfold typecheck_temp_environ in *.
unfold eval_id, force_val in *. 

simpl.
destruct Delta as [[[? ?] ?] ?]. simpl in *.
unfold temp_types in *. simpl in *.
specialize (H1 i).
destruct (type_is_volatile t); simpl in H0; unfold lift in H0; try contradiction.
destruct (t0 ! i); try (contradiction H0).
destruct p. destruct (H1 _ _ (eq_refl _)) as [v [? ?]]. clear H1.
rewrite H.
simpl in H0.
remember (same_base_type t t4).
destruct b0; [ | inv H0].

simpl in H0.
destruct b; inv H0;
intuition;
erewrite same_base_tc_val; eauto.
simpl in H0. rewrite H in H0. inv H0.
erewrite <- same_base_tc_val; eauto.
destruct (typecheck_val x t); try contradiction; auto.
Qed.

Lemma typecheck_deref_sound:
  forall Delta rho e t pt,
   typecheck_environ Delta rho ->
   (denote_tc_assert (typecheck_expr Delta e) rho ->
    typecheck_val (eval_expr e rho) (typeof e) = true) /\
    (forall pt0 : type,
     denote_tc_assert (typecheck_lvalue Delta e) rho ->
     is_pointer_type pt0 = true -> typecheck_val (eval_lvalue e rho) pt0 = true) ->
     denote_tc_assert (typecheck_lvalue Delta (Ederef e t)) rho ->
    is_pointer_type pt = true ->
    typecheck_val (eval_lvalue (Ederef e t) rho) pt = true.
Proof.
intros until pt. intros H IHe H0 H1.
simpl. unfold lift.
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0 as [[[? ?] ?] ?].
destruct IHe as[ ? _].
specialize (H5 H0).
revert H2; case_eq (is_pointer_type (typeof e)); intros; hnf in H2; try contradiction.
clear H H6 H4.
hnf in H3. unfold_lift in H3; hnf in H3.
unfold_lift.
destruct (eval_expr e rho); try contradiction.
destruct pt; inv H1; reflexivity.
Qed.

