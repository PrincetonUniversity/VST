Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Require Export veric.environ_lemmas. 
Require Import veric.binop_lemmas. 
Import Cop.
Import Cop2.

Opaque tc_andp. (* This is needed otherwise certain Qeds take
    forever in Coq 8.3.  *)

(** Definitions of some environments **)
Definition empty_genv := (Globalenvs.Genv.empty_genv fundef type).
Definition empty_tenv := PTree.empty val.

Definition empty_environ : environ :=
mkEnviron (filter_genv empty_genv) (Map.empty _) (Map.empty _).

Definition Delta1 : tycontext := (PTree.set 1%positive (type_int32s, false) 
                                 (PTree.empty (type * bool)),
                                 PTree.empty type, Tvoid,PTree.empty _).

(*
Lemma Zlt_bool_rev: forall x y, Zlt_bool x y = Zgt_bool y x.
Proof.
intros. pose proof (Zlt_cases x y). pose proof (Zgt_cases y x).
destruct (Zlt_bool x y); destruct (Zgt_bool y x); auto;
elimtype False; omega.
Qed.
*)

Lemma Zle_bool_rev: forall x y, Zle_bool x y = Zge_bool y x.
Proof.
intros. pose proof (Zle_cases x y). pose proof (Zge_cases y x).
destruct (Zle_bool x y); destruct (Zge_bool y x); auto;
elimtype False; omega.
Qed.

(*
Lemma Zlt_bool_opp: forall x y, Zlt_bool x y = negb (Zge_bool x y).
Proof.
intros. pose proof (Zlt_cases x y). pose proof (Zge_cases x y).
destruct (Zlt_bool x y); destruct (Zge_bool x y); auto.
elimtype False; omega.
Qed.

Lemma Zgt_bool_opp: forall x y, Zgt_bool x y = negb (Zle_bool x y).
Proof.
intros. pose proof (Zgt_cases x y). pose proof (Zle_cases x y).
destruct (Zgt_bool x y); destruct (Zle_bool x y); auto.
elimtype False; omega.
Qed.
*)

Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.

(** Typechecking soundness **)

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
specialize (H1 _  _ Heqo2). destruct H1 as [b [i0 [? ?]]].
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
 

Transparent Float.intoffloat.
Transparent Float.intuoffloat.

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
unfold typecheck_glob_environ in *. destruct (H3 i g); auto. destruct H6. destruct H6. 
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
destruct (H2 i g); auto. destruct H5; destruct H5. 
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
unfold eval_unop, sem_unary_operation.
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
Qed.


Lemma isCastR: forall tfrom tto ty a, 
  denote_tc_assert (isCastResultType tfrom tto ty a) =
 denote_tc_assert
match Cop.classify_cast tfrom tto with
| Cop.cast_case_default => tc_FF  (invalid_cast tfrom tto)
| Cop.cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed) 
| Cop.cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_neutral  => if eqb_type tfrom ty then tc_TT else 
                            (if orb  (andb (is_pointer_type ty) (is_pointer_type tfrom)) (andb (is_int_type ty) (is_int_type tfrom)) then tc_TT
                                else tc_iszero' a)
| Cop.cast_case_void => tc_noproof
| _ => match tto with 
      | Tint _ _ _  => tc_bool (is_int_type ty) (invalid_cast_result tto ty) 
      | Tfloat _ _  => tc_bool (is_float_type ty) (invalid_cast_result tto ty) 
      | _ => tc_FF (invalid_cast tfrom tto)
      end
end.
Proof. intros; extensionality rho.
 unfold isCastResultType.
 destruct (classify_cast tfrom tto); auto.
 destruct (eqb_type tfrom ty); auto.
 if_tac; auto. apply denote_tc_assert_iszero.
Qed.

Lemma typecheck_cast_sound: 
 forall Delta rho e t,
 typecheck_environ Delta rho ->
(denote_tc_assert (typecheck_expr Delta e) rho ->
 typecheck_val (eval_expr e rho) (typeof e) = true) /\
(forall pt : type,
 denote_tc_assert (typecheck_lvalue Delta e) rho ->
 is_pointer_type pt = true -> typecheck_val (eval_lvalue e rho) pt = true) ->
denote_tc_assert (typecheck_expr Delta (Ecast e t)) rho ->
typecheck_val (eval_expr (Ecast e t) rho) (typeof (Ecast e t)) = true.
Proof.
intros until t; intros H IHe H0.
simpl in *. unfold_lift.
destruct IHe as [? _].
rewrite denote_tc_assert_andp in H0.
destruct H0.
specialize (H1 H0).
unfold eval_cast, sem_cast.
rewrite isCastR in H2.
revert H2; case_eq (classify_cast (typeof e) t); intros;
try solve [destruct t; try contradiction;
    destruct (eval_expr e rho), (typeof e); inv H2; inv  H1; simpl; auto; destruct i; inv H5].
remember (eval_expr e rho) as v.
destruct (typeof e), v, t; inv H1; inv H2; auto;
simpl in H3; unfold_lift in H3; try reflexivity;
try solve [hnf in H3; rewrite <- Heqv in H3;  apply H3];
try solve [destruct i,s; inv H4];
try solve [destruct i0; inv H4];
try solve [rewrite <- Heqv in H3; inv H3].
destruct si2.
rewrite denote_tc_assert_andp in H3. destruct H3.
hnf in H3,H4. unfold_lift in H3; unfold_lift in H4; hnf in H3,H4.
destruct (eval_expr e rho); try contradiction.
simpl. unfold Float.intoffloat. destruct (Float.Zoffloat f); try contradiction.
hnf in H3,H4. rewrite H3.
simpl. rewrite Zle_bool_rev. rewrite H4. simpl.
destruct (typeof e); inv H1.
 destruct t; inv H2; auto.
rewrite denote_tc_assert_andp in H3. destruct H3.
hnf in H3,H4. unfold_lift in H3; unfold_lift in H4; hnf in H3,H4.
destruct (eval_expr e rho); try contradiction.
simpl. unfold Float.intuoffloat. destruct (Float.Zoffloat f); try contradiction.
hnf in H3,H4. rewrite H3.
simpl. rewrite Zle_bool_rev. rewrite H4. simpl.
destruct (typeof e); inv H1.
 destruct t; inv H2; auto.
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

(** Main soundness result for the typechecker **)

Lemma typecheck_both_sound: 
  forall Delta rho e , 
             typecheck_environ Delta rho ->
             (denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr e rho) (typeof e) = true) /\
             (forall pt, 
             denote_tc_assert (typecheck_lvalue Delta e) rho ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue e rho) pt=true).
Proof.
intros. induction e; split; intros; try solve[subst; auto].

(*Const int*)
simpl. subst; destruct t; auto; simpl in H0; inv H0; intuition.

(*Const float*)
simpl in *. subst; destruct t; intuition. 

(*Var*)
eapply typecheck_expr_sound_Evar; eauto.
eapply typecheck_lvalue_Evar; eauto.

(*Temp*)
eapply typecheck_temp_sound; eauto.

(*deref*)  
eapply typecheck_deref_sound; eauto.
(*addrof*)
intuition.
simpl in *. 
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
destruct H0. 
destruct t; auto.

(*Unop*)
eapply typecheck_unop_sound; eauto.
(*binop*)
repeat rewrite andb_true_iff in *; intuition.
clear H4. clear H2. clear H.
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0 as [[H0 E1] E2].
apply (typecheck_binop_sound b Delta rho e1 e2 t H0 (H3 E2) (H1 E1)).

(* cast *)
eapply typecheck_cast_sound; eauto.

(*EField*)
eapply typecheck_expr_sound_Efield; eauto.
eapply typecheck_lvalue_sound_Efield; eauto.
Qed. 

Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ Delta rho -> 
              denote_tc_assert (typecheck_expr Delta e) rho ->
              tc_val (typeof e) (eval_expr e rho).
Proof. intros. 
rewrite tc_val_eq.
assert (TC := typecheck_both_sound Delta rho e). intuition. Qed.


Lemma typecheck_lvalue_sound : forall Delta rho e,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_lvalue Delta e) rho ->
  is_pointer_or_null (eval_lvalue e rho).
Proof.
intros.
 edestruct (typecheck_both_sound _ _ e H).
specialize (H2 (Tpointer Tvoid noattr) H0 (eq_refl _)).
assert (tc_val (Tpointer Tvoid noattr) (eval_lvalue e rho) = 
      (typecheck_val (eval_lvalue e rho) (Tpointer Tvoid noattr) = true)).
rewrite tc_val_eq; auto.
rewrite <- H3 in H2.
apply H2.
Qed.

Lemma get_typed_int:
    forall v att, typecheck_val v (Tint I32 Signed att) = true -> 
                      exists i:int, v = Vint i.
intros; destruct v; inv H; eauto.
Qed.

Definition is_ptr_type (ty: type) : bool :=
  match ty with
  | Tpointer _ _ => true
  | Tarray _ _ _ => true
  | Tfunction _ _ => true
  | Tstruct _ _ _ => true
  | Tunion _ _ _ => true
  | _ => false
end.

(*(*
Lemma tc_binaryop_nomem : forall b e1 e2 m1 m2 t rho,
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
sem_binary_operation b (typeof e1) (eval_expr e1 rho) (eval_expr e2 rho)
  (typeof e2) (m1) =
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m2).
Proof.
intros.
destruct b; simpl in *; auto;
 unfold sem_cmp; destruct (classify_cmp (typeof e1) (typeof e2));
   try destruct i; try destruct s; auto; try contradiction;
   rewrite tc_andp_sound in *; simpl in H; super_unfold_lift;
   ((intuition; unfold denote_tc_iszero in *));
 rewrite denote_tc_assert_orp in H0; repeat rewrite denote_tc_assert_iszero in H0;
  destruct H0.
* destruct (eval_expr e1 rho); try contradiction; auto.
* destruct (eval_expr e2 rho); try contradiction; auto.
* destruct (eval_expr e1 rho); try contradiction; auto.
* destruct (eval_expr e2 rho); try contradiction; auto.
Qed.
*)

Lemma tc_binaryop_relate : forall b e1 e2 m1 t rho,
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
Cop.sem_binary_operation b  (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m1) =
sem_binary_operation b (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho).
Proof.
intros.
destruct b; simpl in *; auto;
 unfold sem_cmp, Cop.sem_cmp; destruct (classify_cmp (typeof e1) (typeof e2));
   try destruct i; try destruct s; auto; try contradiction;
   try rewrite tc_andp_sound in *; simpl in H; super_unfold_lift;
   ((intuition; unfold denote_tc_iszero in *));
 rewrite denote_tc_assert_orp in H0; repeat rewrite denote_tc_assert_iszero in H0;
  destruct H0.
* destruct (eval_expr e1 rho); try contradiction; auto.
* destruct (eval_expr e2 rho); try contradiction; auto.
* destruct (eval_expr e1 rho); try contradiction; auto.
* destruct (eval_expr e2 rho); try contradiction; auto.
Qed.

Definition some_pt_type := Tpointer Tvoid noattr.

Lemma filter_genv_zero_ofs : forall ge ge2 b i t,
  filter_genv ge = ge2 ->
    (forall id, ge2 id = Some (Vptr b i, t) ->
      i = Int.zero).
Proof.
intros. unfold filter_genv in *. rewrite <- H in H0.
remember (Genv.find_symbol ge id). destruct o. 
destruct (type_of_global ge b0); inv H0; auto.
inv H0.
Qed.

Lemma typecheck_force_Some : forall ov t, typecheck_val (force_val ov) t = true
-> exists v, ov = Some v. 
Proof.
intros. destruct ov; destruct t; eauto; simpl in *; congruence. 
Qed. 


Lemma typecheck_binop_sound2:
 forall (Delta : tycontext) (rho : environ) (b : binary_operation)
     (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop b (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true. 
Proof. 
intros. 
pose proof (typecheck_binop_sound).
simpl in H4. unfold_lift in H4. eapply H4; eauto.
Qed. 

Lemma eval_binop_relate_fail :
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) (m : mem),
typecheck_environ  Delta rho ->
forall (ge : genv) te ve,
rho = construct_rho (filter_genv ge) ve te ->
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
denote_tc_assert (typecheck_expr Delta e1) rho ->
None =
sem_binary_operation b  (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho) ->
Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
Clight.eval_expr ge ve te m (Ebinop b e1 e2 t) Vundef.
Proof. 
intros. 
assert (TC1 := typecheck_expr_sound _ _ _ H H1).
assert (TC2 := typecheck_expr_sound _ _ _ H H3).
rewrite tc_val_eq in *.
copy H2.
rewrite den_isBinOpR in H7; simpl in H7.
eapply typecheck_binop_sound2 in H2; eauto.
remember (eval_expr e1 rho); remember (eval_expr e2 rho);
destruct v; destruct v0; 
try solve [apply typecheck_force_Some in H2; destruct H2;
try congruence].
Qed.
  
Opaque tc_andp.
(** Equivalence of CompCert eval_expr and our function eval_expr on programs that typecheck **)

Lemma ptr_compare_no_binop_tc : 
forall e1 e2 b1 i1 b2 i2 rho b t,
typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
Vptr b1 i1 = eval_expr e1 rho ->
Vptr b2 i2 = eval_expr e2 rho ->
true = is_comparison b ->
~denote_tc_assert (isBinOpResultType b e1 e2 t) rho.
Proof.
intros.
unfold not. intro.
rewrite <- H1 in *. rewrite <- H2 in *.
rewrite den_isBinOpR in *.
destruct b; inv H3;
remember (typeof e1); remember (typeof e2);
destruct t1; try solve[inv H0];
destruct t0; try solve[inv H];
simpl in H4;
try rewrite tc_andp_sound in *; simpl in *; super_unfold_lift;
try rewrite <- H1 in *; try rewrite <- H2 in *; intuition.

Qed.

Lemma eval_both_relate:
  forall Delta ge te ve rho e m, 
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight.eval_expr ge ve te m e  (eval_expr e rho))
           /\
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof. 
intros. generalize dependent ge. induction e; intros;
try solve[intuition; constructor; auto | subst; inv H1]; intuition.

(* var*)

assert (TC_Sound:= typecheck_expr_sound).
rewrite tc_val_eq in TC_Sound.
specialize (TC_Sound Delta rho (Evar i t) H0 H1).
simpl in TC_Sound|-*.
super_unfold_lift.
unfold deref_noload in TC_Sound|-*.
revert TC_Sound; case_eq (access_mode t); intros; try solve [inv TC_Sound].
rename H2 into MODE.

simpl in *. rewrite MODE in H1.
unfold get_var_type, eval_var in *. 
remember (Map.get (ve_of rho) i); destruct o; try destruct p; 
try rewrite eqb_type_eq in *; simpl in *.
destruct (type_eq t t0); simpl in *; intuition.
subst t0. if_tac; intuition.
apply Clight.eval_Elvalue with b Int.zero;
  [ | constructor; simpl; rewrite MODE; auto].
apply eval_Evar_local.
subst rho.
simpl in Heqo. symmetry in Heqo; apply Heqo.
subst rho. 
unfold typecheck_environ in *. 
destruct H0 as [? [Hve [Hge _]]].
hnf in Hve,Hge.
revert H1; case_eq ((var_types Delta) ! i); intros; try contradiction.
destruct (Hve _ _ H0). simpl in *; congruence.
revert H1; case_eq ((glob_types Delta) ! i); intros; try contradiction.
destruct (Hge _ _ H1) as [b [ofs [? ?]]].
simpl. simpl in H3. 
rewrite H3.

repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
destruct H2. unfold tc_bool in H2.
if_tac in H2; try contradiction.
apply Clight.eval_Elvalue with b ofs; [  | econstructor 2; apply MODE].
assert (ZO := filter_genv_zero_ofs _ _ _ _ _ (eq_refl _) _ H3).  subst.
apply Clight.eval_Evar_global.
symmetry in Heqo; apply Heqo.
unfold filter_genv in *. invSome. destruct (type_of_global ge b0); inv H8; auto. 

unfold filter_genv in *.  
remember (Genv.find_symbol ge i). 
destruct o; try congruence. 
assert (b = b0). clear - Heqo0 H3. rename H3 into H4. 
destruct (type_of_global ge b0); inv H4; auto. 
subst. 
remember (type_of_global ge b0). 
destruct o; try congruence. inv H3. 
remember (eqb_type t (globtype g)). destruct b.
symmetry in Heqb. apply eqb_type_true in Heqb. auto. 
destruct t; inv TC_Sound.  inv H3. rewrite <- H7 in H4; inv H4. 

assert (TC_Sound:= typecheck_lvalue_sound).
specialize (TC_Sound Delta rho (Evar i t) H0 H1).
 
simpl in *. unfold eval_var in *. 
remember (Map.get (ve_of rho) i); destruct o; try destruct p; 
try rewrite eqb_type_eq in *; simpl in *.
destruct (type_eq t t0); simpl in *; intuition.
subst t0. if_tac; intuition.
exists b. exists Int.zero. intuition. constructor.
unfold Map.get in Heqo. unfold construct_rho in *.
destruct rho; inv H; simpl in *;  auto. 

remember (ge_of rho i). destruct o; try destruct p; auto;
try rewrite eqb_type_eq in *; simpl in *; intuition.
destruct (type_eq t t0); simpl in *. subst t0.

unfold get_var_type in *. 
remember ((var_types Delta) ! i). 
destruct o; try rewrite eqb_type_eq in *; simpl in *; super_unfold_lift; intuition.
destruct (type_eq t t0); simpl in *; [ | contradiction]. subst t0.
symmetry in Heqo1.
destruct rho.  
unfold typecheck_environ in *. 
intuition. clear H2 H5. 
unfold typecheck_var_environ, typecheck_glob_environ in *. 
specialize (H0 i t Heqo1). unfold ge_of in *. unfold Map.get in *. 
destruct H0. congruence.

destruct rho. 
unfold typecheck_environ in *; intuition. clear H2 H0 H5. 
unfold typecheck_glob_environ in *. 
remember ((glob_types Delta) ! i). destruct o; simpl in H1; try congruence.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift. destruct H1. 
rename H3 into H4. 
symmetry in Heqo2. specialize (H4 _ _ Heqo2).  destruct H4. destruct H2. 
destruct H2. simpl in Heqo0. rewrite H2 in *. inv Heqo0. exists x. exists x0. split; auto. 
unfold construct_rho in *. inv H. simpl in Heqo. clear H1. 
remember (filter_genv ge). symmetry in Heqg0. 
assert (ZO := filter_genv_zero_ofs _ _ _ _ _ Heqg0 _ H2).  subst.
apply Clight.eval_Evar_global. auto.  unfold filter_genv in H2.
destruct (Genv.find_symbol ge i). destruct (type_of_global ge b); inv H2; auto. 
congruence.  

unfold filter_genv in H2.
remember (Genv.find_symbol ge i).  destruct o; try congruence.  
assert (x = b). destruct (type_of_global ge b); inv H2; auto. subst.
destruct (type_of_global ge b). inv H2; auto. inv H2. rewrite <- H1 in *. simpl in *.
congruence. 
intuition. contradiction.

(*temp*)  
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (Etempvar i t)). simpl in *. 
intuition.  
constructor. unfold eval_id in *. remember (Map.get (te_of rho)  i);
destruct o;  auto. destruct rho; inv H; unfold make_tenv in *.
unfold Map.get in *. auto. 
simpl in *. destruct t; contradiction H3.

(*deref*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). intuition. simpl in H1.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
intuition. simpl. super_unfold_lift; unfold_tc_denote.
 remember (eval_expr e rho); destruct v;
intuition. 
exists b. exists i. simpl in *. intuition. constructor.
auto.

(*addrof*)

simpl in H1. 
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift.
assert (ISPTR := eval_lvalue_ptr rho e Delta (te_of rho) (ve_of rho) (ge_of rho)).
specialize (IHe ge).
assert (mkEnviron (ge_of rho) (ve_of rho) (te_of rho) = rho). destruct rho; auto.
destruct rho. unfold typecheck_environ in *. intuition. 
simpl. destruct H10. destruct H9. intuition. congruence. 
destruct H10. destruct H9. destruct H6. destruct H6. destruct H9.  simpl in *.
intuition. rewrite H6 in *. constructor. inv H10. auto.

(*unop*)
simpl in *. 
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
unfold eval_unop in *. intuition. unfold force_val. 
remember (sem_unary_operation u (typeof e) (eval_expr e rho)).
destruct o. eapply Clight.eval_Eunop. eapply IHe; eauto. rewrite Heqo. auto.
apply typecheck_expr_sound in H3; auto. unfold sem_unary_operation in *.
destruct u. simpl in *. remember (typeof e); destruct t0; try inv H2;
try destruct i;try destruct s; try inv H2; simpl in *; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_notbool in *;
simpl in *; inv Heqo. 

simpl in *. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inversion H3; simpl in *; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_notint in *;
simpl in *; inv Heqo. 

simpl in *. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inversion H3; simpl in *; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_neg in *;
simpl in *; inv Heqo.

(*binop*)
simpl in *. 
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
unfold eval_binop in *; super_unfold_lift; intuition. unfold force_val.
remember (sem_binary_operation b (typeof e1) (typeof e2)(eval_expr e1 rho) (eval_expr e2 rho)).
{ destruct o. 
  + eapply Clight.eval_Ebinop. eapply IHe1; eauto.
    eapply IHe2. apply H. apply H3.

    remember (eval_expr e1 rho); remember (eval_expr e2 rho);
    destruct v0; destruct v1; simpl;
    rewrite Heqv0 at 1; rewrite Heqv1;
    rewrite Heqv0 in Heqo at 1;
    rewrite Heqv1 in Heqo;
    try rewrite Heqo;
    try apply tc_binaryop_relate with (t:=t); auto.
    
  + specialize (IHe1 ge). specialize (IHe2 ge). intuition.
         clear H6 H8. 
    remember (eval_expr e1 rho). remember (eval_expr e2 rho).
         destruct v; destruct v0; 
         rewrite Heqv in Heqo at 1, H7;
         rewrite Heqv0 in Heqo, H2;
         try eapply eval_binop_relate_fail; eauto.
}


(*Cast*) {
assert (TC := typecheck_expr_sound _ _ _ H0 H1).
rewrite tc_val_eq in TC.
simpl in *; 
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
unfold eval_cast in *; super_unfold_lift; intuition.
eapply Clight.eval_Ecast.
eapply IHe; auto.
unfold sem_cast, Cop.sem_cast.
remember (classify_cast (typeof e) t) as o; destruct o;
 destruct (eval_expr e rho); inv TC; try reflexivity;
 try solve [destruct (ident_eq id1 id2); inv H4; destruct (fieldlist_eq fld1 fld2); inv H1; 
   (reflexivity || destruct t; inv H4; destruct (typeof e); try destruct i0; inv Heqo)].
simpl; destruct (cast_float_int si2 f); inv H4; reflexivity.
simpl; destruct (cast_float_long si2 f); inv H4; reflexivity.
simpl; destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H4; reflexivity.
simpl; destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H4; reflexivity.
}
(*Field*)
specialize (IHe ge H). assert (TC := typecheck_expr_sound _ _ _ H0 H1). 
simpl in H1. remember (access_mode t). destruct m0; try solve [inv H1]. repeat rewrite tc_andp_sound in *. 
simpl in H1. 
repeat( try rewrite tc_andp_sound in *; simpl in *; super_unfold_lift). 
destruct H1. destruct H1.
destruct IHe. specialize (H5 H1). destruct H5 as [b [ofs H5]]. 
destruct H5. 
 remember (typeof e). 
destruct t0; try solve[inv H3]. remember (field_offset i f). destruct r; inv H3. simpl in *. rewrite <- Heqr in *.
unfold deref_noload in *. rewrite <- Heqm0 in *. 
eapply Clight.eval_Elvalue; eauto. 
eapply Clight.eval_Efield_struct; eauto. 
eapply Clight.eval_Elvalue; auto. apply H5.
rewrite <- Heqt0.
apply Clight.deref_loc_copy. auto. simpl. 
rewrite H6. apply Clight.deref_loc_reference. auto. 

unfold deref_noload. rewrite <- Heqm0. simpl. 
eapply Clight.eval_Elvalue; eauto.
eapply Clight.eval_Efield_union. 
eapply Clight.eval_Elvalue; eauto.
apply Clight.deref_loc_copy. 
rewrite <- Heqt0. auto. eauto.
simpl. rewrite H6. simpl. apply Clight.deref_loc_reference; auto. 

assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). intuition. simpl in H1. 
simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 unfold eval_field,offset_val in *; super_unfold_lift; remember (eval_lvalue e rho).
destruct H1. destruct H1. specialize (H4 H1).
destruct H4 as [b [ofs H4]].
remember (typeof e) as t0. destruct t0; intuition.
remember (field_offset i f) as r.
destruct r; intuition.
 destruct v; intuition. simpl in *. exists b. exists (Int.add ofs (Int.repr z)). 
intuition. inv H7.
 eapply Clight.eval_Efield_struct; auto.
eapply Clight.eval_Elvalue in H6. apply H6.
rewrite <- Heqt0. auto. apply Clight.deref_loc_copy. simpl; auto.
rewrite <- Heqt0; reflexivity. auto.
inv H7; auto.
subst v.
exists b, ofs. rewrite H7. simpl. split; auto.
eapply Clight.eval_Efield_union; eauto.
eapply Clight.eval_Elvalue; eauto.
rewrite <- Heqt0. apply Clight.deref_loc_copy.
auto. 
Qed. 

Lemma eval_expr_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ  Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight.eval_expr ge ve te m e  (eval_expr e rho)).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.



Lemma eval_lvalue_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te->
           typecheck_environ  Delta rho ->
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
apply eval_both_relate.
Qed.

Lemma tc_lvalue_nonvol : forall rho Delta e,
(denote_tc_assert (typecheck_lvalue Delta e) rho) ->
type_is_volatile (typeof e) = false.
Proof.
intros.
destruct e; intuition; simpl in *. 
unfold get_var_type in *. 

destruct ((var_types Delta) ! i); intuition; simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 super_unfold_lift;
intuition. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; simpl in *; super_unfold_lift; intuition.

super_unfold_lift; intuition. unfold tc_bool in *. rewrite if_negb in *.
destruct ((glob_types Delta) ! i). simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 super_unfold_lift. 
destruct H. if_tac in H0; auto; inv H0. inv H. 


repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift; intuition. clear - H1. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; intuition.

repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift. intuition. unfold tc_bool in *.  rewrite if_negb in *. 
if_tac in H1; auto. inv H1. 
Qed.

(*Proof for "backwards environment checking" that an environment that typechecks
must have come from an update on an environment that typechecks. 
TODO: These Lemmas
should eventually be put in more meaningful places in this file. *)

Lemma join_te_eqv :forall te1 te2 id b1 b2 t1,
te1 ! id = Some (t1, b1) -> te2 ! id = Some (t1, b2) ->
(join_te te1 te2) ! id = Some (t1,andb b1 b2).
Proof.
intros. 
unfold join_te. rewrite PTree.fold_spec. rewrite <- fold_left_rev_right.
assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto. 
assert (forall t, te1 ! id = Some t -> In (id, t) (rev (PTree.elements te1))).
intros. apply In_rev. rewrite rev_involutive. apply PTree.elements_correct.
auto.

induction (rev (PTree.elements te1)). simpl in *.
apply H2 in H. inv H.

simpl in *. destruct a. simpl in *. destruct p0. simpl.
remember (te2 ! p). destruct o. destruct p0.
(* destruct (eq_dec t t0).
 subst. *)
rewrite PTree.gsspec. if_tac. subst. specialize (H1 (t,b)).
spec H1; [solve [auto] | ].
inversion2  H H1.
rewrite H0 in Heqo; inv Heqo. auto.
apply IHl; auto.
intros. inversion2 H H4. specialize (H2 _ H).
destruct H2. inv H2. congruence.  auto.
apply IHl; auto; intros. rewrite H in *. inv H3. specialize (H2 (t1, b1)).
intuition. inv H2. congruence.
Qed.
 
Lemma temp_types_same_type : forall id i t b Delta,
(temp_types Delta) ! id = Some (t, b) ->
exists b0 : bool,
  (temp_types (initialized i Delta)) ! id = Some (t, b || b0).
Proof.
intros.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o.
destruct p. unfold temp_types in *. simpl. rewrite PTree.gsspec.
if_tac. subst. rewrite H in *. inv Heqo. exists true.   rewrite orb_true_r. 
eauto. exists false.   rewrite orb_false_r. eauto. exists false. rewrite orb_false_r. 
auto. 
Qed.

Lemma temp_types_update_dist : forall d1 d2 ,
(temp_types (join_tycon (d1) (d2))) =
join_te (temp_types (d1)) (temp_types (d2)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold temp_types. simpl. auto.
Qed.

Lemma var_types_update_dist : forall d1 d2 ,
(var_types (join_tycon (d1) (d2))) =
(var_types (d1)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold var_types. simpl. auto.
Qed. 

Lemma ret_type_update_dist : forall d1 d2, 
(ret_type (join_tycon (d1) (d2))) =
(ret_type (d1)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold var_types. simpl. auto.
Qed. 

Lemma glob_types_update_dist :
forall d1 d2, 
(glob_types (join_tycon (d1) (d2))) =
(glob_types (d1)).
Proof.
intros. destruct d1. destruct d2. destruct p. destruct p0. 
destruct p. destruct p0. simpl. auto.
Qed. 
 

Lemma var_types_update_tycon:
  forall c Delta, var_types (update_tycon Delta c) = var_types Delta
with
var_types_join_labeled : forall l Delta,
var_types (join_tycon_labeled l Delta) = var_types Delta.
Proof.
assert (forall i Delta, var_types (initialized i Delta) = var_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity. 
destruct c; intros; simpl; try reflexivity. 
apply H. 
destruct o. apply H. auto. 
rewrite var_types_update_tycon. apply var_types_update_tycon. 

rewrite var_types_update_dist. apply var_types_update_tycon. 
apply var_types_join_labeled. 

intros. destruct l. simpl. apply var_types_update_tycon. 
simpl. rewrite var_types_update_dist.  
rewrite var_types_update_tycon. reflexivity.  
 
Qed.
 
Lemma glob_types_update_tycon:
  forall c Delta, glob_types (update_tycon Delta c) = glob_types Delta
 with
glob_types_join_labeled : forall Delta e l,
glob_types (update_tycon Delta (Sswitch e l)) = glob_types Delta. 
Proof. 
clear glob_types_update_tycon.
assert (forall i Delta, glob_types (initialized i Delta) = glob_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity.  
induction c; intros; try apply H; try reflexivity. 
simpl. destruct o. apply H. auto. 
simpl. 
rewrite IHc2. 
auto. 

simpl.  rewrite glob_types_update_dist. auto. 

auto.

clear glob_types_join_labeled.
intros. simpl. 
destruct l. simpl. auto. 
simpl in *. rewrite glob_types_update_dist. 
auto. 
Qed. 

Ltac try_false :=
try  solve[exists false; rewrite orb_false_r; eauto]. 
 
Lemma update_tycon_te_same : forall c Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (update_tycon Delta c)) ! id = Some (t,b || b2)

with update_labeled_te_same : forall ls Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (join_tycon_labeled ls Delta)) ! id = Some (t,b || b2) .
Focus 1. 
destruct c; intros; simpl; try_false. 

simpl. eapply temp_types_same_type; eauto.

simpl. destruct o; eauto. simpl. eapply temp_types_same_type; eauto.
try_false; eauto. 

assert (forall (c : statement) (Delta : tycontext)
                         (id : positive) (t : type) (b : bool),
                       (temp_types Delta) ! id = Some (t, b) ->
                       exists b2 : bool,
                         (temp_types (update_tycon Delta c)) ! id =
                         Some (t, b || b2)) by auto.
edestruct update_tycon_te_same. apply H.
specialize (update_tycon_te_same c2 _ _ _ _ H1).
destruct (update_tycon_te_same). exists (x || x0). rewrite orb_assoc. eauto. 


simpl. rewrite temp_types_update_dist.

edestruct (update_tycon_te_same c1). apply H.
edestruct (update_tycon_te_same c2). apply H. 
erewrite join_te_eqv;
eauto. exists (x && x0). rewrite orb_andb_distrib_r.  auto.

apply update_labeled_te_same.  exact H.  (*these are the problem if it won't qed*) 

intros. destruct ls. simpl. eauto.
simpl. rewrite temp_types_update_dist.
edestruct update_tycon_te_same. apply H.
edestruct update_labeled_te_same. apply H.
exists (x && x0).  
erewrite join_te_eqv. rewrite <- orb_andb_distrib_r. auto. 
eauto. eauto. Qed. 


Lemma typecheck_environ_update_te:
  forall rho c Delta, typecheck_temp_environ (te_of rho) (temp_types (update_tycon Delta c)) 
     ->
typecheck_temp_environ  (te_of rho) (temp_types Delta)

with typecheck_ls_update_te : forall Delta ty b id l,
(temp_types Delta) ! id = Some (ty, b) -> 
exists b2, (temp_types (join_tycon_labeled l Delta)) ! id = Some (ty, b2).
Proof.
intros. 
unfold typecheck_temp_environ in H. unfold typecheck_temp_environ.  
destruct c; intros; simpl in *; try solve[eapply H; apply H0].

destruct (eq_dec id i). subst.
destruct (H i true ty). unfold initialized. rewrite H0. 
unfold temp_types. simpl. rewrite PTree.gsspec. rewrite peq_true. 
auto. destruct H1. destruct H2. inv H2. exists x. auto. 
apply H. 
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto.

destruct o.
destruct (eq_dec id i). subst. destruct (H i true ty).
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. inv H0. 
rewrite PTree.gsspec. rewrite peq_true. eauto. congruence.
destruct H1. destruct H2. inv H2. eauto. 
eapply H. unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto. eauto.


destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H1).
edestruct H. apply H2. destruct H3. exists x1. 
split. apply H3. destruct b. auto. auto. 


destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H0).
specialize (H id ((b || x) && (b || x0)) ty ).  
spec H.  
 unfold join_tycon. remember (update_tycon Delta c1).
destruct t. destruct p. destruct p. remember (update_tycon Delta c2).
destruct t3. destruct p. destruct p. unfold temp_types in *.
unfold update_tycon. simpl in *. 

apply join_te_eqv; eauto.    destruct b; auto. simpl in *.
destruct H. exists x1. split. destruct H. auto. left. auto. 

 edestruct (update_labeled_te_same l Delta id).  apply H0. 
 edestruct H. apply H1.  
destruct H2. exists x0. destruct b; auto. 

intros. destruct l; simpl in *.
destruct (update_tycon_te_same s _ _ _ _ H).
eauto.

 destruct (update_tycon_te_same s _ _ _ _ H).
edestruct typecheck_ls_update_te. apply H.
rewrite temp_types_update_dist. erewrite join_te_eqv; eauto.
Qed.

Lemma set_temp_ve : forall Delta i,
var_types (initialized i Delta) = var_types (Delta).
Proof.
intros. destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed. 

Lemma set_temp_ge : forall Delta i,
glob_types (initialized i Delta) = glob_types (Delta).
Proof.
intros. destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed. 

Lemma set_temp_ret : forall Delta i,
ret_type (initialized i Delta) = ret_type (Delta).
intros. 
destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed.


Lemma update_tycon_eqv_ve : forall Delta c id,
(var_types (update_tycon Delta c)) ! id = (var_types (Delta)) ! id

with update_le_eqv_ve : forall (l : labeled_statements) (id : positive) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = 
(var_types Delta) ! id.
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ve. auto.
destruct o. rewrite set_temp_ve. auto.
auto.
rewrite update_tycon_eqv_ve. apply update_tycon_eqv_ve.

rewrite var_types_update_dist.
rewrite update_tycon_eqv_ve. auto.

erewrite update_le_eqv_ve. auto.

intros. 
 destruct l. simpl in *. rewrite update_tycon_eqv_ve.
reflexivity.
 simpl in *. rewrite var_types_update_dist.
rewrite update_tycon_eqv_ve. auto.
Qed.

Lemma update_tycon_eqv_ret : forall Delta c,
(ret_type (update_tycon Delta c)) = (ret_type (Delta)) 

with update_le_eqv_ret : forall (l : labeled_statements)  Delta,
(ret_type (join_tycon_labeled l Delta)) = 
(ret_type Delta).
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ret. auto.
destruct o. rewrite set_temp_ret. auto.
auto.
rewrite update_tycon_eqv_ret. apply update_tycon_eqv_ret.

rewrite ret_type_update_dist.
rewrite update_tycon_eqv_ret. auto.

rewrite update_le_eqv_ret. auto.

intros. 
 destruct l. simpl in *. rewrite update_tycon_eqv_ret.
reflexivity.
 simpl in *. rewrite ret_type_update_dist.
rewrite update_tycon_eqv_ret. auto.
Qed.


Lemma update_tycon_same_ve : forall Delta c id v,
(var_types (update_tycon Delta c)) ! id = Some v <->
(var_types (Delta)) ! id = Some v


with update_le_same_ve : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = Some v <->
(var_types Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_ve in *; auto.
intros; split; intros;
rewrite update_le_eqv_ve in *; auto.
Qed.


Lemma update_tycon_eqv_ge : forall Delta c id,
(glob_types (update_tycon Delta c)) ! id = (glob_types (Delta)) ! id

with update_le_eqv_ge : forall (l : labeled_statements) (id : positive)  Delta,
(glob_types (join_tycon_labeled l Delta)) ! id =
(glob_types Delta) ! id. 
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ge. auto.
destruct o. rewrite set_temp_ge. auto.
auto.
rewrite update_tycon_eqv_ge. apply update_tycon_eqv_ge. 

rewrite glob_types_update_dist.
rewrite update_tycon_eqv_ge. auto.
erewrite update_le_eqv_ge. auto.

intros. 
 destruct l. simpl in *. rewrite update_tycon_eqv_ge.
auto. 
simpl in *. rewrite glob_types_update_dist.
rewrite update_tycon_eqv_ge. auto.
Qed.   

Lemma update_tycon_same_ge : forall Delta c id v,
(glob_types (update_tycon Delta c)) ! id = Some v <->
(glob_types (Delta)) ! id = Some v


with update_le_same_ge : forall (l : labeled_statements) (id : positive) (v : global_spec) Delta,
(glob_types (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_types Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_ge in *; auto.
intros; split; intros;
rewrite update_le_eqv_ge in *; auto.
Qed.    

Lemma typecheck_environ_update_ve : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_var_environ (ve_of rho) (var_types (update_tycon Delta c)) ->
typecheck_var_environ (ve_of rho) (var_types Delta).
Proof.
intros. 

destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ve in *; try apply H;
unfold typecheck_var_environ in *; intros; apply H; try rewrite var_types_update_dist; 
try apply join_ve_eqv;
repeat rewrite update_tycon_same_ve in *; try rewrite update_le_same_ve;
auto.
Qed. 



Lemma typecheck_environ_update_ge : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_glob_environ (ge_of rho) (glob_types (update_tycon Delta c)) ->
typecheck_glob_environ (ge_of rho) (glob_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ge in *; try apply H;
unfold typecheck_glob_environ in *; intros; apply H; try rewrite glob_types_update_dist; 
try apply join_ge_eqv;
repeat rewrite update_tycon_same_ge in *; try rewrite update_le_same_ge;
auto.
Qed. 

Lemma typecheck_environ_update:
  forall rho c Delta, typecheck_environ (update_tycon Delta c) rho ->
       typecheck_environ Delta rho.
Proof.
intros. unfold typecheck_environ in *. intuition. 
clear H H1 H3. unfold typecheck_temp_environ in *. 
eapply typecheck_environ_update_te; eauto.

clear -H. eapply typecheck_environ_update_ve; eauto. 

eapply typecheck_environ_update_ge.
eauto.  

clear - H3. 
unfold same_env in *. intros. 
specialize (H3 id t).
repeat rewrite update_tycon_same_ge in *. specialize (H3 H). 
destruct H3; auto. destruct H0. 
rewrite update_tycon_same_ve in *. eauto. 
Qed. 

Lemma typecheck_bool_val:
  forall v t, typecheck_val v t = true -> bool_type t = true ->
      exists b, strict_bool_val v t = Some b.
Proof.
intros.
destruct t; inv H0;
destruct v; inv H; simpl; try rewrite H1; eauto. 
Qed.

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite PTree.gsspec; auto.
Qed.

Lemma cop_2_sem_cast : forall t1 t2 e,
Cop.sem_cast (e) t1 t2 = Cop2.sem_cast t1 t2 e.
Proof.
intros.
destruct t1; destruct t2; destruct e; auto.
Qed.

Lemma cast_exists : forall Delta e2 t rho 
(TC: typecheck_environ Delta rho), 
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isCastResultType (typeof e2) t t e2)
  rho ->
sem_cast (typeof e2) t (eval_expr e2 rho)  =
Some (force_val (sem_cast (typeof e2) t (eval_expr e2 rho))).
Proof.
intros. 
assert (exists v, sem_cast (typeof e2) t (eval_expr e2 rho) = Some v).

apply typecheck_expr_sound in H.
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent Float.intoffloat.
Transparent Float.intuoffloat.
Transparent liftx.
destruct t; destruct v; destruct t0; simpl in *;
try congruence; try contradiction; eauto;
try solve [
unfold Float.intoffloat, Float.intuoffloat; repeat invSome;
inversion2 H1 H0; hnf in H2,H3; rewrite H3; rewrite Zle_bool_rev; rewrite H2;
simpl; eauto];
try solve [
try destruct i; try destruct s; try destruct i0; try destruct i1; try destruct s0; eauto |

destruct i; destruct s; super_unfold_lift; try solve[simpl in *; 
  super_unfold_lift;  unfold_tc_denote; destruct H0; 
try rewrite <- Heqv in *; 
unfold Float.intoffloat; 
destruct (Float.Zoffloat f0); try contradiction;
try rewrite H0; try rewrite H1; simpl; eauto | 
simpl in *;  unfold Float.intuoffloat; destruct H0;
unfold_tc_denote; try rewrite <- Heqv in *; destruct (Float.Zoffloat f0);
try rewrite H0; try rewrite H1; simpl; eauto; try contradiction] |

try destruct i0; try destruct i1; destruct s; simpl in *; try contradiction; try rewrite H; eauto ].

destruct i; destruct s; super_unfold_lift;
simpl in *; super_unfold_lift;
unfold Float.intoffloat, Float.intuoffloat;
try (
destruct H0 as [H0 H1]; hnf in H0,H1; rewrite <- Heqv in *;
destruct (Float.Zoffloat f0); try contradiction;
hnf in H0,H1; rewrite H0; rewrite Zle_bool_rev; rewrite H1;
simpl; eauto);
simpl; eauto.

auto.
Opaque Float.intoffloat.
Opaque Float.intuoffloat.
Opaque liftx.
destruct H1. rewrite H1. auto.
Qed.


Lemma eval_cast_sem_cast:
  forall v t t', eval_cast t t' v = force_val (sem_cast t t' v).
Proof.
unfold sem_cast, eval_cast, classify_cast.
intros.
pose (tx:=t); pose (t'x := t'); pose (v' := v).
destruct t,t'; simpl; try reflexivity;
try solve [destruct v; reflexivity];
try solve[ destruct i; try reflexivity; try solve [destruct v; reflexivity]];
try solve[ destruct i0; try reflexivity]; simpl.
destruct i0, s0, v; reflexivity.
destruct i,v; simpl; try reflexivity; destruct (cast_float_int s f0); reflexivity.
unfold eval_cast_f2f.
destruct v; try reflexivity.
simpl. destruct (cast_float_long s f0); reflexivity.
destruct v; simpl; try reflexivity.
destruct (ident_eq i i0 && fieldlist_eq f f0);  reflexivity.
destruct v; simpl; try reflexivity.
destruct (ident_eq i i0 && fieldlist_eq f f0);  reflexivity.
destruct i0,  v; reflexivity.
Qed.

Lemma sem_cast_eval_cast:
  forall v1 t1 t2 v,
  sem_cast t1 t2 v1  = Some v -> eval_cast t1 t2 v1 = v.
Proof.
intros.
rewrite eval_cast_sem_cast.
rewrite H; reflexivity.
Qed.

Lemma typecheck_val_eval_cast: 
  forall t2 e2 rho Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2 t2 e2) rho ->
      typecheck_val (eval_cast (typeof e2) t2 (eval_expr e2 rho)) t2 = true.
Proof. intros ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ H2 H5 H6).
assert (H8 := typecheck_expr_sound _ _ _ H2 H5).
rewrite tc_val_eq in H8.
clear - H7 H6 H8.
rewrite eval_cast_sem_cast. 
revert H7; case_eq (sem_cast (typeof e2) t2 (eval_expr e2 rho) ); intros; inv H7.
simpl.
rewrite isCastR in H6.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2; inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2); inv H2; inv H1; auto;
try (unfold sem_cast in H0; simpl in H0;
      destruct i0; simpl in*; destruct s; inv H0; simpl; auto);
 try solve [super_unfold_lift; unfold denote_tc_iszero in H6; rewrite H99 in *; contradiction].
simpl in *. super_unfold_lift. rewrite H99 in *. inv H6. auto.
simpl in *. super_unfold_lift. rewrite H99 in *. inv H6. auto.
simpl in *. unfold isCastResultType in H6. simpl in H6.
unfold sem_cast in H0. simpl in H0.
destruct i; simpl in*; destruct s; try destruct f; inv H0; simpl; auto;
invSome; simpl; auto.
Qed.

Definition func_tycontext_t_denote :=
forall p t id ty b,  list_norepet (map fst p ++ map fst t ) ->   
((make_tycontext_t p t) ! id = Some (ty,b) <-> (In (id,ty) p /\ b=true) \/ (In (id,ty) t /\ b=false)). 

Definition func_tycontext_v_denote :=
forall v id ty, list_norepet (map fst v) ->
((make_tycontext_v v) ! id = Some ty <-> In (id,ty) v). 

Lemma func_tycontext_v_sound : func_tycontext_v_denote. 
unfold func_tycontext_v_denote. intros. 
split; intros; induction v. simpl in *. 
rewrite PTree.gempty in *. congruence. 

simpl in *. destruct a. inv H. rewrite PTree.gsspec in *. if_tac in H0. 
inv H0. auto. intuition. 

inv H0.

simpl in *. destruct a. simpl in *. rewrite PTree.gsspec. destruct H0. 
inv H0. if_tac. auto. intuition. inv H. if_tac. subst. 
clear - H0 H3. rewrite in_map_iff in *. destruct H3. exists (i,ty). auto. 
apply IHv; auto. 
Qed. 
 

Lemma set_inside : forall i0 t1 t p id, 
list_disjoint (map fst p) (i0 :: map fst t) ->
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
          (PTree.set i0 (t1, false)
             (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p) ! id = 
(PTree.set i0 (t1, false) (
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
                (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p)) ! id       
. 
Proof.
intros.
induction t.  
  simpl in *. rewrite PTree.gsspec. 
  if_tac. 
    subst. 
    induction p. 
      simpl in *. rewrite PTree.gsspec. rewrite peq_true. auto.

      simpl in *. rewrite PTree.gsspec. if_tac. subst.
      clear - H. unfold list_disjoint in *. specialize (H (fst a) (fst a)). 
      intuition. apply IHp. unfold list_disjoint in *. intros. 
      apply H; simpl in *; auto.

    induction p. 
       simpl in *. rewrite PTree.gsspec. if_tac. intuition.
       auto. 

       simpl in *.  repeat rewrite PTree.gsspec in *. destruct a.
       simpl in *. if_tac. auto. rewrite IHp.  auto. unfold list_disjoint in *. 
       intros. apply H; simpl in *; auto. 

  simpl in *. rewrite PTree.gsspec in *. if_tac. 
    subst. 
    induction p. 
      simpl in *. rewrite PTree.gsspec in *. rewrite peq_true in *.
      auto.

      simpl in *. rewrite PTree.gsspec in *. destruct a0. simpl in *. 
      if_tac. subst. clear - H. specialize (H p0 p0). intuition.  apply IHp. 
      unfold list_disjoint in *. intros. apply H; simpl in *; auto. 
      intros. apply IHt. unfold list_disjoint in *. intros; simpl in *; apply H;      auto.
      auto. auto. intuition.  

    destruct a. simpl in *. induction p. 
      simpl in *. rewrite PTree.gsspec. if_tac; subst. intuition.
      repeat rewrite PTree.gsspec. auto.  

      simpl in *. destruct a. simpl in *. 
      spec IHt. unfold list_disjoint in *. intros; apply H; simpl in *; auto. 
      intuition. 
      repeat rewrite PTree.gsspec in *. if_tac.
        subst.  auto. 

        apply IHp. unfold list_disjoint in *.   intros. apply H. simpl in *. 
        auto.  auto. intros. auto. 
       
Qed.   

Lemma func_tycontext_t_sound : func_tycontext_t_denote. 
unfold func_tycontext_t_denote.
split; intros;
  unfold make_tycontext_t in *; 
  apply list_norepet_app in H; destruct H as [? [? ?]]. 
  induction t; induction p; simpl in *. 

    rewrite PTree.gempty in *; congruence. 

    left. destruct a; simpl in *. rewrite PTree.gsspec in *. if_tac in H0. 
    inv H0. auto.
    inv H.  destruct IHp; auto. unfold list_disjoint.  intros. inv H4. 
    destruct H. subst. auto. intuition.  

    right. destruct a. simpl in *. rewrite PTree.gsspec in *. 
    if_tac in H0. subst. inv H0. auto. destruct IHt. inv H1; auto. 
    unfold list_disjoint in *. intros. inv H4. auto. intuition. intuition. 


    simpl in *. rewrite PTree.gsspec in *. if_tac in H0. destruct a0. simpl in *.
    subst. inv H0. intuition. destruct a0. simpl in *.  destruct a. simpl in *. 
    destruct IHp. inv H; auto. intro; intros. apply H2; simpl in *; auto. 
    auto. intros. destruct IHt. inv H1; auto. intro; intros; apply H2; simpl in *; auto.
    auto. destruct H7. destruct H7. inv H7. intuition. auto. auto. left. 
    split. right. apply H4. apply H4. right. auto. 


  induction t; induction p; simpl in *. 
    
    intuition. 

    rewrite PTree.gsspec. if_tac. subst. destruct a. simpl in *. 
    destruct H0. destruct H0. destruct H0. inv H0. auto. subst. 
    clear - H H0. inv H. rewrite in_map_iff in *. destruct H3.
    exists (i,ty). auto. inv H0. inv H3. destruct H0. destruct H0. 
    destruct a. destruct H0. subst. inv H0. intuition.

    simpl in *. apply IHp. inv H; auto. intro. intros. inv H6. left.
    subst. auto. destruct H0. inv H0. destruct H0. destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct a. simpl in *. inv H0; subst. 
    rewrite PTree.gsspec. rewrite peq_true. auto. subst. 
    destruct a. simpl in *. rewrite PTree.gsspec. if_tac. 
    subst. clear -H0 H1. inv H1. rewrite in_map_iff in *. 
    destruct H3. exists (i,ty); auto. apply IHt. inv H1; auto. 
    intro; auto. right. auto. 
   
    spec IHt. inv H1; auto.  spec IHt. intro; intros; apply H2; simpl in *; auto.
    spec IHp.  inv H; auto. spec IHp. intro; intros; apply H2; simpl in *; auto. 
    destruct a. destruct a0. destruct H0. simpl in *.
    destruct H0. destruct H0. inv H0.  
    rewrite PTree.gsspec in *. rewrite peq_true. auto. subst. 
    rewrite PTree.gsspec in *. if_tac. subst. inv H. rewrite in_map_iff in H5. 
    destruct H5. exists (i0,ty); auto. spec IHp. auto. spec IHp; auto. 
    
    
    simpl in *. rewrite PTree.gsspec. if_tac. subst. destruct H0. destruct H0.
    inv H0. specialize (H2 i0 i0). destruct H2; simpl; auto. subst. 
    spec IHt. auto. rewrite PTree.gsspec in *. rewrite peq_true in *. auto. 
    
    destruct H0. destruct H0. inv H0. spec IHp. auto. 
    spec IHp; auto. intros; auto. destruct H5. destruct H5; congruence. destruct H5. 
    clear - H5 H1. inv H1. destruct H2. apply in_map_iff. exists (id, ty). auto. subst.
    spec IHp. auto. spec IHp; auto. spec IHt; auto. rewrite PTree.gsspec in *.
    if_tac in IHt. intuition. intros. auto. 

Qed. 

 Definition cast_no_val_change (from: type)(to:type) : bool :=
match from, to with
| Tint _ _ _, Tint I32 _ _ => true
| Tpointer _ _, Tpointer _ _ => true
| Tfloat _ _ , Tfloat F64 _ => true
| _, _ => false
end. 

Lemma cast_no_change : forall v from to,
is_true (typecheck_val v from)  ->
is_true (cast_no_val_change from to) ->
Cop.sem_cast v from to = Some v. 
Proof. 
intros. destruct v; destruct from; simpl in *; try congruence; destruct to; simpl in *; try congruence; auto; 
try destruct i1; try destruct f1; simpl in *; try congruence; auto.
Qed. 

Lemma tc_exprlist_length : forall Delta tl el rho, 
denote_tc_assert (typecheck_exprlist Delta tl el) rho ->
length tl = length el. 
Proof. 
intros. generalize dependent el. induction tl; intros. simpl in *. destruct el. inv H. auto. 
inv H. simpl in H. destruct el; try solve [inv H]. simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift.
intuition.
Qed. 

Lemma neutral_cast_typecheck_val : forall e t rho Delta,
true = is_neutral_cast (typeof e) t ->
denote_tc_assert (isCastResultType (typeof e) t t e) rho ->
denote_tc_assert (typecheck_expr Delta e) rho ->
typecheck_environ Delta rho ->
typecheck_val (eval_expr e rho) t = true. 
Proof.
intros.
rewrite isCastR in H0.
apply typecheck_expr_sound in H1; auto. rewrite tc_val_eq in H1.
destruct (typeof e); destruct t; simpl in H; simpl in H0;
try congruence; remember (eval_expr e rho); destruct v;
simpl in H0; try congruence; auto; 
destruct i; destruct s; try destruct i0; try destruct s0;
unfold is_neutral_cast in *;
simpl in *; try congruence; super_unfold_lift; 
try rewrite <- Heqv in *;  unfold denote_tc_iszero in *;
try apply H0; try contradiction.
Qed. 

Lemma allowed_val_cast_sound : forall v tfrom tto,
allowedValCast v tfrom tto = true -> 
typecheck_val v tfrom = true ->
typecheck_val v tto = true. 
Proof. 
intros. 
destruct v; destruct tfrom; destruct tto; try solve [simpl in *; try congruence]; auto;  first  [destruct i1 | destruct i0 | destruct i]; try destruct s; unfold allowedValCast in *; try solve [simpl in *; try congruence].
Qed.

Definition typecheck_tid_ptr_compare
Delta id := 
match (temp_types Delta) ! id with
| Some (t, _) =>
   is_int_type t 
| None => false
end. 

Lemma typecheck_tid_ptr_compare_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id, typecheck_tid_ptr_compare Delta id = true ->
                typecheck_tid_ptr_compare Delta' id = true.
Proof.
unfold typecheck_tid_ptr_compare;
intros.
destruct H as [? _].
specialize (H id).
destruct ((temp_types Delta) ! id) as [[? ?]|]; try discriminate.
destruct ((temp_types Delta') ! id) as [[? ?]|]; try contradiction.
 destruct H; subst; auto.
Qed.


Lemma tycontext_sub_refl:
 forall Delta, tycontext_sub Delta Delta.
Proof.
intros. destruct Delta as [[[T V] r] G].
unfold tycontext_sub.
intuition.
 + unfold sub_option. unfold temp_types. simpl. 
   destruct (T ! id) as [[? ?]|]; split; auto; destruct b; auto.
 + unfold sub_option, glob_types. simpl. 
   destruct (G ! id); auto.
Qed.


Lemma initialized_ne : forall Delta id1 id2,
id1 <> id2 ->
(temp_types Delta) ! id1 = (temp_types (initialized id2 Delta)) ! id1.

intros.
destruct Delta as [[[? ?] ?] ?]. unfold temp_types; simpl.
unfold initialized. simpl. unfold temp_types; simpl.
destruct (t ! id2). destruct p. simpl.  rewrite PTree.gso; auto.
auto.
Qed.

(*
Lemma initialized_sub_temp :
forall id Delta i Delta',
(forall id, sub_option (temp_types Delta) ! id (temp_types Delta') ! id) ->
 sub_option (temp_types (initialized i Delta)) ! id
     (temp_types (initialized i Delta')) ! id.
Proof.
intros.
   destruct (eq_dec id i).
     - subst. destruct Delta as [[[? ?] ?] ?].
       destruct Delta' as [[[? ?] ?] ?].
       unfold initialized, temp_types  in *. 
       simpl in *. specialize (H i). unfold sub_option in *.
       remember (t ! i). destruct o. 
         * destruct p. simpl in *.
           rewrite PTree.gss. rewrite H. simpl. rewrite PTree.gss.
           auto.
         * simpl. rewrite <- Heqo. auto.
     - repeat rewrite <- initialized_ne by auto. auto.
Qed.
*)

Lemma initialized_sub :
  forall Delta Delta' i ,
    tycontext_sub Delta Delta' ->
    tycontext_sub (initialized i Delta) (initialized i Delta').
Proof.
intros.
unfold tycontext_sub in *. 
destruct H as [? [? [? ?]]].
repeat split; intros.
 + specialize (H id); clear - H.
        destruct (eq_dec  i id).
        -  unfold initialized. subst.
           destruct ((temp_types Delta)!id) as [[? ?] |] eqn:?.
         unfold temp_types at 1; simpl; rewrite PTree.gss.
        destruct ((temp_types Delta')!id) as [[? ?] |]. destruct H; subst t0.
         unfold temp_types at 1. simpl. rewrite PTree.gss. auto. contradiction.
         rewrite Heqo. auto.
        -   rewrite <- initialized_ne by auto.
           destruct ((temp_types Delta)!id) as [[? ?] |] eqn:?; auto.
           rewrite <- initialized_ne by auto.
        destruct ((temp_types Delta')!id) as [[? ?] |]; [| contradiction].
         auto.
 + repeat rewrite set_temp_ve; auto.
 + repeat rewrite set_temp_ret; auto. 
 + repeat rewrite set_temp_ge; auto.
Qed.


Definition te_one_denote (v1 v2 : option (type * bool)):=
match v1, v2 with 
| Some (t1,b1),Some (t2, b2) =>  Some (t1, andb b1 b2)
| _, _ => None
end.

Lemma join_te_denote2:
forall d1 d2 id,
  ((join_te d1 d2) ! id) = te_one_denote (d1 ! id) (d2 ! id).
Proof.
intros. remember (d1 ! id). remember (d2 ! id).
destruct o; destruct o0.
   -  unfold te_one_denote. destruct p; destruct p0.
      remember (eqb_type t t0). destruct b1.
        + symmetry in Heqb1. apply eqb_type_true in Heqb1.
          subst. apply join_te_eqv; auto.
        + unfold join_te.
(* Print join_te'.
 rewrite PTree.fold_spec.
SearchAbout PTree.elements.
SearchAbout PTree.fold.
*)
Admitted.

Lemma tycontext_sub_join:
 forall Delta1 Delta2 Delta1' Delta2',
  tycontext_sub Delta1 Delta1' -> tycontext_sub Delta2 Delta2' ->
  tycontext_sub (join_tycon Delta1 Delta2) (join_tycon Delta1' Delta2').
Proof.
intros [[[A1 B1] C1] D1] [[[A2 B2] C2] D2] [[[A1' B1'] C1'] D1'] [[[A2' B2'] C2'] D2']
  [? [? [? ?]]] [? [? [? ?]]].
simpl in *.
unfold join_tycon.
split; [ | split; [ | split]]; simpl; auto.
intro id; specialize (H id); specialize (H3 id).
unfold temp_types in *.
simpl in *.
clear - H H3.
unfold sub_option in *.
repeat rewrite join_te_denote2.
unfold te_one_denote.
destruct (A1 ! id) as [[? b1] |].
destruct (A1' ! id) as [[? b1'] |]; [ | contradiction].
destruct H; subst t0.
destruct (A2 ! id) as [[? b2] |].
destruct (A2' ! id) as [[? b2'] |]; [ | contradiction].
destruct H3; subst t1.
split; auto. destruct b1,b1'; inv H0; simpl; auto.
destruct (A2' ! id) as [[? b2'] |]; split; auto.
auto.
Qed.

Lemma temp_types_same_type' : forall i (Delta: tycontext),
 (temp_types (initialized i Delta)) ! i =
  match (temp_types Delta) ! i with
   | Some (t, b) => Some (t, true)
  | None => None 
  end.
Proof.
intros.
unfold initialized.
destruct ((temp_types Delta) ! i) as [[? ?]|] eqn:?.
unfold temp_types at 1. simpl. rewrite PTree.gss. auto.
auto.
Qed.

Lemma update_tycon_sub:
  forall Delta Delta', tycontext_sub Delta Delta' ->
   forall h, tycontext_sub (update_tycon Delta h) (update_tycon Delta' h).
Proof.
intros.
destruct H as [? [? [? ?]]]. 
repeat split; intros; auto.  
 +  clear - H.
    generalize dependent Delta.
    revert h id Delta'.
    induction h; intros; try apply H; simpl; try destruct o;
     auto.
    -          destruct (eq_dec id i). subst.
        rewrite temp_types_same_type'.
        specialize (H i).
        destruct ((temp_types Delta) ! i) as [[? ?]|] eqn:?.
        rewrite temp_types_same_type'.
        destruct ((temp_types Delta') ! i) as [[? ?]|] eqn:?; [ | contradiction].
        destruct H; subst t0. split; auto. auto.
         specialize (H id).
          rewrite <- initialized_ne by auto. 
        destruct ((temp_types Delta) ! id) as [[? ?]|] eqn:?; auto.
          rewrite <- initialized_ne by auto. 
        destruct ((temp_types Delta') ! id) as [[? ?]|] eqn:?; auto.
  -  repeat rewrite temp_types_update_dist.
       specialize (H id).
        destruct (eq_dec id i). subst.
        rewrite temp_types_same_type'.
        destruct ((temp_types Delta) ! i) as [[? ?]|] eqn:?; auto.
        rewrite temp_types_same_type'.
        destruct ((temp_types Delta') ! i) as [[? ?]|] eqn:?; [ | contradiction].
        destruct H; subst t0. split; auto. auto.
          rewrite <- initialized_ne by auto. 
        destruct ((temp_types Delta) ! id) as [[? ?]|] eqn:?; auto.
          rewrite <- initialized_ne by auto. 
        destruct ((temp_types Delta') ! id) as [[? ?]|] eqn:?; auto.
  -
Admitted.


