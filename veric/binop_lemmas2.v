Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.Cop2.
Import Cop.
 
Lemma eval_expr_any:
  forall {CS: compspecs} rho e v,
    eval_expr e any_environ = v ->
    v <> Vundef ->
    eval_expr e rho = v
with eval_lvalue_any:
  forall {CS: compspecs} rho e v,
    eval_lvalue e any_environ = v ->
    v <> Vundef ->
    eval_lvalue e rho = v.   
Proof.
{ clear eval_expr_any.
 intros  ? ?.
 induction e; simpl; intros; subst; unfold_lift; try reflexivity;
 unfold_lift in H0;
 cbv delta [eval_unop eval_binop force_val2 force_val1 deref_noload always 
                 Datatypes.id deref_noload force_ptr force_val
                  eval_var eval_id
                 ] 
       in H0|-*; simpl in *;
 repeat match goal with
 | _ => reflexivity
 | |- match access_mode ?t with
                              | _ => _ end _ = _ => 
   destruct (access_mode t); simpl in *
 | |- context [match eval_expr ?e any_environ with _ => _ end] =>
          destruct (eval_expr e any_environ) eqn:?; try congruence;
          rewrite (IHe _ (eq_refl _)); auto
 | _ => try congruence
 end.
*  
 apply eval_lvalue_any; auto.
* destruct (eval_expr e any_environ) eqn:?; simpl in *;
  [elimtype False; apply H0; clear;
   try destruct u;
   destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try reflexivity
  | rewrite (IHe _ (eq_refl _)) by congruence; auto ..
  ].
*
  destruct (eval_expr e1 any_environ) eqn:?; simpl in *;
  [ elimtype False; apply H0; clear 
  | rewrite (IHe1 _ (eq_refl _)) by congruence; auto .. ].
 +destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try reflexivity; destruct (eval_expr e2 any_environ); reflexivity.
 +destruct (eval_expr e2 any_environ) eqn:?; simpl in *;
  [ elimtype False; apply H0; clear 
  | rewrite (IHe2 _ (eq_refl _)) by congruence; auto .. ].
   destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   reflexivity.
 +destruct (eval_expr e2 any_environ) eqn:?; simpl in *;
  [ elimtype False; apply H0; clear 
  | rewrite (IHe2 _ (eq_refl _)) by congruence; auto .. ].
   destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   reflexivity.
+destruct (eval_expr e2 any_environ) eqn:?; simpl in *;
  [ elimtype False; apply H0; clear 
  | rewrite (IHe2 _ (eq_refl _)) by congruence; auto .. ].
   destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   reflexivity.
 +destruct (eval_expr e2 any_environ) eqn:?; simpl in *;
  [ elimtype False; apply H0; clear 
  | rewrite (IHe2 _ (eq_refl _)) by congruence; auto .. ].
   destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   reflexivity.
 +destruct (eval_expr e2 any_environ) eqn:?; simpl in *;
  [ elimtype False; apply H0; clear 
  | rewrite (IHe2 _ (eq_refl _)) by congruence; auto .. ].
   destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   reflexivity.
* 
   destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
  (destruct (eval_expr e any_environ) eqn:?; simpl in *;
  [elimtype False; apply H0; clear
  | try rewrite (IHe _ (eq_refl _)) by congruence; 
     auto .. ]); auto.
* destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   simpl in *; unfold always; auto.
   destruct (cenv_cs ! i0) as [co |]; auto.
   destruct (field_offset cenv_cs i (co_members co)); auto.
   f_equal.
   apply eval_lvalue_any; auto.
   intro. rewrite H in H0. apply H0; reflexivity.
   unfold force_ptr in *.
   destruct (eval_lvalue e any_environ) eqn:?; simpl in *;
   destruct (cenv_cs ! i0);
   try congruence.
   rewrite (eval_lvalue_any _ _ _ _ Heqv); auto.
}
{ clear eval_lvalue_any.
 intro.
 induction e; simpl; intros; subst; unfold_lift; try reflexivity;
 unfold_lift in H0.
*
 unfold eval_var in *;  simpl in *; congruence.
*
 destruct (eval_expr e any_environ) eqn:?; simpl in *;
  try congruence.
 rewrite (eval_expr_any _ _ _ _ Heqv); auto.
  * destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in *; unfold always; auto.
    destruct (cenv_cs ! i0) as [co |]; auto.
    destruct (field_offset cenv_cs i (co_members co)); auto.
    f_equal.
    apply IHe; auto.
    intro. rewrite H in H0. apply H0; reflexivity.
    unfold force_ptr in *.
    destruct (eval_lvalue e any_environ) eqn:?; simpl in *;
    destruct (cenv_cs ! i0);
    try congruence.
    rewrite (IHe _ (eq_refl _)); auto.
}
Qed.

Lemma denote_tc_assert_ilt':
  forall {CS: compspecs} e j, denote_tc_assert (tc_ilt e j) = denote_tc_assert (tc_ilt' e j).
Proof.
  intros.
extensionality rho.
 unfold tc_ilt; simpl.
 unfold_lift.
 destruct (eval_expr e any_environ) eqn:?; simpl; auto.
 apply (eval_expr_any rho) in Heqv; try congruence.
 rewrite Heqv; simpl.
 destruct (Int.ltu i j) eqn:?; simpl;
 unfold_lift; simpl.
 apply pred_ext; intuition.
 unfold is_true. rewrite Heqv.
 simpl. rewrite Heqb.
 apply pred_ext; intuition.
Qed.

Lemma typecheck_val_void:
  forall v, typecheck_val v Tvoid = true -> False.
Proof.
destruct v; simpl; congruence.
Qed.

Definition denote_tc_assert' {CS: compspecs} (a: tc_assert) (rho: environ) : mpred.
pose (P := denote_tc_assert a rho).
unfold denote_tc_assert in P.
super_unfold_lift.
destruct a; apply P.
Defined.

Lemma denote_tc_assert'_eq{CS: compspecs}:
  denote_tc_assert' = denote_tc_assert.
Proof.
extensionality a rho.
destruct a; reflexivity.
Qed.

Lemma int_eq_true : forall x y,
true = Int.eq x y -> x = y.
Proof.
intros. assert (X := Int.eq_spec x y). if_tac in X; auto. congruence.
Qed.

Definition check_pp_int' e1 e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp'
                         (tc_comparable' e1 e2)
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.

Definition check_pl_long' e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp'
                         (tc_iszero' e2)
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.


Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.

Lemma or_False: forall x, (x \/ False) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma or_True: forall x, (x \/ True) = True.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma True_or: forall x, (True \/ x) = True.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma False_or: forall x, (False \/ x) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.


Lemma tc_orp_sound : forall {CS: compspecs} a1 a2 rho m, 
    denote_tc_assert (tc_orp a1 a2) rho m <->  
    denote_tc_assert (tc_orp' a1 a2) rho m. 
Proof.
intros.
 unfold tc_orp.
 destruct a1; simpl; unfold_lift;
 repeat first [rewrite False_or | rewrite True_or | rewrite or_False | rewrite or_True];
  try apply iff_refl;
  destruct a2; simpl in *; unfold_lift;
 repeat first [rewrite False_or | rewrite True_or | rewrite or_False | rewrite or_True];
  try apply iff_refl.
Qed. 

Lemma denote_tc_assert_orp: forall {CS: compspecs} x y rho, 
  denote_tc_assert (tc_orp x y) rho = 
   orp (denote_tc_assert x rho) (denote_tc_assert y rho).
Proof.
 intros.
 apply pred_ext; intro m; rewrite tc_orp_sound; intro; assumption.
Qed. 

Lemma is_true_true: is_true true = True.
Proof. apply prop_ext; intuition. Qed.
Lemma is_true_false: is_true false = False.
Proof. apply prop_ext; intuition. Qed.


Lemma denote_tc_assert_iszero: forall {CS: compspecs} e rho,
  denote_tc_assert (tc_iszero e) rho = 
  match (eval_expr e rho) with 
  | Vint i => prop (is_true (Int.eq i Int.zero))
  | Vlong i => prop (is_true (Int.eq (Int.repr (Int64.unsigned i)) Int.zero))
   | _ => FF end.
Proof.
 intros.
 unfold tc_iszero.
 destruct (eval_expr e any_environ) eqn:?; simpl; auto;
 rewrite (eval_expr_any rho e _ Heqv) by congruence.
 destruct (Int.eq i Int.zero); reflexivity.
 destruct (Int.eq (Int.repr (Int64.unsigned i)) Int.zero); reflexivity.
Qed. 

Lemma denote_tc_assert_iszero': forall {CS: compspecs} e,
  denote_tc_assert (tc_iszero e) = denote_tc_assert (tc_iszero' e).
Proof.
intros.
extensionality rho.
rewrite denote_tc_assert_iszero.
reflexivity.
Qed.

Lemma denote_tc_assert_nonzero: forall {CS: compspecs} e rho,
  denote_tc_assert (tc_nonzero e) rho = 
  match (eval_expr e rho) with 
  | Vint i => prop (is_true (negb (Int.eq i Int.zero)))
   | _ => FF end.
Proof.
 intros.
 unfold tc_nonzero.
 destruct (eval_expr e any_environ) eqn:?; simpl; auto;
 try rewrite (eval_expr_any rho e _ Heqv) by congruence;
 unfold_lift.
 destruct (eval_expr e rho); try reflexivity.
 simpl.
 destruct (Int.eq i Int.zero); reflexivity.
 destruct (Int.eq i Int.zero) eqn:?; simpl; try reflexivity.
 unfold_lift; simpl; rewrite (eval_expr_any rho e _ Heqv) by congruence.
 simpl. rewrite Heqb; reflexivity.
 unfold_lift; simpl; rewrite (eval_expr_any rho e _ Heqv) by congruence;
  reflexivity.
 unfold_lift; simpl; rewrite (eval_expr_any rho e _ Heqv) by congruence;
  reflexivity.
 unfold_lift; simpl; rewrite (eval_expr_any rho e _ Heqv) by congruence;
  reflexivity.
 unfold_lift; simpl; rewrite (eval_expr_any rho e _ Heqv) by congruence;
  reflexivity.
Qed.

Lemma denote_tc_assert_nonzero': forall {CS: compspecs} e,
  denote_tc_assert (tc_nonzero e) = denote_tc_assert (tc_nonzero' e).
Proof.
intros.
extensionality rho.
rewrite denote_tc_assert_nonzero.
simpl.  unfold_lift. destruct (eval_expr e rho); simpl; auto.
destruct (Int.eq i Int.zero); reflexivity.
Qed.

Lemma denote_tc_assert_nodivover: forall {CS: compspecs} e1 e2 rho,
  denote_tc_assert (tc_nodivover e1 e2) rho = 
         match eval_expr e1 rho, eval_expr e2 rho with
                           | Vint n1, Vint n2 => prop (is_true (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone)))
                           | _ , _ => FF
                          end.
Proof.
 intros.
 unfold tc_nodivover.
 destruct (eval_expr e1 any_environ) eqn:?;
 destruct (eval_expr e2 any_environ) eqn:?;
 simpl; auto.
 rewrite (eval_expr_any rho e1 _ Heqv) by congruence.
 rewrite (eval_expr_any rho e2 _ Heqv0) by congruence.
 destruct (negb (Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone)) eqn:?.
 simpl; try   reflexivity.
 simpl.  unfold_lift.
 rewrite (eval_expr_any rho e1 _ Heqv) by congruence;
 rewrite (eval_expr_any rho e2 _ Heqv0) by congruence.
 simpl. rewrite Heqb. reflexivity.
Qed.

Lemma denote_tc_assert_nodivover': forall {CS: compspecs} e1 e2,
  denote_tc_assert (tc_nodivover e1 e2) = denote_tc_assert (tc_nodivover' e1 e2).
Proof.
intros.
extensionality rho.
rewrite denote_tc_assert_nodivover; reflexivity.
Qed.

Lemma denote_tc_assert_andp'': 
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_andp' a b) rho =
            andp (denote_tc_assert a rho) (denote_tc_assert b rho).
Proof.
 intros. reflexivity. Qed.

Lemma denote_tc_assert_orp'': 
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_orp' a b) rho =
             orp (denote_tc_assert a rho) (denote_tc_assert b rho).
Proof.
 intros. reflexivity. Qed.

Lemma denote_tc_assert_andp': 
  forall {CS: compspecs} a b, denote_tc_assert (tc_andp a b) =
                        denote_tc_assert (tc_andp' a b).
Proof. intros. extensionality rho. apply denote_tc_assert_andp. Qed.

Lemma denote_tc_assert_orp': 
  forall {CS: compspecs} a b, denote_tc_assert (tc_orp a b) =
                        denote_tc_assert (tc_orp' a b).
Proof. intros. extensionality rho. apply denote_tc_assert_orp. Qed.

Lemma denote_tc_assert_comparable':
  forall {CS: compspecs} a b, 
    denote_tc_assert (tc_comparable a b) =
    denote_tc_assert (tc_comparable' a b).
Proof.
intros; extensionality rho.
unfold tc_comparable.
simpl; unfold_lift;  unfold denote_tc_comparable.
destruct (eval_expr a rho) eqn:Ha;
destruct (eval_expr a any_environ) eqn:Ha';
simpl; unfold_lift;  unfold denote_tc_comparable;
rewrite ?Ha, ?Ha'; simpl; auto;
try solve [
   rewrite (eval_expr_any rho a _ Ha') in Ha by congruence;
   inv Ha].
destruct (eval_expr b rho) eqn:Hb;
destruct (eval_expr b any_environ) eqn:Hb';
simpl; unfold_lift;  unfold denote_tc_comparable;
rewrite ?Ha, ?Ha', ?Hb, ?Hb'; simpl; auto;
rewrite (eval_expr_any rho b _ Hb') in Hb by congruence;   inv Hb.
rewrite (eval_expr_any rho a _ Ha') in Ha by congruence; inv Ha.
destruct (Int.eq_dec i Int.zero).
subst. rewrite Int.eq_true.
destruct (Int.eq_dec i1 Int.zero).
subst. rewrite Int.eq_true.
simpl. 
rewrite !prop_true_andp by auto.
super_unfold_lift.
unfold TT. f_equal. apply prop_ext; intuition.
rewrite Int.eq_false by auto. simpl.
simpl; unfold_lift;  unfold denote_tc_comparable.
rewrite (eval_expr_any rho a _ Ha')  by congruence.
rewrite (eval_expr_any rho _ _ Hb')  by congruence.
auto.
rewrite Int.eq_false by auto. simpl.
simpl; unfold_lift;  unfold denote_tc_comparable.
rewrite (eval_expr_any rho a _ Ha')  by congruence.
rewrite (eval_expr_any rho _ _ Hb')  by congruence.
auto.
Qed.

Hint Rewrite @denote_tc_assert_andp' @denote_tc_assert_andp''
    @denote_tc_assert_orp' @denote_tc_assert_orp''
    @denote_tc_assert_iszero' @denote_tc_assert_nonzero'
    @denote_tc_assert_nodivover' @denote_tc_assert_ilt'
    @denote_tc_assert_comparable'
     : dtca.

Ltac dtca := autorewrite with dtca; auto.

Definition stupid_typeconv ty := 
match ty with
| Tarray t _ a => Tpointer t a
| Tfunction _ _ _ => Tpointer ty noattr
| _ => ty
end.

Definition classify_sub' ty1 ty2 := 
match stupid_typeconv ty1 with
| Tpointer ty a =>
    match stupid_typeconv ty2 with
    | Tint _ _ _ => sub_case_pi ty
    | Tlong _ _ => sub_case_pl ty
    | Tpointer _ _ => sub_case_pp ty
    | _ => sub_default
    end
| _ => sub_default
end.

Lemma classify_sub_eq : classify_sub = classify_sub'.
Proof.
unfold classify_sub, classify_sub'; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Definition classify_cmp' ty1 ty2 := 
  match stupid_typeconv ty1, stupid_typeconv ty2 with 
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ _ _ => cmp_case_pp
  | Tint _ _ _, Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tlong _ _ => cmp_case_pl
  | Tlong _ _ , Tpointer _ _ => cmp_case_lp
  | _, _ => cmp_default
  end.

Lemma classify_cmp_eq: classify_cmp = classify_cmp'.
Proof.
unfold classify_cmp, classify_cmp'; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Definition classify_add' ty1 ty2 := 
 match stupid_typeconv ty1 with
 | Tint _ _ _ =>
    match stupid_typeconv ty2 with
    | Tpointer ty a => add_case_ip ty
    |  _ => add_default
    end
| Tlong _ _ =>
    match stupid_typeconv ty2 with
    | Tpointer ty a => add_case_lp ty
    | _ => add_default
    end
| Tpointer ty a =>
    match stupid_typeconv ty2 with
    | Tint _ _ _ => add_case_pi ty
    | Tlong _ _ => add_case_pl ty
    | _ => add_default
    end
 | _ => add_default
end.

Lemma classify_add_eq:  classify_add = classify_add'.
Proof.
unfold classify_add; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Definition classify_shift' (ty1: type) (ty2: type) :=
  match stupid_typeconv ty1, stupid_typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | Tint I32 Unsigned _, Tlong _ _ => shift_case_il Unsigned
  | Tint _ _ _, Tlong _ _ => shift_case_il Signed
  | Tlong s _, Tint _ _ _ => shift_case_li s
  | Tlong s _, Tlong _ _ => shift_case_ll s
  | _,_  => shift_default
  end.

Lemma classify_shift_eq:  classify_shift = classify_shift'.
Proof.
unfold classify_shift; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Lemma den_isBinOpR: forall {CS: compspecs} op a1 a2 ty,
  denote_tc_assert (isBinOpResultType op a1 a2 ty) = 
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in 
denote_tc_assert 
match op with
  | Cop.Oadd => match classify_add' (typeof a1) (typeof a2) with 
                    | Cop.add_case_pi t => tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_ip t => tc_andp' (tc_andp' (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_pl t => tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_lp t => tc_andp' (tc_andp' (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end
  | Cop.Osub => match classify_sub' (typeof a1) (typeof a2) with 
                    | Cop.sub_case_pi t => tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pl t => tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pp t =>  (*tc_isptr may be redundant here*)
                             tc_andp' (tc_andp' (tc_andp' (tc_andp' (tc_andp' (tc_andp' (tc_samebase a1 a2)
                             (tc_isptr a1))
                              (tc_isptr a2))
                               (tc_bool (is_int32_type ty) reterr))
			        (tc_bool (negb (Int.eq (Int.repr (sizeof cenv_cs t)) Int.zero)) 
                                      (pp_compare_size_0 t)))
                                 (tc_bool (complete_type cenv_cs t) reterr))
                                  (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end 
  | Cop.Omul => binarithType (typeof a1) (typeof a2) ty deferr reterr
  | Cop.Omod => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => 
                           tc_andp' (tc_nonzero' a2) 
                           (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Unsigned => 
                           tc_andp' (tc_nonzero' a2) 
                           (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp' (tc_andp' (tc_nonzero' a2) 
                                                      (tc_nodivover' a1 a2))
                                                     (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp' (tc_andp' (tc_nonzero' a2) 
                                                      (tc_nodivover' a1 a2))
                                                     (tc_bool (is_long_type ty) reterr)
                    | _ => tc_FF deferr
            end
  | Cop.Odiv => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => tc_andp' (tc_nonzero' a2) (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Unsigned => tc_andp' (tc_nonzero' a2) (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp' (tc_andp' (tc_nonzero' a2) (tc_nodivover' a1 a2)) 
                                                        (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp' (tc_andp' (tc_nonzero' a2) (tc_nodivover' a1 a2)) 
                                                        (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_f  =>  tc_bool (is_float_type ty) reterr 
                    | Cop.bin_case_s  =>  tc_bool (is_single_type ty) reterr 
                    | Cop.bin_default => tc_FF deferr
            end
  | Cop.Oshl | Cop.Oshr => match classify_shift' (typeof a1) (typeof a2) with
                    | Cop.shift_case_ii _ =>  tc_andp' (tc_ilt' a2 Int.iwordsize) (tc_bool (is_int32_type ty) 
                                                                                         reterr)
                    | _ => tc_FF deferr
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor => 
                   match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i _ =>tc_bool (is_int32_type ty) reterr
                    | _ => tc_FF deferr
                   end   
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => 
                   match classify_cmp' (typeof a1) (typeof a2) with
                    | Cop.cmp_default => 
                           tc_bool (is_numeric_type (typeof a1) 
                                         && is_numeric_type (typeof a2)
                                          && is_int_type ty)
                                             deferr
		    | Cop.cmp_case_pp => check_pp_int' a1 a2 op ty e
                    | Cop.cmp_case_pl => check_pp_int' (Ecast a1 (Tint I32 Unsigned noattr)) a2 op ty e
(*check_pl_long' a2 op ty e*)
                    | Cop.cmp_case_lp => check_pp_int' (Ecast a2 (Tint I32 Unsigned noattr)) a1 op ty e
(*check_pl_long' a1 op ty e*)
                   end
  end.
Proof.
 intros.
 rewrite <- classify_add_eq. rewrite <- classify_sub_eq.
 rewrite <- classify_shift_eq. rewrite <- classify_cmp_eq.
 unfold isBinOpResultType, classify_add, classify_sub, classify_binarith, classify_shift, 
  classify_cmp, check_pp_int, check_pp_int', 
  (*check_pl_long, check_pl_long', *)
  typeconv,
  remove_attributes, change_attributes;
  destruct op; dtca;
 extensionality rho;
 destruct (typeof a1) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ]; dtca;
 destruct (typeof a2) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ]; dtca.



Qed.

Lemma denote_tc_assert'_andp'_e:
 forall {CS: compspecs} a b rho m, denote_tc_assert' (tc_andp' a b) rho m ->
    denote_tc_assert' a rho m /\ denote_tc_assert' b rho m.
Proof. intros.
 rewrite denote_tc_assert'_eq in *. apply H.
Qed.

Lemma cast_int_long_nonzero:
  forall s i, Int.eq i Int.zero = false -> 
             Int64.eq (cast_int_long s i) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
rewrite Int64.eq_false; auto.
unfold cast_int_long.
contradict H0.
unfold Int64.zero in H0.
destruct s.
assert (Int64.signed (Int64.repr (Int.signed i)) = Int64.signed (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.signed_repr in H.
rewrite Int64.signed_repr in H.
rewrite <- (Int.repr_signed i).
rewrite H. reflexivity.
pose proof (Int64.signed_range Int64.zero).
rewrite Int64.signed_zero in H1.
auto.
pose proof (Int.signed_range i).
clear - H1.
destruct H1.
split.
apply Z.le_trans with Int.min_signed; auto.
compute; congruence.
apply Z.le_trans with Int.max_signed; auto.
compute; congruence.

assert (Int64.unsigned (Int64.repr (Int.unsigned i)) = Int64.unsigned (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.unsigned_repr in H.
rewrite Int64.unsigned_repr in H.
rewrite <- (Int.repr_unsigned i).
rewrite H. reflexivity.
split; compute; congruence. 
pose proof (Int.unsigned_range i).
clear - H1.
destruct H1.
split; auto.
unfold Int64.max_unsigned.
apply Z.le_trans with Int.modulus.
omega.
compute; congruence.
Qed.

Definition typecheck_numeric_val (v: val) (t: type) : Prop :=
 match v,t with
 | Vint _, Tint _ _ _ => True
 | Vlong _, Tlong _ _ => True
 | Vfloat _, Tfloat F64 _ => True
 | _, _ => False
 end.


Lemma typecheck_val_of_bool:
 forall x i3 s3 a3, typecheck_val (Val.of_bool x) (Tint i3 s3 a3) = true.
Proof.
intros.
destruct x, i3,s3; simpl; auto.
Qed.

Lemma typecheck_val_sem_cmp:
 forall op v1 t1 v2 t2 i3 s3 a3,
 typecheck_numeric_val v1 t1 ->
 typecheck_numeric_val v2 t2 ->
typecheck_val
  (force_val
     (Cop2.sem_cmp op t1 t2 true2 v1 v2))
  (Tint i3 s3 a3) = true.
Proof.
destruct op; intros;
destruct v1; 
  destruct t1 as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction H;
destruct v2; 
  destruct t2 as  [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction H0;
 unfold Cop2.sem_cmp, classify_cmp, typeconv,
  Cop2.sem_binarith, Cop2.sem_cast, classify_cast;
 simpl;
 try apply typecheck_val_of_bool.
Qed.

Lemma typecheck_val_cmp_eqne_ip:
 forall op v1 t1 v2 t0 a0 i2 s0 a1,
 match op with Ceq => True | Cne => True | _ => False end ->
 match v1,t1 with
 | Vint i, Tint _ _ _ => Int.eq i Int.zero = true
 | Vlong i, Tlong _ _ => Int.eq (Int.repr (Int64.unsigned i)) Int.zero = true
 | _, _ => False
 end ->
 typecheck_val v2 (Tpointer t0 a0) = true ->
typecheck_val
  (force_val
     (Cop2.sem_cmp op t1 (Tpointer t0 a0) true2 v1 v2))
  (Tint i2 s0 a1) = true.
Proof.
intros until 1; rename H into CMP; intros;
 destruct op; try contradiction CMP; clear CMP;
 destruct v1, t1; try contradiction H;
 destruct v2; inv H0; try rewrite H2;
 try destruct i0; destruct s; 
unfold Cop2.sem_cmp, classify_cmp, typeconv,
  Cop2.sem_binarith, sem_cast, classify_cast, sem_cmp_pp;
 simpl; try rewrite H;
 try reflexivity;
 try apply typecheck_val_of_bool.
Qed.

Lemma typecheck_val_cmp_eqne_pi:
 forall op v1 t1 v2 t0 a0 i2 s0 a1,
 match op with Ceq => True | Cne => True | _ => False end ->
 match v1,t1 with
 | Vint i, Tint _ _ _ => Int.eq i Int.zero = true
 | Vlong i, Tlong _ _ => Int.eq (Int.repr (Int64.unsigned i)) Int.zero = true
 | _, _ => False
 end ->
 typecheck_val v2 (Tpointer t0 a0) = true ->
typecheck_val
  (force_val
     (Cop2.sem_cmp op (Tpointer t0 a0) t1 true2 v2 v1))
  (Tint i2 s0 a1) = true.
Proof.
intros until 1; rename H into CMP; intros.
 destruct op; try contradiction CMP; clear CMP;
 destruct v1, t1; try contradiction H;
 destruct v2; inv H0; try rewrite H2;
 try destruct i0; destruct s; 
unfold Cop2.sem_cmp, classify_cmp, typeconv,
  sem_binarith, sem_cast, classify_cast, sem_cmp_pp;
 simpl; try rewrite H;
 try reflexivity;
 try apply typecheck_val_of_bool.
Qed.


Ltac sem_cmp_solver t1 t2 := 
match t1 with 
  | Tint ?i ?s _ => destruct i,s
  | Tlong ?s _ => destruct s
  | Tfloat ?i _ => try (is_var i; destruct i)
  | _ => idtac
  end;
  match t2 with 
  | Tint ?i ?s _ => destruct i,s
  | Tlong ?s _ => destruct s  
  | Tfloat ?i _ => try (is_var i; destruct i)
  | _ => idtac
  end;
  unfold Cop2.sem_cmp, sem_cmp_pp, sem_cmp_pl, sem_cmp_lp; simpl;
 repeat match goal with
            | H: _ = true |- _ =>
                try rewrite H; clear H
            | H: if ?A then True else False |- _ =>
                  destruct A eqn:?; try contradiction; clear H 
            end;
  try reflexivity;
  try apply typecheck_val_of_bool.
