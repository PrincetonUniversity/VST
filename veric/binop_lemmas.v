Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Import Cop.

Lemma typecheck_val_void:
  forall v, typecheck_val v Tvoid = true -> False.
Proof.
destruct v; simpl; congruence.
Qed.

Definition denote_tc_assert' (a: tc_assert) (rho: environ) : Prop.
pose (P := denote_tc_assert a rho).
unfold denote_tc_assert in P.
super_unfold_lift.
destruct a; apply P.
Defined.

Lemma denote_tc_assert'_eq:
  denote_tc_assert' = denote_tc_assert.
Proof.
extensionality a rho.
destruct a; reflexivity.
Qed.

Ltac typecheck_sound_solver1 H0 e1 e2 t :=
rewrite <- denote_tc_assert'_eq in *;
simpl in *;
 destruct (typeof e1) as [ | [ | | | ] [ | ]  | [ | ]  | | | | | | ]; 
      try (contradiction H0);
 destruct (typeof e2) as [ | [ | | | ] [ | ]  | [ | ]  | | | | | | ]; 
      try (contradiction H0);
 destruct t; try (contradiction H0);
simpl in *.

Lemma cmp_sound_aux:
  forall b i s a , typecheck_val (force_val (Some (Val.of_bool b))) (Tint i s a) = true.
Proof. destruct b; reflexivity. Qed.
 
Lemma int_eq_true : forall x y,
true = Int.eq x y -> x = y.
Proof.
intros. assert (X := Int.eq_spec x y). if_tac in X; auto. congruence.
Qed.

Definition check_pp_int' e1 e2 op t :=
match op with 
| Cop.Oeq | Cop.One => tc_andp 
                         (tc_orp (tc_iszero' e1) (tc_iszero' e2))
                         (tc_bool (is_int_type t) (pp_compare_size_0 t))
| _ => tc_noproof
end.


Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.

Lemma denote_tc_assert_orp: forall x y rho, 
  denote_tc_assert (tc_orp x y) rho = (denote_tc_assert x rho \/ denote_tc_assert y rho).
Proof.
 intros.
 unfold tc_orp.
 unfold denote_tc_assert;
 destruct x,y; simpl; auto;
 try solve [unfold_lift; simpl; apply prop_ext; intuition].
Qed. 

Lemma denote_tc_assert_andp: forall x y rho, 
  denote_tc_assert (tc_andp x y) rho = (denote_tc_assert x rho /\ denote_tc_assert y rho).
Proof.
 intros.
 unfold tc_andp.
 unfold denote_tc_assert;
 destruct x,y; simpl; auto;
 unfold_lift; simpl; apply prop_ext; intuition.
Qed. 

Lemma is_true_true: is_true true = True.
Proof. apply prop_ext; intuition. Qed.
Lemma is_true_false: is_true false = False.
Proof. apply prop_ext; intuition. Qed.

Lemma and_False: forall x, (x /\ False) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma den_isBinOpR: forall op a1 a2 ty,
  denote_tc_assert (isBinOpResultType op a1 a2 ty) = 
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in 
 denote_tc_assert
 match op with
  | Cop.Oadd => match Cop.classify_add (typeof a1) (typeof a2) with 
                    | Cop.add_default => tc_FF deferr 
                    | Cop.add_case_ii _ => tc_bool (is_int_type ty) reterr
                    | Cop.add_case_pi _ _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr ) 
                    | Cop.add_case_ip _ _ => tc_andp (tc_isptr a2) (tc_bool (is_pointer_type ty) reterr )
                    | _ => tc_bool (is_float_type ty) deferr 
            end
  | Cop.Osub => match Cop.classify_sub (typeof a1) (typeof a2) with 
                    | Cop.sub_default => tc_FF deferr 
                    | Cop.sub_case_ii _ => tc_bool (is_int_type ty) reterr 
                    | Cop.sub_case_pi _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr )
                    | Cop.sub_case_pp ty2 =>  (*tc_isptr may be redundant here*)
                             tc_andp (tc_andp (tc_andp (tc_andp (tc_samebase a1 a2)
                             (tc_isptr a1)) (tc_isptr a2)) (tc_bool (is_int_type ty) reterr ))
			     (tc_bool (negb (Int.eq (Int.repr (sizeof ty2)) Int.zero)) (pp_compare_size_0 ty2))
                    | _ => tc_bool (is_float_type ty)deferr 
            end 
  | Cop.Omul => match Cop.classify_mul (typeof a1) (typeof a2) with 
                    | Cop.mul_default => tc_FF deferr 
                    | Cop.mul_case_ii _ => tc_bool (is_int_type ty) reterr 
                    | _ => tc_bool (is_float_type ty) deferr 
            end 
  | Cop.Omod => match Cop.classify_binint (typeof a1) (typeof a2) with
                    | Cop.binint_case_ii Unsigned => 
                           tc_andp (tc_nonzero a2) 
                           (tc_bool (is_int_type ty) reterr )
                    | Cop.binint_case_ii Signed => tc_andp (tc_andp (tc_nonzero a2) 
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_int_type ty) reterr )
                    | Cop.binint_default => tc_FF deferr 
            end
  | Cop.Odiv => match Cop.classify_div (typeof a1) (typeof a2) with
                    | Cop.div_case_ii Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_int_type ty) reterr )
                    | Cop.div_case_ii Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2)) (tc_bool (is_int_type ty) reterr )
                    | Cop.div_case_ff | Cop.div_case_if _ | Cop.div_case_fi _ =>
                          tc_bool (is_float_type ty) reterr 
                    | Cop.div_default => tc_FF deferr 
            end
  | Cop.Oshl | Cop.Oshr => match Cop.classify_shift (typeof a1) (typeof a2) with
                    | Cop.shift_case_ii _ =>  tc_andp (tc_ilt a2 Int.iwordsize) (tc_bool (is_int_type ty) reterr )
                    | _ => tc_FF deferr 
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor => 
                   match Cop.classify_binint (typeof a1) (typeof a2) with
                    | Cop.binint_case_ii _ =>tc_bool (is_int_type ty) reterr 
                    | _ => tc_FF deferr 
                   end   
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => 
                   match Cop.classify_cmp (typeof a1) (typeof a2) with
                    | Cop.cmp_default => tc_FF deferr 
		    | Cop.cmp_case_pp => check_pp_int' a1 a2 op ty
                    | _ => tc_bool (is_int_type ty) reterr 
                   end
  end.
Proof.
 intros.
 unfold isBinOpResultType, classify_cmp;  destruct op; auto;
 unfold check_pp_int';
 extensionality rho;
 destruct (typeof a1), (typeof a2); simpl; auto;
 try (destruct i; auto; destruct s; auto;
       try (destruct i0; auto; destruct s0; auto));
 unfold_lift; unfold tc_iszero;  
   destruct (is_int_type ty); simpl; unfold_lift; auto;
  try rewrite tc_andp_TT2;
 repeat rewrite denote_tc_assert_andp;
 repeat rewrite denote_tc_assert_orp;
 repeat rewrite and_False;
 simpl; unfold_lift; simpl; f_equal; auto;
 unfold denote_tc_iszero;
 clear;
 repeat (match goal with a: expr |- _ => destruct a; simpl; auto end);
 try solve [unfold_lift; simpl; destruct (Int.eq i Int.zero); simpl;  symmetry; try apply is_true_true; try apply is_true_false].
Qed.

(*
Lemma check_pp_int_sound : forall e1 e2 t op rho, 
denote_tc_assert' (check_pp_int e1 e2 op t) rho ->
is_int_type t = true /\ 
((exists tt, e1 = Econst_int Int.zero tt) \/
(exists tt, e2 = Econst_int Int.zero tt)).
Proof.
intros.
unfold check_pp_int in *.
destruct op; simpl in H; try inv H;
destruct e1; simpl in H; try inv H;
destruct e2; simpl in H; try inv H; 
try (unfold tc_bool in H; 
          try remember (Int.eq i Int.zero); 
          try remember (Int.eq i0 Int.zero);
          repeat if_tac in H; simpl in H;
          try (contradiction H);
          try (apply int_eq_true in Heqb);
          try (apply int_eq_true in Heqb0);
          subst;
split;  eauto). 
Qed.
*)

Lemma typecheck_cmp_sound:
forall op (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type)
   (CMP:  match op with Oeq | One | Olt | Ogt | Ole | Oge => True | _ => False end),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType op e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof.
intros. rewrite den_isBinOpR in H0.
destruct op; try (contradiction CMP);
abstract(
simpl in H0;
intros; typecheck_sound_solver1 H0 e1 e2 t;
unfold eval_binop; unfold sem_binary_operation, sem_cmp; simpl;
remember (eval_expr e1 rho); destruct v; try solve[inv H3];
remember (eval_expr e2 rho); destruct v; try solve[inv H2];
try apply cmp_sound_aux;
try (destruct H0; try contradiction;
simpl in *; unfold is_true in *; rewrite H0; auto)).
Qed.

Lemma typecheck_sub_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Osub e1 e2 t) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Osub (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros; typecheck_sound_solver1 H0 e1 e2 t;
unfold tc_bool, eval_binop in *; simpl in *; unfold sem_sub; simpl;
try (remember (Int.eq (Int.repr (sizeof t0)) Int.zero) as ez; destruct ez; simpl in *; auto);
 try (rewrite (Int.eq_false (Int.repr 1) Int.zero) in H0 by (intro Hx; inv Hx); simpl in H0);
destruct (eval_expr e1 rho); inv H2; destruct (eval_expr e2 rho); inv H1;
 simpl in *; decompose [and] H0; try contradiction; auto;
 try (destruct (zeq b b0); inv H3; simpl; auto).
Qed.

Lemma typecheck_divmod_sound:
forall op (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type)
   (OPER: match op with Odiv | Omod => True | _ => False end),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType op e1 e2 t) rho ->
    denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros.
destruct op; try contradiction;
abstract (typecheck_sound_solver1 H0 e1 e2 t;
(( destruct H0 as  [H0 H0']; hnf in H0,H0') ||
(hnf in H0));
destruct (eval_expr e1 rho); try contradiction;
destruct (eval_expr e2 rho); try contradiction;
unfold eval_binop, sem_binary_operation, sem_div, sem_mod;
try (destruct (Int.eq i1 Int.zero); try (contradiction H0); simpl);
try (destruct (Int.eq i0 (Int.repr Int.min_signed) && Int.eq i1 Int.mone);
      inv H0');
 simpl; auto).
Qed.

Lemma typecheck_shift_sound:
forall op (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type)
   (OPER: match op with Oshl | Oshr => True | _ => False end),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType op e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
destruct op; try contradiction;
abstract (
intros; typecheck_sound_solver1 H0 e1 e2 t;
unfold eval_binop; unfold sem_binary_operation, sem_shl, sem_shr; simpl;
destruct (eval_expr e1 rho); inv H3;
destruct (eval_expr e2 rho); inv H2;
simpl; rewrite H0; reflexivity).
Qed.



Ltac typecheck_sound_solver Delta rho e1 e2 t :=
 match goal with
 | H: denote_tc_assert (typecheck_expr Delta e2) rho,
   H0: denote_tc_assert (isBinOpResultType _ e1 e2 t) rho,
   H1: typecheck_val (eval_expr e2 rho) (typeof e2) = true,
   H2: typecheck_val (eval_expr e1 rho) (typeof e1) = true |- _ =>
 typecheck_sound_solver1 H0 e1 e2 t;
try solve [destruct (eval_expr e1 rho); inv H2;
               destruct (eval_expr e2 rho); inv H1;
               try (contradiction H0);
               simpl; auto]
end.

Lemma typecheck_binop_sound:
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type),
denote_tc_assert (typecheck_expr Delta (Ebinop b e1 e2 t)) rho ->
(denote_tc_assert (typecheck_expr Delta e1) rho ->
 typecheck_val (eval_expr e1 rho) (typeof e1) = true) ->
(denote_tc_assert (typecheck_expr Delta e2) rho ->
 typecheck_val (eval_expr e2 rho) (typeof e2) = true) ->
typecheck_val (eval_expr (Ebinop b e1 e2 t) rho) (typeof (Ebinop b e1 e2 t)) =
true.
Proof. 
intros. simpl in *.  rewrite tc_andp_sound in H. 
simpl in *. super_unfold_lift; rewrite tc_andp_sound in H. 
simpl in *. super_unfold_lift; intuition.  
destruct b;
try (eapply typecheck_sub_sound; eauto);
try solve [eapply typecheck_divmod_sound; simpl; eauto];
try solve [eapply typecheck_shift_sound; simpl; eauto];
try solve [eapply typecheck_cmp_sound; simpl; eauto];
clear H4; abstract (typecheck_sound_solver Delta rho e1 e2 t).
Qed.


