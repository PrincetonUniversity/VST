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
intros.
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


