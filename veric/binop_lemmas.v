Load loadpath.
Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Import Cop.

Lemma typecheck_add_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oadd e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oadd (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_add in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
try solve [simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
 destruct t; simpl in *; auto; unfold_coerce;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; tc_assert_ext; auto].
Qed. 

Lemma typecheck_sub_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Osub e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Osub (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_sub in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
try solve[
destruct t; simpl in *; auto;
try (remember (negb (Int.eq (Int.repr (sizeof t0)) Int.zero)); 
unfold tc_bool in *; try if_tac in H0); simpl in *; unfold_coerce; tc_assert_ext; auto; 
try solve [destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; tc_assert_ext; auto; repeat (if_tac; auto)]].
Qed. 
 
Lemma typecheck_mul_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Omul e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Omul (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_sub in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce; tc_assert_ext; auto; repeat (if_tac; auto). 
Qed. 

Lemma typecheck_div_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Odiv e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Odiv (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_div in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
 destruct t; simpl in *; auto; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *;
unfold_coerce; tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 

Lemma typecheck_mod_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Omod e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Omod (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_mod in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
destruct t; simpl in *; auto; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; unfold_coerce; tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 

Lemma typecheck_and_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oand e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oand (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_and in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 

Lemma typecheck_or_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oor e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oor (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_or in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 

Lemma typecheck_xor_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oxor e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oxor (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_xor in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 

Lemma typecheck_shl_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oshl e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oshl (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_shl in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
 destruct t; simpl in *; auto; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *;
unfold_coerce; tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 


Lemma typecheck_shr_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oshr e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oshr (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_shr in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
 destruct t; simpl in *; auto; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *;
unfold_coerce; tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto). 
Qed. 


Lemma typecheck_eq_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oeq e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oeq (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_cmp in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
unfold_coerce; tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto); of_bool_destruct; auto. 
Qed. 

Lemma typecheck_ne_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType One e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop One (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_cmp in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto); of_bool_destruct; auto. 
Qed. 

Lemma typecheck_lt_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Olt e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Olt (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_cmp in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto); of_bool_destruct; auto. 
Qed. 

Lemma typecheck_le_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Ole e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Ole (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_cmp in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto); of_bool_destruct; auto. 
Qed. 

Lemma typecheck_gt_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Ogt e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Ogt (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_cmp in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto); of_bool_destruct; auto. 
Qed. 

Lemma typecheck_ge_sound:
forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oge e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop Oge (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof. 
intros. simpl in *; unfold eval_binop; unfold sem_binary_operation.
unfold sem_cmp in *. 
destruct (typeof e1); destruct (typeof e2); simpl in *; auto;

try destruct i; try destruct s; try destruct i0; try destruct s0; 
simpl in *; try solve[inv H0]; unfold_coerce;
tc_assert_ext; auto;
destruct (eval_expr e1 rho); destruct (eval_expr e2 rho); auto;
simpl in *; destruct t; simpl in *; auto; unfold_coerce;
 tc_assert_ext; auto; repeat (try rewrite orb_if; rewrite andb_if);
repeat (if_tac; auto); of_bool_destruct; auto. 
Qed. 


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
simpl in *. unfold_coerce; rewrite tc_andp_sound in H. 
simpl in *. unfold_coerce; intuition.  
destruct b. 
eapply typecheck_add_sound; eauto.  
eapply typecheck_sub_sound; eauto.
eapply typecheck_mul_sound; eauto.
eapply typecheck_div_sound; eauto.
eapply typecheck_mod_sound; eauto.
eapply typecheck_and_sound; eauto.
eapply typecheck_or_sound; eauto.
eapply typecheck_xor_sound; eauto.
eapply typecheck_shl_sound; eauto.
eapply typecheck_shr_sound; eauto.
eapply typecheck_eq_sound; eauto.
eapply typecheck_ne_sound; eauto.
eapply typecheck_lt_sound; eauto.
eapply typecheck_gt_sound; eauto.
eapply typecheck_le_sound; eauto. 
eapply typecheck_ge_sound; eauto. 
Qed.


