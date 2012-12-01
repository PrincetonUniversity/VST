Load loadpath.
Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Import Cop.

Lemma eval_binop_relate_fail_add :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oadd e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_add (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oadd e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_add in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence. 
Qed.

Lemma eval_binop_relate_fail_sub :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Osub e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_sub (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Osub e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_sub in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.


Lemma eval_binop_relate_fail_mul :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Omul e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_mul (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Omul e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_mul in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_div :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Odiv e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_div (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Odiv e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_div in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_mod :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Omod e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_mod (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Omod e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_mod in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_shl :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oshl e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_shl (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oshl e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_shl in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_shr :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oshr e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_shr (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oshr e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_shr in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_and :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oand e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_and (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oand e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_and in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_or :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oor e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_or (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oor e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_or in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_xor :
 forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oxor e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_xor (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oxor e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_xor in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_eq :
   forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oeq e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_cmp Ceq (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) 
     (typeof e2) Mem.empty ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oeq e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_cmp in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_ne :
   forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType One e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_cmp Cne (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) 
     (typeof e2) Mem.empty ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop One e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_cmp in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_lt :
   forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Olt e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_cmp Clt (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) 
     (typeof e2) Mem.empty ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Olt e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_cmp in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_gt :
   forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Ogt e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_cmp Cgt (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) 
     (typeof e2) Mem.empty ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Ogt e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_cmp in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_le :
   forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Ole e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_cmp Cle (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) 
     (typeof e2) Mem.empty ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Ole e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_cmp in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

Lemma eval_binop_relate_fail_ge :
   forall (Delta : tycontext) (rho : environ) (e1 e2 : expr) 
     (t : type) (m : mem),
   typecheck_environ rho Delta = true ->
   forall (ge : genv) (te : temp_env) (ve : env),
   rho = construct_rho (filter_genv ge) ve te ->
   denote_tc_assert (typecheck_expr Delta e2) rho ->
   denote_tc_assert (isBinOpResultType Oge e1 e2 t) rho ->
   denote_tc_assert (typecheck_expr Delta e1) rho ->
   None =
   sem_cmp Cge (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) 
     (typeof e2) Mem.empty ->
   Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
   Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   Clight.eval_expr ge ve te m (Ebinop Oge e1 e2 t) Vundef.
Proof.
intros. 

simpl in *. 
unfold sem_cmp in *. 

remember (eval_expr e2 rho). remember (eval_expr e1 rho).
destruct (typeof e1); destruct (typeof e2); simpl in *; try congruence;
destruct v0; simpl in *; try congruence; destruct v;
simpl in *; try congruence; 

try destruct i; try destruct s; simpl in *; try congruence;
try destruct i0; try destruct s0; simpl in *; try congruence;
unfold lift2 in *; unfold lift1 in *; unfold lift0 in *; auto; 
try rewrite <- Heqv in *; try rewrite <- Heqv0 in *;
tc_assert_ext; try contradiction;
 
simpl in *; try congruence; 
repeat rewrite andb_if in H4; 
repeat rewrite orb_if in H4;
repeat if_tac in H4; simpl in *; try congruence; try contradiction.
Qed.

