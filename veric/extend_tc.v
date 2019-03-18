Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.

Require Import VST.veric.seplog. (*For definition of tycontext*)

Local Open Scope pred.

Definition tc_expr {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred:=
  fun rho => denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist {CS: compspecs} (Delta: tycontext) (t : list type) (e: list expr) : environ -> mpred :=
      fun rho => denote_tc_assert (typecheck_exprlist Delta t e) rho.

Definition tc_lvalue {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred :=
     fun rho => denote_tc_assert (typecheck_lvalue Delta e) rho.

Definition tc_temp_id {CS: compspecs} (id : positive) (ty : type)
  (Delta : tycontext) (e : expr) : environ -> mpred  :=
     fun rho => denote_tc_assert (typecheck_temp_id id ty Delta e) rho.

Definition tc_expropt {CS: compspecs} Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `!!(t=Tvoid)
                     | Some e' => tc_expr Delta (Ecast e' t)
   end.

Definition tc_temp_id_load id tfrom Delta v : environ -> mpred  :=
fun rho => !! (exists tto, (temp_types Delta) ! id = Some tto
                      /\ tc_val tto (eval_cast tfrom tto (v rho))).

Lemma extend_prop: forall P, boxy extendM (prop P).
Proof.
intros.
hnf.
apply pred_ext. intros ? ?. apply H; auto. apply extendM_refl.
repeat intro. apply H.
Qed.

Hint Resolve extend_prop.

Lemma extend_tc_temp_id_load :  forall id tfrom Delta v rho, boxy extendM (tc_temp_id_load id tfrom Delta v rho).
Proof.
intros. unfold tc_temp_id_load. auto.
Qed.

Lemma extend_tc_andp:
 forall {CS: compspecs} A B rho,
   boxy extendM (denote_tc_assert A rho) ->
   boxy extendM (denote_tc_assert B rho) ->
   boxy extendM (denote_tc_assert (tc_andp A B) rho).
Proof.
intros.
rewrite denote_tc_assert_andp.
apply boxy_andp; auto.
apply extendM_refl.
Qed.

Lemma extend_tc_bool:
 forall {CS: compspecs} A B rho,
   boxy extendM (denote_tc_assert (tc_bool A B) rho).
Proof.
intros.
destruct A; simpl; apply  extend_prop.
Qed.

Lemma extend_tc_int_or_ptr_type:
 forall {CS: compspecs} A rho,
   boxy extendM (denote_tc_assert (tc_int_or_ptr_type A) rho).
Proof.
intros.
apply  extend_tc_bool.
Qed.

Lemma extend_tc_Zge:
 forall {CS: compspecs} v i rho,
   boxy extendM (denote_tc_assert (tc_Zge v i) rho).
Proof.
intros.
induction v; simpl; unfold_lift; simpl;
unfold denote_tc_Zle; try apply extend_prop;
repeat match goal with |- boxy _ (match ?A with  _ => _ end) => destruct A end;
try apply extend_prop.
Qed.


Lemma extend_tc_Zle:
 forall {CS: compspecs} v i rho,
   boxy extendM (denote_tc_assert (tc_Zle v i) rho).
Proof.
intros.
induction v; simpl; unfold_lift; simpl;
unfold denote_tc_Zge; try apply extend_prop;
repeat match goal with |- boxy _ (match ?A with  _ => _ end) => destruct A end;
try apply extend_prop.
Qed.

Lemma extend_tc_iszero:
 forall {CS: compspecs} v rho,
   boxy extendM (denote_tc_assert (tc_iszero v) rho).
Proof.
intros.
rewrite denote_tc_assert_iszero.
destruct (eval_expr v rho); apply extend_prop.
Qed.

Lemma extend_valid_pointer':
  forall a b, boxy extendM (valid_pointer' a b).
Proof.
intros.
apply boxy_i; intros.
apply extendM_refl.
unfold valid_pointer' in *.
simpl in *.
destruct a; simpl in *; auto.
forget (b0, Ptrofs.unsigned i + b) as p.
destruct (w @ p) eqn:?H; try contradiction.
destruct H as [w2 ?].
apply (resource_at_join _ _ _ p) in H.
rewrite H1 in H.
inv H; auto.
clear - H0 RJ.
eapply join_nonidentity; eauto.
destruct H as [w2 ?].
apply (resource_at_join _ _ _ p) in H.
rewrite H1 in H.
inv H; auto.
Qed.

Lemma extend_andp: forall P Q, 
  boxy extendM P -> boxy extendM Q -> boxy extendM (andp P Q).
Proof.
 intros.
 apply boxy_i; intros.
 apply extendM_refl.
 destruct H2; split; eapply boxy_e; eauto.
Qed.

Lemma extend_orp: forall P Q, 
  boxy extendM P -> boxy extendM Q -> boxy extendM (orp P Q).
Proof.
 intros.
 apply boxy_i; intros.
 apply extendM_refl.
 destruct H2; [left|right]; eapply boxy_e; eauto.
Qed.

Lemma extend_tc_test_eq:
  forall {CS: compspecs} e1 e2 rho,
 boxy extendM (denote_tc_assert (tc_test_eq e1 e2) rho).
Proof.
intros.
rewrite denote_tc_assert_test_eq'.
apply boxy_i; intros.
apply extendM_refl.
simpl in *.
super_unfold_lift.
unfold denote_tc_test_eq in *.
destruct (eval_expr e1 rho); auto;
destruct (eval_expr e2 rho); auto.
+ destruct H0; split; auto.
  destruct H1 as [H1|H1]; [left|right];
  apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H1).
+ destruct H0; split; auto.
  destruct H1 as [H1|H1]; [left|right];
  apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H1).
+
 unfold test_eq_ptrs in *.
 simple_if_tac;
 (eapply boxy_e;
  [apply extend_andp; try apply extend_orp; apply extend_valid_pointer' | apply H | apply H0]).
Qed.

Lemma extend_tc_test_order:
  forall {CS: compspecs} e1 e2 rho,
 boxy extendM (denote_tc_assert (tc_test_order e1 e2) rho).
Proof.
intros.
rewrite denote_tc_assert_test_order'.
apply boxy_i; intros.
apply extendM_refl.
simpl in *.
super_unfold_lift.
unfold denote_tc_test_order in *.
destruct (eval_expr e1 rho); auto;
destruct (eval_expr e2 rho); auto.
+ unfold test_order_ptrs in *.
  simple_if_tac; auto.
 eapply boxy_e;
  [apply extend_andp; eapply extend_orp; apply extend_valid_pointer' | apply H | apply H0].
Qed.

Lemma extend_isCastResultType:
 forall {CS: compspecs} t t' v rho,
   boxy extendM (denote_tc_assert (isCastResultType t t' v) rho).
Proof.
intros.
 unfold isCastResultType;
 destruct (classify_cast t t');
 repeat apply extend_tc_andp;
 try match goal with |- context [eqb_type _ _] => destruct (eqb_type t t') end;
 repeat match goal with
 | |- boxy _ (match ?A with  _ => _ end) => destruct A
 | |- boxy _ (denote_tc_assert (if ?A then _ else _) rho) => destruct A
 | |- boxy _ (denote_tc_assert (match t' with _ => _ end) rho) =>
        destruct t' as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ]
 end;
 repeat apply extend_tc_andp;
 try apply extend_prop;
 try simple apply extend_tc_bool;
 try simple apply extend_tc_Zge;
 try simple apply extend_tc_Zle;
 try simple apply extend_tc_iszero;
 try simple apply extend_tc_test_eq;
 try simple apply extend_tc_test_order.
Qed.

Lemma extend_tc_temp_id: forall {CS: compspecs} id ty Delta e rho, boxy extendM (tc_temp_id id ty Delta e rho).
Proof.
intros. unfold tc_temp_id. unfold typecheck_temp_id.
destruct ((temp_types Delta) ! id) as [? | ];
 repeat apply extend_tc_andp;
 try apply extend_prop;
 try simple apply extend_tc_bool.
 apply extend_isCastResultType.
Qed.

Lemma extend_tc_samebase:
  forall {CS: compspecs} e1 e2 rho,
boxy extendM (denote_tc_assert (tc_samebase e1 e2) rho).
Proof.
intros.
unfold denote_tc_assert; simpl.
unfold_lift.
destruct (eval_expr e1 rho), (eval_expr e2 rho);
  apply extend_prop.
Qed.

Lemma extend_tc_nonzero:
 forall {CS: compspecs} v rho,
   boxy extendM (denote_tc_assert (tc_nonzero v) rho).
Proof.
intros.
rewrite denote_tc_assert_nonzero.
destruct (eval_expr v rho); apply extend_prop.
Qed.


Lemma extend_tc_nodivover:
 forall {CS: compspecs} e1 e2 rho,
   boxy extendM (denote_tc_assert (tc_nodivover e1 e2) rho).
Proof.
intros.
rewrite denote_tc_assert_nodivover.
destruct (eval_expr e1 rho); try apply extend_prop;
destruct (eval_expr e2 rho); try apply extend_prop.
Qed.

Lemma extend_tc_nosignedover:
 forall op {CS: compspecs} e1 e2 rho,
   boxy extendM (denote_tc_assert (tc_nosignedover op e1 e2) rho).
Proof.
intros.
unfold denote_tc_assert.
unfold_lift.
unfold denote_tc_nosignedover.
destruct (eval_expr e1 rho); try apply extend_prop;
destruct (eval_expr e2 rho); try apply extend_prop.
Qed.

Lemma extend_tc_nobinover:
 forall op {CS: compspecs} e1 e2 rho,
   boxy extendM (denote_tc_assert (tc_nobinover op e1 e2) rho).
Proof.
intros.
unfold tc_nobinover.
unfold if_expr_signed.
destruct (typeof e1); try apply extend_prop.
destruct s; try apply extend_prop.
destruct (eval_expr e1 any_environ); try apply extend_prop;
destruct (eval_expr e2 any_environ); try apply extend_prop;
try apply extend_tc_nosignedover;
simple_if_tac; try apply extend_prop; try apply extend_tc_nosignedover.
destruct (eval_expr e1 any_environ); try apply extend_prop;
destruct (eval_expr e2 any_environ); try apply extend_prop;
try apply extend_tc_nosignedover;
try destruct s; try apply extend_prop; try apply extend_tc_nosignedover.
all: simple_if_tac; try apply extend_prop; try apply extend_tc_nosignedover.
Qed.

Lemma boxy_orp {A} `{H : ageable A}:
     forall (M: modality) , reflexive _ (app_mode M) ->
      forall P Q, boxy M P -> boxy M Q -> boxy M (P || Q).
Proof.
destruct M;
intros.
simpl in *.
apply boxy_i; intros; auto.
destruct H4; [left|right];
eapply boxy_e; eauto.
Qed.

Lemma extend_tc_orp:
 forall {CS: compspecs} A B rho,
   boxy extendM (denote_tc_assert A rho) ->
   boxy extendM (denote_tc_assert B rho) ->
   boxy extendM (denote_tc_assert (tc_orp A B) rho).
Proof.
intros.
rewrite denote_tc_assert_orp.
apply boxy_orp; auto.
apply extendM_refl.
Qed.


Lemma extend_tc_ilt:
 forall {CS: compspecs} e i rho,
   boxy extendM (denote_tc_assert (tc_ilt e i) rho).
Proof.
intros.
rewrite denote_tc_assert_ilt'.
simpl. unfold_lift.
destruct (eval_expr e rho); try apply extend_prop.
Qed.

Lemma extend_tc_llt:
 forall {CS: compspecs} e i rho,
   boxy extendM (denote_tc_assert (tc_llt e i) rho).
Proof.
intros.
rewrite denote_tc_assert_llt'.
simpl. unfold_lift.
destruct (eval_expr e rho); try apply extend_prop.
Qed.

Lemma extend_tc_andp':
 forall {CS: compspecs} A B rho,
   boxy extendM (denote_tc_assert A rho) ->
   boxy extendM (denote_tc_assert B rho) ->
   boxy extendM (denote_tc_assert (tc_andp' A B) rho).
Proof.
intros.
apply boxy_andp; auto.
apply extendM_refl.
Qed.

Ltac extend_tc_prover := 
  match goal with
  | |- _ => solve [immediate]
  | |- _ => apply extend_prop
  | |- _ => first
              [ simple apply extend_tc_bool
              | simple apply extend_tc_int_or_ptr_type
              | simple apply extend_tc_andp
              | simple apply extend_tc_andp'
              | simple apply extend_tc_Zge
              | simple apply extend_tc_Zle
              | simple apply extend_tc_iszero
              | simple apply extend_tc_nonzero
              | simple apply extend_tc_nodivover
              | simple apply extend_tc_nobinover
              | simple apply extend_tc_samebase
              | simple apply extend_tc_ilt
              | simple apply extend_tc_llt
              | simple apply extend_isCastResultType
              | simple apply extend_tc_test_eq
              | simple apply extend_tc_test_order]
  | |- boxy _ (denote_tc_assert (if ?A then _ else _) _) => destruct A
  | |- boxy _ (denote_tc_assert match tc_bool ?A _ with _ => _ end _) =>
             destruct A
  | |- boxy _ (denote_tc_assert match ?A with Some _ => _ | None => _ end _) =>
          destruct A
  end.

Lemma extend_tc_binop: forall {CS: compspecs} Delta e1 e2 b t rho, 
  boxy extendM (denote_tc_assert (typecheck_expr Delta e1) rho) ->
  boxy extendM (denote_tc_assert (typecheck_expr Delta e2) rho) ->
  boxy extendM (denote_tc_assert (isBinOpResultType b e1 e2 t) rho).
Proof.
intros.
destruct b;
unfold isBinOpResultType, tc_int_or_ptr_type, check_pp_int;
match goal with
| |- context [classify_add] => destruct (classify_add (typeof e1) (typeof e2)) eqn:C
| |- context [classify_sub] => destruct (classify_sub (typeof e1) (typeof e2)) eqn:C
| |- context [classify_cmp] => destruct (classify_cmp (typeof e1) (typeof e2)) eqn:C
| |- context [classify_shift] => destruct (classify_shift (typeof e1) (typeof e2)) eqn:C
| |- _ => idtac
end;
repeat extend_tc_prover;
destruct (typeof e1) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
destruct (typeof e2) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
try inv C; try apply extend_prop;
unfold binarithType, classify_binarith; repeat extend_tc_prover.
Qed.

Lemma extend_tc_expr: forall {CS: compspecs} Delta e rho, boxy extendM (tc_expr Delta e rho)
 with extend_tc_lvalue: forall {CS: compspecs} Delta e rho, boxy extendM (tc_lvalue Delta e rho).
Proof.
*
 clear extend_tc_expr.
 intros.
 unfold tc_expr.
 unfold tc_lvalue in extend_tc_lvalue.
  induction e; simpl;
  try pose proof (extend_tc_lvalue CS Delta e rho);
  clear extend_tc_lvalue;
try solve [
  repeat extend_tc_prover;
  try destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
  simpl;
  repeat extend_tc_prover
 ].
 + (* unop *)
   repeat extend_tc_prover.
   destruct u; simpl; repeat extend_tc_prover;
   destruct (typeof e) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
   simpl; repeat extend_tc_prover.
   unfold denote_tc_assert. unfold_lift. apply extend_tc_nosignedover.
   unfold denote_tc_assert. unfold_lift. apply extend_tc_nosignedover.
   unfold denote_tc_assert. unfold_lift. apply extend_tc_nosignedover.
   unfold denote_tc_assert. unfold_lift. apply extend_tc_nosignedover.
 + repeat extend_tc_prover. eapply extend_tc_binop; eauto.
 + 
  destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
  repeat extend_tc_prover;
   destruct (typeof e) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
   simpl; repeat extend_tc_prover.
*
 clear extend_tc_lvalue.
 intros.
 unfold tc_expr in *.
 unfold tc_lvalue.
 induction e; simpl;
 try specialize (extend_tc_expr CS Delta e rho);
 repeat extend_tc_prover;
 destruct (typeof e) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 simpl; repeat extend_tc_prover.
Qed.

Lemma extend_tc_exprlist: forall {CS: compspecs} Delta t e rho, boxy extendM (tc_exprlist Delta t e rho).
Proof.
 intros. unfold tc_exprlist.
  revert e; induction t; destruct e; intros; simpl; auto;
  try apply extend_prop.
 repeat apply extend_tc_andp; auto.
 apply extend_tc_expr.
 try simple apply extend_isCastResultType.
Qed.

Lemma extend_tc_expropt: forall {CS: compspecs} Delta e t rho, boxy extendM (tc_expropt Delta e t rho).
Proof.
  intros. unfold tc_expropt.
  destruct e.
  + apply extend_tc_expr.
  + apply extend_prop.
Qed.

Hint Resolve extend_tc_expr extend_tc_temp_id extend_tc_temp_id_load extend_tc_exprlist extend_tc_expropt extend_tc_lvalue.
Hint Resolve (@extendM_refl rmap _ _ _ _ _).

Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.expr_lemmas.

Section CENV_SUB.
  Context {CS CS': compspecs}
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')).
  
  Lemma tc_expr_cenv_sub a rho Delta w (T: @tc_expr CS Delta a rho w): @tc_expr CS' Delta a rho w.
  Proof. unfold tc_expr in *. apply  (denote_tc_assert_cenv_sub' CSUB); trivial. Qed.
  
   Lemma tc_iszero_cenv_sub Delta rho w: forall e
     (TC: @tc_expr CS Delta e rho w),
    (@denote_tc_assert CS (@tc_iszero CS e) rho) w ->
    (@denote_tc_assert CS' (@tc_iszero CS' e) rho) w.
   Proof.
   intros.
    rewrite denote_tc_assert_iszero' in H.
    rewrite denote_tc_assert_iszero' in *.
    simpl in *. super_unfold_lift.
    unfold denote_tc_iszero in *.
    destruct (@eval_expr CS e rho) eqn:Hv; auto; try contradiction.
    apply eval_expr_cenv_sub_Vint in Hv; eauto; rewrite Hv; auto.
    apply eval_expr_cenv_sub_Vlong in Hv; eauto; rewrite Hv; auto.
   Qed.
  
  Lemma eqb_type_false': forall a b, a<>b -> eqb_type a b = false.
  Proof. intros. apply eqb_type_false; auto. Qed.

Lemma denote_tc_assert_iszero_cenv_sub'' rho w:
  forall e
    (CAST: app_pred (@denote_tc_assert CS (@tc_iszero CS e) rho) w),
    app_pred (@denote_tc_assert CS (@tc_iszero CS' e) rho) w.
Proof.
intros.
unfold tc_iszero in *.
destruct (@eval_expr CS e any_environ) eqn:?; auto.
-
simpl in CAST.
unfold_lift in CAST.
destruct (@eval_expr CS e rho) eqn:?; auto;
try contradiction CAST;
destruct (@eval_expr CS' e any_environ) eqn:?; auto;
try solve [simpl; unfold_lift; rewrite Heqv0; auto].
 +
  apply (eval_expr_cenv_sub_Vint CSUB) in Heqv0.
  apply (eval_expr_any rho) in Heqv1; [ | clear; congruence].
  inversion2 Heqv0 Heqv1.
  do 3 red in CAST. simpl in CAST. 
  rewrite (is_true_e _ CAST).
  apply I.
 +
  apply (eval_expr_cenv_sub_Vint CSUB) in Heqv0.
  apply (eval_expr_any rho) in Heqv1; [ | clear; congruence].
  inversion2 Heqv0 Heqv1.
 +
  apply (eval_expr_cenv_sub_Vlong CSUB) in Heqv0.
  apply (eval_expr_any rho) in Heqv1; [ | clear; congruence].
  inversion2 Heqv0 Heqv1.
 +
  apply (eval_expr_cenv_sub_Vlong CSUB) in Heqv0.
  apply (eval_expr_any rho) in Heqv1; [ | clear; congruence].
  inversion2 Heqv0 Heqv1. 
  do 3 red in CAST. simpl in CAST. 
  rewrite (is_true_e _ CAST).
  apply I.
-
apply (eval_expr_cenv_sub_Vint CSUB) in Heqv.
rewrite Heqv. auto.
-
apply (eval_expr_cenv_sub_Vlong CSUB) in Heqv.
rewrite Heqv. auto.
-
apply (eval_expr_cenv_sub_Vfloat CSUB) in Heqv.
rewrite Heqv. auto.
-
apply (eval_expr_cenv_sub_Vsingle CSUB) in Heqv.
rewrite Heqv. auto.
-
apply (eval_expr_cenv_sub_Vptr CSUB) in Heqv.
rewrite Heqv. auto.
Qed.

Require Import VST.veric.binop_lemmas4.

Lemma denote_tc_assert_test_eq_cenv_sub'' rho w:
  forall e1 e2
    (CAST: app_pred (@denote_tc_assert CS (@tc_test_eq CS e1 e2) rho) w),
    app_pred (@denote_tc_assert CS (@tc_test_eq CS' e1 e2) rho) w.
Proof.
intros.
unfold tc_test_eq in *.
destruct (@eval_expr CS e1 any_environ) eqn:?; auto;
simpl in CAST;
unfold_lift in CAST;
unfold denote_tc_test_eq in CAST;
repeat 
 (match goal with
  | H: app_pred (denote_tc_assert match @eval_expr CS ?e ?rho with _ => _ end _) _ |- _ =>
         destruct (@eval_expr CS e rho) eqn:?H
  | H: app_pred match @eval_expr CS ?e ?rho with _ => _ end _ |- _ =>
         destruct (@eval_expr CS e rho) eqn:?H
  | |- app_pred (denote_tc_assert match @eval_expr ?cs ?e ?rho with _ => _ end _) _ =>
     destruct (@eval_expr cs e rho) eqn:?H
(*  | |- app_pred match @eval_expr ?cs ?e ?rho with _ => _ end _ =>
     destruct (@eval_expr cs e rho) eqn:?H*)
  | H: @eval_expr CS _ _ = _ |- _ => rewrite H
  | H: @eval_expr CS ?e any_environ = _,
    H': @eval_expr CS' ?e' rho = _ |- _ =>
          constr_eq e e'; 
       rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ H) in H'; 
        symmetry in H'; inv H'
  | H: @eval_expr ?cs ?e any_environ = _ |- _ =>
          lazymatch goal with H': @eval_expr cs e rho = _ |- _ => fail | _ => idtac end;
          apply (eval_expr_any rho) in H; [| clear; congruence]
  | H: @eval_expr CS ?e rho = Vint _,
    H': @eval_expr CS' ?e' rho =  _ |- _ =>
      constr_eq e e'; 
       rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ H) in H';
      symmetry in H'; inv H'
  | H: @eval_expr CS ?e rho = Vlong _,
    H': @eval_expr CS' ?e' rho =  _ |- _ =>
      constr_eq e e'; 
       rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ H) in H';
      symmetry in H'; inv H'
  | H: @eval_expr CS ?e rho = Vptr _ _,
    H': @eval_expr CS' ?e' rho =  _ |- _ =>
      constr_eq e e'; 
       rewrite (eval_expr_cenv_sub_Vptr CSUB _ _ _ _ H) in H';
      symmetry in H'; inv H'
 | H: app_pred (denote_tc_assert (tc_test_eq' _ _) _) _ |- _ =>
    simpl in H; unfold denote_tc_test_eq in H; unfold_lift in H
 | |- app_pred (denote_tc_assert (tc_test_eq' _ _) _) _ => 
        unfold denote_tc_assert, denote_tc_test_eq; unfold_lift
 | H: app_pred (andp _ _) _ |- _ => destruct H
 | H: app_pred (prop _) _ |- _ => simpl in H
 |  |- app_pred ((` denote_tc_test_eq) _ _ _) _  =>
    unfold denote_tc_test_eq; unfold_lift
 |  H: app_pred ((` denote_tc_test_eq) _ _ _) _ |- _ =>
    unfold denote_tc_test_eq in H; unfold_lift in H
 | H: app_pred (if Archi.ptr64 then _ else _) _ |- _ =>
   destruct Archi.ptr64 eqn:Hp; try contradiction
 | Hp: Archi.ptr64 = _ |- context[Archi.ptr64] => rewrite Hp
 | |- context [Archi.ptr64] => destruct Archi.ptr64 eqn:Hp
 | Hp: Archi.ptr64 = _ , H: context[Archi.ptr64] |- _ => rewrite Hp in H
 | H: app_pred (denote_tc_assert (if ?A then _ else _) _) _ |- _ =>
   match A with context [Int.eq ?i Int.zero] =>
     let H1 := fresh "H" in 
     assert (H1 := Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero)
   end
 | H: Vint _ = Vint _ |- _ => inv H
 | H: Vlong _ = Vlong _ |- _ => inv H
 | |- _ => rewrite Int.eq_true
 | |- _ => rewrite Int64.eq_true
 | |- _ => progress (simpl in *)
  end; auto; try contradiction; simpl; subst; try congruence; auto).
Qed.

    Lemma isCastResultType_cenv_sub Delta rho w: forall e a
    (TC: @tc_expr CS Delta e rho w)
    (CAST: @denote_tc_assert CS (@isCastResultType CS  (typeof e) a e) rho w),
    @denote_tc_assert CS' (@isCastResultType CS' (typeof e) a e) rho w.
  Proof.
intros.
simple apply (denote_tc_assert_cenv_sub CSUB); auto.
unfold isCastResultType in *.
destruct (classify_cast (typeof e) a); auto.
-
destruct (eqb_type (typeof e) a); auto.
simple_if_tac; auto.
simple_if_tac; auto.
simple_if_tac; auto.
simple_if_tac; auto.
simple_if_tac; auto.
eapply denote_tc_assert_iszero_cenv_sub''; eauto.
-
rewrite denote_tc_assert_andp in CAST; 
rewrite denote_tc_assert_andp; destruct CAST; split; auto.
destruct (is_pointer_type a); auto.
eapply denote_tc_assert_iszero_cenv_sub''; eauto.
-
rewrite denote_tc_assert_andp in CAST; 
rewrite denote_tc_assert_andp; destruct CAST; split; auto.
destruct (is_pointer_type a); auto.
eapply denote_tc_assert_iszero_cenv_sub''; eauto.
-
destruct (is_pointer_type _); auto.
eapply denote_tc_assert_test_eq_cenv_sub''; eauto.
-
destruct (is_pointer_type _); auto.
eapply denote_tc_assert_test_eq_cenv_sub''; eauto.
Qed.

  Lemma tc_exprlist_cenv_sub (*{CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS'))*) Delta rho w:
    forall types bl, (@tc_exprlist CS Delta types bl rho) w ->
                     (@tc_exprlist CS' Delta types bl rho) w.
  Proof.
    induction types; simpl; intros.
    + destruct bl; simpl in *; trivial.
    + destruct bl; simpl in *; trivial.
        specialize (IHtypes bl).
      unfold tc_exprlist in H|-*. rename a into t.
   unfold typecheck_exprlist; fold typecheck_exprlist.
      change 
        (app_pred (@denote_tc_assert CS
            (tc_andp (@typecheck_expr CS Delta (Ecast e t))
             (@typecheck_exprlist CS Delta types bl))  rho) w) in H.
    rewrite denote_tc_assert_andp in H.
    rewrite denote_tc_assert_andp.
    destruct H. split; auto.
    eapply tc_expr_cenv_sub; try eassumption.
  Qed.

  End CENV_SUB.