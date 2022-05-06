Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.

Require Import VST.veric.seplog. (*For definition of tycontext*)
Import LiftNotation.
Import compcert.lib.Maps.
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
   match e with None => `!!(t=Ctypes.Tvoid)
                     | Some e' => tc_expr Delta (Ecast e' t)
   end.

Definition tc_temp_id_load id tfrom Delta v : environ -> mpred  :=
fun rho => !! (exists tto, (temp_types Delta) ! id = Some tto
                      /\ tc_val tto (eval_cast tfrom tto (v rho))).

Lemma extend_prop: forall P, boxy extendM (prop P : mpred).
Proof.
intros.
hnf.
apply pred_ext. intros ? ?. apply H; auto. apply extendM_refl.
repeat intro. apply H.
Qed.

#[export] Hint Resolve extend_prop : core.

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
intros ?; hnf.
exists (core x); apply join_comm, core_unit.
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

Lemma extend_andp: forall (P Q : mpred),
  boxy extendM P -> boxy extendM Q -> boxy extendM (andp P Q).
Proof.
 intros.
 apply boxy_i; intros.
 apply extendM_refl.
 destruct H2; split; eapply boxy_e; eauto.
Qed.

Lemma extend_orp: forall (P Q : mpred), 
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
destruct (typeof e1) as [ | _ [ | ] _ | | | | | | | ],
       (typeof e2) as [ | _ [ | ] _ | | | | | | | ];
unfold denote_tc_nosignedover;
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
destruct (typeof e1) as [ | _ [ | ] _ | [ | ] _ | | | | | | ],
       (typeof e2) as [ | _ [ | ] _ | [ | ] _ | | | | | | ];
      try apply extend_prop;
destruct (eval_expr e1 any_environ); try apply extend_prop;
destruct (eval_expr e2 any_environ); try apply extend_prop;
try apply extend_tc_nosignedover.
all:
simple_if_tac; try apply extend_prop; try apply extend_tc_nosignedover.
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
intros ?; eexists; apply join_comm, core_unit.
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
intros ?; eexists; apply join_comm, core_unit.
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
   unfold denote_tc_assert. unfold_lift. apply extend_tc_nosignedover.
 + repeat extend_tc_prover. eapply extend_tc_binop; eauto.
 + 
  destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
  repeat extend_tc_prover;
   destruct (typeof e) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
   simpl; repeat extend_tc_prover.
   destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ]; 
  repeat extend_tc_prover.
   destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[[] [|]] | ]; 
  repeat extend_tc_prover.
   destruct (field_offset (@cenv_cs CS) i (co_members c0)) as [[? [|]] | ]; 
  repeat extend_tc_prover.
   destruct (union_field_offset (@cenv_cs CS) i (co_members c0)) as [[[] [|]] | ]; 
  repeat extend_tc_prover.
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
   destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ]; 
  repeat extend_tc_prover.
   destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[[] [|]] | ]; 
  repeat extend_tc_prover.
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

Definition extendM_refl_rmap := @extendM_refl rmap _ _ _ _ _.

#[export] Hint Resolve extend_tc_expr extend_tc_temp_id extend_tc_temp_id_load extend_tc_exprlist extend_tc_expropt extend_tc_lvalue : core.
#[export] Hint Resolve extendM_refl_rmap : core.

Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.expr_lemmas.

Lemma tc_bool_i:
 forall {cs: compspecs} b e rho w,
   b = true -> app_pred (denote_tc_assert (tc_bool b e) rho) w.
Proof.
intros. subst. apply I.
Qed.

Section CENV_SUB.
  Context {CS CS': compspecs}
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')).

 Definition is_tc_FF (a: tc_assert) :=
  match a with tc_FF _ => True | _ => False end.

 Definition dec_tc_FF (a: tc_assert) : {is_tc_FF a}+{~is_tc_FF a}.
 Proof. destruct a; simpl; auto. Qed.


  Lemma tc_nodivover'_cenv_sub a1 a2 rho w:
   app_pred (@denote_tc_assert CS (@tc_nodivover' a1 a2) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_nodivover' a1 a2) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a1 rho) Vundef).
  rewrite e. simpl. tauto.
  destruct (Val.eq (@eval_expr CS a2 rho) Vundef).
  rewrite e. destruct (@eval_expr CS a1 rho); simpl; intro H; contradiction H.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n0).
  auto.
  Qed.  


  Lemma tc_samebase_cenv_sub a1 a2 rho w:
   app_pred (@denote_tc_assert CS (@tc_samebase a1 a2) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_samebase a1 a2) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a1 rho) Vundef).
  rewrite e. simpl. tauto.
  destruct (Val.eq (@eval_expr CS a2 rho) Vundef).
  rewrite e. destruct (@eval_expr CS a1 rho); simpl; intro H; contradiction H.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n0).
  auto.
  Qed.  


  Lemma tc_nonzero'_cenv_sub a rho w:
   app_pred (@denote_tc_assert CS (@tc_nonzero' a) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_nonzero' a) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a rho) Vundef).
  rewrite e. simpl. tauto.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  auto.
  Qed.  

  Lemma tc_ilt'_cenv_sub a i rho w:
   app_pred (@denote_tc_assert CS (@tc_ilt' a i) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_ilt' a i) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a rho) Vundef).
  rewrite e. simpl. tauto.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  auto.
  Qed.  

  Lemma tc_llt'_cenv_sub a i rho w:
   app_pred (@denote_tc_assert CS (@tc_llt' a i) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_llt' a i) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a rho) Vundef).
  rewrite e. simpl. tauto.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  auto.
  Qed.  

  Lemma tc_test_eq'_cenv_sub a1 a2 rho w:
   app_pred (@denote_tc_assert CS (@tc_test_eq' a1 a2) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_test_eq' a1 a2) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a1 rho) Vundef).
  rewrite e. simpl. tauto.
  destruct (Val.eq (@eval_expr CS a2 rho) Vundef).
  rewrite e. destruct (@eval_expr CS a1 rho); simpl; intro H; contradiction H.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n0).
  auto.
  Qed.  

  Lemma tc_test_eq_cenv_sub a1 a2 rho w:
   app_pred (@denote_tc_assert CS (@tc_test_eq CS a1 a2) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_test_eq CS' a1 a2) rho) w.
  Proof.
  rewrite !denote_tc_assert_test_eq'.
  apply tc_test_eq'_cenv_sub.
  Qed.

  Lemma tc_test_order'_cenv_sub a1 a2 rho w:
   app_pred (@denote_tc_assert CS (@tc_test_order' a1 a2) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_test_order' a1 a2) rho) w.
  Proof.
  simpl. unfold_lift.
  destruct (Val.eq (@eval_expr CS a1 rho) Vundef).
  rewrite e. simpl. tauto.
  destruct (Val.eq (@eval_expr CS a2 rho) Vundef).
  rewrite e. destruct (@eval_expr CS a1 rho); simpl; intro H; contradiction H.
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n).
  rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n0).
  auto.
  Qed.

Ltac tc_expr_cenv_sub_tac := 
repeat
match goal with
 | H: app_pred (@denote_tc_assert _ (tc_andp _ _) _) _ |- _ =>
     rewrite denote_tc_assert_andp in H; destruct H
 | |- app_pred (@denote_tc_assert _ (tc_andp _ _) _) _ =>
     rewrite denote_tc_assert_andp; split
 | H: app_pred (@denote_tc_assert _ (tc_andp' _ _) _) _ |- _ =>
     destruct H
 | |- app_pred (@denote_tc_assert _ (tc_andp' _ _) _) _ =>
      split
 | |- _ => solve [simple apply tc_bool_i; auto]
 | H: app_pred (@denote_tc_assert _ (tc_bool _ _) _) _ |- _ =>
      apply tc_bool_e in H; rewrite ?H in *
 | |- app_pred (@denote_tc_assert _ (tc_bool true _) _) _ =>
     apply I
  | |- app_pred (@denote_tc_assert _ (tc_isptr ?a) _) _  =>
       apply (isptr_eval_expr_cenv_sub CSUB); auto
 | |- app_pred (@denote_tc_assert _ tc_TT _) _ => apply I
 | |- app_pred (@denote_tc_assert _ (tc_bool (complete_type _ _) _) _) _ =>
           solve [rewrite (cenv_sub_complete_type _ _ CSUB); simpl; auto]
 | |- context [tc_int_or_ptr_type] =>
           solve [unfold tc_int_or_ptr_type in *; tc_expr_cenv_sub_tac]
 | |- _ => solve [simple apply tc_nodivover'_cenv_sub; auto]
 | |- _ => solve [simple apply tc_samebase_cenv_sub; auto]
 | |- _ => solve [simple apply tc_nonzero'_cenv_sub; auto]
 | |- _ => solve [simple apply tc_ilt'_cenv_sub; auto]
 | |- _ => solve [simple apply tc_llt'_cenv_sub; auto]
 | |- _ => solve [simple apply tc_test_eq'_cenv_sub; auto]
 | |- _ => solve [simple apply tc_test_eq_cenv_sub; auto]
 | |- _ => solve [simple apply tc_test_order'_cenv_sub; auto]
 | |- app_pred (denote_tc_assert (tc_bool ?A _) _) _ =>
    match A with context [sizeof ?t] => unfold sizeof;
     rewrite (cenv_sub_sizeof CSUB t) by assumption;
     solve [simple apply tc_bool_i; auto]
   end
end;
  try solve [eauto].


Ltac tc_expr_cenv_sub_tac2 :=  
 (match goal with
   | H: app_pred (@denote_tc_assert _ match @eval_expr CS ?a ?rho with _ => _ end _) _ |- _ =>
        let H' := fresh in
        destruct (Val.eq (@eval_expr CS a rho) Vundef) as [H' | H' ];
         [ rewrite H' in H;
            try match goal with |- context [@eval_expr CS' a rho] =>
             destruct (@eval_expr CS' a rho) eqn:?
           end
         | rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ H');
           destruct (@eval_expr CS a rho) eqn:?]
    | |- app_pred (@denote_tc_assert _ match @eval_expr CS' ?a ?rho with _ => _ end _) _ =>
       destruct (@eval_expr CS' a rho) eqn:?H
    | |- app_pred (@denote_tc_assert _ (if _ then tc_TT else _) _) _ =>
    simple_if_tac; [apply I | ]
   end;
  try assumption;
  try (simple apply (denote_tc_assert_cenv_sub CSUB); auto)).

  Lemma tc_nobinover_cenv_sub op a1 a2 rho w:
   app_pred (@denote_tc_assert CS (@tc_nobinover op CS a1 a2) rho) w ->
   app_pred (@denote_tc_assert CS' (@tc_nobinover op CS' a1 a2) rho) w.
 Proof.
  unfold tc_nobinover.
  unfold if_expr_signed.
  intros.
  destruct (typeof a1) as [ | _ [ | ] | [ | ] | [ | ] | | | | | ]; 
  destruct (typeof a2) as [ | _ [ | ] | [ | ]  | | | | | | ]; 
  tc_expr_cenv_sub_tac; repeat tc_expr_cenv_sub_tac2.
 Qed.
  
Lemma tc_expr_cenv_sub_unop:
 forall 
 (u : unary_operation)
 (a : expr)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (w : rmap)
 (T : (@tc_expr CS Delta (Eunop u a t) rho) w)
 (IHa : (@tc_expr CS Delta a rho) w -> (@tc_expr CS' Delta a rho) w),
 (@tc_expr CS' Delta (Eunop u a t) rho) w.
Proof.
  intros.
  unfold tc_expr in *; simpl in T|-*.
  tc_expr_cenv_sub_tac.
  destruct u; simpl in H|-*;
  destruct (typeof a) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
  tc_expr_cenv_sub_tac.
  unfold tc_int_or_ptr_type in *;
  tc_expr_cenv_sub_tac.  
  all: try apply (denote_tc_nosignedover_eval_expr_cenv_sub CSUB); auto.
 pose proof (denote_tc_nosignedover_eval_expr_cenv_sub CSUB rho
                        (Econst_long Int64.zero (Ctypes.Tlong Signed a0)) a w Z.sub Signed ).
 simpl eval_expr in H2. 
  unfold denote_tc_assert in H1|-*. 
  replace (typeof (Econst_long Int64.zero (Ctypes.Tlong Signed a0)))
  with (Ctypes.Tlong Signed a0) in * by (destruct a0; reflexivity).
  simpl in H1|-*.
  destruct (typeof a); auto.
  destruct s; auto.
  apply (denote_tc_nosignedover_eval_expr_cenv_sub CSUB rho
                        (Econst_long Int64.zero (Ctypes.Tlong Signed a0)) a w Z.sub Unsigned); 
    auto.
Qed.


Lemma denote_tc_assert_andp_i:
  forall x y rho w, 
   app_pred (denote_tc_assert x rho) w ->
   app_pred (denote_tc_assert y rho) w ->
   app_pred (denote_tc_assert (tc_andp x y) rho) w.
Proof.
intros.
rewrite denote_tc_assert_andp. split; auto.
Qed.

Lemma denote_tc_assert_andp'_imp:
 forall x x' y y' rho w,
  (app_pred (@denote_tc_assert CS x rho) w -> app_pred (@denote_tc_assert CS' x' rho) w) ->
  (app_pred (@denote_tc_assert CS y rho) w -> app_pred (@denote_tc_assert CS' y' rho) w) ->
  app_pred (@denote_tc_assert CS (tc_andp' x y) rho) w ->
  app_pred (@denote_tc_assert CS' (tc_andp' x' y') rho) w.
Proof.
intros.
destruct H1.
split; auto.
Qed.

Lemma denote_tc_assert_andp_imp:
 forall x x' y y' rho w,
  (app_pred (@denote_tc_assert CS x rho) w -> app_pred (@denote_tc_assert CS' x' rho) w) ->
  (app_pred (@denote_tc_assert CS y rho) w -> app_pred (@denote_tc_assert CS' y' rho) w) ->
  app_pred (@denote_tc_assert CS (tc_andp x y) rho) w ->
  app_pred (@denote_tc_assert CS' (tc_andp x' y') rho) w.
Proof.
intros.
rewrite @denote_tc_assert_andp in H1|-*.
eapply denote_tc_assert_andp'_imp; eauto.
Qed.

Lemma denote_tc_assert_andp'_imp2:
 forall x x' y y' rho w,
  (app_pred (@denote_tc_assert CS y rho) w -> 
   app_pred (@denote_tc_assert CS x rho) w -> 
   app_pred (@denote_tc_assert CS' x' rho) w) ->
  (app_pred (@denote_tc_assert CS x rho) w ->
   app_pred (@denote_tc_assert CS y rho) w ->
   app_pred (@denote_tc_assert CS' y' rho) w) ->
  app_pred (@denote_tc_assert CS (tc_andp' x y) rho) w ->
  app_pred (@denote_tc_assert CS' (tc_andp' x' y') rho) w.
Proof.
intros.
destruct H1.
split; auto.
Qed.

Lemma denote_tc_assert_andp_imp2:
 forall x x' y y' rho w,
  (app_pred (@denote_tc_assert CS y rho) w -> 
   app_pred (@denote_tc_assert CS x rho) w -> 
   app_pred (@denote_tc_assert CS' x' rho) w) ->
  (app_pred (@denote_tc_assert CS x rho) w ->
   app_pred (@denote_tc_assert CS y rho) w ->
   app_pred (@denote_tc_assert CS' y' rho) w) ->
  app_pred (@denote_tc_assert CS (tc_andp x y) rho) w ->
  app_pred (@denote_tc_assert CS' (tc_andp x' y') rho) w.
Proof.
intros.
rewrite @denote_tc_assert_andp in H1|-*.
eapply denote_tc_assert_andp'_imp2; eauto.
Qed.

Lemma tc_bool_cenv_sub:
 forall b e rho w,
  app_pred (@denote_tc_assert CS (tc_bool b e) rho) w ->
  app_pred (@denote_tc_assert CS' (tc_bool b e) rho) w.
Proof.
intros.
apply tc_bool_e in H.
apply tc_bool_i.
auto.
Qed.

Lemma tc_complete_type_cenv_sub:
 forall t e rho w,
  app_pred (@denote_tc_assert CS (tc_bool (complete_type (@cenv_cs CS) t) e) rho) w ->
  app_pred (@denote_tc_assert CS' (tc_bool (complete_type (@cenv_cs CS') t) e) rho) w.
Proof.
intros.
apply tc_bool_e in H.
apply tc_bool_i.
rewrite (cenv_sub_complete_type _ _ CSUB); auto.
Qed.

Local Lemma tc_andp'_intro:
  forall x y rho w Q P,
   (app_pred (@denote_tc_assert CS x rho) w ->
    app_pred (@denote_tc_assert CS y rho) w ->
    Q -> P) ->
   (app_pred (@denote_tc_assert CS (tc_andp' x y) rho) w -> Q -> P).
Proof.
intros.
destruct H; auto.
Qed.

Local Lemma tc_andp_intro:
  forall x y rho w Q P,
   (app_pred (@denote_tc_assert CS x rho) w ->
    app_pred (@denote_tc_assert CS y rho) w ->
    Q -> P) ->
   (app_pred (@denote_tc_assert CS (tc_andp x y) rho) w -> Q -> P).
Proof.
intros.
rewrite @denote_tc_assert_andp in H.
destruct H; auto.
Qed.

Local Lemma tc_bool_intro:
  forall b e rho w Q P,
   (b = true -> Q -> P) ->
   (app_pred (@denote_tc_assert CS (tc_bool b e) rho) w -> Q -> P).
Proof.
intros.
apply tc_bool_e in H. auto.
Qed.

Lemma tc_check_pp_int'_cenv_sub:
 forall a1 a2 op t e rho w,
 app_pred (@denote_tc_assert CS (check_pp_int' a1 a2 op t e) rho) w ->
 app_pred (@denote_tc_assert CS' (check_pp_int' a1 a2 op t e) rho) w.
Proof.
unfold check_pp_int'.
intros.
destruct op; try contradiction H; revert H;
 (apply denote_tc_assert_andp'_imp; 
  [ | apply tc_bool_cenv_sub]).
all: try simple apply tc_test_eq'_cenv_sub.
all: try simple apply tc_test_order'_cenv_sub.
Qed.

Lemma tc_expr_cenv_sub_binop:
 forall 
 (b : binary_operation)
 (a1 a2 : expr)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (w : rmap)
 (T : (@tc_expr CS Delta (Ebinop b a1 a2 t) rho) w)
 (IHa1 : (@tc_expr CS Delta a1 rho) w -> (@tc_expr CS' Delta a1 rho) w)
 (IHa2 : (@tc_expr CS Delta a2 rho) w -> (@tc_expr CS' Delta a2 rho) w),
 (@tc_expr CS' Delta (Ebinop b a1 a2 t) rho) w.
Proof.
  intros.
  rename T into H.
  revert H.
  unfold tc_expr, typecheck_expr;
  fold (@typecheck_expr CS);
  fold (@typecheck_expr CS').
  repeat apply denote_tc_assert_andp_imp; auto.
 clear - CSUB.
  rewrite !den_isBinOpR.
  cbv zeta.
   repeat match goal with |- _ -> app_pred (denote_tc_assert match ?A with _ => _ end _) _ =>
      destruct A; auto
   end;
  unfold tc_int_or_ptr_type.
Local Ltac andp_simpl := 
 repeat first [simple apply tc_andp'_intro
                  |simple apply tc_andp_intro
                  |simple apply tc_bool_intro; intro
                  |match goal with |- _ -> _ -> _ => intros _ end
                  ].

all:
 repeat
 first [simple apply denote_tc_assert_andp'_imp2; andp_simpl
        |simple apply denote_tc_assert_andp_imp2; andp_simpl
        |simple apply tc_bool_cenv_sub
        |apply isptr_eval_expr_cenv_sub; auto
        |simple apply tc_complete_type_cenv_sub
        |simple apply tc_nobinover_cenv_sub
        |simple apply tc_nodivover'_cenv_sub
        |simple apply tc_samebase_cenv_sub
        |simple apply tc_nonzero'_cenv_sub
        |simple apply tc_ilt'_cenv_sub
        |simple apply tc_llt'_cenv_sub
        |simple apply tc_test_eq'_cenv_sub
        |simple apply tc_test_eq_cenv_sub
        |simple apply tc_test_order'_cenv_sub
        |simple apply tc_check_pp_int'_cenv_sub
        |unfold sizeof; rewrite (cenv_sub_sizeof CSUB) by assumption
        | match goal with |- _ -> app_pred (denote_tc_assert (binarithType' _ _ _ _ _) _) _ =>
               unfold binarithType'; destruct (classify_binarith' _ _)
          end
        | solve [intro H; contradiction H]
     ].
Qed.

Lemma tc_expr_cenv_sub_cast:
 forall
 (a : expr)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (w : rmap)
 (T : (@tc_expr CS Delta (Ecast a t) rho) w)
 (IHa : (@tc_expr CS Delta a rho) w -> (@tc_expr CS' Delta a rho) w),
 (@tc_expr CS' Delta (Ecast a t) rho) w.
Proof.
  intros.
  unfold tc_expr in *; simpl in T|-*.
  tc_expr_cenv_sub_tac.
   unfold isCastResultType in *;
   repeat match goal with |- app_pred (denote_tc_assert match ?A with _ => _ end _) _ =>
      destruct A; tc_expr_cenv_sub_tac
   end;
   tc_expr_cenv_sub_tac; try simple_if_tac;
   try solve [simpl in *; super_unfold_lift;
                  try rewrite denote_tc_assert_iszero in H0;
                  try rewrite denote_tc_assert_iszero in H1;
                  rewrite ?denote_tc_assert_iszero;
                 destruct (Val.eq (@eval_expr CS a rho) Vundef) as [e|n];
                  [rewrite e in *; contradiction | 
                    rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ n); auto]].
Qed.

Lemma tc_expr_cenv_sub_field:
 forall
 (a : expr)
  (tc_lvalue_cenv_sub : forall  (rho : environ)
                       (Delta : tycontext) (w : rmap),
                     (@tc_lvalue CS Delta a rho) w ->
                     (@tc_lvalue CS' Delta a rho) w)
 (i : ident)
 (t : type) 
 (rho : environ)
 (Delta : tycontext)
 (w : rmap)
 (T : (@tc_expr CS Delta (Efield a i t) rho) w)
 (IHa : (@tc_expr CS Delta a rho) w -> (@tc_expr CS' Delta a rho) w),
 (@tc_expr CS' Delta (Efield a i t) rho) w.
Proof.
intros.
  unfold tc_expr in *; simpl in T|-*.
  tc_expr_cenv_sub_tac.
    destruct (access_mode t); tc_expr_cenv_sub_tac.
    destruct (typeof a); tc_expr_cenv_sub_tac.
   *
    destruct ((@cenv_cs CS) ! i0) eqn:?; try contradiction.
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]]|] eqn:?H; try contradiction.
    eapply (field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H1; try eassumption.
    rewrite H1; auto.
    intros.
    assert (H2' := CSUB id); hnf in H2'; rewrite H3 in H2'; auto.
    apply cenv_consistent.
   *
    destruct ((@cenv_cs CS) ! i0) eqn:?; try contradiction.
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[[] [|]]|] eqn:?H; try contradiction.
    rewrite <- (union_field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H1; try eassumption.
    rewrite H1. auto.
   intros. specialize (CSUB id).  hnf in CSUB.  rewrite H3 in CSUB; auto.
   apply co_consistent_complete. 
   apply (cenv_consistent i0); auto.
Qed.

Lemma tc_lvalue_cenv_sub_field:
 forall
 (a : expr)
 (i : ident)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (w : rmap) 
 (T : (@denote_tc_assert CS (@typecheck_lvalue CS Delta (Efield a i t)) rho) w)
 (IHa : (@denote_tc_assert CS (@typecheck_lvalue CS Delta a) rho) w ->
         (@denote_tc_assert CS' (@typecheck_lvalue CS' Delta a) rho) w),
(@denote_tc_assert CS' (@typecheck_lvalue CS' Delta (Efield a i t)) rho) w.
Proof.
   intros.
   simpl in T|-*;  tc_expr_cenv_sub_tac.
    destruct (typeof a); tc_expr_cenv_sub_tac.
   *
    destruct ((@cenv_cs CS) ! i0) eqn:?; try contradiction.
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (field_offset (@cenv_cs CS) i (co_members c))  as [[? [|]]|] eqn:?H; try contradiction.
    eapply (field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H1; try eassumption.
    rewrite H1; auto.
    intros.
    assert (H2' := CSUB id); hnf in H2'; rewrite H3 in H2'; auto.
    apply cenv_consistent.
   *
    destruct ((@cenv_cs CS) ! i0) eqn:?; try contradiction.
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[[] [|]]|] eqn:?H; try contradiction.
    rewrite <- (union_field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H1; try eassumption.
    rewrite H1. auto.
   intros. specialize (CSUB id).  hnf in CSUB.  rewrite H3 in CSUB; auto.
   apply co_consistent_complete. 
   apply (cenv_consistent i0); auto.
Qed.

Lemma tc_expr_cenv_sub a rho Delta w (T: @tc_expr CS Delta a rho w):
                            @tc_expr CS' Delta a rho w
     with tc_lvalue_cenv_sub a rho Delta w (T: @tc_lvalue CS Delta a rho w): 
                            @tc_lvalue CS' Delta a rho w.
  Proof.
- clear  tc_expr_cenv_sub.
  induction a;
  try solve [apply  (denote_tc_assert_cenv_sub CSUB); auto];
  try solve [unfold tc_expr in *; simpl in T|-*; tc_expr_cenv_sub_tac].
 + (* Ederef *)
  unfold tc_expr in *; simpl in T|-*.
  destruct (access_mode t) eqn:?H; auto.
  tc_expr_cenv_sub_tac.
 + (* Eunop *) 
    apply (tc_expr_cenv_sub_unop _ _ _ _ _ _ T IHa).
 + (* Ebinop *)
    apply (tc_expr_cenv_sub_binop _ _ _ _ _ _ _ T IHa1 IHa2).
 +  (* Ecast *)
    apply (tc_expr_cenv_sub_cast _ _ _ _ _ T IHa).
 + (* Efield *) 
    apply (tc_expr_cenv_sub_field a (tc_lvalue_cenv_sub a) _ _ _ _ _ T IHa).
- clear  tc_lvalue_cenv_sub.
  unfold tc_lvalue in *.
  induction a;
  try solve [apply  (denote_tc_assert_cenv_sub CSUB); auto].
 + (* Ederef *)
   rename T into H; revert H.
  unfold typecheck_lvalue;
   fold (@typecheck_lvalue CS); fold (@typecheck_lvalue CS');
   fold (@typecheck_expr CS); fold (@typecheck_expr CS').
   repeat simple apply denote_tc_assert_andp_imp.
   apply tc_expr_cenv_sub.
   apply tc_bool_cenv_sub.
   apply isptr_eval_expr_cenv_sub; auto.
 + (* Efield *) 
   apply (tc_lvalue_cenv_sub_field _ _ _ _ _ _ T IHa).
 Qed.

  Lemma tc_exprlist_cenv_sub Delta rho w:
    forall types bl, (@tc_exprlist CS Delta types bl rho) w ->
                     (@tc_exprlist CS' Delta types bl rho) w.
  Proof.
    induction types; simpl; intros.
    + destruct bl; simpl in *; trivial.
    + destruct bl. trivial.
       revert H.
    unfold tc_exprlist.
   unfold typecheck_exprlist; 
        fold (@typecheck_exprlist CS);
        fold (@typecheck_exprlist CS').
        simple apply denote_tc_assert_andp_imp.
        intros; eapply tc_expr_cenv_sub_cast; eauto.
        apply tc_expr_cenv_sub.
        apply IHtypes.
   Qed.
End CENV_SUB.