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

Require Import VST.veric.expr_lemmas.

Section CENV_SUB.
  Context {CS CS': compspecs}
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')).
  
  Lemma tc_expr_cenv_sub a rho Delta w (T: @tc_expr CS Delta a rho w): @tc_expr CS' Delta a rho w.
  Proof. unfold tc_expr in *. apply  (denote_tc_assert_cenv_sub' CSUB); trivial. Qed.
  
    Lemma eval_anyenv_cenv_sub: forall e, @eval_expr CS e any_environ = @eval_expr CS' e any_environ /\
                                        @eval_lvalue CS e any_environ = @eval_lvalue CS' e any_environ. 
  Proof.
    induction e; simpl in *; auto; intuition; unfold liftx, lift; simpl; try solve [rewrite H; trivial].
    assert (stable: forall id co, (@cenv_cs CS) ! id = @Some composite co -> (@cenv_cs CS') ! id = @Some composite co).
    { intros. specialize (CSUB id). rewrite H3 in CSUB. simpl in CSUB; trivial. }
    specialize (@Cop_sem_binary_operation_stable (@cenv_cs CS) (@cenv_cs CS') stable b); intros.
   Admitted. (*similar stuff in tycontext:
Lemma binop_stable_stable: forall b e1 e2,
  binop_stable env b e1 e2 = true ->
  binop_stable env' b e1 e2 = true.
Proof.
  intros.
  destruct b; unfold binop_stable in H |- *; auto.
  + destruct (Cop.classify_add (typeof e1) (typeof e2));
    try (eapply (complete_type_stable env env'); eauto).
     auto.
  + destruct (Cop.classify_sub (typeof e1) (typeof e2));
    try (eapply (complete_type_stable env env'); eauto).
     auto.
Qed.

Lemma Cop_Sem_add_ptr_int_stable ty si u v (H:complete_type env ty = true):
  Cop.sem_add_ptr_int env ty si u v =
  Cop.sem_add_ptr_int env' ty si u v.
Proof. unfold Cop.sem_add_ptr_int.
  destruct u; destruct v; trivial; erewrite <- sizeof_stable; eauto.
Qed.

Lemma Cop_Sem_add_ptr_long_stable ty u v (H:complete_type env ty = true):
  Cop.sem_add_ptr_long env ty u v =
  Cop.sem_add_ptr_long env' ty u v.
Proof. unfold Cop.sem_add_ptr_long.
  destruct u; destruct v; trivial; erewrite <- sizeof_stable; eauto.
Qed.

Lemma Cop_sem_binary_operation_stable:
  forall b v1 e1 v2 e2 m,
  binop_stable env b e1 e2 = true ->
  Cop.sem_binary_operation env b v1 (typeof e1) v2 (typeof e2) m =
    Cop.sem_binary_operation env' b v1 (typeof e1) v2 (typeof e2) m.
Proof.
  intros.
  unfold binop_stable in H.
  destruct b; try auto.
  + simpl.
    unfold Cop.sem_add.
    destruct (Cop.classify_add (typeof e1) (typeof e2)), v1, v2;
    try (erewrite <- Cop_Sem_add_ptr_int_stable; eauto);
    try (erewrite <- Cop_Sem_add_ptr_long_stable; eauto);
(*    try (eapply (complete_type_stable env env'); eauto);*)
    try erewrite <- sizeof_stable; eauto.
  + simpl.
    unfold Cop.sem_sub.
    destruct (Cop.classify_sub (typeof e1) (typeof e2)), v1, v2;
    try erewrite <- sizeof_stable; eauto.
Qed.

Lemma field_offset_stable: forall i id co ofs,
  composite_env_consistent env ->
  env ! i = Some co ->
  field_offset env id (co_members co) = Errors.OK ofs ->
  field_offset env' id (co_members co) = Errors.OK ofs.
Proof.
  unfold field_offset.
  generalize 0.
  intros.
  destruct (H i co H0) as [HH _ _ _].
  revert z H1.
  clear H H0.
  induction (co_members co); intros.
  + simpl in H1 |- *.
    inversion H1.
  + simpl in H1 |- *.
    destruct a.
    simpl in HH.
    rewrite andb_true_iff in HH.
    if_tac.
    - rewrite alignof_stable with (env := env) by tauto. assumption.
    - rewrite alignof_stable with (env := env) by tauto.
      rewrite sizeof_stable with (env := env) by tauto.
      apply IHm; try tauto.
Qed.
              *)
  
    Lemma isCastResultType_cenv_sub Delta rho w: forall e a
    (TC: @tc_expr CS Delta e rho w)
    (CAST: @denote_tc_assert CS (@isCastResultType CS  (typeof e) a e) rho w),
    @denote_tc_assert CS' (@isCastResultType CS' (typeof e) a e) rho w.
  Proof.
    induction e;  unfold isCastResultType; intros; auto.
    + remember (classify_cast (typeof (Econst_int i t)) a) as q; destruct q; auto.
      remember (eqb_type (typeof (Econst_int i t)) a) as r; destruct r; auto; trivial.
      remember ((is_pointer_type a && is_pointer_type (typeof (Econst_int i t))
               || (if Archi.ptr64
                   then is_long_type a && is_long_type (typeof (Econst_int i t))
                   else is_int_type a && is_int_type (typeof (Econst_int i t))))%bool) as u; destruct u; auto.
      simpl. simpl in *. 
    Admitted.
    
  Lemma tc_exprlist_cenv_sub (*{CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS'))*) Delta rho w:
    forall types bl, (@tc_exprlist CS Delta types bl rho) w ->
                     (@tc_exprlist CS' Delta types bl rho) w.
  Proof.
    induction types; simpl; intros.
    + destruct bl; simpl in *; trivial.
    + destruct bl; simpl in *; trivial. specialize (IHtypes bl).
      unfold tc_exprlist in H. simpl in H.  unfold tc_exprlist. simpl.
      do 2 rewrite denote_tc_assert_andp.
      do 2 rewrite denote_tc_assert_andp in H. destruct H as [[? ?] ?].
      split; [ clear IHtypes H1 | auto]. split; [ apply (tc_expr_cenv_sub); apply H | ].
assert (@tc_expr CS Delta e rho w).      apply H. unfold isCastResultType. simpl.
      Search isCastResultType.
      Search tc_andp.
      remember (@typecheck_expr CS Delta e) as TCE. remember (@typecheck_expr CS' Delta e) as TCE'.
      remember (@isCastResultType CS (typeof e) a e) as CAST.    
      remember (@isCastResultType CS' (typeof e) a e) as CAST'.
      remember (@typecheck_exprlist CS Delta types bl) as BL.
      remember (@typecheck_exprlist CS' Delta types bl) as BL'.
      unfold tc_andp; simpl. unfold tc_andp in H; simpl in H.
 Admitted.

  End CENV_SUB.