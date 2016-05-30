Require Import msl.log_normalize.
Require Import msl.alg_seplog.
Require Export veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.binop_lemmas2.

Open Local Scope pred.

Definition tc_expr {CS: compspecs}  (Delta: tycontext) (e: expr) : environ -> mpred:= 
  fun rho => denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist {CS: compspecs} (Delta: tycontext) (t : list type) (e: list expr) : environ -> mpred := 
      fun rho => denote_tc_assert (typecheck_exprlist Delta t e) rho.

Definition tc_lvalue {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred := 
     fun rho => denote_tc_assert (typecheck_lvalue Delta e) rho.

Definition allowedValCast v tfrom tto :=
match Cop.classify_cast tfrom tto with 
| Cop.cast_case_neutral => if andb (is_int_type tfrom) (is_pointer_type tto) 
                          then 
                            match v with 
                              | Vint i => (Int.eq i Int.zero)
                              | _ => false 
                            end
                          else if eqb (is_int_type tfrom) 
                                      (is_int_type tto)
                               then true else false
| Cop.cast_case_i2i _ _ => true
| Cop.cast_case_l2l => true
| Cop.cast_case_f2f => true
| Cop.cast_case_s2s => true
| _  => false
end. 

Definition tc_temp_id {CS: compspecs} (id : positive) (ty : type) 
  (Delta : tycontext) (e : expr) : environ -> mpred  :=
     fun rho => denote_tc_assert (typecheck_temp_id id ty Delta e) rho.  

Definition tc_temp_id_load id tfrom Delta v : environ -> mpred  :=
fun rho => !! (exists tto, exists x, (temp_types Delta) ! id = Some (tto, x) 
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

Lemma extend_isCastResultType:
 forall {CS: compspecs} t t' v rho,
   boxy extendM (denote_tc_assert (isCastResultType t t' v) rho).
Proof.
intros.
 unfold isCastResultType;
 destruct (Cop.classify_cast t t');
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
 try simple apply extend_tc_iszero.
Qed.

Lemma extend_tc_temp_id: forall {CS: compspecs} id ty Delta e rho, boxy extendM (tc_temp_id id ty Delta e rho). 
Proof. 
intros. unfold tc_temp_id. unfold typecheck_temp_id.
destruct ((temp_types Delta) ! id) as [[? ?] | ];
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
destruct (eval_expr e1 rho); try apply extend_prop.
destruct (eval_expr e2 rho); try apply extend_prop.
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

Lemma extend_valid_pointer':
  forall a b, boxy extendM (valid_pointer' a b).
Proof.
intros.
apply boxy_i; intros.
apply extendM_refl.
unfold valid_pointer' in *.
simpl in *.
destruct a; simpl in *; auto.
forget (b0, Int.unsigned i + b) as p.
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

Lemma extend_tc_comparable:
  forall {CS: compspecs} e1 e2 rho,
 boxy extendM (denote_tc_assert (tc_comparable e1 e2) rho).
Proof.
intros.
rewrite denote_tc_assert_comparable'.
apply boxy_i; intros.
apply extendM_refl.
simpl in *.
super_unfold_lift.
unfold denote_tc_comparable in *.
destruct (eval_expr e1 rho); auto;
destruct (eval_expr e2 rho); auto.
destruct H0; split; auto.
destruct H1 as [H1|H1]; [left|right];
apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H1).
destruct H0; split; auto.
destruct H1 as [H1|H1]; [left|right];
apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H1).
unfold comparable_ptrs in *.
if_tac.
destruct H0; split.
destruct H0 as [?|?]; [left|right];
apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H0).
destruct H1 as [?|?]; [left|right];
apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H1).
destruct H0.
split.
apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H0).
apply (boxy_e _ _ (extend_valid_pointer' _ _) _ w' H H1).
Qed.

Lemma extend_tc_expr: forall {CS: compspecs} Delta e rho, boxy extendM (tc_expr Delta e rho)
 with extend_tc_lvalue: forall {CS: compspecs} Delta e rho, boxy extendM (tc_lvalue Delta e rho).
Proof.
*
 clear extend_tc_expr.
 intros.
unfold tc_expr.
  induction e; simpl;
  destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
  simpl;
 unfold isBinOpResultType, binarithType;
 try (destruct u; simpl);
 repeat apply extend_tc_andp;
 repeat match goal with
 | |- boxy _ (denote_tc_assert match ?A with  _ => _ end _) => destruct A 
 | |- boxy _ (denote_tc_assert (if ?A then _ else _) rho) => destruct A
 | |- context [typeof ?e] => 
      destruct (typeof e) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ]; 
      try apply extend_prop
 end;
 repeat apply extend_tc_andp;
 repeat apply extend_tc_orp;
 try apply extend_prop; 
 try simple apply extend_tc_bool;
 try simple apply extend_tc_Zge;
 try simple apply extend_tc_Zle;
 try simple apply extend_tc_iszero;
 try simple apply extend_tc_nonzero;
 try simple apply extend_tc_nodivover;
 try simple apply extend_tc_samebase;
 try simple apply extend_tc_ilt;
 try simple apply extend_isCastResultType;
 try simple apply extend_tc_comparable;
 auto;
 try apply extend_tc_lvalue.
*
 clear extend_tc_lvalue.
 intros.
 unfold tc_lvalue.
 induction e; simpl;
 try apply extend_prop;
 repeat apply extend_tc_andp;
 repeat match goal with
 | |- boxy _ (denote_tc_assert match ?A with  _ => _ end _) => destruct A 
 | |- boxy _ (denote_tc_assert (if ?A then _ else _) rho) => destruct A
 | |- context [typeof ?e] => 
      destruct (typeof e) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ]; 
      try apply extend_prop
 end;
 repeat apply extend_tc_andp;
 repeat apply extend_tc_orp;
 try apply extend_prop; 
 try simple apply extend_tc_bool;
 try simple apply extend_tc_Zge;
 try simple apply extend_tc_Zle;
 try simple apply extend_tc_iszero;
 try simple apply extend_tc_nonzero;
 try simple apply extend_tc_nodivover;
 try simple apply extend_tc_samebase;
 try simple apply extend_tc_ilt;
 try simple apply extend_isCastResultType;
 try simple apply extend_tc_comparable;
 auto;
 try apply extend_tc_lvalue.
 apply extend_tc_expr.
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

Hint Resolve extend_tc_expr extend_tc_temp_id extend_tc_temp_id_load extend_tc_exprlist extend_tc_lvalue.
Hint Resolve (@extendM_refl rmap _ _ _ _ _).
