Require Import VST.veric.Clight_base.
Require Import VST.msl.msl_standard.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.binop_lemmas5.
Require Import VST.veric.binop_lemmas6.
Require Import VST.veric.expr_lemmas2.
Require Export VST.veric.expr_lemmas3.
Require Import VST.veric.juicy_mem.
Import Cop.
Import Cop2.
Import Clight_Cop2.

(** Main soundness result for the typechecker **)

Lemma typecheck_both_sound:
  forall {CS: compspecs} Delta rho m e ,
             typecheck_environ Delta rho ->
             (denote_tc_assert (typecheck_expr Delta e) rho m ->
             tc_val (typeof e) (eval_expr e rho)) /\
             (forall pt,
             denote_tc_assert (typecheck_lvalue Delta e) rho m ->
             is_pointer_type pt = true ->
             tc_val pt (eval_lvalue e rho)).
Proof.
intros. induction e; split; intros; try solve[subst; auto]; try contradiction.

* (*Const int*)
simpl in *. destruct t; try contradiction.
destruct i0; try contradiction. auto.

* (*Const float*)
destruct f; simpl in *; subst; destruct t; try destruct f; intuition.
* (* Const single *)
destruct f; simpl in *; subst; destruct t; try destruct f; intuition.

* (*Var*)
eapply typecheck_expr_sound_Evar; eauto.

*eapply typecheck_lvalue_Evar; eauto.

* (*Temp*)
eapply typecheck_temp_sound; eauto.

* (*deref*)

simpl in H0 |- *.
unfold deref_noload.
destruct (access_mode t) eqn:?H; try inversion H0.
unfold Datatypes.id.
unfold_lift.
simpl.
rewrite !denote_tc_assert_andp in H0.
simpl in H0.
destruct H0.
unfold_lift in H2.
destruct (eval_expr e rho); inversion H2.
simpl.
destruct t; try reflexivity; try inversion H1.
- destruct i0, s; inversion H4.
- destruct f; inversion H4.

*

simpl in H0 |- *.
unfold tc_val.
rewrite !denote_tc_assert_andp in H0.
simpl in H0.
destruct H0 as [[? ?] ?].
unfold tc_bool in H2; simpl in H2.
destruct (is_pointer_type (typeof e)) eqn:?H; [|inversion H2].
unfold_lift.
unfold_lift in H3.
destruct (eval_expr e rho); inversion H3.
simpl.
unfold is_pointer_type in H1.
destruct pt; try reflexivity; try solve [inversion H1].
destruct (eqb_type (Tpointer pt a) int_or_ptr_type); inv H1.
apply I.

* (*addrof*)
intuition.
simpl in *.
rewrite denote_tc_assert_andp in H0.
destruct H0.
destruct t; auto.
unfold tc_val, is_pointer_type in H3|-*.
destruct (eqb_type (Tpointer t a) int_or_ptr_type) eqn:J.
apply eqb_type_true in J. rewrite J in H3.
contradiction H3.
specialize (H2 (Tpointer t a) H0).
unfold tc_val in H2.
rewrite J in H2.
unfold is_pointer_type in H2. rewrite J in H2.
apply H2; auto.

* (*Unop*)
eapply typecheck_unop_sound; eauto.
* (*binop*)
repeat rewrite andb_true_iff in *; intuition.
clear H4. clear H2. clear H.
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0 as [[H0 E1] E2].
apply (typecheck_binop_sound b rho m e1 e2 t H0 (H3 E2) (H1 E1)).

* (* cast *)
destruct IHe.
eapply typecheck_cast_sound; eauto.

* (*EField*)
eapply typecheck_expr_sound_Efield; eauto.
*
eapply typecheck_lvalue_sound_Efield; eauto.
* (* Esizeof *)
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0.
apply tc_bool_e in H0.
apply tc_bool_e in H1.
rewrite eqb_type_spec in H1.
subst.
simpl.
reflexivity.
* (* Ealignof *)
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0.
apply tc_bool_e in H0.
apply tc_bool_e in H1.
rewrite eqb_type_spec in H1.
subst.
simpl.
reflexivity.
Qed.

Lemma typecheck_expr_sound : forall {CS: compspecs} Delta rho m e,
 typecheck_environ Delta rho ->
              denote_tc_assert (typecheck_expr Delta e) rho m ->
              tc_val (typeof e) (eval_expr e rho).
Proof. intros.
assert (TC := typecheck_both_sound Delta rho m e). intuition. Qed.


Lemma typecheck_lvalue_sound : forall {CS: compspecs} Delta rho m e,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_lvalue Delta e) rho m ->
  is_pointer_or_null (eval_lvalue e rho).
Proof.
intros.
 edestruct (typecheck_both_sound _ _ m e H).
specialize (H2 (Tpointer Tvoid noattr) H0 (eq_refl _)).
apply H2.
Qed.

Ltac unfold_cop2_sem_cmp :=
unfold Clight_Cop2.sem_cmp, Clight_Cop2.sem_cmp_pl, Clight_Cop2.sem_cmp_lp, Clight_Cop2.sem_cmp_pp.

Lemma eval_binop_relate:
 forall {CS: compspecs} Delta (ge: genv) te ve rho b e1 e2 t m
        (Hcenv: genv_cenv ge = @cenv_cs CS),
    rho = construct_rho (filter_genv ge) ve te ->
    typecheck_environ Delta rho ->
    ((denote_tc_assert (typecheck_expr Delta e1) rho) (m_phi m) ->
      Clight.eval_expr ge ve te (m_dry m) e1 (eval_expr e1 rho)) ->
    ((denote_tc_assert (typecheck_expr Delta e2) rho) (m_phi m) ->
       Clight.eval_expr ge ve te (m_dry m) e2 (eval_expr e2 rho)) ->
    (denote_tc_assert (typecheck_expr Delta (Ebinop b e1 e2 t)) rho) (m_phi m) ->
    Clight.eval_expr ge ve te (m_dry m) (Ebinop b e1 e2 t)
                     (eval_expr (Ebinop b e1 e2 t) rho).
Proof.
intros until 1. intros H H0 H1 H2 H3.
simpl in *. super_unfold_lift.
rewrite !denote_tc_assert_andp in H3.
destruct H3 as [[H3 TC1] TC2].
specialize (H1 TC1).
specialize (H2 TC2).
apply typecheck_expr_sound in TC1; [| auto].
apply typecheck_expr_sound in TC2; [| auto].
clear H0 H.
clear Delta.
eapply eval_binop_relate'; eassumption.
Qed.

Lemma valid_pointer_dry0:
  forall b ofs m, app_pred (valid_pointer (Vptr b ofs)) (m_phi m) ->
           Mem.valid_pointer (m_dry m) b (Ptrofs.unsigned ofs) = true.
Proof.
intros.
rewrite <- (Z.add_0_r (Ptrofs.unsigned ofs)).
apply valid_pointer_dry; auto.
Qed.



Definition some_pt_type := Tpointer Tvoid noattr.

Lemma tc_force_Some : forall ov t, tc_val t (force_val ov)
-> exists v, ov = Some v.
Proof.
  intros.
 unfold tc_val in H.
  destruct (eqb_type t int_or_ptr_type);
 destruct ov; destruct t; eauto; simpl in *; try tauto;
  destruct f; tauto.
Qed.

Lemma typecheck_binop_sound2:
 forall {CS: compspecs} (Delta : tycontext) (rho : environ) m (b : binary_operation)
     (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho m ->
   denote_tc_assert (isBinOpResultType b e1 e2 t) rho m ->
   denote_tc_assert (typecheck_expr Delta e1) rho m ->
   tc_val (typeof e2) (eval_expr e2 rho) ->
   tc_val (typeof e1) (eval_expr e1 rho) ->
   tc_val t
     (eval_binop b (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
intros.
pose proof (typecheck_binop_sound).
simpl in H4. unfold_lift in H4. eapply H4; eauto.
Qed.

Lemma eval_binop_relate_fail :
forall {CS: compspecs} (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) m,
typecheck_environ  Delta rho ->
forall (ge : genv) te ve,
rho = construct_rho (filter_genv ge) ve te ->
denote_tc_assert (typecheck_expr Delta e2) rho (m_phi m) ->
denote_tc_assert (isBinOpResultType b e1 e2 t) rho (m_phi m) ->
denote_tc_assert (typecheck_expr Delta e1) rho (m_phi m) ->
None =
sem_binary_operation' b  (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho) ->
Clight.eval_expr ge ve te (m_dry m) e2 (eval_expr e2 rho) ->
Clight.eval_expr ge ve te (m_dry m) e1 (eval_expr e1 rho) ->
Clight.eval_expr ge ve te (m_dry m) (Ebinop b e1 e2 t) Vundef.
Proof.
intros.
assert (TC1 := typecheck_expr_sound _ _ _ _ H H1).
assert (TC2 := typecheck_expr_sound _ _ _ _ H H3).
copy H2.
rewrite den_isBinOpR in H7; simpl in H7.
eapply typecheck_binop_sound2 in H2; eauto.
remember (eval_expr e1 rho); remember (eval_expr e2 rho);
destruct v; destruct v0;
try solve [exfalso; eapply tc_val_Vundef; eauto];
apply tc_force_Some in H2; destruct H2; try congruence.
Qed.

Opaque tc_andp.
(** Equivalence of CompCert eval_expr and our function eval_expr on programs that typecheck **)

Lemma tc_test_eq0:
  forall b i m,
  (denote_tc_test_eq (Vptr b i) (Vint Int.zero)) (m_phi m) ->
  Mem.weak_valid_pointer (m_dry m) b (Ptrofs.unsigned i) = true.
Proof.
intros.
destruct H;
apply weak_valid_pointer_dry in H0;
apply H0.
Qed.

Lemma cop2_sem_cast :
    forall t1 t2 v m,
 (classify_cast t1 t2 = classify_cast size_t tbool ->
   denote_tc_test_eq v (Vint Int.zero) (m_phi m) )->
  t1 <> int_or_ptr_type ->
  t2 <> int_or_ptr_type ->
  tc_val t1 v ->
 Cop.sem_cast v t1 t2 (m_dry m) = sem_cast t1 t2 v.
Proof.
intros.
 unfold Cop.sem_cast, sem_cast.
assert (Cop.classify_cast t1 t2 = classify_cast t1 t2). {
  clear - H0 H1.
  apply eqb_type_false in H0.
  apply eqb_type_false in H1.
  destruct t1; auto; destruct t2; auto;
  unfold Cop.classify_cast, classify_cast; auto; rewrite ?H0,?H1; auto.
}
rewrite <- H3 in *.
rewrite H3.
destruct (classify_cast t1 t2);
destruct v; try reflexivity.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv H3; simpl in H2; try inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv H3; simpl in H2; try inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv H3; simpl in H2; try inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv H3; simpl in H2; try inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
  - revert H2; simple_if_tac; intros H2; inv H2.
+ unfold sem_cast_i2bool.
    simpl.
  destruct Archi.ptr64 eqn:Hp; auto; simpl.
  specialize (H H3).
  do 3 red in H;
  rewrite Hp in H; try contradiction;
  (red in H; destruct H as [_ H];
  apply weak_valid_pointer_dry in H;
  unfold Mem.weak_valid_pointer;
  rewrite H; reflexivity).
Qed.

Ltac destruct_eqb_type := 
match goal with H: context [eqb_type ?t1 ?t2] |- _ =>
 let J := fresh "J" in 
  destruct (eqb_type t1 t2) eqn:?J;
 [apply eqb_type_true in J | apply eqb_type_false in J]
end.

Lemma classify_cast_eq:
 forall t1 t2,
  t1 <> int_or_ptr_type ->
  t2 <> int_or_ptr_type ->
  classify_cast t1 t2 = Cop.classify_cast t1 t2.
Proof.
intros.
destruct t1,t2; try reflexivity;
unfold classify_cast;
try rewrite (proj2 (eqb_type_false _ _) H0);
try rewrite (proj2 (eqb_type_false _ _) H);
reflexivity.
Qed.

Definition cast_pointer_to_bool t1 t2 :=
 match t1 with (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
           match t2 with Tint IBool _ _ => true | _ => false end
 | _ => false
end.

Lemma sem_cast_e1:
 forall t t1 v1 v m,
   sem_cast t t1 v = Some v1 ->
   cast_pointer_to_bool t t1 = false ->
   tc_val t v ->
   Cop.sem_cast v t t1 m = Some v1.
Proof.
intros.
destruct (eqb_type t int_or_ptr_type) eqn:J;
 [apply eqb_type_true in J; subst t
 | apply eqb_type_false in J];
(destruct (eqb_type t1 int_or_ptr_type) eqn:J0;
 [apply eqb_type_true in J0; subst t1
 | apply eqb_type_false in J0]).
* unfold sem_cast, sem_cast_pointer in H; simpl in *.
  rewrite N.eqb_refl in *.
  simpl in H.
  inv H.
  destruct v1; auto; inv H1.
*
unfold sem_cast, classify_cast in H.
rewrite eqb_type_refl in H.
destruct t1; auto.
destruct i,s; auto; try solve [destruct v; inv H];
destruct (classify_cast int_or_ptr_type (Tint IBool Signed a)) eqn:J;
 try congruence; inv J. (* contradiction H0. reflexivity. *)
inv H.
destruct f; inv H.
clear H0.
unfold int_or_ptr_type at 1 in H.
rewrite (proj2 (eqb_type_false _ _) J0) in H.
inv H.
*
unfold sem_cast in H.
destruct t; try solve [inv H].
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
rewrite eqb_type_refl in H.
rewrite (proj2 (eqb_type_false _ _) J) in H.
inv H.
*
revert H.
clear - J J0 H0 H1.
unfold Cop.sem_cast, sem_cast.
unfold Cop.classify_cast, classify_cast, sem_cast_pointer, 
 sem_cast_l2bool, sem_cast_i2bool.
rewrite ?(proj2 (eqb_type_false _ _) J);
rewrite ?(proj2 (eqb_type_false _ _) J0).
destruct t1   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto;
destruct t   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto; try discriminate H0;
 auto;
 destruct Archi.ptr64 eqn:Hp; auto;
 destruct v; auto; try contradiction;
 try solve [simpl in H1; rewrite Hp in H1; inv H1];
 try solve [simpl in H1; revert H1; simple_if_tac; intros []].
 
 simpl in H1; revert H1; simple_if_tac; simpl; rewrite Hp; intros [].
Qed.

Lemma cop2_sem_cast' :
    forall {CS: compspecs} t2 e rho m,
 (denote_tc_assert (isCastResultType (typeof e) t2 e) rho) (m_phi m) ->
  tc_val (typeof e) (eval_expr e rho) ->
 Cop.sem_cast (eval_expr e rho) (typeof e) t2 (m_dry m) =
 sem_cast (typeof e) t2 (eval_expr e rho).
Proof.
intros.
rewrite isCastR in H.
destruct (typeof e)   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto;
destruct t2  as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto; 
try contradiction.
all: try solve [ destruct (eval_expr e rho); try contradiction; reflexivity].
all: (*try solve [*)
unfold classify_cast, is_pointer_type in H;
unfold sem_cast, classify_cast;
unfold tc_val, is_pointer_or_null in H0;
repeat match type of H with context [eqb_type ?A int_or_ptr_type] =>
  destruct (eqb_type A int_or_ptr_type) eqn:?J; try contradiction
end;
simpl; destruct Archi.ptr64 eqn:Hp; simpl in H;
destruct (eval_expr e rho) eqn:?; try contradiction; subst; try reflexivity.
all: simpl.
all: try solve [

rewrite denote_tc_assert_test_eq' in H;
simpl in H;
unfold_lift in H;
unfold denote_tc_test_eq in H;
rewrite Heqv, Hp in H; destruct H;
apply weak_valid_pointer_dry in H1;
unfold Mem.weak_valid_pointer; rewrite H1, Hp; reflexivity].
simpl in H0; rewrite Hp in H0; inv H0.
Qed.

(*
Lemma cop2_sem_cast'': 
  forall (CS: compspecs) (rho: environ) e t m v,
 app_pred (denote_tc_assert (isCastResultType (typeof e) t e) rho)
  (m_phi m) ->
 sem_cast (typeof e) t (eval_expr e rho) = Some v ->
 t <> Tvoid ->
 Cop.sem_cast (eval_expr e rho) (typeof e) t (m_dry m) = Some v.
Proof.
intros.
rewrite isCastR in H.
unfold sem_cast, classify_cast, is_pointer_type, sem_cast_i2bool, sem_cast_l2bool in H0, H.
destruct (typeof e)   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto;
destruct t  as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto; 
try contradiction.

destruct (eval_expr e rho); try discriminate; try reflexivity; simpl; auto.
destruct Archi.ptr64; auto.

unfold classify_ca

all: try solve [ destruct (eval_expr e rho); try discriminate; reflexivity].
all: (*try solve [*)
unfold classify_cast, is_pointer_type in H;
unfold sem_cast, classify_cast;
unfold tc_val, is_pointer_or_null in H0;
repeat match type of H with context [eqb_type ?A int_or_ptr_type] =>
  destruct (eqb_type A int_or_ptr_type) eqn:?J; try contradiction
end;
simpl; destruct Archi.ptr64 eqn:Hp; simpl in H;
destruct (eval_expr e rho) eqn:?; try contradiction; subst; try reflexivity.
all: simpl.
all: try solve [

rewrite denote_tc_assert_test_eq' in H;
simpl in H;
unfold_lift in H;
unfold denote_tc_test_eq in H;
rewrite Heqv, Hp in H; destruct H;
apply weak_valid_pointer_dry in H1;
unfold Mem.weak_valid_pointer; rewrite H1, Hp; reflexivity].
all: rewrite Hp; auto.




destruct (eqb_type (typeof e) int_or_ptr_type) eqn:J;
 [apply eqb_type_true in J; rewrite J in *
 | apply eqb_type_false in J];
(destruct (eqb_type t int_or_ptr_type) eqn:J0;
 [apply eqb_type_true in J0; subst t
 | apply eqb_type_false in J0]).
* auto.
*
elimtype False.
clear - H0 J J0 H1.
unfold sem_cast  in H0.
unfold classify_cast in H0.
rewrite eqb_type_refl in H0.
rewrite <- eqb_type_false in J0.
rewrite J0 in H0.
unfold int_or_ptr_type in H0.
destruct Archi.ptr64 eqn:Hp;
destruct t  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
try discriminate.
unfold sem_cast_i2l in H0.
destruct t eqn:?; try discriminate H0.
congruence.
all: try congruence.
rewrite eqb_type_false in H0 by auto.
unfo
rewrite isCastR in H.
destruct t  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto.
destruct i,s; auto; try solve [destruct (eval_expr e rho); inv H0].
unfold isCastResultType in H.
simpl classify_cast in H.
cbv iota in H.
rewrite denote_tc_assert_andp in H.
destruct H.
contradiction H1.
unfold isCastResultType in H.
simpl classify_cast in H.
cbv iota in H.
rewrite denote_tc_assert_andp in H.
destruct H.
contradiction H1.
destruct f; contradiction H.
unfold isCastResultType in H.
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
rewrite (proj2 (eqb_type_false _ _) J0) in H.
rewrite eqb_type_refl in H.
contradiction H.
*
unfold Cop.sem_cast.
unfold sem_cast in H0.
destruct (typeof e); try solve [inv H0].
contradiction.
unfold classify_cast in H0.
unfold int_or_ptr_type at 1 in H0.
rewrite eqb_type_refl in H0.
rewrite (proj2 (eqb_type_false _ _) J) in H0.
inv H0.
*
rewrite cop2_sem_cast'; auto.
Qed.
*)


Lemma isBinOpResultType_binop_stable: forall {CS: compspecs} b e1 e2 t rho phi,
  denote_tc_assert (isBinOpResultType b e1 e2 t) rho phi ->
  binop_stable cenv_cs b e1 e2 = true.
Proof.
  intros.
  destruct b; auto;
  unfold isBinOpResultType in H;
  unfold binop_stable.
  + destruct (classify_add (typeof e1) (typeof e2));
    rewrite ?denote_tc_assert_andp in H;
    repeat match goal with
    | H: app_pred (_ && _) _ |- _ => destruct H
    end;
    try solve [eapply tc_bool_e; eauto].
    auto.
  + destruct (classify_sub (typeof e1) (typeof e2));
    rewrite ?denote_tc_assert_andp in H;
    repeat match goal with
    | H: app_pred (_ && _) _ |- _ => destruct H
    end;
    try solve [eapply tc_bool_e; eauto].
    auto.
Qed.

Lemma eval_unop_relate:
 forall {CS: compspecs} Delta (ge: genv) te ve rho u e t m 
 (Hcenv : genv_cenv ge = @cenv_cs CS)
 (H : rho = construct_rho (filter_genv ge) ve te)
 (H0 : typecheck_environ Delta rho)
 (H1 : (denote_tc_assert (typecheck_expr Delta e) rho) (m_phi m) ->
     Clight.eval_expr ge ve te (m_dry m) e (eval_expr e rho))
 (H2 : (denote_tc_assert (typecheck_lvalue Delta e) rho) (m_phi m) ->
     exists (b : block) (ofs : ptrofs),
       Clight.eval_lvalue ge ve te (m_dry m) e b ofs /\
       eval_lvalue e rho = Vptr b ofs)
 (H3 : (denote_tc_assert (typecheck_expr Delta (Eunop u e t)) rho)
       (m_phi m)),
Clight.eval_expr ge ve te (m_dry m) (Eunop u e t)
  (eval_expr (Eunop u e t) rho).
Proof.
intros.
simpl in *.
super_unfold_lift.
rewrite denote_tc_assert_andp in H3; destruct H3.
intuition. clear H2.
unfold eval_unop in *. unfold force_val1, force_val.
remember (sem_unary_operation u (typeof e) (eval_expr e rho)).
eapply Clight.eval_Eunop. eapply H5.  rewrite Heqo.

unfold sem_unary_operation. unfold Cop.sem_unary_operation.
apply typecheck_expr_sound in H4; auto.
destruct u;
  simpl in H3;
  destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl;
  hnf in H4; try contradiction;
  repeat match goal with
       | H: app_pred (denote_tc_assert (tc_andp _ _) _) _ |- _ => 
          rewrite denote_tc_assert_andp in H; destruct H
       | H: app_pred (denote_tc_assert (if ?A then _ else _) _) _ |- _ =>
           first [change A with false in H | change A with true in H]; cbv iota in H
       | H: app_pred (denote_tc_assert (tc_iszero _) _) _ |- _ =>
                   rewrite denote_tc_assert_iszero in H
       | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => apply tc_bool_e in H
       end;
  destruct (eval_expr e rho) eqn:?;
  try match type of H4 with context [if ?A then _ else _] => destruct A end;
  try contradiction; try reflexivity;
 unfold Cop.sem_notbool; simpl;
 unfold Cop.bool_val, bool_val;
 apply tc_bool_e in H1; apply negb_true_iff in H1; rewrite H1;
 try reflexivity;
 unfold classify_bool, typeconv, remove_attributes, change_attributes;
 rewrite denote_tc_assert_test_eq' in H3;
 simpl in H3; unfold denote_tc_test_eq in H3; unfold_lift in H3; rewrite Heqv in H3.
*
 destruct Archi.ptr64 eqn:Hp; simpl eval_expr in H3; unfold_lift in H3; destruct H3;
 apply weak_valid_pointer_dry in H6;
 simpl; unfold Mem.weak_valid_pointer; rewrite H6; reflexivity.
*
 destruct Archi.ptr64 eqn:Hp; simpl eval_expr in H3; unfold_lift in H3; destruct H3;
 apply weak_valid_pointer_dry in H6;
 simpl; unfold Mem.weak_valid_pointer; rewrite H6; reflexivity.
Qed.

Lemma eqb_type_sym: forall a b, eqb_type a b = eqb_type b a.
Proof.
intros.
destruct (eqb_type a b) eqn:?.
rewrite -> eqb_type_spec in Heqb0. subst; symmetry; apply eqb_type_refl.
apply eqb_type_false in Heqb0.
assert (b<>a) by congruence.
rewrite <- eqb_type_spec in H.
destruct (eqb_type b a); auto.
Qed.

Lemma Ptrofs_to_int_repr: 
  Archi.ptr64=false -> 
  forall i, Ptrofs.to_int (Ptrofs.repr i) = Int.repr i.
Proof.
intros.
try solve [inversion H];
unfold Ptrofs.to_int;
apply Int.eqm_samerepr;
change Int.eqm with Ptrofs.eqm;
apply Ptrofs.eqm_sym;
apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma eval_both_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho (m_phi m) ->
             Clight.eval_expr ge ve te (m_dry m) e  (eval_expr e rho))
           /\
           (denote_tc_assert (typecheck_lvalue Delta e) rho (m_phi m) ->
             exists b, exists ofs,
              Clight.eval_lvalue ge ve te (m_dry m) e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof.
intros until m; intro Hcenv; intros.
(*generalize dependent ge.*)
 induction e; intros;
try solve[intuition; constructor; auto | subst; inv H1]; intuition.

* (* eval_expr Evar*)

assert (TC_Sound:= typecheck_expr_sound).
specialize (TC_Sound Delta rho _ (Evar i t) H0 H1).
simpl in H1, TC_Sound |- *.
super_unfold_lift.
destruct (access_mode t) eqn:MODE; try solve [inv H1].

unfold get_var_type, eval_var in *.
remember (Map.get (ve_of rho) i); destruct o; try destruct p;
try rewrite eqb_type_eq in *; simpl in *.
destruct (type_eq t t0); simpl in *; [| exfalso; eapply tc_val_Vundef; eauto].
subst t0.
apply Clight.eval_Elvalue with b Ptrofs.zero;
  [ | constructor; simpl; rewrite MODE; auto].
apply eval_Evar_local.
subst rho.
simpl in Heqo. symmetry in Heqo; apply Heqo.
subst rho.
unfold typecheck_environ in *.
destruct H0 as [? [Hve Hge]].
hnf in Hve,Hge.
revert H1; case_eq ((var_types Delta) ! i); intros; try contradiction.
specialize (Hve i t0). destruct Hve as [Hve _].
destruct (Hve H0). simpl in *; congruence.
revert H1; case_eq ((glob_types Delta) ! i); intros; try contradiction.
destruct (Hge _ _ H1) as [b ?].
simpl. simpl in H3.
rewrite H3.

repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
unfold tc_bool in H2.
destruct (eqb_type t t0); try contradiction.
apply Clight.eval_Elvalue with b Ptrofs.zero; [  | econstructor 2; apply MODE].
apply Clight.eval_Evar_global; auto.

* (* eval_lvalue Evar *)
 simpl in H1.
 unfold get_var_type in H1.
 subst rho; simpl in *.
 unfold eval_var.
 destruct_var_types i eqn:HH1&HH2; rewrite ?HH1, ?HH2 in *;
  [| destruct_glob_types i eqn:HH3&HH4; rewrite ?HH3, ?HH4 in *; [| inv H1]].
 +
 destruct (eqb_type t t0) eqn:?; [| inv H1].
 apply eqb_type_true in Heqb0; subst t0.
 exists b; exists Ptrofs.zero; split; auto.
 constructor; auto.
 +
 destruct (eqb_type t t0) eqn:?; [| inv H1].
 apply eqb_type_true in Heqb0; subst t0.
 exists b; exists Ptrofs.zero; split; auto.
 constructor 2; auto.

* (*temp*)
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (m_phi m) (Etempvar i t)). simpl in *.
intuition.
constructor. unfold eval_id in *. remember (Map.get (te_of rho)  i);
destruct o;  auto. destruct rho; inv H; unfold make_tenv in *.
unfold Map.get in *. auto.
simpl in *.
clear - H3.
destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
  try contradiction H3.
unfold tc_val in H3. 
destruct (eqb_type _ _); contradiction H3.

* (*deref*)
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (m_phi m) (Ederef e t)). simpl in *.
intuition.
destruct (access_mode t) eqn:?H; try inversion H3.
rewrite !denote_tc_assert_andp in H3.
destruct H3 as [[? ?] ?].
simpl in H5.
unfold_lift in H5.
unfold_lift.
apply tc_bool_e in H6.
specialize (H1 H3).
hnf in H7.
destruct (eval_expr e rho) eqn:?H; try contradiction.
eapply eval_Elvalue.
econstructor. eassumption.
simpl.
constructor. auto.
* (*deref*)
assert (TC:= typecheck_lvalue_sound _ _ _ _ H0 H3).
simpl in *.
rewrite !denote_tc_assert_andp in H3.
destruct H3 as [[? ?] ?].
specialize (H1 H3).
apply tc_bool_e in H4. simpl in H4.
hnf in H5.
destruct (eval_expr e rho) eqn:?; try contradiction.
exists b, i. simpl in *. unfold_lift. intuition. constructor.
auto.
* (*addrof*)

simpl in H3.
rewrite !denote_tc_assert_andp in H3.
destruct H3.
assert (ISPTR := eval_lvalue_ptr rho (m_phi m) e Delta (te_of rho) (ve_of rho) (ge_of rho)).
specialize (H2 H3).
apply tc_bool_e in H4.
assert (mkEnviron (ge_of rho) (ve_of rho) (te_of rho) = rho). destruct rho; auto.
destruct rho. unfold typecheck_environ in *. intuition.
destruct H2 as [b [? ?]]. destruct H9 as [base [ofs ?]].  simpl in *.
intuition. rewrite H10 in *. constructor. inv H7. auto.

* (*unop*)
 eapply eval_unop_relate; eauto.
* (*binop*)
  eapply eval_binop_relate; eauto.
* (*Cast*)
assert (TC := typecheck_expr_sound _ _ _ _ H0 H3).
simpl in *.
rewrite denote_tc_assert_andp in H3.
destruct H3.
assert (TC' := typecheck_expr_sound _ _ _ _ H0 H3).
unfold force_val1, force_val in *; super_unfold_lift; intuition.
eapply Clight.eval_Ecast.
eapply H5; auto.
destruct (sem_cast (typeof e) t (eval_expr e rho)) eqn:?H;
 [ | contradiction (tc_val_Vundef t)].
revert H1.
revert H4.
intros.
destruct (eqb_type (typeof e) t) eqn:Heq.
+
apply eqb_type_true in Heq. subst t.
destruct (eqb_type (typeof e) int_or_ptr_type) eqn:Heq'.
apply eqb_type_true in Heq'.
rewrite cop2_sem_cast'; auto.
apply eqb_type_false in Heq'.
rewrite cop2_sem_cast'; auto.
+
assert (Heq2 := Heq).
apply eqb_type_false in Heq.
destruct (eqb_type t int_or_ptr_type) eqn:Heq'.
apply eqb_type_true in Heq'. subst t.
elimtype False; clear - Heq Heq2 H1.
unfold sem_cast, classify_cast in H1.
rewrite Heq2 in H1.
rewrite eqb_type_refl in H1.
unfold int_or_ptr_type at 1 in H1.
change (eqb true false) with false in H1. cbv iota in H1.
destruct (typeof e)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] eqn:Tx, (eval_expr e rho); 
  simpl in H1;   try discriminate H1.
destruct (eqb_type (typeof e) int_or_ptr_type) eqn:Heq''.
apply eqb_type_true in Heq''. rewrite Heq'' in *.
clear - H1 TC' Heq2.
destruct t  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] eqn:Tx, (eval_expr e rho); 
  simpl in H1;   try discriminate H1; try contradiction TC'; inv H1; simpl; auto.
rewrite H0.
unfold sem_cast in *. 
unfold classify_cast in H0. unfold int_or_ptr_type at 1 in H0.
 rewrite eqb_type_refl in H0. 
rewrite eqb_type_sym in Heq2.
rewrite Heq2 in H0.
change (eqb false true) with false in H0.
cbv iota in H0. inv H0.
unfold sem_cast, classify_cast, int_or_ptr_type at 1 in H0.
rewrite eqb_type_sym in Heq2.
rewrite Heq2 in H0.
rewrite eqb_type_refl in H0.
change (eqb false true) with false in H0.
cbv iota in H0. inv H0.
apply eqb_type_false in Heq''.
apply eqb_type_false in Heq'.
rewrite cop2_sem_cast'; auto.
* (*Field*)
 assert (TC := typecheck_expr_sound _ _ _ _ H0 H3).
 clear H1; rename H3 into H1.
simpl in H1.
 destruct (access_mode t) eqn:?; try solve [inv H1].
 rewrite denote_tc_assert_andp in H1. destruct H1.
 specialize (H2 H1). destruct H2 as [b [ofs [? ?]]].
 destruct (typeof e) eqn:?; try solve[inv H3];
 destruct (cenv_cs ! i0) as [co |] eqn:Hco; try solve [inv H3].
+
   destruct (field_offset cenv_cs i (co_members co)) eqn:?;
     try contradiction.
  inv H3. simpl in *.
  eapply Clight.eval_Elvalue; eauto.
  eapply Clight.eval_Efield_struct; eauto.
  eapply Clight.eval_Elvalue; auto. eassumption.
  rewrite Heqt0.
  apply Clight.deref_loc_copy. auto.
  rewrite Hcenv; eassumption.
  rewrite Hcenv; eassumption.
  unfold_lift.
  unfold Datatypes.id; simpl.
  rewrite Heqt0. rewrite H4. simpl. rewrite Hco. rewrite Heqr.
   apply Clight.deref_loc_reference. auto.

+ simpl. unfold_lift.
   rewrite Heqt0. simpl. rewrite Hco.
  eapply Clight.eval_Elvalue; eauto.
  eapply Clight.eval_Efield_union.
  eapply Clight.eval_Elvalue; eauto.
  apply Clight.deref_loc_copy.
  rewrite Heqt0. auto. eauto.
  rewrite Hcenv; eauto.
  rewrite H4. simpl.
  apply Clight.deref_loc_reference; auto.
*
 clear H1.
 assert (TC:= typecheck_lvalue_sound _ _ _ _ H0 H3).
 simpl in *.
 rewrite denote_tc_assert_andp in H3. destruct H3.
 unfold eval_field,offset_val in *; super_unfold_lift.
 specialize (H2 H1).
destruct H2 as [b [ofs H4]].
destruct H4.
rewrite H4 in TC|-*.
 destruct (typeof e) eqn:?; try contradiction;
destruct (cenv_cs ! i0) as [co |] eqn:Hco; try solve [inv H3].
+
destruct (field_offset cenv_cs i (co_members co)) eqn:?; try contradiction.
exists b. exists (Ptrofs.add ofs (Ptrofs.repr z)).
intuition.
 eapply Clight.eval_Efield_struct; auto; try eassumption.
eapply Clight.eval_Elvalue in H2. apply H2.
rewrite Heqt0. apply Clight.deref_loc_copy. simpl; auto.
rewrite Hcenv; eassumption.
rewrite Hcenv; eassumption.
+
exists b, ofs. simpl. split; auto.
eapply Clight.eval_Efield_union; eauto.
eapply Clight.eval_Elvalue; eauto.
rewrite Heqt0. apply Clight.deref_loc_copy.
auto.
rewrite Hcenv; eassumption.
*
simpl in H1.
repeat rewrite denote_tc_assert_andp in H1.
destruct H1.
apply tc_bool_e in H1.
apply tc_bool_e in H2.
rewrite eqb_type_spec in H2.
subst.
unfold eval_expr.
unfold_lift; simpl.
rewrite <- Hcenv.
apply Clight.eval_Esizeof.
*
simpl in H1.
repeat rewrite denote_tc_assert_andp in H1.
destruct H1.
apply tc_bool_e in H1.
apply tc_bool_e in H2.
unfold eval_expr.
unfold_lift; simpl.
unfold alignof; rewrite <- Hcenv.
constructor.
Qed.

Lemma eval_expr_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho (m_phi m) ->
             Clight.eval_expr ge ve te (m_dry m) e  (eval_expr e rho)).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.

Lemma eval_lvalue_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_lvalue Delta e) rho (m_phi m) ->
             exists b, exists ofs,
              Clight.eval_lvalue ge ve te (m_dry m) e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.

(*
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
*)






