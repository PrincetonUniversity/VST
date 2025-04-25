Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Clight_Cop2.
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
{
 clear eval_expr_any.
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
  apply IHe; auto.
*
  apply eval_lvalue_any; auto.
* destruct (eval_expr e any_environ) eqn:?; simpl in *;
  [exfalso; apply H0; clear;
   try destruct u;
   destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try reflexivity
  | rewrite -> (IHe _ (eq_refl _)) by congruence; auto ..
  ].
  simpl. unfold Cop2.bool_val; simple_if_tac; reflexivity.
*
  destruct (eval_expr e1 any_environ) eqn:?; simpl in *;
  [ exfalso; apply H0; clear
  | rewrite -> (IHe1 _ (eq_refl _)) by congruence; auto .. ].
 {
  destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try reflexivity;
   cbv beta iota delta [
    sem_binary_operation'
    Clight_Cop2.sem_add Clight_Cop2.sem_sub
    classify_add classify_sub sem_sub_pi sem_sub_pl sem_sub_pp
    Clight_Cop2.sem_add_ptr_int
    Clight_Cop2.sem_add_ptr_long
    sem_add_int_ptr sem_add_ptr_int
    sem_add_long_ptr sem_add_ptr_long
   Clight_Cop2.sem_cmp classify_cmp typeconv
    remove_attributes change_attributes 
   ];
  try (simple_if_tac; [ | reflexivity]);
  repeat match goal with |- context [eqb_type ?A ?B] =>
  let J := fresh "J" in 
    destruct (eqb_type A B) eqn:J;
      [apply eqb_type_true in J; try solve [inv J] | apply eqb_type_false in J]
  end;
  try reflexivity;
  destruct (eval_expr e2 any_environ); reflexivity.
 }
all:  destruct (eval_expr e2 any_environ) eqn:?; simpl in *;
  [ exfalso; apply H0; clear
  | rewrite -> (IHe2 _ (eq_refl _)) by congruence; auto .. ];
   destruct b;
   destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try reflexivity;
   cbv beta iota delta [
    sem_binary_operation'
    Clight_Cop2.sem_add Clight_Cop2.sem_sub
    classify_add classify_sub sem_sub_pi sem_sub_pl sem_sub_pp
    Clight_Cop2.sem_add_ptr_int
    Clight_Cop2.sem_add_ptr_long
    sem_add_int_ptr sem_add_ptr_int
    sem_add_long_ptr sem_add_ptr_long
   Clight_Cop2.sem_cmp classify_cmp typeconv
    remove_attributes change_attributes 
   ];
  try (simple_if_tac; [ | reflexivity]);
  repeat match goal with |- context [eqb_type ?A ?B] =>
  let J := fresh "J" in 
    destruct (eqb_type A B) eqn:J;
      [apply eqb_type_true in J; try solve [inv J] | apply eqb_type_false in J]
  end;
   reflexivity.
*
   destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
  (destruct (eval_expr e any_environ) eqn:?; simpl in *;
  [exfalso; apply H0; clear
  | try rewrite -> (IHe _ (eq_refl _)) by congruence;
     auto .. ]); auto;
  try (unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast; repeat simple_if_tac; reflexivity).
* destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   simpl in *; unfold always; auto;
   destruct (cenv_cs !! i0) as [co |]; auto.
 -
   destruct (field_offset cenv_cs i (co_members co)) as [[? [|]]|]; auto.
   f_equal.
   apply eval_lvalue_any; auto.
   intro. rewrite H in H0. apply H0; reflexivity.
 -
   destruct (union_field_offset cenv_cs i (co_members co)) as [[? [|]]|]; auto.
   destruct (eval_lvalue e any_environ) eqn:?; simpl in *;
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
  apply eval_expr_any; auto.
  * destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in *; unfold always; auto;
    destruct (cenv_cs !! i0) as [co |]; auto.
   -
    destruct (field_offset cenv_cs i (co_members co)) as [[? [|]]|]; auto.
    f_equal.
    apply IHe; auto.
    intro. rewrite H in H0. apply H0; reflexivity.
   -
    destruct (union_field_offset cenv_cs i (co_members co)) as [[? [|]]|]; auto.
    destruct (eval_lvalue e any_environ) eqn:?; simpl in *;
    try congruence.
    rewrite (IHe _ (eq_refl _)); auto.
}
Qed.

Section mpred.

Context `{!heapGS Σ}.

Lemma denote_tc_assert_ilt':
  forall {CS: compspecs} e j rho, denote_tc_assert (tc_ilt e j) rho ⊣⊢ denote_tc_assert (tc_ilt' e j) rho.
Proof.
  intros.
 unfold tc_ilt; simpl.
 unfold_lift.
 destruct (eval_expr e any_environ) eqn:?; simpl; auto.
 apply (eval_expr_any rho) in Heqv; try congruence.
 rewrite Heqv; simpl.
 destruct (Int.ltu i j) eqn:?; simpl; 
 unfold_lift; simpl; rewrite ?Heqv; simpl; auto.
 iSplit; auto; iPureIntro.
 apply Int.ltu_inv in Heqb.
 destruct Heqb. auto.
Qed.

Lemma denote_tc_assert_llt':
  forall {CS: compspecs} e j rho, denote_tc_assert (tc_llt e j) rho ⊣⊢ denote_tc_assert (tc_llt' e j) rho.
Proof.
  intros.
 unfold tc_llt; simpl.
 unfold_lift.
 destruct (eval_expr e any_environ) eqn:?; simpl; auto.
 apply (eval_expr_any rho) in Heqv; try congruence.
 rewrite Heqv; simpl.
 destruct (Int64.ltu i j) eqn:?; simpl; 
 unfold_lift; simpl; rewrite ?Heqv; simpl; auto.
 iSplit; auto; iPureIntro.
 apply Int64.ltu_inv in Heqb.
 destruct Heqb. auto.
Qed.

Lemma tc_val_void:
  forall v, tc_val Tvoid v <-> False.
Proof.
destruct v; simpl; tauto.
Qed.

(*Definition denote_tc_assert' {CS: compspecs} (a: tc_assert) (rho: environ) : mpred.
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
Qed.*)

Lemma int_eq_true : forall x y,
true = Int.eq x y -> x = y.
Proof.
intros. assert (X := Int.eq_spec x y). rewrite <- H in X; congruence.
Qed.

Definition check_pp_int' e1 e2 op t e :=
  match op with
  | Cop.Oeq | Cop.One =>
      tc_andp'
        (tc_test_eq' e1 e2)
        (tc_bool (is_int_type t) (op_result_type e))
  | Cop.Ole | Cop.Olt | Cop.Oge | Cop.Ogt =>
      tc_andp'
        (tc_test_order' e1 e2)
        (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.

Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e.
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.

Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e.
Proof. intros; unfold tc_andp; reflexivity. Qed.

Lemma tc_orp_sound : forall {CS: compspecs} a1 a2 rho,
    denote_tc_assert (tc_orp a1 a2) rho ⊣⊢
    denote_tc_assert (tc_orp' a1 a2) rho.
Proof.
intros.
 unfold tc_orp.
 destruct a1,a2; simpl; unfold_lift;
  rewrite ?bi.or_False ?bi.False_or ?bi.or_True ?bi.True_or; reflexivity.
Qed.

Lemma denote_tc_assert_orp: forall {CS: compspecs} x y rho,
  denote_tc_assert (tc_orp x y) rho ⊣⊢
  (denote_tc_assert x rho) ∨ (denote_tc_assert y rho).
Proof.
 intros; apply tc_orp_sound.
Qed.

Lemma is_true_true: is_true true = True%type.
Proof. apply Axioms.prop_ext; intuition. Qed.
Lemma is_true_false: is_true false = False%type.
Proof. apply Axioms.prop_ext; intuition. Qed.

Lemma denote_tc_assert_iszero: forall {CS: compspecs} e rho,
  denote_tc_assert (tc_iszero e) rho =
  match (eval_expr e rho) with
  | Vint i => ⌜is_true (Int.eq i Int.zero)⌝
  | Vlong i => ⌜is_true (Int64.eq i Int64.zero)⌝
   | _ => False end.
Proof.
 intros.
 unfold tc_iszero.
 destruct (eval_expr e any_environ) eqn:?; simpl; auto;
 rewrite -> (eval_expr_any rho e _ Heqv) by congruence.
 destruct (Int.eq i Int.zero); reflexivity.
 destruct (Int64.eq i Int64.zero); reflexivity.
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
  denote_tc_assert (tc_nonzero e) rho ⊣⊢
  match (eval_expr e rho) with
  | Vint i => ⌜i <> Int.zero⌝
  | Vlong i =>⌜i <> Int64.zero⌝
  | _ => False end.
Proof.
  intros.
  unfold tc_nonzero.
  destruct (eval_expr e any_environ) eqn:?; simpl; auto;
  try rewrite -> (eval_expr_any rho e _ Heqv) by congruence;
  unfold_lift.
  + destruct (Int.eq i Int.zero) eqn:?; simpl; unfold_lift; unfold denote_tc_nonzero; simpl;
         rewrite -> ?(eval_expr_any rho e _ Heqv) by congruence; auto.
         iSplit; auto; iPureIntro; intros ? ->; inv Heqb.
  + destruct (Int64.eq i Int64.zero) eqn:?; simpl; unfold_lift; unfold denote_tc_nonzero; simpl;
         rewrite -> ?(eval_expr_any rho e _ Heqv) by congruence; auto.
         iSplit; auto; iPureIntro; intros ? ->; inv Heqb.
Qed.

Lemma denote_tc_assert_nonzero': forall {CS: compspecs} e rho,
  denote_tc_assert (tc_nonzero e) rho ⊣⊢ denote_tc_assert (tc_nonzero' e) rho.
Proof.
intros.
rewrite denote_tc_assert_nonzero.
simpl. unfold_lift. destruct (eval_expr e rho); simpl; auto.
Qed.

Lemma denote_tc_assert_nodivover: forall {CS: compspecs} e1 e2 rho,
  denote_tc_assert (tc_nodivover e1 e2) rho ⊣⊢
         match eval_expr e1 rho, eval_expr e2 rho with
          | Vint n1, Vint n2 => ⌜~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone)⌝
          | Vlong n1, Vlong n2 => ⌜~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone)⌝
          | Vint n1, Vlong n2 => True
          | Vlong n1, Vint n2 => ⌜~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone)⌝
          | _ , _ => False
        end.
Proof.
  intros.
  unfold tc_nodivover.
  destruct (eval_expr e1 any_environ) eqn:?;
  destruct (eval_expr e2 any_environ) eqn:?;
  simpl; auto;
    rewrite -> (eval_expr_any rho e1 _ Heqv) by congruence;
    rewrite -> (eval_expr_any rho e2 _ Heqv0) by congruence;
    auto.
 +
    destruct (negb (Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone)) eqn:?.
    simpl; unfold_lift; iSplit; auto; iPureIntro; intros ? [? ?]; subst; inv Heqb.
    simpl; unfold_lift; 
    rewrite -> (eval_expr_any rho e1 _ Heqv) by congruence;
    rewrite -> (eval_expr_any rho e2 _ Heqv0) by congruence; reflexivity.
 +
    destruct (negb (Int64.eq i (Int64.repr Int64.min_signed) && Int.eq i0 Int.mone)) eqn:?.
    simpl; unfold_lift; iSplit; auto; iPureIntro; intros ? [? ?]; subst; inv Heqb.
    simpl; unfold_lift; 
    rewrite -> (eval_expr_any rho e1 _ Heqv) by congruence;
    rewrite -> (eval_expr_any rho e2 _ Heqv0) by congruence; reflexivity.
 +
    destruct (negb (Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone)) eqn:?.
    simpl; unfold_lift; iSplit; auto; iPureIntro; intros ? [? ?]; subst; inv Heqb.
    simpl; unfold_lift; 
    rewrite -> (eval_expr_any rho e1 _ Heqv) by congruence;
    rewrite -> (eval_expr_any rho e2 _ Heqv0) by congruence; reflexivity.
Qed.

Lemma denote_tc_assert_nodivover': forall {CS: compspecs} e1 e2 rho,
  denote_tc_assert (tc_nodivover e1 e2) rho ⊣⊢ denote_tc_assert (tc_nodivover' e1 e2) rho.
Proof.
intros.
rewrite denote_tc_assert_nodivover; reflexivity.
Qed.

Lemma denote_tc_assert_andp'':
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_andp' a b) rho =
            ((denote_tc_assert a rho) ∧ (denote_tc_assert b rho)).
Proof.
 intros. reflexivity. Qed.

Lemma denote_tc_assert_orp'':
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_orp' a b) rho =
             ((denote_tc_assert a rho) ∨ (denote_tc_assert b rho)).
Proof.
 intros. reflexivity. Qed.

Lemma denote_tc_assert_andp':
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_andp a b) rho ⊣⊢
                        denote_tc_assert (tc_andp' a b) rho.
Proof. intros. apply denote_tc_assert_andp. Qed.

Lemma denote_tc_assert_orp':
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_orp a b) rho ⊣⊢
                        denote_tc_assert (tc_orp' a b) rho.
Proof. intros. apply denote_tc_assert_orp. Qed.

Lemma denote_tc_assert_test_eq':
  forall {CS: compspecs} a b rho,
    denote_tc_assert (tc_test_eq a b) rho ⊣⊢
    denote_tc_assert (tc_test_eq' a b) rho.
Proof.
  intros.
  unfold tc_test_eq.
  simpl; unfold_lift;  unfold denote_tc_test_eq.
 destruct (Val.eq (eval_expr a any_environ) Vundef);
   [rewrite e; reflexivity | ].
 rewrite <- (eval_expr_any rho _ _ (eq_refl _) n).
 destruct (Val.eq (eval_expr b any_environ) Vundef).
 rewrite e; destruct (eval_expr a rho) eqn:Ha; simpl; unfold_lift; rewrite Ha; reflexivity.
 rewrite <- (eval_expr_any rho _ _ (eq_refl _) n0).
 clear n n0.
 destruct (eval_expr a rho) eqn:Ha; simpl; unfold_lift; try rewrite Ha;
  try reflexivity;
 destruct (eval_expr b rho) eqn:Hb; simpl; unfold_lift; 
   rewrite ?Ha ?Hb;
  try reflexivity.
*
  destruct Archi.ptr64 eqn:Hp; simpl; unfold_lift.
  +
  rewrite Ha Hb; simpl; rewrite Hp; reflexivity.
  +
  pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero).
  pose proof (Int.eq_spec i0 Int.zero); destruct (Int.eq i0 Int.zero).
  simpl. iSplit; auto.
  simpl. unfold_lift. rewrite Ha Hb /= Hp. auto.
  simpl. unfold_lift. rewrite Ha Hb /= Hp. auto.
*
  destruct Archi.ptr64 eqn:Hp; simpl; unfold_lift.
  +
  pose proof (Int64.eq_spec i Int64.zero); destruct (Int64.eq i Int64.zero).
  pose proof (Int64.eq_spec i0 Int64.zero); destruct (Int64.eq i0 Int64.zero).
  simpl. iSplit; auto.
  simpl. unfold_lift. rewrite Ha Hb /= Hp. auto.
  simpl. unfold_lift. rewrite Ha Hb /= Hp. auto.
 +
  rewrite Ha Hb /= Hp; reflexivity.
Qed.

Lemma denote_tc_assert_test_order':
  forall {CS: compspecs} a b rho,
    denote_tc_assert (tc_test_order a b) rho ⊣⊢
    denote_tc_assert (tc_test_order' a b) rho.
Proof.
  intros.
  unfold tc_test_order.
  simpl; unfold_lift;  unfold denote_tc_test_order.
  destruct (eval_expr a rho) eqn:Ha;
  destruct (eval_expr a any_environ) eqn:Ha';
  simpl; unfold_lift;  unfold denote_tc_test_order;
  rewrite ?Ha ?Ha'; simpl; auto;
  try solve [
    rewrite -> (eval_expr_any rho a _ Ha') in Ha by congruence;
    inv Ha];
  destruct (eval_expr b rho) eqn:Hb;
  destruct (eval_expr b any_environ) eqn:Hb';
  simpl; unfold_lift;  unfold denote_tc_test_eq;
  rewrite ?Ha ?Ha' ?Hb ?Hb'; simpl; auto;
  rewrite -> (eval_expr_any rho b _ Hb') in Hb by congruence; inv Hb;
  rewrite -> (eval_expr_any rho a _ Ha') in Ha by congruence; inv Ha.
*
  destruct Archi.ptr64 eqn:Hp.
 +
  simpl. unfold_lift.
  rewrite -> (eval_expr_any rho b _ Hb') by congruence;
  rewrite -> (eval_expr_any rho a _ Ha') by congruence.
  simpl. rewrite Hp. auto.
 +
  simpl. {
  destruct (Int.eq_dec i Int.zero).
   +
    subst. rewrite Int.eq_true.
    destruct (Int.eq_dec i1 Int.zero).
    - subst. rewrite Int.eq_true.
      simpl. iSplit; auto.
    - rewrite -> Int.eq_false by auto. simpl.
      simpl; unfold_lift;  unfold denote_tc_test_eq.
      rewrite -> (eval_expr_any rho a _ Ha')  by congruence.
      rewrite -> (eval_expr_any rho _ _ Hb')  by congruence.
      simpl. rewrite Hp. auto.
  + rewrite -> Int.eq_false by auto. simpl.
    simpl; unfold_lift;  unfold denote_tc_test_eq.
    rewrite -> (eval_expr_any rho a _ Ha')  by congruence.
    rewrite -> (eval_expr_any rho _ _ Hb')  by congruence.
    simpl. rewrite Hp.
    auto.
  }
*
  destruct Archi.ptr64 eqn:Hp.
 +
  simpl. {
  destruct (Int64.eq_dec i Int64.zero).
   +
    subst. rewrite Int64.eq_true.
    destruct (Int64.eq_dec i1 Int64.zero).
    - subst. rewrite Int64.eq_true.
      simpl. iSplit; auto.
    - rewrite -> Int64.eq_false by auto. simpl.
      simpl; unfold_lift;  unfold denote_tc_test_eq.
      rewrite -> (eval_expr_any rho a _ Ha')  by congruence.
      rewrite -> (eval_expr_any rho _ _ Hb')  by congruence.
      simpl. rewrite Hp.
      auto.
  + rewrite -> Int64.eq_false by auto. simpl.
    simpl; unfold_lift;  unfold denote_tc_test_eq.
    rewrite -> (eval_expr_any rho a _ Ha')  by congruence.
    rewrite -> (eval_expr_any rho _ _ Hb')  by congruence.
    simpl. rewrite Hp.
    auto.
  }
 +
  simpl. unfold_lift.
  rewrite -> (eval_expr_any rho b _ Hb') by congruence;
  rewrite -> (eval_expr_any rho a _ Ha') by congruence.
  simpl. rewrite Hp. auto.
Qed.

Lemma denote_tc_assert_andp_andp'_eq:
 forall {CS: compspecs} x y x' y' rho,
   (denote_tc_assert x rho ⊣⊢ denote_tc_assert x' rho) ->
   (denote_tc_assert y rho ⊣⊢ denote_tc_assert y' rho) ->
   denote_tc_assert (tc_andp x y) rho ⊣⊢ denote_tc_assert (tc_andp' x' y') rho.
Proof. intros. rewrite denote_tc_assert_andp'.
 simpl. unfold_lift. by rewrite H H0.
Qed.

Lemma denote_tc_assert_andp'_eq:
 forall {CS: compspecs} x y x' y' rho,
   (denote_tc_assert x rho ⊣⊢ denote_tc_assert x' rho) ->
   (denote_tc_assert y rho ⊣⊢ denote_tc_assert y' rho) ->
   denote_tc_assert (tc_andp' x y) rho ⊣⊢ denote_tc_assert (tc_andp' x' y') rho.
Proof. intros. simpl. unfold_lift. by rewrite H H0.
Qed.

Lemma denote_tc_assert_orp_orp'_eq:
 forall {CS: compspecs} x y x' y' rho,
   (denote_tc_assert x rho ⊣⊢ denote_tc_assert x' rho) ->
   (denote_tc_assert y rho ⊣⊢ denote_tc_assert y' rho) ->
   denote_tc_assert (tc_orp x y) rho ⊣⊢ denote_tc_assert (tc_orp' x' y') rho.
Proof. intros. rewrite denote_tc_assert_orp'.
 simpl. unfold_lift. by rewrite H H0.
Qed.

Lemma denote_tc_assert_orp'_eq:
 forall {CS: compspecs} x y x' y' rho,
   (denote_tc_assert x rho ⊣⊢ denote_tc_assert x' rho) ->
   (denote_tc_assert y rho ⊣⊢ denote_tc_assert y' rho) ->
   denote_tc_assert (tc_orp' x y) rho ⊣⊢ denote_tc_assert (tc_orp' x' y') rho.
Proof. intros.
 simpl. unfold_lift. by rewrite H H0.
Qed.

Local Hint Resolve 
  denote_tc_assert_andp_andp'_eq denote_tc_assert_andp'_eq
  denote_tc_assert_orp_orp'_eq denote_tc_assert_orp'_eq
  denote_tc_assert_iszero' denote_tc_assert_nonzero'
  denote_tc_assert_nodivover' denote_tc_assert_ilt' denote_tc_assert_llt'
  denote_tc_assert_test_eq' denote_tc_assert_test_order' : dtca.

Definition stupid_typeconv ty :=
match ty with
| Tarray t _ a => Tpointer t a
| Tfunction _ _ _ => Tpointer ty noattr
| Tint _ _ _ => typeconv ty
| _ => ty
end.

Lemma classify_cast_eq : forall t1 t2, eqb_type t1 int_or_ptr_type = false -> eqb_type t2 int_or_ptr_type = false ->
  Cop.classify_cast t1 t2 = Clight_Cop2.classify_cast t1 t2.
Proof.
  intros; unfold classify_cast, Clight_Cop2.classify_cast.
  destruct t2; auto.
  - destruct i; auto.
    destruct t1; auto.
    rewrite H; reflexivity.
  - destruct t1; auto; rewrite H0; reflexivity.
Qed.

Definition classify_sub' ty1 ty2 :=
match stupid_typeconv ty1 with
| Tpointer ty a =>
    match stupid_typeconv ty2 with
    | Tint _ si _ => sub_case_pi ty si
    | Tlong _ _ => sub_case_pl ty
    | Tpointer _ _ => sub_case_pp ty
    | _ => sub_default
    end
| _ => sub_default
end.

Lemma classify_sub_eq : classify_sub = classify_sub'.
Proof.
unfold classify_sub, classify_sub'; extensionality t1 t2.
destruct t1, t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Inductive classify_sub_rel (ty1 ty2 : type) : classify_sub_cases -> Prop :=
| classify_sub_pp t1 t2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tpointer t2 a2) :
  classify_sub_rel ty1 ty2 (sub_case_pp t1)
| classify_sub_pi t1 a1 sz si a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tint sz si a2) :
  classify_sub_rel ty1 ty2 (sub_case_pi t1 si)
| classify_sub_pl t1 a1 si a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tlong si a2) :
  classify_sub_rel ty1 ty2 (sub_case_pl t1)
| classify_sub_default (Hdefault : forall t1 a1, stupid_typeconv ty1 = Tpointer t1 a1 -> match stupid_typeconv ty2 with Tpointer _ _ | Tint _ _ _ | Tlong _ _ => False | _ => True end) :
  classify_sub_rel ty1 ty2 sub_default.

Lemma classify_sub_reflect : forall ty1 ty2, classify_sub_rel ty1 ty2 (classify_sub' ty1 ty2).
Proof.
  intros; unfold classify_sub'.
  destruct (stupid_typeconv ty1) eqn: Hty1, (stupid_typeconv ty2) eqn: Hty2;
    econstructor; rewrite ?Hty1 ?Hty2; done.
Qed.

Definition classify_cmp' ty1 ty2 :=
  match stupid_typeconv ty1, stupid_typeconv ty2 with
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ si _ => cmp_case_pi si
  | Tint _ si _, Tpointer _ _ => cmp_case_ip si
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

Inductive classify_cmp_rel (ty1 ty2 : type) : classify_cmp_cases -> Prop :=
| classify_cmp_pp t1 t2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tpointer t2 a2) :
  classify_cmp_rel ty1 ty2 cmp_case_pp
| classify_cmp_pi t1 a1 sz si a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tint sz si a2) :
  classify_cmp_rel ty1 ty2 (cmp_case_pi si)
| classify_cmp_ip a1 sz si t2 a2 (Hty1 : stupid_typeconv ty1 = Tint sz si a1) (Hty2 : stupid_typeconv ty2 = Tpointer t2 a2) :
  classify_cmp_rel ty1 ty2 (cmp_case_ip si)
| classify_cmp_pl t1 a1 si a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tlong si a2) :
  classify_cmp_rel ty1 ty2 cmp_case_pl
| classify_cmp_lp a1 si t2 a2 (Hty1 : stupid_typeconv ty1 = Tlong si a1) (Hty2 : stupid_typeconv ty2 = Tpointer t2 a2) :
  classify_cmp_rel ty1 ty2 cmp_case_lp
| classify_cmp_default (Hdefault : forall t1 a1, stupid_typeconv ty1 = Tpointer t1 a1 -> match stupid_typeconv ty2 with Tpointer _ _ | Tint _ _ _ | Tlong _ _ => False | _ => True end) :
  classify_cmp_rel ty1 ty2 cmp_default.

Lemma classify_cmp_reflect : forall ty1 ty2, classify_cmp_rel ty1 ty2 (classify_cmp' ty1 ty2).
Proof.
  intros; unfold classify_cmp'.
  destruct (stupid_typeconv ty1) eqn: Hty1, (stupid_typeconv ty2) eqn: Hty2;
    econstructor; rewrite ?Hty1 ?Hty2; done.
Qed.

Definition classify_add' ty1 ty2 :=
 match stupid_typeconv ty1 with
 | Tint _ si _ =>
    match stupid_typeconv ty2 with
    | Tpointer ty a => add_case_ip si ty
    |  _ => add_default
    end
| Tlong _ _ =>
    match stupid_typeconv ty2 with
    | Tpointer ty a => add_case_lp ty
    | _ => add_default
    end
| Tpointer ty a =>
    match stupid_typeconv ty2 with
    | Tint _ si _ => add_case_pi ty si
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

Inductive classify_add_rel (ty1 ty2 : type) : classify_add_cases -> Prop :=
| classify_add_pi t1 a1 sz si a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tint sz si a2) :
  classify_add_rel ty1 ty2 (add_case_pi t1 si)
| classify_add_ip a1 sz si t2 a2 (Hty1 : stupid_typeconv ty1 = Tint sz si a1) (Hty2 : stupid_typeconv ty2 = Tpointer t2 a2) :
  classify_add_rel ty1 ty2 (add_case_ip si t2)
| classify_add_pl t1 a1 si a2 (Hty1 : stupid_typeconv ty1 = Tpointer t1 a1) (Hty2 : stupid_typeconv ty2 = Tlong si a2) :
  classify_add_rel ty1 ty2 (add_case_pl t1)
| classify_add_lp a1 si t2 a2 (Hty1 : stupid_typeconv ty1 = Tlong si a1) (Hty2 : stupid_typeconv ty2 = Tpointer t2 a2) :
  classify_add_rel ty1 ty2 (add_case_lp t2)
| classify_add_default (Hdefault1 : forall t1 a1, stupid_typeconv ty1 = Tpointer t1 a1 -> match stupid_typeconv ty2 with Tint _ _ _ | Tlong _ _ => False | _ => True end)
  (Hdefault2 : forall t2 a2, stupid_typeconv ty2 = Tpointer t2 a2 -> match stupid_typeconv ty1 with Tint _ _ _ | Tlong _ _ => False | _ => True end) :
  classify_add_rel ty1 ty2 add_default.

Lemma classify_add_reflect : forall ty1 ty2, classify_add_rel ty1 ty2 (classify_add' ty1 ty2).
Proof.
  intros; unfold classify_add'.
  destruct (stupid_typeconv ty1) eqn: Hty1, (stupid_typeconv ty2) eqn: Hty2;
    econstructor; rewrite ?Hty1 ?Hty2; done.
Qed.

Definition classify_shift' (ty1: type) (ty2: type) :=
  match stupid_typeconv ty1, stupid_typeconv ty2 with
  | Tint sz sg _, Tint _ _ _ => shift_case_ii
    match sz, sg with 
    | I32, Unsigned => Unsigned
    | _, _ => Signed
    end
  | Tint sz sg _, Tlong _ _ => shift_case_il
    match sz, sg with
    | I32, Unsigned => Unsigned
    | _, _ => Signed
    end
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

Definition is_integer_type t := match t with Tint _ _ _ | Tlong _ _ => true | _ => false end.

Inductive classify_shift_rel (ty1 ty2 : type) : classify_shift_cases -> Prop :=
| classify_shift_iiu sz2 sg2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint I32 Unsigned a1) (Hty2 : stupid_typeconv ty2 = Tint sz2 sg2 a2) :
  classify_shift_rel ty1 ty2 (shift_case_ii Unsigned)
| classify_shift_iis sz1 sz2 sg1 sg2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint sz1 sg1 a1) (Hty2 : stupid_typeconv ty2 = Tint sz2 sg2 a2)
    (Hsigned : sz1 <> I32 \/ sg1 = Signed) :
  classify_shift_rel ty1 ty2 (shift_case_ii Signed)
| classify_shift_ilu sg2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint I32 Unsigned a1) (Hty2 : stupid_typeconv ty2 = Tlong sg2 a2) :
  classify_shift_rel ty1 ty2 (shift_case_il Unsigned)
| classify_shift_ils sz1 sg1 sg2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint sz1 sg1 a1) (Hty2 : stupid_typeconv ty2 = Tlong sg2 a2)
    (Hsigned : sz1 <> I32 \/ sg1 = Signed) :
  classify_shift_rel ty1 ty2 (shift_case_il Signed)
| classify_shift_li sz2 sg1 sg2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tlong sg1 a1) (Hty2 : stupid_typeconv ty2 = Tint sz2 sg2 a2) :
  classify_shift_rel ty1 ty2 (shift_case_li sg1)
| classify_shift_ll sg1 sg2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tlong sg1 a1) (Hty2 : stupid_typeconv ty2 = Tlong sg2 a2) :
  classify_shift_rel ty1 ty2 (shift_case_ll sg1)
| classify_shift_default (Hdefault : is_integer_type (stupid_typeconv ty1) = false \/ is_integer_type (stupid_typeconv ty2) = false) :
  classify_shift_rel ty1 ty2 shift_default.

Lemma classify_shift_reflect : forall ty1 ty2, classify_shift_rel ty1 ty2 (classify_shift' ty1 ty2).
Proof.
  intros; unfold classify_shift'.
  destruct (stupid_typeconv ty1) eqn: Hty1, (stupid_typeconv ty2) eqn: Hty2;
    try (econstructor; rewrite ?Hty1 ?Hty2; auto); destruct i, s; try (econstructor; rewrite ?Hty1 ?Hty2; auto).
Qed.

Definition classify_binarith' (ty1: type) (ty2: type) :=
  match stupid_typeconv ty1, stupid_typeconv ty2 with
  | Tint i1 s1 _, Tint i2 s2 _ => bin_case_i 
    match i1, s1, i2, s2 with
    | I32, Unsigned, _, _ => Unsigned
    | _, _, I32, Unsigned => Unsigned
    | _, _, _, _ => Signed
    end
  | Tint _ _ _, Tlong s _ => bin_case_l s
  | Tlong s _, Tint _ _ _ => bin_case_l s
  | Tlong s1 _, Tlong s2 _ => bin_case_l
    match s1, s2 with
    | Signed, Signed => Signed
    | _, _ => Unsigned
    end
  | Tfloat F32 _, Tfloat F32 _ => bin_case_s
  | Tfloat _ _, Tfloat _ _ => bin_case_f
  | Tfloat F64 _, (Tint _ _ _ | Tlong _ _) => bin_case_f
  | (Tint _ _ _ | Tlong _ _), Tfloat F64 _ => bin_case_f
  | Tfloat F32 _, (Tint _ _ _ | Tlong _ _) => bin_case_s
  | (Tint _ _ _ | Tlong _ _), Tfloat F32 _ => bin_case_s
  | _, _ => bin_default
  end.

Definition binarithType' t1 t2 ty deferr reterr : tc_assert :=
  match classify_binarith' t1 t2 with
  | Cop.bin_case_i sg =>  tc_bool (is_int32_type ty) reterr
  | Cop.bin_case_l sg => tc_bool (is_long_type ty) reterr
  | Cop.bin_case_f   => tc_bool (is_float_type ty) reterr
  | Cop.bin_case_s   => tc_bool (is_single_type ty) reterr
  | Cop.bin_default => tc_FF deferr
  end.

Lemma classify_binarith_eq: classify_binarith = classify_binarith'.
Proof.
  unfold classify_binarith; extensionality t1 t2.
  destruct t1,t2; simpl; auto;
  try destruct i,s; auto;
  try destruct i0,s0; auto;
  try destruct s; auto;
  try destruct s0; auto.
Qed.

Lemma binarithType_eq: binarithType = binarithType'.
Proof.
  unfold binarithType, binarithType'; extensionality t1 t2 ty e1 e2.
  rewrite classify_binarith_eq.
  auto.
Qed.

Inductive classify_binarith_rel (ty1 ty2 : type) : binarith_cases -> Prop :=
| classify_binarith_i_un i1 i2 s1 s2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint i1 s1 a1) (Hty2 : stupid_typeconv ty2 = Tint i2 s2 a2)
    (Hunsigned : (i1 = I32 /\ s1 = Unsigned) \/ (i2 = I32 /\ s2 = Unsigned)) :
  classify_binarith_rel ty1 ty2 (bin_case_i Unsigned)
| classify_binarith_i_si i1 i2 s1 s2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint i1 s1 a1) (Hty2 : stupid_typeconv ty2 = Tint i2 s2 a2)
    (Hsigned : ~(i1 = I32 /\ s1 = Unsigned) /\ ~(i2 = I32 /\ s2 = Unsigned)) :
  classify_binarith_rel ty1 ty2 (bin_case_i Signed)
| classify_binarith_il i1 s1 a1 s2 a2 (Hty1 : stupid_typeconv ty1 = Tint i1 s1 a1) (Hty2 : stupid_typeconv ty2 = Tlong s2 a2) :
  classify_binarith_rel ty1 ty2 (bin_case_l s2)
| classify_binarith_li s1 a1 i2 s2 a2 (Hty1 : stupid_typeconv ty1 = Tlong s1 a1) (Hty2 : stupid_typeconv ty2 = Tint i2 s2 a2) :
  classify_binarith_rel ty1 ty2 (bin_case_l s1)
| classify_binarith_l_si a1 a2 (Hty1 : stupid_typeconv ty1 = Tlong Signed a1) (Hty2 : stupid_typeconv ty2 = Tlong Signed a2) :
  classify_binarith_rel ty1 ty2 (bin_case_l Signed)
| classify_binarith_l_un s1 s2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tlong s1 a1) (Hty2 : stupid_typeconv ty2 = Tlong s2 a2)
    (Hunsigned : s1 <> Signed \/ s2 <> Signed) :
  classify_binarith_rel ty1 ty2 (bin_case_l Unsigned)
| classify_binarith_ss a1 a2 (Hty1 : stupid_typeconv ty1 = Tfloat F32 a1) (Hty2 : stupid_typeconv ty2 = Tfloat F32 a2) :
  classify_binarith_rel ty1 ty2 bin_case_s
| classify_binarith_ff s1 s2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tfloat s1 a1) (Hty2 : stupid_typeconv ty2 = Tfloat s2 a2)
    (Hfloat : s1 <> F32 \/ s2 <> F32) :
  classify_binarith_rel ty1 ty2 bin_case_f
| classify_binarith_fi s2 i2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tfloat F64 a1) (Hty2 : stupid_typeconv ty2 = Tint i2 s2 a2) :
  classify_binarith_rel ty1 ty2 bin_case_f
| classify_binarith_fl s2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tfloat F64 a1) (Hty2 : stupid_typeconv ty2 = Tlong s2 a2) :
  classify_binarith_rel ty1 ty2 bin_case_f
| classify_binarith_if i1 s1 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint i1 s1 a1) (Hty2 : stupid_typeconv ty2 = Tfloat F64 a2) :
  classify_binarith_rel ty1 ty2 bin_case_f
| classify_binarith_lf s1 a1 a2 (Hty1 : stupid_typeconv ty1 = Tlong s1 a1) (Hty2 : stupid_typeconv ty2 = Tfloat F64 a2) :
  classify_binarith_rel ty1 ty2 bin_case_f
| classify_binarith_si s2 i2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tfloat F32 a1) (Hty2 : stupid_typeconv ty2 = Tint i2 s2 a2) :
  classify_binarith_rel ty1 ty2 bin_case_s
| classify_binarith_sl s2 a1 a2 (Hty1 : stupid_typeconv ty1 = Tfloat F32 a1) (Hty2 : stupid_typeconv ty2 = Tlong s2 a2) :
  classify_binarith_rel ty1 ty2 bin_case_s
| classify_binarith_is i1 s1 a1 a2 (Hty1 : stupid_typeconv ty1 = Tint i1 s1 a1) (Hty2 : stupid_typeconv ty2 = Tfloat F32 a2) :
  classify_binarith_rel ty1 ty2 bin_case_s
| classify_binarith_ls s1 a1 a2 (Hty1 : stupid_typeconv ty1 = Tlong s1 a1) (Hty2 : stupid_typeconv ty2 = Tfloat F32 a2) :
  classify_binarith_rel ty1 ty2 bin_case_s
| classify_binarith_default (Hdefault : is_numeric_type (stupid_typeconv ty1) = false \/ is_numeric_type (stupid_typeconv ty2) = false) :
  classify_binarith_rel ty1 ty2 bin_default.

Lemma classify_binarith_reflect : forall ty1 ty2, classify_binarith_rel ty1 ty2 (classify_binarith' ty1 ty2).
Proof.
  intros; unfold classify_binarith'.
  destruct (stupid_typeconv ty1) eqn: Hty1, (stupid_typeconv ty2) eqn: Hty2;
    try solve [try destruct f; econstructor; rewrite ?Hty1 ?Hty2 /=; auto].
  - destruct i, i0; try (econstructor; rewrite ?Hty1 ?Hty2 /=; auto; intuition; try done);
      destruct s0; try (econstructor; rewrite ?Hty1 ?Hty2 /=; auto; intuition; try done);
      destruct s; try (econstructor; rewrite ?Hty1 ?Hty2 /=; auto; intuition; try done).
  - destruct s, s0; [eapply classify_binarith_l_si | eapply classify_binarith_l_un ..];
      rewrite ?Hty1 ?Hty2 /=; auto.
  - destruct f, f0; econstructor; eauto.
Qed.

Opaque stupid_typeconv.

Lemma den_isBinOpR: forall {CS: compspecs} op a1 a2 ty rho,
  denote_tc_assert (isBinOpResultType op a1 a2 ty) rho ⊣⊢
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in
denote_tc_assert
match op with
  | Cop.Oadd => match classify_add' (typeof a1) (typeof a2) with
                    | Cop.add_case_pi t _ => tc_andp' (tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_ip _ t => tc_andp' (tc_andp' (tc_andp' (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a2)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_pl t => tc_andp' (tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_lp t => tc_andp' (tc_andp' (tc_andp' (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a2)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_default => tc_andp 
                                           (binarithType' (typeof a1) (typeof a2) ty deferr reterr)
                                           (tc_nobinover Z.add a1 a2)
            end
  | Cop.Osub => match classify_sub' (typeof a1) (typeof a2) with
                    | Cop.sub_case_pi t _ => tc_andp' (tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pl t => tc_andp' (tc_andp' (tc_andp' (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pp t =>
                             tc_andp' (tc_andp' (tc_andp' (tc_andp' (tc_andp' (tc_andp' 
                              (tc_andp' (tc_andp' (tc_samebase a1 a2)
                             (tc_isptr a1))
                              (tc_isptr a2))
                               (tc_int_or_ptr_type (typeof a1)))
                               (tc_int_or_ptr_type (typeof a2)))
                               (tc_bool (is_ptrofs_type ty) reterr))
			        (tc_bool (negb (Z.eqb (sizeof t) 0))
                                      (pp_compare_size_0 t)))
                                 (tc_bool (complete_type cenv_cs t) reterr))
                                  (tc_bool (Z.leb (sizeof t) Ptrofs.max_signed)
                                         (pp_compare_size_exceed t))
                    | Cop.sub_default => tc_andp 
                                        (binarithType' (typeof a1) (typeof a2) ty deferr reterr)
                                        (tc_nobinover Z.sub a1 a2)
            end
  | Cop.Omul => tc_andp (binarithType' (typeof a1) (typeof a2) ty deferr reterr)
                   (tc_nobinover Z.mul a1 a2)
  | Cop.Omod => match classify_binarith' (typeof a1) (typeof a2) with
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
  | Cop.Odiv => match classify_binarith' (typeof a1) (typeof a2) with
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
                    | Cop.shift_case_il _ =>  tc_andp' (tc_llt' a2 (Int64.repr 32)) (tc_bool (is_int32_type ty)
                                                                                         reterr)
                    | Cop.shift_case_li _ =>  tc_andp' (tc_ilt' a2 Int64.iwordsize') (tc_bool (is_long_type ty)
                                                                                         reterr)
                    | Cop.shift_case_ll _ =>  tc_andp' (tc_llt' a2 Int64.iwordsize) (tc_bool (is_long_type ty)
                                                                                         reterr)
                    | _ => tc_FF deferr
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor =>
                   match classify_binarith' (typeof a1) (typeof a2) with
                    | Cop.bin_case_i _ =>tc_bool (is_int32_type ty) reterr
                    | Cop.bin_case_l _ =>tc_bool (is_long_type ty) reterr
                    | Cop.bin_case_f => tc_FF deferr
                    | Cop.bin_case_s => tc_FF deferr
                    | Cop.bin_default => tc_FF deferr
                   end
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
                   match classify_cmp' (typeof a1) (typeof a2) with
                    | Cop.cmp_default =>
                           tc_bool (is_numeric_type (typeof a1)
                                         && is_numeric_type (typeof a2)
                                          && is_int_type ty)
                                             deferr
 		                | Cop.cmp_case_pp => tc_andp' (tc_andp' (tc_int_or_ptr_type (typeof a1)) 
                                      (tc_int_or_ptr_type (typeof a2)))
                              (check_pp_int' a1 a2 op ty e)
                   | Cop.cmp_case_pi si =>
                          tc_andp' (tc_int_or_ptr_type (typeof a1))
                            (check_pp_int' a1 (Ecast a2 size_t) op ty e)
                   | Cop.cmp_case_ip si => 
                          tc_andp' (tc_int_or_ptr_type (typeof a2))
                           (check_pp_int' (Ecast a1 size_t) a2 op ty e)
                   | Cop.cmp_case_pl => 
                          tc_andp' (tc_int_or_ptr_type (typeof a1))
                            (check_pp_int' a1 (Ecast a2 size_t) op ty e)
                   | Cop.cmp_case_lp => 
                          tc_andp' (tc_int_or_ptr_type (typeof a2))
                          (check_pp_int' (Ecast a1 size_t) a2 op ty e)
                   end
  end rho.
Proof.
  intros.
 rewrite <- classify_add_eq. rewrite <- classify_sub_eq.
 rewrite <- classify_shift_eq. rewrite <- classify_cmp_eq.
 rewrite <- classify_binarith_eq. rewrite <- binarithType_eq.
 unfold isBinOpResultType;
  destruct op; auto; match goal with |-context[match ?A with _ => _ end] => destruct A end;
    rewrite ?denote_tc_assert_andp ?denote_tc_assert_ilt' ?denote_tc_assert_llt' ?denote_tc_assert_test_eq' ?denote_tc_assert_test_order'; try reflexivity;
    destruct s; rewrite !denote_tc_assert_andp !denote_tc_assert_nonzero' ?denote_tc_assert_nodivover'; reflexivity.
Qed.

(*Lemma denote_tc_assert'_andp'_e:
 forall {CS: compspecs} a b rho m, denote_tc_assert' (tc_andp' a b) rho m ->
    denote_tc_assert' a rho m /\ denote_tc_assert' b rho m.
Proof. intros.
 rewrite denote_tc_assert'_eq in *. apply H.
Qed.*)

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
rewrite Int64.signed_zero in H.
auto.
pose proof (Int.signed_range i).
clear - H.
destruct H.
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
clear - H.
destruct H.
split; auto.
unfold Int64.max_unsigned.
apply Z.le_trans with Int.modulus.
lia.
compute; congruence.
Qed.

Definition tc_numeric_val (v: val) (t: type) : Prop :=
 match v,t with
 | Vint _, Tint _ _ _ => True
 | Vlong _, Tlong _ _ => True
 | Vfloat _, Tfloat F64 _ => True
 | _, _ => False
 end.

Inductive tc_numeric_rel : val -> type -> Prop :=
| tc_numeric_int i sz si a : tc_numeric_rel (Vint i) (Tint sz si a)
| tc_numeric_long i si a : tc_numeric_rel (Vlong i) (Tlong si a)
| tc_numeric_float i a : tc_numeric_rel (Vfloat i) (Tfloat F64 a).

Lemma tc_numeric_reflect : forall v t, tc_numeric_val v t <-> tc_numeric_rel v t.
Proof.
  destruct v, t; simpl; split; try done; try solve [by inversion 1]; try constructor.
  destruct f0; try done; constructor.
Qed.

Lemma tc_val_of_bool:
 forall x i3 s3 a3, tc_val (Tint i3 s3 a3) (Val.of_bool x).
Proof.
intros.
destruct x, i3,s3; simpl; try split; auto;
rewrite <- Z.leb_le;
reflexivity.
Qed.

Lemma tc_bool2val:
 forall x i3 s3 a3, tc_val (Tint i3 s3 a3) (bool2val x).
Proof.
intros.
destruct x, i3,s3; simpl; try split; auto;
rewrite <- Z.leb_le;
reflexivity.
Qed.

Lemma tc_val_sem_cmp:
 forall op v1 t1 v2 t2 i3 s3 a3,
 tc_numeric_val v1 t1 ->
 tc_numeric_val v2 t2 ->
tc_val (Tint i3 s3 a3)
  (force_val (Clight_Cop2.sem_cmp op t1 t2 v1 v2)).
Proof.
Opaque tc_val.
destruct op; intros;
destruct v1;
  destruct t1 as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction H;
destruct v2;
  destruct t2 as  [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction H0;
 apply tc_bool2val.
Transparent tc_val.
Qed.

Lemma tc_val'_sem_cmp_pp: forall cmp v1 v2 v i s a,
  sem_cmp_pp cmp v1 v2 = Some v ->
  tc_val' (Tint i s a) v.
Proof.
  intros.
  unfold sem_cmp_pp, option_map in H.
  forget (if Archi.ptr64 then Val.cmplu_bool true2 cmp v1 v2 else Val.cmpu_bool true2 cmp v1 v2) as v0.
  destruct v0; inv H.
  intros _; apply tc_bool2val.
Qed.

Lemma tc_val'_sem_cmp: forall cmp t v1 v2 t1 t2,
  is_int_type t = true ->
  tc_val' t (force_val2 (Clight_Cop2.sem_cmp cmp t1 t2) v1 v2).
Proof.
  intros.
  destruct t; inv H.
  unfold force_val2, force_val.
  destruct (Clight_Cop2.sem_cmp cmp t1 t2 v1 v2) eqn:?H; [| intros ?; congruence].
  unfold Clight_Cop2.sem_cmp in H.
  Opaque tc_val.
  destruct (Cop.classify_cmp t1 t2).
  + revert H; simple_if_tac; intros; [congruence |].
    eapply tc_val'_sem_cmp_pp; eauto.
  + revert H; simple_if_tac; intros; [congruence |].
    unfold sem_cmp_pi in H.
    destruct v2; [ inv H | | inv H .. |].
    - eapply tc_val'_sem_cmp_pp; eauto.
    - destruct Archi.ptr64; inv H;
      try (eapply tc_val'_sem_cmp_pp; eauto).
  + revert H; simple_if_tac; intros; [congruence |].
    unfold sem_cmp_ip in H.
    destruct v1; [ inv H | | inv H .. |].
    - eapply tc_val'_sem_cmp_pp; eauto.
    - destruct Archi.ptr64; inv H;
      try (eapply tc_val'_sem_cmp_pp; eauto).
  + revert H; simple_if_tac; intros; [congruence |].
    unfold sem_cmp_pl in H.
    destruct v2; try congruence.
    - eapply tc_val'_sem_cmp_pp; eauto.
    - destruct Archi.ptr64; inv H.
      eapply tc_val'_sem_cmp_pp; eauto.
  + revert H; simple_if_tac; intros; [congruence |].
    unfold sem_cmp_lp in H.
    destruct v1; try congruence.
    - eapply tc_val'_sem_cmp_pp; eauto.
    - destruct Archi.ptr64; inv H.
      eapply tc_val'_sem_cmp_pp; eauto.
  + unfold sem_cmp_default, Clight_Cop2.sem_binarith in H.
    destruct (Cop.classify_binarith t1 t2).
    - unfold both_int in H.
      forget (Clight_Cop2.sem_cast t1 (Cop.binarith_type (Cop.bin_case_i s0)) v1) as v1'.
      forget (Clight_Cop2.sem_cast t2 (Cop.binarith_type (Cop.bin_case_i s0)) v2) as v2'.
      destruct v1'; [| inv H].
      destruct v0; inv H.
      destruct v2'; [| inv H1].
      destruct v0; inv H1.
      intros _; apply tc_bool2val.
    - unfold both_long in H.
      forget (Clight_Cop2.sem_cast t1 (Cop.binarith_type (Cop.bin_case_l s0)) v1) as v1'.
      forget (Clight_Cop2.sem_cast t2 (Cop.binarith_type (Cop.bin_case_l s0)) v2) as v2'.
      destruct v1'; [| inv H].
      destruct v0; inv H.
      destruct v2'; [| inv H1].
      destruct v0; inv H1.
      intros _; apply tc_bool2val.
    - unfold both_float in H.
      forget (Clight_Cop2.sem_cast t1 (Cop.binarith_type (Cop.bin_case_f)) v1) as v1'.
      forget (Clight_Cop2.sem_cast t2 (Cop.binarith_type (Cop.bin_case_f)) v2) as v2'.
      destruct v1'; [| inv H].
      destruct v0; inv H.
      destruct v2'; [| inv H1].
      destruct v0; inv H1.
      intros _; apply tc_bool2val.
    - unfold both_single in H.
      forget (Clight_Cop2.sem_cast t1 (Cop.binarith_type (Cop.bin_case_s)) v1) as v1'.
      forget (Clight_Cop2.sem_cast t2 (Cop.binarith_type (Cop.bin_case_s)) v2) as v2'.
      destruct v1'; [| inv H].
      destruct v0; inv H.
      destruct v2'; [| inv H1].
      destruct v0; inv H1.
      intros _; apply tc_bool2val.
    - inv H.
Qed.

Lemma tc_val_cmp_eqne_ip:
 forall op v1 t1 v2 t0 a0 i2 s0 a1,
 match op with Ceq => True | Cne => True | _ => False end ->
 match v1,t1 with
 | Vint i, Tint _ _ _ => Int.eq i Int.zero = true
 | Vlong i, Tlong _ _ => Int64.eq (Int64.repr (Int64.unsigned i)) Int64.zero = true
 | _, _ => False
 end ->
 tc_val (Tpointer t0 a0) v2 ->
tc_val (Tint i2 s0 a1)
  (force_val (Clight_Cop2.sem_cmp op t1 (Tpointer t0 a0) v1 v2)).
Proof.
Opaque tc_val.
intros until 1; rename H into CMP; intros;
 destruct op; try contradiction CMP; clear CMP;
 destruct v1, t1; try contradiction H;
 destruct v2; 
 try (inv H0; try rewrite H2;
 try destruct i0; destruct s;
unfold Clight_Cop2.sem_cmp, classify_cmp, typeconv,
  Clight_Cop2.sem_binarith, sem_cast, classify_cast, sem_cmp_lp, sem_cmp_pp;
 simpl; try rewrite H;
 try reflexivity;
 try apply tc_bool2val).
Transparent tc_val.
all: try solve [hnf in H0; destruct (eqb_type _ _); inv H0].
Abort.

Lemma tc_val_cmp_eqne_pi:
 forall op v1 t1 v2 t0 a0 i2 s0 a1,
 match op with Ceq => True | Cne => True | _ => False end ->
 match v1,t1 with
 | Vint i, Tint _ _ _ => Int.eq i Int.zero = true
 | Vlong i, Tlong _ _ => Int64.eq (Int64.repr (Int64.unsigned i)) Int64.zero = true
 | _, _ => False
 end ->
tc_val (Tpointer t0 a0) v2 ->
tc_val (Tint i2 s0 a1) 
  (force_val (Clight_Cop2.sem_cmp op (Tpointer t0 a0) t1 v2 v1)).
Proof.
Opaque tc_val.
intros until 1; rename H into CMP; intros.
 destruct op; try contradiction CMP; clear CMP;
 destruct v1, t1; try contradiction H;
 destruct v2; 
 try (inv H0; try rewrite H2;
 try destruct i0; destruct s;
unfold Clight_Cop2.sem_cmp, classify_cmp, typeconv,
  sem_binarith, sem_cast, classify_cast, sem_cmp_pl, sem_cmp_pp;
 simpl; try rewrite H;
 try reflexivity;
 try apply tc_bool2val).
Transparent tc_val.
Abort.

End mpred.
