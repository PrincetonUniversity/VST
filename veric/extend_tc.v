Require Export VST.veric.Clight_base.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.expr_lemmas.

Require Import VST.veric.seplog. (*For definition of tycontext*)
Import LiftNotation.

Section mpred.

Context `{!heapGS Σ}.

Definition tc_expr {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred :=
  fun rho => denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist {CS: compspecs} (Delta: tycontext) (t : list type) (e: list expr) : environ -> mpred :=
      fun rho => denote_tc_assert (typecheck_exprlist Delta t e) rho.

Definition tc_lvalue {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred :=
     fun rho => denote_tc_assert (typecheck_lvalue Delta e) rho.

Definition tc_temp_id {CS: compspecs} (id : positive) (ty : type)
  (Delta : tycontext) (e : expr) : environ -> mpred  :=
     fun rho => denote_tc_assert (typecheck_temp_id id ty Delta e) rho.

Definition tc_expropt {CS: compspecs} Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `⌜t=Ctypes.Tvoid⌝
                     | Some e' => `bi_absorbingly (tc_expr Delta (Ecast e' t))
   end.

Definition tc_temp_id_load id tfrom Delta v : environ -> mpred  :=
fun rho => ⌜exists tto, (temp_types Delta) !! id = Some tto
                      /\ tc_val tto (eval_cast tfrom tto (v rho))⌝.

Ltac extend_tc_prover :=
  match goal with
  | |- _ => apply _
  | |- Absorbing (if ?A then _ else _) => destruct A
  | |- Absorbing (match ?A with _ => _ end) => destruct A
  | |- Absorbing (match ?A with _ => _ end _) => destruct A
  end.

Global Instance denote_tc_assert_absorbing : forall {CS: compspecs} a rho, Absorbing (denote_tc_assert a rho).
Proof.
  intros; induction a; simpl; try apply _; unfold_lift; rewrite /denote_tc_nonzero /denote_tc_iszero /denote_tc_test_eq /denote_tc_test_order
    /denote_tc_igt /denote_tc_lgt /denote_tc_Zle  /denote_tc_Zge /denote_tc_nodivover /denote_tc_nosignedover /test_eq_ptrs /test_order_ptrs; repeat extend_tc_prover.
Qed.

Global Instance tc_expropt_absorbing: forall {CS: compspecs} Delta e t rho, Absorbing (tc_expropt Delta e t rho).
Proof.
  intros. unfold tc_expropt.
  destruct e; apply _.
Qed.

Lemma tc_bool_i:
 forall {cs: compspecs} b e rho,
   b = true -> True ⊢ denote_tc_assert (tc_bool b e) rho.
Proof.
intros. subst. auto.
Qed.

Section CENV_SUB.
  Context {CS CS': compspecs}
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')).

 Definition is_tc_FF (a: tc_assert) :=
  match a with tc_FF _ => True%type | _ => False%type end.

 Definition dec_tc_FF (a: tc_assert) : {is_tc_FF a}+{~is_tc_FF a}.
 Proof. destruct a; simpl; auto. Qed.


  Lemma tc_test_eq_cenv_sub a1 a2 rho:
   denote_tc_assert(CS := CS) (tc_test_eq(CS := CS) a1 a2) rho ⊢
   denote_tc_assert(CS := CS') (tc_test_eq(CS := CS') a1 a2) rho.
  Proof.
    rewrite !denote_tc_assert_test_eq'.
    apply denote_tc_assert_cenv_sub; auto.
  Qed.

Lemma entails_refl : forall (P : mpred), P ⊢ P.
Proof. done. Qed.

Lemma pure_intro_l : forall (P : Prop) (Q R : mpred), P -> (Q ⊢ R) -> Q ⊢ ⌜P⌝ ∧ R.
Proof.
  intros ???? ->; iIntros "$"; auto.
Qed.

Lemma pure_intro_r : forall (P : Prop) (Q R : mpred), P -> (Q ⊢ R) -> Q ⊢ R ∧ ⌜P⌝.
Proof.
  intros ???? ->; iIntros "$"; auto.
Qed.

Ltac tc_expr_cenv_sub_tac := 
repeat
match goal with
 | |- @denote_tc_assert _ _ _ (tc_andp _ _) _ ⊢ _ =>
     rewrite !denote_tc_assert_andp
 | |- _ ∧ @denote_tc_assert _ _ _ (tc_bool (complete_type _ _) _) _ ⊢ _ =>
        rewrite (tc_bool_e (complete_type _ _)); apply bi.pure_elim_r; intros
 | |- @denote_tc_assert _ _ _ (tc_bool (complete_type _ _) _) _ ∧ _ ⊢ _ =>
        rewrite tc_bool_e; apply bi.pure_elim_l; intros
 | |- _ ⊢ @denote_tc_assert _ _ _ (tc_bool (complete_type _ _) _) _ ∧ _ =>
      rewrite -> (cenv_sub_complete_type _ _ CSUB) by assumption; apply pure_intro_l; first apply I
 | |- _ ⊢ _ ∧ @denote_tc_assert _ _ _ (tc_bool (complete_type _ _) _) _ =>
      rewrite -> (cenv_sub_complete_type _ _ CSUB) by assumption; apply pure_intro_r; first apply I
 | |- _ ⊢ (_ ∧ @denote_tc_assert _ _ _ (tc_bool (complete_type _ _) _) _) ∧ _ =>
      do 2 rewrite (bi.and_comm _ (@denote_tc_assert _ _ _ (tc_bool (complete_type _ _) _) _)); rewrite -!assoc
 | |- _ ∧ _ ⊢ _ ∧ _ => apply bi.and_mono
 | |- _ => solve [simple apply tc_test_eq_cenv_sub; auto]
 | |- @denote_tc_assert _ _ _ (tc_bool ?A _) _ ⊢ _ =>
    match A with context [sizeof ?t] => unfold sizeof;
     rewrite -> (cenv_sub_sizeof CSUB t) by assumption
   end
end;
  try solve [eauto].

Ltac tc_expr_cenv_sub_tac2 :=  
 (match goal with
   | |- @denote_tc_assert _ _ _ match @eval_expr CS ?a ?rho with _ => _ end _ ⊢ _ =>

        let H' := fresh in
        destruct (Val.eq (@eval_expr CS a rho) Vundef) as [H' | H'];
         [ rewrite H';
            try match goal with |- context [@eval_expr CS' a rho] =>
             destruct (@eval_expr CS' a rho) eqn:?
           end
         | rewrite <- ?(eval_expr_cenv_sub_eq CSUB _ _ H');
           destruct (@eval_expr CS a rho) eqn:?]
    | |- _ ⊢ @denote_tc_assert _ _ _ match @eval_expr CS' ?a ?rho with _ => _ end _ =>
       destruct (@eval_expr CS' a rho) eqn:?H
    | |- _ ⊢ @denote_tc_assert _ _ _ (if _ then tc_TT else _) _ =>
    simple_if_tac; [auto | ]
   end;
  try assumption;
  try (simple apply (denote_tc_assert_cenv_sub CSUB); auto)).

  Lemma tc_nobinover_cenv_sub op a1 a2 rho:
   denote_tc_assert(CS := CS) (tc_nobinover op (CS := CS) a1 a2) rho ⊢
   denote_tc_assert(CS := CS') (tc_nobinover op (CS := CS') a1 a2) rho.
 Proof.
  unfold tc_nobinover.
  unfold if_expr_signed.
  destruct (typeof a1) as [ | _ [ | ] | [ | ] | [ | ] | | | | | ]; 
  destruct (typeof a2) as [ | _ [ | ] | [ | ]  | | | | | | ]; 
  tc_expr_cenv_sub_tac; repeat tc_expr_cenv_sub_tac2.
 Qed.

Lemma tc_expr_cenv_sub_unop:
 forall 
 (u : Cop.unary_operation)
 (a : expr)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (IHa : @tc_expr CS Delta a rho ⊢ @tc_expr CS' Delta a rho),
 @tc_expr CS Delta (Eunop u a t) rho ⊢
 @tc_expr CS' Delta (Eunop u a t) rho.
Proof.
  intros.
  unfold tc_expr in *; unfold typecheck_expr; fold typecheck_expr.
  tc_expr_cenv_sub_tac.
  destruct u; simpl;
  destruct (typeof a) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
  tc_expr_cenv_sub_tac; try apply (denote_tc_assert_cenv_sub CSUB).
Qed.

Lemma tc_complete_type_cenv_sub:
 forall t e rho,
  denote_tc_assert(CS := CS) (tc_bool (complete_type (@cenv_cs CS) t) e) rho ⊢
  denote_tc_assert(CS := CS') (tc_bool (complete_type (@cenv_cs CS') t) e) rho.
Proof.
intros.
unfold tc_bool.
destruct (complete_type _ _) eqn: Hc; [|iIntros "[]"].
rewrite (cenv_sub_complete_type _ _ CSUB); auto.
Qed.

Lemma tc_expr_cenv_sub_binop:
 forall 
 (b : Cop.binary_operation)
 (a1 a2 : expr)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (IHa1 : @tc_expr CS Delta a1 rho ⊢ @tc_expr CS' Delta a1 rho)
 (IHa2 : @tc_expr CS Delta a2 rho ⊢ @tc_expr CS' Delta a2 rho),
 @tc_expr CS Delta (Ebinop b a1 a2 t) rho ⊢
 @tc_expr CS' Delta (Ebinop b a1 a2 t) rho.
Proof.
  intros.
  unfold tc_expr, typecheck_expr;
  fold (typecheck_expr(CS := CS));
  fold (typecheck_expr(CS := CS')).
  tc_expr_cenv_sub_tac.
  rewrite /isBinOpResultType.
  repeat match goal with |- denote_tc_assert match ?A with _ => _ end _ ⊢ _ =>
    destruct A eqn: ?Hcase
  end; tc_expr_cenv_sub_tac; rewrite ?denote_tc_assert_nonzero' ?denote_tc_assert_nodivover' ?denote_tc_assert_ilt' ?denote_tc_assert_llt' ?denote_tc_assert_test_order';
    try apply (denote_tc_assert_cenv_sub CSUB); try apply tc_nobinover_cenv_sub.
Qed.

Lemma tc_expr_cenv_sub_cast:
 forall
 (a : expr)
 (t : type)
 (rho : environ)
 (Delta : tycontext)
 (IHa : @tc_expr CS Delta a rho ⊢ @tc_expr CS' Delta a rho),
 @tc_expr CS Delta (Ecast a t) rho ⊢
 @tc_expr CS' Delta (Ecast a t) rho.
Proof.
  intros.
  unfold tc_expr, typecheck_expr; fold (typecheck_expr(CS := CS)); fold (typecheck_expr(CS := CS')).
  unfold isCastResultType; tc_expr_cenv_sub_tac.
  repeat match goal with |- denote_tc_assert match ?A with _ => _ end _ ⊢ _ =>
    destruct A eqn: ?Hcase
  end; tc_expr_cenv_sub_tac; rewrite ?denote_tc_assert_iszero';
    try apply (denote_tc_assert_cenv_sub CSUB).
  all: simple_if_tac; rewrite ?denote_tc_assert_iszero'; apply (denote_tc_assert_cenv_sub CSUB).
Qed.

Lemma tc_expr_cenv_sub_field:
 forall
 (a : expr)
  (tc_lvalue_cenv_sub : forall  (rho : environ)
                       (Delta : tycontext),
                     @tc_lvalue CS Delta a rho ⊢
                     @tc_lvalue CS' Delta a rho)
 (i : ident)
 (t : type) 
 (rho : environ)
 (Delta : tycontext)
 (IHa : @tc_expr CS Delta a rho ⊢ @tc_expr CS' Delta a rho),
 @tc_expr CS Delta (Efield a i t) rho ⊢
 @tc_expr CS' Delta (Efield a i t) rho.
Proof.
  intros.
  unfold tc_expr, typecheck_expr; fold (typecheck_lvalue(CS := CS)); fold (typecheck_lvalue(CS := CS')).
  destruct (access_mode t); tc_expr_cenv_sub_tac.
  destruct (typeof a); tc_expr_cenv_sub_tac.
   *
    destruct ((@cenv_cs CS) !! i0) eqn:?; try iIntros "[]".
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]]|] eqn:?H; try iIntros "[]".
    eapply (field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H; try eassumption.
    rewrite H; auto.
    intros.
    assert (H2' := CSUB id); hnf in H2'; rewrite H0 in H2'; auto.
    apply cenv_consistent.
   *
    destruct ((@cenv_cs CS) !! i0) eqn:?; try iIntros "[]".
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[[] [|]]|] eqn:?H; try iIntros "[]".
    rewrite <- (union_field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H; try eassumption.
    rewrite H. auto.
   intros. specialize (CSUB id).  hnf in CSUB.  unfold lookup, composite_env_lookup, ptree_lookup in CSUB. rewrite -> H0 in CSUB; auto.
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
 (IHa : denote_tc_assert(CS := CS) (typecheck_lvalue(CS := CS) Delta a) rho ⊢
        denote_tc_assert(CS := CS') (typecheck_lvalue(CS := CS') Delta a) rho),
 denote_tc_assert(CS := CS) (typecheck_lvalue(CS := CS) Delta (Efield a i t)) rho ⊢
 denote_tc_assert(CS := CS') (typecheck_lvalue(CS := CS') Delta (Efield a i t)) rho.
Proof.
  intros.
  unfold typecheck_lvalue; fold (typecheck_lvalue(CS := CS)); fold (typecheck_lvalue(CS := CS')).
  tc_expr_cenv_sub_tac.
  destruct (typeof a); tc_expr_cenv_sub_tac.
   *
    destruct ((@cenv_cs CS) !! i0) eqn:?; try iIntros "[]".
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]]|] eqn:?H; try iIntros "[]".
    eapply (field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H; try eassumption.
    rewrite H; auto.
    intros.
    assert (H2' := CSUB id); hnf in H2'; rewrite H0 in H2'; auto.
    apply cenv_consistent.
   *
    destruct ((@cenv_cs CS) !! i0) eqn:?; try iIntros "[]".
    assert (H2 := CSUB i0); hnf in H2; rewrite Heqo in H2; rewrite H2.
    destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[[] [|]]|] eqn:?H; try iIntros "[]".
    rewrite <- (union_field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H; try eassumption.
    rewrite H. auto.
   intros. specialize (CSUB id).  hnf in CSUB.  unfold lookup, composite_env_lookup, ptree_lookup in CSUB. rewrite -> H0 in CSUB; auto.
   apply co_consistent_complete. 
   apply (cenv_consistent i0); auto.
Qed.

Lemma tc_expr_cenv_sub a rho Delta: tc_expr(CS := CS) Delta a rho ⊢
                            tc_expr(CS := CS') Delta a rho
     with tc_lvalue_cenv_sub a rho Delta: tc_lvalue(CS := CS) Delta a rho ⊢
                            tc_lvalue(CS := CS') Delta a rho.
Proof.
- clear tc_expr_cenv_sub.
  unfold tc_expr.
  induction a; try apply (denote_tc_assert_cenv_sub CSUB);
    try solve [unfold typecheck_expr; tc_expr_cenv_sub_tac; apply (denote_tc_assert_cenv_sub CSUB)].
  + unfold typecheck_expr; fold (typecheck_expr(CS := CS)); fold (typecheck_expr(CS := CS')).
    destruct (access_mode t); tc_expr_cenv_sub_tac; apply (denote_tc_assert_cenv_sub CSUB).
  + apply tc_expr_cenv_sub_unop, IHa.
  + apply (tc_expr_cenv_sub_binop _ _ _ _ _ _ IHa1 IHa2).
  + apply tc_expr_cenv_sub_cast, IHa.
  + apply tc_expr_cenv_sub_field, IHa. apply tc_lvalue_cenv_sub.
- clear tc_lvalue_cenv_sub.
  unfold tc_lvalue.
  induction a; try apply (denote_tc_assert_cenv_sub CSUB).
  + (* Ederef *)
   unfold typecheck_lvalue;
   fold (typecheck_expr(CS := CS)); fold (typecheck_expr(CS := CS')).
   tc_expr_cenv_sub_tac; apply (denote_tc_assert_cenv_sub CSUB).
  + apply tc_lvalue_cenv_sub_field, IHa.
Time Qed. (* FIXME: This is unreasonably slow. *)

  Lemma tc_exprlist_cenv_sub Delta rho:
    forall types bl, @tc_exprlist CS Delta types bl rho ⊢
                     @tc_exprlist CS' Delta types bl rho.
  Proof.
    induction types; simpl; intros.
    + destruct bl; simpl in *; trivial.
    + destruct bl. trivial.
      unfold tc_exprlist.
      unfold typecheck_exprlist; 
        fold (typecheck_exprlist(CS := CS));
        fold (typecheck_exprlist(CS := CS')).
      rewrite !(denote_tc_assert_andp _ (typecheck_exprlist _ _ _)).
      unfold tc_exprlist in IHtypes; fold (tc_expr(CS := CS) Delta (Ecast e a) rho);
        fold (tc_expr(CS := CS') Delta (Ecast e a) rho). by rewrite tc_expr_cenv_sub IHtypes.
   Qed.

End CENV_SUB.

End mpred.
