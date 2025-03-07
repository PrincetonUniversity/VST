Require Export VST.veric.Clight_base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.expr_lemmas.

Require Import VST.veric.seplog. (*For definition of tycontext*)
Require Import VST.veric.lifting_expr.
Require Import VST.veric.env_pred.
Require Import VST.veric.lifting.
Import LiftNotation.

Section mpred.

Context `{!heapGS Σ}.

Definition tc_expr {CS: compspecs} (Delta: tycontext) (e: expr) : assert :=
  assert_of (denote_tc_assert (typecheck_expr Delta e)).

Definition tc_exprlist {CS: compspecs} (Delta: tycontext) (t : list type) (e: list expr) : assert :=
  assert_of (denote_tc_assert (typecheck_exprlist Delta t e)).

Definition tc_lvalue {CS: compspecs} (Delta: tycontext) (e: expr) : assert :=
  assert_of (denote_tc_assert (typecheck_lvalue Delta e)).

Definition tc_temp_id {CS: compspecs} (id : positive) (ty : type)
  (Delta : tycontext) (e : expr) : assert :=
  assert_of (denote_tc_assert (typecheck_temp_id id ty Delta e)).

Definition tc_expropt {CS: compspecs} Delta (e: option expr) (t: type) : assert :=
  match e with None => ⌜t=Ctypes.Tvoid⌝
                     | Some e' => (tc_expr Delta (Ecast e' t))
  end.

Definition tc_temp_id_load id tfrom Delta v : assert :=
local (fun rho => exists tto, (temp_types Delta) !! id = Some tto
                      /\ tc_val tto (eval_cast tfrom tto (v rho))).

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

Global Instance tc_expr_absorbing : forall {CS: compspecs} Delta a, Absorbing (tc_expr Delta a).
Proof.
  intros; apply monPred_absorbing, _.
Qed.

Global Instance tc_exprlist_absorbing : forall {CS: compspecs} Delta t a, Absorbing (tc_exprlist Delta t a).
Proof.
  intros; apply monPred_absorbing, _.
Qed.

Global Instance tc_lvalue_absorbing : forall {CS: compspecs} Delta a, Absorbing (tc_lvalue Delta a).
Proof.
  intros; apply monPred_absorbing, _.
Qed.

Global Instance tc_expropt_absorbing: forall {CS: compspecs} Delta e t, Absorbing (tc_expropt Delta e t).
Proof.
  intros. unfold tc_expropt.
  destruct e; apply _.
Qed.

Global Instance tc_temp_id_absorbing : forall {CS: compspecs} id ty Delta a, Absorbing (tc_temp_id id ty Delta a).
Proof.
  intros; apply monPred_absorbing, _.
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
 (rho : _)
 (Delta : tycontext)
 (IHa : @tc_expr CS Delta a rho ⊢ @tc_expr CS' Delta a rho),
 @tc_expr CS Delta (Eunop u a t) rho ⊢
 @tc_expr CS' Delta (Eunop u a t) rho.
Proof.
  intros.
  unfold tc_expr in *; simpl.
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
  fold (typecheck_expr(CS := CS')); simpl.
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
  unfold tc_expr, typecheck_expr; fold (typecheck_expr(CS := CS)); fold (typecheck_expr(CS := CS')); simpl.
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
 (rho : environ)
 (Delta : tycontext)
 (tc_lvalue_cenv_sub : @tc_lvalue CS Delta a rho ⊢ @tc_lvalue CS' Delta a rho)
 (i : ident)
 (t : type) 
 (IHa : @tc_expr CS Delta a rho ⊢ @tc_expr CS' Delta a rho),
 @tc_expr CS Delta (Efield a i t) rho ⊢
 @tc_expr CS' Delta (Efield a i t) rho.
Proof.
  intros.
  unfold tc_expr, typecheck_expr; fold (typecheck_lvalue(CS := CS)); fold (typecheck_lvalue(CS := CS')); simpl.
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
   intros. specialize (CSUB id).  hnf in CSUB. rewrite -> H0 in CSUB; auto.
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
  unfold typecheck_lvalue; fold (typecheck_lvalue(CS := CS)); fold (typecheck_lvalue(CS := CS')); simpl.
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
   intros. specialize (CSUB id).  hnf in CSUB. rewrite -> H0 in CSUB; auto.
   apply co_consistent_complete. 
   apply (cenv_consistent i0); auto.
Qed.

Arguments typecheck_expr {Σ heapGS0 CS} Delta !e /.

Lemma tc_expr_lvalue_cenv_sub a rho Delta :
  (tc_expr(CS := CS) Delta a rho ⊢ tc_expr(CS := CS') Delta a rho) /\
  (tc_lvalue(CS := CS) Delta a rho ⊢ tc_lvalue(CS := CS') Delta a rho).
Proof.
  induction a; intros; split; try apply (denote_tc_assert_cenv_sub CSUB).
  + rewrite /tc_expr /=.
    destruct (access_mode t); try done.
    rewrite !denote_tc_assert_andp; apply bi.and_mono; first apply bi.and_mono; first apply IHa; apply (denote_tc_assert_cenv_sub CSUB).
  + (* Ederef *)
    rewrite /tc_lvalue /=.
    rewrite !denote_tc_assert_andp; apply bi.and_mono; first apply bi.and_mono; first apply IHa; apply (denote_tc_assert_cenv_sub CSUB).
  + rewrite /tc_expr /=.
    rewrite !denote_tc_assert_andp; apply bi.and_mono; first apply IHa.
    rewrite /tc_bool; simple_if_tac; done.
  + apply tc_expr_cenv_sub_unop, IHa.
  + apply (tc_expr_cenv_sub_binop _ _ _ _ _ _ (proj1 IHa1) (proj1 IHa2)).
  + apply tc_expr_cenv_sub_cast, IHa.
  + apply tc_expr_cenv_sub_field, IHa. apply IHa.
  + apply tc_lvalue_cenv_sub_field, IHa.
  + rewrite /tc_expr /=.
    rewrite !denote_tc_assert_andp; apply bi.and_mono; first apply tc_complete_type_cenv_sub.
    rewrite /tc_bool; simple_if_tac; done.
  + rewrite /tc_expr /=.
    rewrite !denote_tc_assert_andp; apply bi.and_mono; first apply tc_complete_type_cenv_sub.
    rewrite /tc_bool; simple_if_tac; done.
Qed.

Lemma tc_expr_cenv_sub a rho Delta : tc_expr(CS := CS) Delta a rho ⊢ tc_expr(CS := CS') Delta a rho.
Proof. apply tc_expr_lvalue_cenv_sub. Qed.

(*Lemma tc_expr_cenv_sub' a Delta : tc_expr(CS := CS) Delta a ⊢ tc_expr(CS := CS') Delta a.
Proof. split => rho; apply tc_expr_cenv_sub. Qed.*)

Lemma tc_lvalue_cenv_sub a rho Delta : tc_lvalue(CS := CS) Delta a rho ⊢ tc_lvalue(CS := CS') Delta a rho.
Proof. apply tc_expr_lvalue_cenv_sub. Qed.

(*Lemma tc_lvalue_cenv_sub' a Delta : tc_lvalue(CS := CS) Delta a ⊢ tc_lvalue(CS := CS') Delta a.
Proof. split => rho; apply tc_lvalue_cenv_sub. Qed.*)

Lemma tc_exprlist_cenv_sub Delta rho:
  forall types bl, @tc_exprlist CS Delta types bl rho ⊢
                   @tc_exprlist CS' Delta types bl rho.
Proof.
  induction types; intros.
  + destruct bl; simpl in *; trivial.
  + destruct bl. trivial.
    unfold tc_exprlist.
    unfold typecheck_exprlist; 
      fold (typecheck_exprlist(CS := CS));
      fold (typecheck_exprlist(CS := CS')).
    setoid_rewrite denote_tc_assert_andp.
    unfold tc_exprlist in IHtypes; fold (tc_expr(CS := CS) Delta (Ecast e a) rho);
      fold (tc_expr(CS := CS') Delta (Ecast e a) rho). setoid_rewrite tc_expr_cenv_sub. setoid_rewrite IHtypes; done.
Qed.

End CENV_SUB.

Context `{!envGS Σ}.

(* use this throughout? *)
Definition assert_of' (P : nat -> mpred) := ∀ n, stack_level n -∗ ⎡P n⎤.

Lemma assert_of_eq : forall P, mpred.assert_of P ⊣⊢ assert_of' P.
Proof.
  split => n.
  rewrite /assert_of' /stack_level.
  monPred.unseal.
  setoid_rewrite monPred_at_affinely; simpl.
  iSplit.
  - iIntros "H" (?? [=] [=]); subst; done.
  - iIntros "H"; iApply "H"; done.
Qed.

#[global] Instance assert_of'_mono : Proper (pointwise_relation _ bi_entails ==> bi_entails) assert_of'.
Proof. solve_proper. Qed.

#[global] Instance assert_of'_proper : Proper (pointwise_relation _ base.equiv ==> base.equiv) assert_of'.
Proof. solve_proper. Qed.

(* We can always use tc_expr+eval_expr to satisfy wp_expr. However, wp_expr takes a
   small-footprint approach to the environment, while tc_expr and eval_expr freely
   call on the full environment rho. So to do this, we need to first fix the entire
   environment. *)
Definition curr_env (ge : genv) (rho : environ) : mpred.assert := <affine> ⌜∀ i, ge_of rho !! i = Genv.find_symbol ge i⌝ ∗ ([∗ map] i↦b ∈ ge_of rho, ⎡gvar i b⎤) ∗
  assert_of' (λ n, ∃ q0, <affine> ⌜q0 < 1⌝%Qp ∗ stack_frag n q0 1%Qp (ve_of rho) (te_of rho)).

Definition genv_sub (ge1 ge2 : genv) := forall i v, Genv.find_symbol ge1 i = Some v -> Genv.find_symbol ge2 i = Some v.

Lemma curr_env_e : forall ρ ge0 rho, ⊢ ⎡env_auth ρ⎤ -∗ curr_env ge0 rho -∗
  □ ∀ ge ve te, env_match ρ ge ve te -∗ ⌜genv_sub ge0 ge /\ env_matches rho ge0 ve te⌝.
Proof.
  split => n; rewrite /curr_env; monPred.unseal.
  iIntros "_ %% Hρ %% H".
  rewrite monPred_at_embed !monPred_at_sep monPred_at_affinely monPred_at_intuitionistically monPred_at_big_sepM; monPred.unseal.
  iDestruct "H" as "(%Hge0 & Hge & Hs)".
  rewrite -assert_of_eq /=.
  iDestruct "Hs" as (??) "Hs"; iDestruct (stack_frag_e_1 with "[$Hρ $Hs]") as %(Hve & Hte).
  iAssert ⌜ge_of rho ⊆ ge_of (env_to_environ ρ n)⌝ as %Hsub.
  { iIntros (i).
    destruct (ge_of rho !! i)%stdpp eqn: Hi; rewrite Hi /=.
    - rewrite big_sepM_lookup //.
      iDestruct (gvar_e with "[$Hρ $Hge]") as %Hi'.
      by rewrite ge_of_env Hi'.
    - by destruct (ge_of (env_to_environ ρ n) !! i)%stdpp eqn: Hi'; rewrite Hi'. }
  iPureIntro; simpl; intros ????? Hmatch.
  unfold sqsubseteq in *; subst.
  destruct Hmatch as (Hge & ? & ?).
  split.
  - intros ?? Hi.
    rewrite Hge; rewrite -Hge0 in Hi.
    by eapply lookup_weaken.
  - split3; rewrite ?Hve ?Hte; done.
Qed.

Lemma curr_env_set_temp : forall Delta ge rho i t
  (Hi : temp_types Delta !! i = Some t) (Htc : typecheck_environ Delta rho),
  curr_env ge rho ⊢ (∃ v, temp i v) ∗ (∀ v, temp i v -∗ curr_env ge (env_set rho i v)).
Proof.
  intros.
  destruct Htc as (Htc & _).
  apply Htc in Hi as (v0 & ? & ?).
  iIntros "(% & ? & Hs)".
  iDestruct stack_level_intro as (?) "#l".
  iDestruct ("Hs" with "[$]") as (q0 Hq0) "Hs".
  replace (ve_of rho) with (ve_of rho ∪ ∅) at 1 by (rewrite right_id //).
  replace (te_of rho) with (delete i (te_of rho) ∪ {[i := v0]}) at 1.
  assert (exists q1, 1 = q1 + q0)%Qp as (q1 & Heq).
  { apply Qp.lt_sum in Hq0 as (? & Hq0); rewrite Qp.add_comm in Hq0; eauto. }
  rewrite Heq stack_frag_split.
  iDestruct "Hs" as "(Hs & Hi)".
  iSplitL "Hi".
  { iExists v0. iApply (stack_level_elim with "[$]"). iFrame. }
  iIntros (?) "Hi".
  iPoseProof (stack_level_embed with "[$] Hi") as "Hi"; simpl.
  iDestruct "Hi" as (?) "Hi".
  iCombine "Hs Hi" as "Hs"; rewrite stack_frag_join.
  iDestruct "Hs" as ((<- & _ & _)) "Hs".
  rewrite right_id -insert_union_singleton_r.
  rewrite insert_delete_insert.
  iSplit; first done; iFrame.
  iIntros (?) "#l'"; iDestruct (stack_level_eq with "l l'") as %->.
  rewrite -Heq /=; by iFrame.
  * apply lookup_delete.
  * apply map_disjoint_empty_r.
  * apply map_disjoint_singleton_r_2, lookup_delete.
  * rewrite -insert_union_singleton_r; last apply lookup_delete.
    by apply insert_delete.
Qed.

Lemma wp_tc_expr : forall {CS : compspecs} E f Delta e P (ge : genv) rho,
  cenv_sub cenv_cs ge ->
  typecheck_environ Delta rho ->
  ⊢ curr_env ge rho -∗
    ▷ ⎡tc_expr Delta e rho⎤ ∧
    (curr_env ge rho -∗ ⌜tc_val (typeof e) (eval_expr e rho)⌝ → P (eval_expr e rho)) -∗
  wp_expr ge E f e P.
Proof.
  intros; rewrite /wp_expr.
  iIntros "Hrho H !>" (??) "Hm Hρ".
  iDestruct (curr_env_e with "Hρ Hrho") as "#Hsub".
  iCombine "H Hρ" as "TC".
  iDestruct (add_and _ (▷ ⌜tc_val (typeof e) (eval_expr e rho)⌝) with "TC") as "(TC & >%)".
  { iIntros "((H & _) & ?) !>". rewrite -embed_pure. by iApply typecheck_expr_sound. }
  iCombine "TC Hm" as "H"; iDestruct (add_and _ (▷ ⌜∀ ge ve te,
    env_matches rho ge ve te → cenv_sub cenv_cs ge
      → match_venv (make_env ve) (fn_vars f)
        → Clight.eval_expr ge ve te m e (eval_expr e rho)⌝) with "H") as "(((H & ?) & ?) & >%He)".
  { iIntros "(((H & _) & ?) & Hm) !>" (??????).
    rewrite -embed_pure. iApply eval_expr_relate; eauto; iFrame. }
  rewrite bi.and_elim_r.
  iSpecialize ("H" with "Hrho [//]").
  iIntros "!>"; iExists (eval_expr e rho); iFrame.
  iIntros "!>" (??) "Hmatch".
  iDestruct ("Hsub" with "Hmatch") as %(? & Hmatch).
  iPureIntro; auto.
Qed.

Lemma wp_tc_lvalue : forall {CS : compspecs} E f Delta e P (ge : genv) rho,
  cenv_sub cenv_cs ge ->
  typecheck_environ Delta rho ->
  ⊢ curr_env ge rho -∗
    ▷ ⎡tc_lvalue Delta e rho⎤ ∧
    (curr_env ge rho -∗ ∀ b o, ⌜eval_lvalue e rho = Vptr b (Ptrofs.repr o)⌝ → P (b, o)) -∗
  wp_lvalue ge E f e P.
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "Hrho H !>" (??) "Hm Hρ".
  iDestruct (curr_env_e with "Hρ Hrho") as "#Hsub".
  iCombine "H Hρ" as "TC".
  iDestruct (add_and _ (▷ ⌜isptr (eval_lvalue e rho)⌝) with "TC") as "(TC & >%)".
  { iIntros "((H & _) & ?) !>". edestruct typecheck_both_sound as (_ & Htc); first done.
    rewrite -embed_pure. by iApply (Htc (Tstruct 1%positive noattr)). }
  iCombine "TC Hm" as "H"; iDestruct (add_and _ (▷ ⌜∀ ge ve te,
    env_matches rho ge ve te → cenv_sub cenv_cs ge
      → match_venv (make_env ve) (fn_vars f)
        → ∃ b o, Clight.eval_lvalue ge ve te m e b o Full ∧ eval_lvalue e rho = Vptr b o⌝) with "H") as "(((H & ?) & ?) & >%He)".
  { iIntros "(((H & _) & ?) & Hm) !>" (??????).
    rewrite -embed_pure. iApply eval_lvalue_relate; eauto; iFrame. }
  rewrite bi.and_elim_r.
  destruct (eval_lvalue e rho) eqn: Heval; try contradiction.
  iIntros "!>"; iExists _, _; iFrame.
  iSplitL "".
  - iIntros "!>" (??) "Hmatch %".
    iDestruct ("Hsub" with "Hmatch") as %(? & Hmatch).
    iPureIntro; simpl.
    edestruct He as (? & ? & ? & [=]); by subst.
  - iApply ("H" with "Hrho").
    by rewrite Ptrofs.repr_unsigned.
Qed.

Lemma typecheck_exprlist_sound : forall {CS : compspecs} Delta tys es rho,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_exprlist Delta tys es) rho ⊢ ⌜tc_vals tys (eval_exprlist tys es rho)⌝.
Proof.
  induction tys; simpl; intros.
  - destruct es; simpl; auto.
  - destruct es; simpl; auto.
    rewrite denote_tc_assert_andp IHtys //.
    iIntros "(? & %)".
    iSplit; last done.
    by iApply (typecheck_expr_sound _ _ (Ecast e a)).
Qed.

Lemma eval_exprlist_relate : forall {CS : compspecs} Delta (ge : genv) te ve rho tys es m,
  cenv_sub cenv_cs ge -> env_matches rho ge ve te -> typecheck_environ Delta rho ->
  juicy_mem.mem_auth m ∗ denote_tc_assert (typecheck_exprlist Delta tys es) rho ⊢
  ⌜Clight.eval_exprlist ge ve te m es tys (eval_exprlist tys es rho)⌝.
Proof.
  induction tys; simpl; intros.
  - destruct es; simpl.
    + apply bi.pure_intro; constructor.
    + iIntros "(? & [])".
  - destruct es; simpl.
    { iIntros "(? & [])". }
    rewrite denote_tc_assert_andp.
    iIntros "(Hm & H)"; iDestruct (IHtys with "[$Hm H]") as %?; [done.. | by rewrite bi.and_elim_r |].
    rewrite bi.and_elim_l.
    iDestruct (eval_expr_relate _ _ _ _ _ (Ecast e a) with "[$Hm $H]") as %He; [done..|].
    iPureIntro.
    inv He.
    econstructor; eauto.
    { inv H3. }
Qed.

End mpred.

Lemma wp_tc_exprlist : forall `{!VSTGS OK_ty Σ} {CS : compspecs} E f Delta tys es P (ge : genv) rho,
  cenv_sub cenv_cs ge ->
  typecheck_environ Delta rho ->
  ⊢ curr_env ge rho -∗
    ▷ ⎡tc_exprlist Delta tys es rho⎤ ∧
    (curr_env ge rho -∗ ⌜tc_vals tys (eval_exprlist tys es rho)⌝ → P (eval_exprlist tys es rho)) -∗
  wp_exprs ge E f es tys P.
Proof.
  intros; rewrite /wp_exprs.
  iIntros "Hrho H" (??) "Hm Hρ".
  iDestruct (curr_env_e with "Hρ Hrho") as "#Hsub".
  iCombine "H Hρ" as "TC".
  iDestruct (add_and _ (▷ ⌜tc_vals tys (eval_exprlist tys es rho)⌝) with "TC") as "(TC & >%)".
  { iIntros "((H & _) & ?) !>". rewrite -embed_pure. by iApply typecheck_exprlist_sound. }
  iCombine "TC Hm" as "H"; iDestruct (add_and _ (▷ ⌜∀ ge ve te,
    env_matches rho ge ve te → cenv_sub cenv_cs ge
      → match_venv (make_env ve) (fn_vars f)
        → Clight.eval_exprlist ge ve te m es tys (eval_exprlist tys es rho)⌝) with "H") as "(((H & ?) & ?) & >%Hes)".
  { iIntros "(((H & _) & ?) & Hm) !>" (??????).
    rewrite -embed_pure. iApply eval_exprlist_relate; eauto; iFrame. }
  rewrite bi.and_elim_r.
  iSpecialize ("H" with "Hrho [//]").
  iIntros "!>"; iExists (eval_exprlist tys es rho); iFrame.
  iIntros "!>" (??) "Hmatch".
  iDestruct ("Hsub" with "Hmatch") as %(? & Hmatch).
  iPureIntro; auto.
Qed.
