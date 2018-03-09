Require Import VST.floyd.base.

Local Open Scope logic.

Lemma denote_tc_assert_andp:
  forall {CS: compspecs} (a b : tc_assert) (rho : environ),
  denote_tc_assert (tc_andp a b) rho =
  andp (denote_tc_assert a rho)
    (denote_tc_assert b rho).
Proof.
intros.
apply expr2.denote_tc_assert_andp.
Qed.

Lemma denote_tc_assert_orp:
  forall {CS: compspecs} (a b : tc_assert) (rho : environ),
  denote_tc_assert (tc_orp a b) rho =
  orp (denote_tc_assert a rho)
    (denote_tc_assert b rho).
Proof.
intros.
apply binop_lemmas2.denote_tc_assert_orp.
Qed.

Lemma denote_tc_assert_bool:
  forall {CS: compspecs} b c rho, denote_tc_assert (tc_bool b c) rho =
               prop (b=true).
Proof.
intros.
unfold tc_bool.
destruct b.
apply pred_ext; normalize; apply derives_refl.
apply pred_ext.  apply @FF_left.
normalize. inv H.
Qed.

Lemma neutral_isCastResultType:
  forall {cs: compspecs}  P t t' v rho,
   is_neutral_cast t' t = true ->
   P |-- denote_tc_assert (isCastResultType t' t v) rho.
Proof.
intros.
  unfold isCastResultType;
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |], t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
try solve [
     inv H; simpl; try apply @TT_right;
           simpl; if_tac; apply @TT_right].
*
unfold classify_cast.
destruct Archi.ptr64 eqn:Hp.
apply @TT_right.
rewrite if_true by auto.
destruct (eqb_type _ _); apply @TT_right.
*
unfold classify_cast.
destruct Archi.ptr64 eqn:Hp.
apply @TT_right.
rewrite if_true by auto.
destruct (eqb_type _ _); apply @TT_right.
*
unfold classify_cast.
unfold is_neutral_cast in H.
rewrite orb_true_iff in H.
destruct H.
rewrite (eqb_type_true _ _ H).
rewrite !eqb_reflx. rewrite eqb_type_refl. apply @TT_right.
rewrite andb_true_iff in H.
destruct H.
rewrite negb_true_iff in H, H0. rewrite H,H0.
rewrite eqb_reflx.
if_tac; try apply @TT_right.
unfold is_pointer_type.
rewrite H,H0.
apply @TT_right.
Qed.

Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e.
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.

Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e.
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : norm.

Definition tc_LR_strong {cs: compspecs} Delta e lr :=
  match lr with
  | LLLL => tc_lvalue Delta e
  | RRRR => tc_expr Delta e
  end.

Definition tc_LR {cs: compspecs} Delta e lr :=
  match e with
  | Ederef e0 t =>
     match lr with
     | LLLL => denote_tc_assert
                 (tc_andp
                   (typecheck_expr Delta e0)
                   (tc_bool (is_pointer_type (typeof e0))(op_result_type e)))
     | RRRR => denote_tc_assert
                match access_mode t with
                | By_reference =>
                   (tc_andp
                      (typecheck_expr Delta e0)
                      (tc_bool (is_pointer_type (typeof e0))(op_result_type e)))
                | _ => tc_FF (deref_byvalue t)
                end
    end
  | _ => tc_LR_strong Delta e lr
  end.

Definition eval_LR {cs: compspecs} e lr :=
  match lr with
  | LLLL => eval_lvalue e
  | RRRR => eval_expr e
  end.

Lemma tc_LR_tc_LR_strong: forall {cs: compspecs} Delta e lr rho,
  tc_LR Delta e lr rho && !! isptr (eval_LR e lr rho) |-- tc_LR_strong Delta e lr rho.
Proof.
  intros.
  unfold tc_LR, tc_LR_strong.
  destruct e; try solve [apply andp_left1; auto].
  unfold tc_lvalue, tc_expr.
  destruct lr; simpl.
  + rewrite !denote_tc_assert_andp.
    simpl.
    unfold denote_tc_isptr.
    unfold_lift.
    auto.
  + destruct (access_mode t); try solve [apply andp_left1; auto].
    rewrite !denote_tc_assert_andp.
    simpl.
    unfold denote_tc_isptr.
    unfold_lift.
    auto.
Qed.

