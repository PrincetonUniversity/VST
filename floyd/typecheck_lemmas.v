Require Import floyd.base.

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
apply pred_ext; normalize.
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
     inv H; simpl; try apply @TT_right;
    simpl; if_tac; apply @TT_right.
Qed.

Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e.
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.

Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e.
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : norm.

