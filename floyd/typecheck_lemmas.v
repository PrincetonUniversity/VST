
Require Import VST.floyd.base.

Local Open Scope logic.

Lemma denote_tc_assert_andp:
  forall {CS: compspecs} (a b : tc_assert),
  denote_tc_assert (tc_andp a b) = andp (denote_tc_assert a) (denote_tc_assert b).
Proof.
  intros.
  extensionality rho.
  simpl.
  apply expr2.denote_tc_assert_andp.
Qed.

Lemma denote_tc_assert_orp:
  forall {CS: compspecs} (a b : tc_assert),
  denote_tc_assert (tc_orp a b) = orp (denote_tc_assert a) (denote_tc_assert b).
Proof.
  intros.
  extensionality rho.
  simpl.
  apply binop_lemmas2.denote_tc_assert_orp.
Qed.

Lemma denote_tc_assert_bool:
  forall {CS: compspecs} b c, denote_tc_assert (tc_bool b c) =
               prop (b=true).
Proof.
  intros.
  extensionality rho; simpl.
  unfold tc_bool.
  destruct b.
  apply pred_ext; normalize; apply derives_refl.
  apply pred_ext.  apply @FF_left.
  normalize. inv H.
Qed.

Lemma neutral_isCastResultType_64:
 Archi.ptr64 = true ->
  forall {cs: compspecs}  P t t' v rho,
   is_neutral_cast t' t = true ->
   P |-- denote_tc_assert (isCastResultType t' t v) rho.
Proof.
intro Hp.
intros.
unfold isCastResultType, classify_cast; rewrite Hp.
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |], t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
try solve [
     inv H; simpl; try apply @TT_right;
           simpl; (destruct (eqb_tac _ _)); apply @TT_right].
*
try destruct (eqb_type _ _); apply @TT_right.
*
unfold is_neutral_cast in H.
destruct (eqb_type (Tpointer t a0) int_or_ptr_type) eqn:H0.
rewrite (eqb_type_true _ _ H0).
destruct (eqb_type (Tpointer t' a) int_or_ptr_type) eqn:H1.
rewrite (eqb_type_true _ _ H1).
apply @TT_right.
rewrite (eqb_type_true _ _ H0) in H.
rewrite H1 in H. inv H.
destruct (eqb_type (Tpointer t' a) int_or_ptr_type) eqn:H1.
rewrite (eqb_type_true _ _ H1) in H.
rewrite expr_lemmas4.eqb_type_sym in H.
rewrite H0 in H. inv H.
rewrite orb_true_iff in H.
unfold is_pointer_type.
rewrite H0,H1.
simpl.
simple_if_tac; apply @TT_right.
Qed.

Lemma neutral_isCastResultType_32:
 Archi.ptr64 = false ->
  forall {cs: compspecs}  P t t' v rho,
   is_neutral_cast t' t = true ->
   P |-- denote_tc_assert (isCastResultType t' t v) rho.
Proof.
intro Hp.
intros.
unfold isCastResultType, classify_cast; rewrite Hp.
  unfold isCastResultType;
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |], t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
try solve [
     inv H; simpl; try apply @TT_right;
           simpl; (destruct (eqb_tac _ _)); apply @TT_right].
*
simpl; simple_if_tac; apply @TT_right.
*
simpl; simple_if_tac; apply @TT_right.
*
unfold is_neutral_cast in H.
rewrite orb_true_iff in H.
destruct H.
rewrite (eqb_type_true _ _ H).
rewrite !eqb_reflx. rewrite eqb_type_refl. apply @TT_right.
rewrite andb_true_iff in H.
destruct H.
rewrite negb_true_iff in H, H0. rewrite H,H0.
rewrite eqb_reflx.
destruct (eqb_type (Tpointer t' a) (Tpointer t a0)); try apply @TT_right.
unfold is_pointer_type.
rewrite H,H0.
apply @TT_right.
Qed.


Lemma neutral_isCastResultType:
  forall {cs: compspecs}  P t t' v rho,
   is_neutral_cast t' t = true ->
   P |-- denote_tc_assert (isCastResultType t' t v) rho.
Proof.
destruct Archi.ptr64 eqn:Hp.
exact (@neutral_isCastResultType_64 Hp).
exact (@neutral_isCastResultType_32 Hp).
Qed.

Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e.
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.

Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e.
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : norm.

Definition typecheck_LR_strong {cs: compspecs} Delta e lr :=
  match lr with
  | LLLL => typecheck_lvalue Delta e
  | RRRR => typecheck_expr Delta e
  end.

Definition typecheck_LR {cs: compspecs} Delta e lr :=
  match e with
  | Ederef e0 t =>
     match lr with
     | LLLL => tc_andp
                 (typecheck_expr Delta e0)
                 (tc_bool (is_pointer_type (typeof e0))(op_result_type e))
     | RRRR => match access_mode t with
               | By_reference =>
                  tc_andp
                     (typecheck_expr Delta e0)
                     (tc_bool (is_pointer_type (typeof e0))(op_result_type e))
               | _ => tc_FF (deref_byvalue t)
               end
    end
  | _ => typecheck_LR_strong Delta e lr
  end.

Definition tc_LR_strong {cs: compspecs} Delta e lr := denote_tc_assert (typecheck_LR_strong Delta e lr).

Definition tc_LR {cs: compspecs} Delta e lr := denote_tc_assert (typecheck_LR Delta e lr).
(*
Definition tc_LR_strong {cs: compspecs} Delta e lr :=
  match lr with
  | LLLL => typecheck_lvalue Delta e
  | RRRR => typecheck_expr Delta e
  end.
  
Definition typecheck_LR {cs: compspecs} Delta e lr: tc_assert :=
  match e with
  | Ederef e0 t =>
     match lr with
     | LLLL => tc_andp
                 (typecheck_expr Delta e0)
                 (tc_bool (is_pointer_type (typeof e0))(op_result_type e))
     | RRRR => match access_mode t with
               | By_reference =>
                   tc_andp
                     (typecheck_expr Delta e0)
                     (tc_bool (is_pointer_type (typeof e0))(op_result_type e))
               | _ => tc_FF (deref_byvalue t)
               end
    end
  | _ => typecheck_LR_strong Delta e lr
  end.
*)
Definition eval_LR {cs: compspecs} e lr :=
  match lr with
  | LLLL => eval_lvalue e
  | RRRR => eval_expr e
  end.

Lemma tc_LR_tc_LR_strong: forall {cs: compspecs} Delta e lr rho,
  tc_LR Delta e lr rho && !! isptr (eval_LR e lr rho) |-- tc_LR_strong Delta e lr rho.
Proof.
  intros.
  unfold tc_LR, tc_LR_strong, typecheck_LR, typecheck_LR_strong.
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

