Require Import VST.floyd.base2.

Lemma tc_environ_init: forall Delta id rho,
                         tc_environ (initialized id Delta) rho ->
                         tc_environ Delta rho.
Proof.
intros.
unfold tc_environ in *. destruct Delta.
unfold initialized in *. simpl in *. unfold temp_types in *.
unfold var_types in *. unfold ret_type in *. simpl in *.
remember (tyc_temps ! id). destruct o; auto.
destruct p. unfold typecheck_environ in *. intuition.
clear - H0 Heqo. unfold typecheck_temp_environ in *.
intros. destruct (eq_dec id id0). subst.
specialize (H0 id0 true t). spec H0.
unfold temp_types in *. simpl in *. rewrite PTree.gss. auto.
destruct H0. exists x. intuition. unfold temp_types in *.
simpl in H. rewrite H in *. inv Heqo. auto.
apply H0.
unfold temp_types in *. simpl in *.
rewrite PTree.gso. auto. auto.
Qed.
Opaque tc_andp.

Lemma temp_types_init_same:
 forall Delta id t b, (temp_types Delta)!id = Some (t,b) ->
                         (temp_types (initialized id Delta)) ! id = Some (t,true).
Proof.
intros.
destruct Delta; simpl in *.
unfold initialized; simpl. rewrite H.
unfold temp_types; simpl.
rewrite PTree.gss; auto.
Qed.

Lemma tc_expr_init:
  forall {CS: compspecs} i Delta rho e,
    tc_expr Delta e rho |-- tc_expr (initialized i Delta) e rho
with tc_lvalue_init:
  forall {CS: compspecs} i Delta rho e,
    tc_lvalue Delta e rho |-- tc_lvalue (initialized i Delta) e rho.
Proof.
  clear tc_expr_init; induction e; intros; auto;
  unfold tc_expr in *; simpl in *;
   try solve [destruct t as [ | [ | | | ] | [ | ] | [ | ] | | | | | ]; auto].
  + destruct (access_mode t) eqn:?; auto.
    unfold get_var_type in *.
    rewrite set_temp_ve.
    destruct ((var_types Delta) ! i0); auto.
    rewrite set_temp_ge.
    destruct ((glob_types Delta) ! i0); apply derives_refl.
  + (* destruct (negb (type_is_volatile t)); auto.*)
    destruct ( (temp_types Delta) ! i0) eqn:?; [ | apply @FF_left].
    destruct p.
    destruct (eq_dec i i0). subst.
    - apply temp_types_init_same in Heqo. rewrite Heqo.
       simpl. destruct (is_neutral_cast t0 t || same_base_type t0 t)%bool; auto.
      destruct b; auto. apply @TT_right.
    - rewrite <- initialized_ne by auto.  rewrite Heqo.
       simpl. destruct (is_neutral_cast t0 t || same_base_type t0 t)%bool; auto.
  + destruct (access_mode t) eqn:?H; try inversion H;
      try apply @FF_left.
    rewrite !denote_tc_assert_andp, !denote_tc_assert_bool; simpl.
    repeat apply @andp_derives; auto.
  + rewrite !denote_tc_assert_andp, !denote_tc_assert_bool; simpl.
    repeat apply @andp_derives; auto.
     apply tc_lvalue_init; auto.
  + rewrite !denote_tc_assert_andp; simpl.
    repeat apply @andp_derives; auto.
  + rewrite !denote_tc_assert_andp; simpl.
    repeat apply @andp_derives; auto.
  + rewrite !denote_tc_assert_andp; simpl.
    apply andp_derives; auto.
  + destruct (access_mode t); auto.
    rewrite !denote_tc_assert_andp; simpl.
    apply andp_derives; auto.
    apply tc_lvalue_init; auto.
  + clear tc_lvalue_init.
    unfold tc_lvalue; induction e; simpl; auto.
    unfold get_var_type.
    rewrite !set_temp_ve.
    destruct ((var_types Delta) ! i0);
      rewrite ?denote_tc_assert_bool; auto.
    rewrite set_temp_ge.
    destruct ((glob_types Delta) ! i0);
      rewrite ?denote_tc_assert_bool; apply derives_refl.
     rewrite !denote_tc_assert_andp; simpl.
      rewrite ?denote_tc_assert_bool; auto.
    repeat apply andp_derives; auto.
    apply tc_expr_init; auto.
     simpl.
     rewrite !denote_tc_assert_andp; simpl.
    repeat apply andp_derives; auto.
Qed.
