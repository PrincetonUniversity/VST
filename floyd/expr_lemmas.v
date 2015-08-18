Require Import floyd.base.

Lemma eval_field_initialized: 
  forall Delta i, eval_field (initialized i Delta) = eval_field Delta.
Proof.
intros.
extensionality t f p.
destruct t; simpl; auto; rewrite set_temp_ct; simpl; auto.
Qed.

Lemma eval_expr_initialized:
  forall Delta i e, eval_expr (initialized i Delta) e = eval_expr Delta e
 with eval_lvalue_initialized:
  forall Delta i e, eval_lvalue (initialized i Delta) e = eval_lvalue Delta e.
Proof.
clear eval_expr_initialized.
intros.
extensionality rho.
induction e; simpl; auto; unfold_lift; 
   rewrite ?composite_types_initialized; try rewrite IHe; simpl; auto.
rewrite eval_lvalue_initialized; simpl; auto.
unfold_lift; unfold sem_binary_operation', sem_add, sem_sub,
  sem_add_default, sem_sub_default; 
 try destruct b; rewrite IHe1,  IHe2; simpl; auto.
unfold sem_add_pi, sem_add_ip, sem_add_pl, sem_add_lp;
rewrite set_temp_ct;
simpl; auto.
unfold sem_sub_pi, sem_sub_pl, sem_sub_pp;
rewrite set_temp_ct;
simpl; auto.
rewrite eval_field_initialized, eval_lvalue_initialized; auto.
rewrite set_temp_ct; auto.
rewrite set_temp_ct; auto.

clear eval_lvalue_initialized.
intros.
extensionality rho.
induction e; simpl; auto; unfold_lift; 
   rewrite ?composite_types_initialized; try rewrite IHe; simpl; auto.
rewrite eval_expr_initialized; simpl; auto.
rewrite eval_field_initialized;  auto.
Qed.


Lemma eval_field_update_tycon:
  forall Delta i, eval_field (update_tycon Delta i) = eval_field Delta.
Proof.
intros.
extensionality t f p.
destruct t; simpl; auto;
rewrite composite_types_update_tycon;
simpl; auto.
Qed.

Lemma eval_expr_update_tycon:
  forall Delta i e, eval_expr (update_tycon Delta i) e = eval_expr Delta e
 with eval_lvalue_update_tycon:
  forall Delta i e, eval_lvalue (update_tycon Delta i) e = eval_lvalue Delta e.
Proof.
clear eval_expr_update_tycon.
intros.
extensionality rho.
induction e; simpl; auto; unfold_lift; 
   rewrite ?composite_types_update_tycon; try rewrite IHe; simpl; auto.
rewrite eval_lvalue_update_tycon; simpl; auto.
unfold_lift; unfold sem_binary_operation', sem_add, sem_sub,
  sem_add_default, sem_sub_default; 
 try destruct b; rewrite IHe1,  IHe2; simpl; auto.
unfold sem_add_pi, sem_add_ip, sem_add_pl, sem_add_lp;
rewrite composite_types_update_tycon;
simpl; auto.
unfold sem_sub_pi, sem_sub_pl, sem_sub_pp;
rewrite composite_types_update_tycon;
simpl; auto.
rewrite eval_field_update_tycon, eval_lvalue_update_tycon; auto.

clear eval_lvalue_update_tycon.
intros.
extensionality rho.
induction e; simpl; auto; unfold_lift; 
   rewrite ?composite_types_update_tycon; try rewrite IHe; simpl; auto.
rewrite eval_expr_update_tycon; simpl; auto.
rewrite eval_field_update_tycon;  auto.
Qed.

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


Lemma denote_tc_assert_initialized_tc_bool:
  forall i Delta b t,
   denote_tc_assert (initialized i Delta) (tc_bool b t) = 
   denote_tc_assert Delta (tc_bool b t).
Proof. intros. destruct b; simpl; auto. Qed.

Lemma denote_tc_assert_initialized_tc_nonzero:
  forall i Delta e, 
    denote_tc_assert (initialized i Delta) (tc_nonzero (initialized i Delta) e)
      = denote_tc_assert Delta (tc_nonzero Delta e).
Proof.
intros;     unfold tc_nonzero in *; simpl.
      rewrite ?eval_expr_initialized.
     destruct (eval_expr Delta e any_environ); simpl; 
     rewrite ?eval_expr_initialized; auto.
     if_tac; simpl; auto. unfold_lift. extensionality rho.
     rewrite ?eval_expr_initialized; auto.
Qed.

Lemma denote_tc_assert_initialized_tc_iszero:
  forall i Delta e, 
    denote_tc_assert (initialized i Delta) (tc_iszero (initialized i Delta) e)
      = denote_tc_assert Delta (tc_iszero Delta e).
Proof.
intros;     unfold tc_iszero in *; simpl.
      rewrite ?eval_expr_initialized.
     destruct (eval_expr Delta e any_environ); simpl; 
     rewrite ?eval_expr_initialized; auto.
     if_tac; simpl; auto.
     if_tac; simpl; auto.
Qed.

Lemma denote_tc_assert_initialized_tc_nodivover:
  forall i Delta e1 e2, 
    denote_tc_assert (initialized i Delta) (tc_nodivover (initialized i Delta) e1 e2)
      = denote_tc_assert Delta (tc_nodivover Delta e1 e2).
Proof.
intros.
     unfold tc_nodivover in *; simpl in *.
     rewrite ?eval_expr_initialized; auto.
     destruct (eval_expr Delta e1 any_environ); simpl in *;     
     rewrite ?eval_expr_initialized; auto.
     destruct (eval_expr Delta e2 any_environ); simpl in *;     
     rewrite ?eval_expr_initialized; auto.
     if_tac; simpl in *; auto.
     rewrite ?eval_expr_initialized; auto.
Qed.

Lemma denote_tc_assert_initialized_tc_ilt:
  forall i Delta e1 e2, 
    denote_tc_assert (initialized i Delta) (tc_ilt (initialized i Delta) e1 e2)
      = denote_tc_assert Delta (tc_ilt Delta e1 e2).
Proof.
intros.
     unfold tc_ilt in *; simpl in *.
     rewrite ?eval_expr_initialized; auto.
     destruct (eval_expr Delta e1 any_environ); simpl in *;     
     rewrite ?eval_expr_initialized; auto.
    if_tac; auto. simpl. unfold_lift; extensionality rho.
     rewrite ?eval_expr_initialized; auto.
Qed.

Lemma denote_tc_assert_initialized_tc_comparable:
  forall i Delta e1 e2, 
    denote_tc_assert (initialized i Delta) (tc_comparable (initialized i Delta) e1 e2)
      = denote_tc_assert Delta (tc_comparable Delta e1 e2).
Proof.
intros.
     unfold tc_comparable in *; simpl in *.
     rewrite ?eval_expr_initialized; auto.
     destruct (eval_expr Delta e1 any_environ); simpl in *;     
     rewrite ?eval_expr_initialized; auto.
     destruct (eval_expr Delta e2 any_environ); simpl in *;     
     rewrite ?eval_expr_initialized; auto.
    if_tac; auto.
  simpl. unfold_lift. extensionality rho.
  rewrite !eval_expr_initialized; auto.
Qed.


Lemma tc_expr_init:
  forall i Delta rho e, 
    tc_expr Delta e rho |-- tc_expr (initialized i Delta) e rho
with tc_lvalue_init:
  forall i Delta rho e, 
    tc_lvalue Delta e rho |-- tc_lvalue (initialized i Delta) e rho.
Proof.
  clear tc_expr_init; induction e; intros; auto;
  unfold tc_expr in *; simpl in *;
   try solve [destruct t as [ | [ | | | ] | [ | ] | [ | ] | | | | | ]; auto].
  + destruct (access_mode t) eqn:?; auto.
    unfold get_var_type in *.
    rewrite set_temp_ve.
    destruct ((var_types Delta) ! i0); auto.
    destruct (eqb_type t t0); auto.
    rewrite set_temp_ge.
    destruct ((glob_types Delta) ! i0); auto.
    destruct (eqb_type t t0); auto.
  + (* destruct (negb (type_is_volatile t)); auto.*)
    destruct ( (temp_types Delta) ! i0) eqn:?; [ | apply @FF_left].
    destruct p.  
    destruct (eq_dec i i0). subst. 
    - apply temp_types_init_same in Heqo. rewrite Heqo.
       simpl. destruct (is_neutral_cast t0 t || same_base_type t0 t)%bool; auto.
      destruct b; auto. apply @TT_right.
    - rewrite <- initialized_ne by auto.  rewrite Heqo.
       simpl. destruct (is_neutral_cast t0 t || same_base_type t0 t)%bool; auto.
      destruct b; auto.
  + destruct (access_mode t) eqn:?H; try inversion H;
      try apply @FF_left.
    rewrite !denote_tc_assert_andp, !denote_tc_assert_bool.
    repeat apply @andp_derives; auto.
    simpl. unfold_lift. rewrite eval_expr_initialized; auto.
  + rewrite !denote_tc_assert_andp, !denote_tc_assert_bool.
    repeat apply @andp_derives; auto.
     apply tc_lvalue_init; auto.
  + rewrite !denote_tc_assert_andp.
    repeat apply @andp_derives; auto.
    unfold isUnOpResultType.
    destruct u; simpl; auto;
      destruct (typeof e) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; simpl;
       rewrite ?denote_tc_assert_andp in *;
      repeat apply andp_derives; auto;
       rewrite ?denote_tc_assert_initialized_tc_bool,
            ?denote_tc_assert_initialized_tc_comparable; auto.
  + rewrite !denote_tc_assert_andp.
    repeat apply @andp_derives; auto.
     unfold isBinOpResultType.
    rewrite !set_temp_ct.
    destruct b; auto;
 try match goal with
     |  |- appcontext [classify_binarith] =>
                 destruct (classify_binarith (typeof e1) (typeof e2))
                as [ [|] | [|] | | | ];
       rewrite ?denote_tc_assert_andp in *;
      rewrite ?eval_expr_initialized, 
             ?denote_tc_assert_initialized_tc_bool,
             ?denote_tc_assert_initialized_tc_nodivover,
             ?denote_tc_assert_initialized_tc_iszero,
             ?denote_tc_assert_initialized_tc_nonzero;
      apply derives_refl
    |  |- appcontext [classify_cmp] =>
                 destruct (classify_cmp (typeof e1) (typeof e2));
          unfold check_pp_int;
       rewrite ?denote_tc_assert_andp, ?denote_tc_assert_orp;
      rewrite ?eval_expr_initialized, 
             ?denote_tc_assert_initialized_tc_bool,
             ?denote_tc_assert_initialized_tc_nodivover,
             ?denote_tc_assert_initialized_tc_comparable,
             ?denote_tc_assert_initialized_tc_iszero,
             ?denote_tc_assert_initialized_tc_nonzero;
      apply derives_refl
 end.
(*    try solve [rewrite denote_tc_assert_initialized_tc_nonzero; auto].
*)
    - destruct (classify_add (typeof e1) (typeof e2));
       rewrite ?denote_tc_assert_andp in *; intuition;
       simpl in *;
      rewrite ?eval_expr_initialized, ?denote_tc_assert_initialized_tc_bool;
      auto.
      unfold binarithType in *; simpl in *.
      destruct (typeof e1) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; auto;
      destruct (typeof e2) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; auto;
     rewrite ?denote_tc_assert_initialized_tc_bool; auto.
  - destruct (classify_sub (typeof e1) (typeof e2));
       rewrite ?denote_tc_assert_andp in *; intuition;
       simpl in *;
      rewrite ?eval_expr_initialized, ?denote_tc_assert_initialized_tc_bool;
      auto.
      unfold binarithType in *; simpl in *.
      destruct (typeof e1) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; auto;
      destruct (typeof e2) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; auto;
     rewrite ?denote_tc_assert_initialized_tc_bool; auto.
  -
      unfold binarithType in *; simpl in *.
      destruct (typeof e1) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; auto;
      destruct (typeof e2) as [ | [ | | | ] [|] | [ | ] | [ | ] | | | | | ]; auto;
     rewrite ?denote_tc_assert_initialized_tc_bool; auto.
  - destruct (classify_shift (typeof e1) (typeof e2))
                as [ [|] | [|] | | | ];
       rewrite ?denote_tc_assert_andp in *; intuition;
       simpl in *;
      rewrite ?eval_expr_initialized, ?denote_tc_assert_initialized_tc_bool,
             ?denote_tc_assert_initialized_tc_nodivover,
             ?denote_tc_assert_initialized_tc_nonzero; 
      auto;
      rewrite denote_tc_assert_initialized_tc_ilt; auto.
  -destruct (classify_shift (typeof e1) (typeof e2))
                as [ [|] | [|] | | | ];
       rewrite ?denote_tc_assert_andp in *; intuition;
       simpl in *;
      rewrite ?eval_expr_initialized, ?denote_tc_assert_initialized_tc_bool,
             ?denote_tc_assert_initialized_tc_nodivover,
             ?denote_tc_assert_initialized_tc_nonzero; 
      auto;
      rewrite denote_tc_assert_initialized_tc_ilt; auto.
  + rewrite !denote_tc_assert_andp.
    apply andp_derives; auto.
    clear. unfold isCastResultType.
    destruct (classify_cast (typeof e) t);
    repeat if_tac;
   rewrite  ?denote_tc_assert_initialized_tc_iszero; auto;
   try solve [destruct t; try destruct f;  
                   rewrite  ?denote_tc_assert_initialized_tc_bool;
                   auto];
    rewrite !denote_tc_assert_andp;
    simpl; rewrite eval_expr_initialized; auto.
  + destruct (access_mode t); auto.
    rewrite !denote_tc_assert_andp.
    apply andp_derives; auto.
    apply tc_lvalue_init; auto.
    rewrite ?set_temp_ct.
    destruct (typeof e); auto.
    destruct ((composite_types Delta) ! i1); auto.
    destruct (field_offset (composite_types Delta) i0 (co_members c)); auto.
    destruct ((composite_types Delta) ! i1); auto.
  +
     rewrite !denote_tc_assert_andp.
     rewrite ?denote_tc_assert_initialized_tc_bool, ?set_temp_ct;
                   auto.
  +
     rewrite !denote_tc_assert_andp.
     rewrite ?denote_tc_assert_initialized_tc_bool, ?set_temp_ct;
                   auto.
  + clear tc_lvalue_init.
    unfold tc_lvalue; induction e; simpl; auto.
    unfold get_var_type.
    rewrite !set_temp_ve.
    destruct ((var_types Delta) ! i0); 
      rewrite ?denote_tc_assert_bool; auto.
    rewrite set_temp_ge.
    destruct ((glob_types Delta) ! i0); 
      rewrite ?denote_tc_assert_bool; auto.
     rewrite !denote_tc_assert_andp.
      rewrite ?denote_tc_assert_bool; auto.
    repeat apply andp_derives; auto.
    apply tc_expr_init; auto.
     simpl. rewrite eval_expr_initialized; auto.
     rewrite !denote_tc_assert_andp.
    repeat apply andp_derives; auto.
    destruct (typeof e); rewrite ?set_temp_ct; auto.
    destruct ((composite_types Delta) ! i1); auto.
    destruct (field_offset (composite_types Delta) i0 (co_members c)); auto.
    destruct ((composite_types Delta) ! i1); auto.
Qed.