Require Import VST.veric.base.
Require Import VST.msl.msl_standard.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.expr_lemmas2.
Require Export VST.veric.expr_lemmas3.
Require Import VST.veric.juicy_mem.
Import Cop.
Import Cop2.

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
reflexivity.
* (* Ealignof *)
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0.
apply tc_bool_e in H0.
apply tc_bool_e in H1.
rewrite eqb_type_spec in H1.
subst.
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
unfold Cop2.sem_cmp, Cop2.sem_cmp_pl, Cop2.sem_cmp_lp, Cop2.sem_cmp_pp.

Lemma valid_pointer_dry:
  forall b ofs d m, app_pred (valid_pointer' (Vptr b ofs) d) (m_phi m) ->
           Mem.valid_pointer (m_dry m) b (Int.unsigned ofs + d) = true.
Proof.
intros.
simpl in H.
destruct (m_phi m @ (b, Int.unsigned ofs + d)) eqn:?H; try contradiction.
*
pose proof (juicy_mem_access m (b, Int.unsigned ofs + d)).
rewrite H0 in H1.
unfold access_at in H1.
unfold perm_of_res in H1.
simpl in H1. clear H0.
rewrite if_false in H1.
assert (exists x, (Mem.mem_access (m_dry m)) !! b (Int.unsigned ofs + d) Cur = Some x).
destruct ((Mem.mem_access (m_dry m)) !! b (Int.unsigned ofs + d) Cur); inv H1; eauto.
destruct H0.
apply perm_order'_dec_fiddle with x.
auto.
intro; subst sh. apply H; auto.
*
subst.
pose proof (juicy_mem_access m (b, Int.unsigned ofs + d)).
rewrite H0 in H1.
unfold access_at in H1.
unfold perm_of_res in H1.
simpl in H1. clear H0 H.
unfold Mem.valid_pointer.
unfold Mem.perm_dec.
destruct k.
+
assert (exists x, (Mem.mem_access (m_dry m)) !! b (Int.unsigned ofs + d) Cur = Some x).
rewrite H1. unfold perm_of_sh. repeat if_tac; try contradiction; eauto.
destruct H as [x H]; apply perm_order'_dec_fiddle with x; auto.
+
assert (exists x, (Mem.mem_access (m_dry m)) !! b (Int.unsigned ofs + d) Cur = Some x).
rewrite H1. unfold perm_of_sh. repeat if_tac; try contradiction; eauto.
destruct H as [x H]; apply perm_order'_dec_fiddle with x; auto.
+
assert (exists x, (Mem.mem_access (m_dry m)) !! b (Int.unsigned ofs + d) Cur = Some x).
rewrite H1. unfold perm_of_sh. repeat if_tac; try contradiction; eauto.
destruct H as [x H]; apply perm_order'_dec_fiddle with x; auto.
+
assert (exists x, (Mem.mem_access (m_dry m)) !! b (Int.unsigned ofs + d) Cur = Some x).
rewrite H1. unfold perm_of_sh. repeat if_tac; try contradiction; eauto.
destruct H as [x H]; apply perm_order'_dec_fiddle with x; auto.
Qed.

Lemma weak_valid_pointer_dry:
  forall b ofs m, app_pred (weak_valid_pointer (Vptr b ofs)) (m_phi m) ->
           (Mem.valid_pointer (m_dry m) b (Int.unsigned ofs)
           || Mem.valid_pointer (m_dry m) b (Int.unsigned ofs - 1))%bool = true.
Proof.
intros.
rewrite orb_true_iff.
destruct H; [left  | right].
rewrite <- (Z.add_0_r (Int.unsigned ofs)).
apply valid_pointer_dry; auto.
rewrite <- Z.add_opp_r.
apply valid_pointer_dry; auto.
Qed.

Lemma test_eq_relate:
  forall v1 v2 op m
    (OP: op = Ceq \/ op = Cne),
     (denote_tc_test_eq v1 v2) (m_phi m) ->
     option_map Val.of_bool
     (Val.cmpu_bool (Mem.valid_pointer (m_dry m)) op v1 v2) =
     sem_cmp_pp op v1 v2.
Proof.
intros.
unfold denote_tc_test_eq in H.
 destruct v1; try contradiction; auto;
 destruct v2; try contradiction; auto.
*
 unfold sem_cmp_pp; simpl.
 destruct H.
 hnf in H. subst i; rewrite Int.eq_true. simpl.
 apply weak_valid_pointer_dry in H0.
 rewrite H0. simpl. auto.
*
 unfold sem_cmp_pp; simpl.
 destruct H.
 hnf in H. subst i0; rewrite Int.eq_true. simpl.
 apply weak_valid_pointer_dry in H0.
 rewrite H0. simpl. auto.
*
 unfold sem_cmp_pp; simpl.
 unfold test_eq_ptrs in *.
 unfold sameblock in H.
 destruct (peq b b0);
  simpl proj_sumbool in H; cbv iota in H;
 [rewrite !if_true by auto | rewrite !if_false by auto].
 destruct H.
 apply weak_valid_pointer_dry in H.
 apply weak_valid_pointer_dry in H0.
 rewrite H. rewrite H0.
 simpl.
 reflexivity.
 destruct H.
 apply valid_pointer_dry in H.
 apply valid_pointer_dry in H0.
 rewrite Z.add_0_r in H,H0.
 rewrite H. rewrite H0.
 reflexivity.
Qed.

Lemma test_order_relate:
  forall v1 v2 op m
    (OP: op = Cle \/ op = Clt \/ op = Cge \/ op = Cgt),
     (denote_tc_test_order v1 v2) (m_phi m) ->
     option_map Val.of_bool
     (Val.cmpu_bool (Mem.valid_pointer (m_dry m)) op v1 v2) =
     sem_cmp_pp op v1 v2.
Proof.
  intros.
  unfold denote_tc_test_order in H.
  destruct v1; try contradiction; auto;
  destruct v2; try contradiction; auto.
  unfold sem_cmp_pp; simpl.
  unfold test_order_ptrs in *.
  unfold sameblock in H.
  destruct (peq b b0);
  simpl proj_sumbool in H; cbv iota in H;
    [rewrite !if_true by auto | rewrite !if_false by auto].
  + destruct H.
    apply weak_valid_pointer_dry in H.
    apply weak_valid_pointer_dry in H0.
    rewrite H. rewrite H0.
    simpl.
    reflexivity.
  + inv H.
Qed.

(*
Lemma bin_arith_relate :
forall a b c d v1 v2 t1 t2 m,
t1 <> int_or_ptr_type -> t2 <> int_or_ptr_type ->
Cop.sem_binarith a b c d v1 t1 v2 t2 m =
sem_binarith a b c d t1 t2 v1 v2.
Proof.
intros.
unfold Cop.sem_binarith, sem_binarith, Cop.sem_cast, sem_cast, both_int,both_long,both_float,both_single.
unfold classify_cast.
apply eqb_type_false in H.
apply eqb_type_false in H0.
rewrite H. rewrite H0.
destruct (classify_binarith t1 t2);
 destruct t1 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl; auto;
 destruct v1; auto;
 destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
 simpl; auto;
repeat match goal with
| |- context [match ?v with| Vundef => None| Vint _ => None| Vlong _ => None| Vfloat _ => None| Vsingle _ => None| Vptr _ _ => None end] =>
       destruct v; simpl
| |- context [match ?A with Some _ => None | None => None end] =>
 destruct A; simpl
 end;
 try (destruct (cast_float_int s _); reflexivity);
 try (destruct (cast_float_long s _); reflexivity);
 try (destruct (cast_single_int s _); reflexivity);
 try (destruct (cast_single_long s _); reflexivity);

 auto.
Qed.
*)

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
rewrite den_isBinOpR in H3.
simpl in H3.
forget (op_result_type (Ebinop b e1 e2 t)) as err.
forget (arg_type (Ebinop b e1 e2 t)) as err0.
clear H0.
destruct b;
lazymatch type of H3 with
| context [classify_add'] => destruct (classify_add' (typeof e1) (typeof e2)) eqn:?C
| context [classify_sub'] => destruct (classify_sub' (typeof e1) (typeof e2)) eqn:?C
| context [classify_binarith'] => 
   destruct (classify_binarith' (typeof e1) (typeof e2)) eqn:?C;
   try match goal with
       | |- context [Odiv] => destruct s 
       | |- context [Omod] => destruct s 
       end
| context [classify_shift'] => destruct (classify_shift' (typeof e1) (typeof e2)) eqn:?C
| context [classify_cmp'] => destruct (classify_cmp' (typeof e1) (typeof e2)) eqn:?C
| _ => idtac
end;
simpl in H3; super_unfold_lift;
unfold tc_int_or_ptr_type in *;
repeat match goal with
 |  H: _ /\ _ |- _ => destruct H
 |  H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ =>
       apply tc_bool_e in H
end;
forget (eval_expr e1 rho) as v1;
forget (eval_expr e2 rho) as v2;
subst rho;
econstructor; eauto;
rewrite Hcenv; clear Hcenv;
unfold tc_val in *.
all: try abstract (

destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
try solve [contradiction TC1];
destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
try solve [contradiction TC2];
try inv C;
repeat match goal with
 | H: context [eqb_type ?A ?B] |- _ =>
     let J := fresh "J" in destruct (eqb_type A B) eqn:J;
      [apply eqb_type_true in J | apply eqb_type_false in J]
 | H: context [binarithType'] |- _ =>
     unfold binarithType' in H; simpl in H
 | H: typecheck_error _ |- _ => contradiction H
 | H: negb true = true |- _ => inv H
 | H: isptr ?A |- _ => destruct A; simpl in H; try contradiction H
 | H: is_int _ _ ?A |- _ => unfold is_int in H; destruct A; try solve [contradiction H]
 | H: is_long ?A |- _ => unfold is_long in H; destruct A; try solve [contradiction H]
 | H: is_single ?A |- _ => unfold is_single in H; destruct A; try contradiction H
 | H: is_float ?A |- _ => unfold is_float in H; destruct A; try contradiction H
 end;
cbv beta iota zeta delta [
  sem_binary_operation sem_binary_operation' 
   Cop.sem_add Cop.sem_sub sem_sub Cop.sem_div Cop.sem_cast
   Cop.sem_mod sem_mod Cop.sem_shl Cop.sem_shift sem_shl sem_shift
   Cop.sem_shr sem_shr
   Cop.sem_binarith
]; simpl;
try match goal with
 | H: app_pred (denote_tc_nonzero _) _ |- _ => 
        first [apply denote_tc_nonzero_e in H
              |apply denote_tc_nonzero_e64 in H
              ]; try rewrite H
  end;
try match goal with 
 | H: app_pred (denote_tc_nodivover _ _) _ |- context [Int.signed] => 
        first [apply (denote_tc_nodivover_e64_li Signed) in H
              |apply (denote_tc_nodivover_e64_il Signed) in H
              ]; simpl in H; try rewrite H
 | H: app_pred (denote_tc_nodivover _ _) _ |- context [Int.unsigned] => 
        first [apply (denote_tc_nodivover_e64_li Unsigned) in H
              |apply (denote_tc_nodivover_e64_il Unsigned) in H
              ]; simpl in H; try rewrite H
 | H: app_pred (denote_tc_nodivover _ _) _ |- _ =>
       first [apply denote_tc_nodivover_e in H
              |apply denote_tc_nodivover_e64_ll in H
              ]; try rewrite H
end;
try (rewrite peq_eq_block by auto; try rewrite sizeof_range_true by auto);
try (rewrite Int64_eq_repr_signed32_nonzero by auto);
try (rewrite Int64_eq_repr_unsigned32_nonzero by auto);
try (erewrite denote_tc_igt_e by eauto);
try (erewrite denote_tc_lgt_e by eauto);
try reflexivity
).

*


destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
try solve [contradiction TC1];
destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
try solve [contradiction TC2];
try inv C;
repeat match goal with
 | H: context [eqb_type ?A ?B] |- _ =>
     let J := fresh "J" in destruct (eqb_type A B) eqn:J;
      [apply eqb_type_true in J | apply eqb_type_false in J]
 | H: context [binarithType'] |- _ =>
     unfold binarithType' in H; simpl in H
 | H: typecheck_error _ |- _ => contradiction H
 | H: negb true = true |- _ => inv H
 | H: isptr ?A |- _ => destruct A; simpl in H; try contradiction H
 | H: is_int _ _ ?A |- _ => unfold is_int in H; destruct A; try solve [contradiction H]
 | H: is_long ?A |- _ => unfold is_long in H; destruct A; try solve [contradiction H]
 | H: is_single ?A |- _ => unfold is_single in H; destruct A; try contradiction H
 | H: is_float ?A |- _ => unfold is_float in H; destruct A; try contradiction H
 end;
cbv beta iota zeta delta [
  sem_binary_operation sem_binary_operation' 
   Cop.sem_add Cop.sem_sub sem_sub Cop.sem_div Cop.sem_cast
   Cop.sem_mod sem_mod Cop.sem_shl Cop.sem_shift sem_shl sem_shift
   Cop.sem_shr sem_shr Cop.sem_cmp
   Cop.sem_binarith
]; simpl;
try match goal with
 | H: app_pred (denote_tc_nonzero _) _ |- _ => 
        first [apply denote_tc_nonzero_e in H
              |apply denote_tc_nonzero_e64 in H
              ]; try rewrite H
  end;
try match goal with 
 | H: app_pred (denote_tc_nodivover _ _) _ |- context [Int.signed] => 
        first [apply (denote_tc_nodivover_e64_li Signed) in H
              |apply (denote_tc_nodivover_e64_il Signed) in H
              ]; simpl in H; try rewrite H
 | H: app_pred (denote_tc_nodivover _ _) _ |- context [Int.unsigned] => 
        first [apply (denote_tc_nodivover_e64_li Unsigned) in H
              |apply (denote_tc_nodivover_e64_il Unsigned) in H
              ]; simpl in H; try rewrite H
 | H: app_pred (denote_tc_nodivover _ _) _ |- _ =>
       first [apply denote_tc_nodivover_e in H
              |apply denote_tc_nodivover_e64_ll in H
              ]; try rewrite H
end;
try (rewrite peq_eq_block by auto; try rewrite sizeof_range_true by auto);
try (rewrite Int64_eq_repr_signed32_nonzero by auto);
try (rewrite Int64_eq_repr_unsigned32_nonzero by auto);
try (erewrite denote_tc_igt_e by eauto);
try (erewrite denote_tc_lgt_e by eauto);
try reflexivity.

SearchAbout denote_tc_test_eq.
+ 
erewrite <- test_eq_relate; eauto.
destruct v2; try contradiction H0; try reflexivity.
simpl in H0.

inv H0; try reflexivity.
simpl.


apply test_eq_relate.
erewrite denote_tc_test_eq_Vint_l by eassumption.

erewrite ?denote_tc_test_eq_Vint_r by eassumption.
rewrite ?denote_tc_test_eq_Vint_r by auto.

simpl.


Focus 9.

destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
try solve [contradiction TC1];
destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
try solve [contradiction TC2];
try inv C;
repeat match goal with
 | H: context [eqb_type ?A ?B] |- _ =>
     let J := fresh "J" in destruct (eqb_type A B) eqn:J;
      [apply eqb_type_true in J | apply eqb_type_false in J]
 | H: context [binarithType'] |- _ =>
     unfold binarithType' in H; simpl in H
 | H: typecheck_error _ |- _ => contradiction H
 | H: negb true = true |- _ => inv H
 | H: isptr ?A |- _ => destruct A; simpl in H; try contradiction H
 | H: is_int _ _ ?A |- _ => unfold is_int in H; destruct A; try solve [contradiction H]
 | H: is_long ?A |- _ => unfold is_long in H; destruct A; try solve [contradiction H]
 | H: is_single ?A |- _ => unfold is_single in H; destruct A; try contradiction H
 | H: is_float ?A |- _ => unfold is_float in H; destruct A; try contradiction H
 end;
cbv beta iota zeta delta [
  sem_binary_operation sem_binary_operation' 
   Cop.sem_add Cop.sem_sub sem_sub Cop.sem_div Cop.sem_cast
   Cop.sem_mod sem_mod Cop.sem_shl Cop.sem_shift sem_shl sem_shift
   Cop.sem_binarith
];
try match goal with
 | H: app_pred (denote_tc_nonzero _) _ |- _ => 
        first [apply denote_tc_nonzero_e in H
              |apply denote_tc_nonzero_e64 in H
              ]; try rewrite H
  end;
try match goal with 
 | H: app_pred (denote_tc_nodivover _ _) _ |- context [Int.signed] => 
        first [apply (denote_tc_nodivover_e64_li Signed) in H
              |apply (denote_tc_nodivover_e64_il Signed) in H
              ]; simpl in H; try rewrite H
 | H: app_pred (denote_tc_nodivover _ _) _ |- context [Int.unsigned] => 
        first [apply (denote_tc_nodivover_e64_li Unsigned) in H
              |apply (denote_tc_nodivover_e64_il Unsigned) in H
              ]; simpl in H; try rewrite H
 | H: app_pred (denote_tc_nodivover _ _) _ |- _ =>
       first [apply denote_tc_nodivover_e in H
              |apply denote_tc_nodivover_e64_ll in H
              ]; try rewrite H
end;
try (rewrite peq_eq_block by auto; try rewrite sizeof_range_true by auto);
try (rewrite Int64_eq_repr_signed32_nonzero by auto);
try (rewrite Int64_eq_repr_unsigned32_nonzero by auto);
try (erewrite denote_tc_igt_e by eauto);
try reflexivity.

erewrite denote_tc_igt_e by eauto.
Search Int.ltu.



* (* Osub *)
* (* Omul *)
* (* Odiv *)
* (* Omod *)
* (* Oand *)
* (* Oor *)
* (* Oxor *)
* (* Oshl *)
* (* Oeq *)
* (* One *)
* (* Olt *)
* (* Ogt *)
* (* Ole *)
* (* Oge *)


SearchAbout isBinOpResultType.

simpl in *.
clear H4 H2. rename H3 into H7.
rename H7 into H5.
super_unfold_lift.
unfold eval_binop in *; super_unfold_lift; intuition. unfold force_val2, force_val.

apply typecheck_expr_sound in ; [| auto].

remember (sem_binary_operation' b (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
destruct o.
  + eapply Clight.eval_Ebinop. eapply H6; eauto.
    eapply H1; assumption.
   rewrite Heqo. clear Heqo.
   rewrite Hcenv.
    eapply tc_binaryop_relate; eauto.
    admit. (* typeof e1 <> int_or_ptr_type *)
    admit. (* typeof e2 <> int_or_ptr_type *)
  +
    eapply eval_binop_relate_fail; eassumption.



Lemma tc_binaryop_relate : forall {CS: compspecs} Delta b e1 e2 t rho m
(TCE: typecheck_environ Delta rho)                                  
(TC1: denote_tc_assert (typecheck_expr Delta e1) rho (m_phi m))
(TC2: denote_tc_assert (typecheck_expr Delta e2) rho (m_phi m))
(J1: typeof e1 <> int_or_ptr_type)
(J2: typeof e2 <> int_or_ptr_type),
denote_tc_assert (isBinOpResultType b e1 e2 t) rho (m_phi m) ->
Cop.sem_binary_operation cenv_cs b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m_dry m) =
sem_binary_operation' b (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho).
Proof.
  intros.
  apply typecheck_expr_sound in TC1; [| auto].
  apply typecheck_expr_sound in TC2; [| auto].
  unfold Cop.sem_binary_operation.
  unfold sem_binary_operation'.
  destruct b; auto;
  try solve [apply bin_arith_relate; auto];
  match goal with
  |- ?A = ?B => let opL := fresh in set (opL:=A);
                let opR := fresh in set (opR:=B);
                hnf in opL; hnf in opR; subst opL opR
  end;
  rewrite ?bin_arith_relate by auto.
  * destruct (classify_add (typeof e1) (typeof e2)); reflexivity.
  * destruct (classify_sub (typeof e1) (typeof e2)); reflexivity.
  * rewrite den_isBinOpR in H.
    rewrite <- classify_binarith_eq in H.
    destruct (classify_binarith (typeof e1) (typeof e2)) as [[|] | [|] | | |] eqn:?H.
    + destruct H as [[? ?] ?].
      simpl in H, H1; unfold_lift in H; unfold_lift in H1.
      apply tc_bool_e in H2.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction;
      apply denote_tc_nonzero_e in H;
      apply denote_tc_nodivover_e in H1;
      rewrite H, H1;
      reflexivity.
    + destruct H as [? ?].
      simpl in H; unfold_lift in H.
      apply tc_bool_e in H1.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction;
      apply denote_tc_nonzero_e in H;
      rewrite H;
      reflexivity.
    + destruct H as [[? ?] ?].
      simpl in H, H1; unfold_lift in H; unfold_lift in H1.
      apply tc_bool_e in H2.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction.
      apply denote_tc_nonzero_e64 in H;
      apply denote_tc_nodivover_e64_ll in H1;
      rewrite H, H1;
      reflexivity.
    + destruct H as [? ?].
      simpl in H; unfold_lift in H.
      apply tc_bool_e in H1.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction;
      first
      [ apply denote_tc_nonzero_e64 in H;
        rewrite H;
        reflexivity
      | apply denote_tc_nonzero_e in H;
        apply Int64_eq_repr_signed32_nonzero in H;
        rewrite H;
        reflexivity
      | apply denote_tc_nonzero_e in H;
        apply Int64_eq_repr_unsigned32_nonzero in H;
        rewrite H;
        reflexivity ].
    + destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction; reflexivity.
    + destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction; reflexivity.
    + inv H.
  * rewrite den_isBinOpR in H.
    rewrite <- classify_binarith_eq in H.    
    destruct (classify_binarith (typeof e1) (typeof e2)) as [[|] | [|] | | |] eqn:?H.
    + destruct H as [[? ?] ?].
      simpl in H, H1; unfold_lift in H; unfold_lift in H1.
      apply tc_bool_e in H2.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction;
      apply denote_tc_nonzero_e in H;
      apply denote_tc_nodivover_e in H1;
      rewrite H, H1;
      reflexivity.
    + destruct H as [? ?].
      simpl in H; unfold_lift in H.
      apply tc_bool_e in H1.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction;
      apply denote_tc_nonzero_e in H;
      rewrite H;
      reflexivity.
    + destruct H as [[? ?] ?].
      simpl in H, H1; unfold_lift in H; unfold_lift in H1.
      apply tc_bool_e in H2.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction.
      apply denote_tc_nonzero_e64 in H;
      apply denote_tc_nodivover_e64_ll in H1;
      rewrite H, H1;
      reflexivity.
    + destruct H as [? ?].
      simpl in H; unfold_lift in H.
      apply tc_bool_e in H1.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [inv H0];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl;
      try contradiction;
      first
      [ apply denote_tc_nonzero_e64 in H;
        rewrite H;
        reflexivity
      | apply denote_tc_nonzero_e in H;
        apply Int64_eq_repr_signed32_nonzero in H;
        rewrite H;
        reflexivity
      | apply denote_tc_nonzero_e in H;
        apply Int64_eq_repr_unsigned32_nonzero in H;
        rewrite H;
        reflexivity ].
    + inv H.
    + inv H.
    + inv H.
  * destruct (classify_shift (typeof e1)(typeof e2)); try reflexivity; apply bin_arith_relate.
  * destruct (classify_shift (typeof e1)(typeof e2)); try reflexivity; apply bin_arith_relate.
  * unfold isBinOpResultType in H;
    destruct (classify_cmp (typeof e1) (typeof e2)) eqn:HH;
    try destruct i; try destruct s; auto; try contradiction;
    simpl in H;
    try (rewrite denote_tc_assert_andp in H; destruct H);
    try apply bin_arith_relate.
    + rewrite denote_tc_assert_test_eq' in H.
      clear t H0.
      simpl in H. unfold_lift in H.
      apply test_eq_relate; auto.
    + rewrite denote_tc_assert_test_eq' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity;
      unfold sem_cmp_pl; apply test_eq_relate; auto.
    + rewrite denote_tc_assert_test_eq' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity;
      unfold sem_cmp_pl; apply test_eq_relate; auto.
  * unfold isBinOpResultType in H;
    destruct (classify_cmp (typeof e1) (typeof e2)) eqn:HH;
    try destruct i; try destruct s; auto; try contradiction;
    simpl in H;
    try (rewrite denote_tc_assert_andp in H; destruct H);
    try apply bin_arith_relate.
    + rewrite denote_tc_assert_test_eq' in H.
      clear t H0.
      simpl in H. unfold_lift in H.
      apply test_eq_relate; auto.
    + rewrite denote_tc_assert_test_eq' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity;
      unfold sem_cmp_pl; apply test_eq_relate; auto.
    + rewrite denote_tc_assert_test_eq' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity;
      unfold sem_cmp_pl; apply test_eq_relate; auto.
  * unfold isBinOpResultType, check_pp_int in H.
    destruct (classify_cmp (typeof e1) (typeof e2)) eqn:HH;
    try destruct i; try destruct s; auto; try contradiction;
    try (rewrite denote_tc_assert_andp in H; destruct H);
    try apply bin_arith_relate.
    + rewrite denote_tc_assert_test_order' in H.
      apply test_order_relate; auto.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
  * unfold isBinOpResultType, check_pp_int in H.
    destruct (classify_cmp (typeof e1) (typeof e2)) eqn:HH;
    try destruct i; try destruct s; auto; try contradiction;
    try (rewrite denote_tc_assert_andp in H; destruct H);
    try apply bin_arith_relate.
    + rewrite denote_tc_assert_test_order' in H.
      apply test_order_relate; auto.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
  * unfold isBinOpResultType, check_pp_int in H.
    destruct (classify_cmp (typeof e1) (typeof e2)) eqn:HH;
    try destruct i; try destruct s; auto; try contradiction;
    try (rewrite denote_tc_assert_andp in H; destruct H);
    try apply bin_arith_relate.
    + rewrite denote_tc_assert_test_order' in H.
      apply test_order_relate; auto.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
  * unfold isBinOpResultType, check_pp_int in H.
    destruct (classify_cmp (typeof e1) (typeof e2)) eqn:HH;
    try destruct i; try destruct s; auto; try contradiction;
    try (rewrite denote_tc_assert_andp in H; destruct H);
    try apply bin_arith_relate.
    + rewrite denote_tc_assert_test_order' in H.
      apply test_order_relate; auto.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
    + rewrite denote_tc_assert_test_order' in H.
      simpl in H. unfold_lift in H.
      destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
      try solve [rewrite classify_cmp_eq in HH; inv HH];
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      simpl in H;
      try contradiction; try reflexivity.
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
  Mem.weak_valid_pointer (m_dry m) b (Int.unsigned i) = true.
Proof.
intros.
destruct H.
apply weak_valid_pointer_dry in H0.
apply H0.
Qed.

Lemma cop2_sem_cast :
    forall t1 t2 v m,
 (classify_cast t1 t2 = cast_case_p2bool ->
   denote_tc_test_eq v (Vint Int.zero) (m_phi m) )->
  t1 <> int_or_ptr_type ->
  t2 <> int_or_ptr_type ->
 Cop.sem_cast v t1 t2 (m_dry m) = sem_cast t1 t2 v.
intros.
 unfold Cop.sem_cast, sem_cast.
assert (Cop.classify_cast t1 t2 = classify_cast t1 t2). {
  clear - H0 H1.
  apply eqb_type_false in H0.
  apply eqb_type_false in H1.
  destruct t1; auto; destruct t2; auto;
  unfold Cop.classify_cast, classify_cast; auto; rewrite ?H0,?H1; auto.
}
rewrite <- H2 in *.
destruct (Cop.classify_cast t1 t2);
destruct v; try reflexivity.
specialize (H (eq_refl _)).
do 4 red in H. destruct H as [_ H].
apply weak_valid_pointer_dry in H.
unfold Mem.weak_valid_pointer.
rewrite H. reflexivity.
Qed.

Lemma cop2_sem_cast' :
    forall {CS: compspecs} t2 e rho m,
 (denote_tc_assert (isCastResultType (typeof e) t2 e) rho) (m_phi m) ->
  typeof e <> int_or_ptr_type ->
  t2 <> int_or_ptr_type ->
 Cop.sem_cast (eval_expr e rho) (typeof e) t2 (m_dry m) =
 sem_cast (typeof e) t2 (eval_expr e rho).
Proof.
intros.
apply cop2_sem_cast; auto.
intro.
rewrite isCastR,H2,denote_tc_assert_andp, denote_tc_assert_test_eq' in H.
apply H.
Qed.

Lemma isBinOpResultType_binop_stable: forall {CS: compspecs} b e1 e2 t rho phi,
  denote_tc_assert (isBinOpResultType b e1 e2 t) rho phi ->
  binop_stable cenv_cs b e1 e2 = true.
Proof.
  intros.
  destruct b; auto;
  unfold isBinOpResultType in H;
  unfold binop_stable.
  + destruct (classify_add (typeof e1) (typeof e2));
    try rewrite !denote_tc_assert_andp in H;
    try destruct H as [[_ ?] _];
    try solve [eapply tc_bool_e; eauto].
    auto.
  + destruct (classify_sub (typeof e1) (typeof e2));
    try rewrite !denote_tc_assert_andp in H;
    try destruct H as [[_ ?] _];
    try solve [eapply tc_bool_e; eauto].
    auto.
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
apply Clight.eval_Elvalue with b Int.zero;
  [ | constructor; simpl; rewrite MODE; auto].
apply eval_Evar_local.
subst rho.
simpl in Heqo. symmetry in Heqo; apply Heqo.
subst rho.
unfold typecheck_environ in *.
destruct H0 as [? [Hve [Hge _]]].
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
if_tac in H2; try contradiction.
apply Clight.eval_Elvalue with b Int.zero; [  | econstructor 2; apply MODE].
apply Clight.eval_Evar_global; auto.

* (* eval_lvalue Evar *)
 simpl in H1.
 destruct (get_var_type Delta i) eqn:?; [ | contradiction].
 destruct (eqb_type t t0) eqn:?; inversion H1; clear H1.
 apply eqb_type_true in Heqb; subst t0.
 destruct H0 as [_ [? [? ?]]].
 subst rho; simpl in *.
 hnf in H0,H1.
 unfold get_var_type in Heqo.
 destruct ((var_types Delta)!i) eqn:?; inv Heqo.
 +
 apply H0 in Heqo0. destruct Heqo0 as [b ?];
 exists b; exists Int.zero; split; auto.
 constructor; auto.
 unfold eval_var; simpl. rewrite H.
 rewrite eqb_type_refl. reflexivity.
 +
 destruct ((glob_types Delta)!i) eqn:?; inv H3.
 destruct (H1 _ _ Heqo) as [b ?];
 exists b; exists Int.zero; split; auto.
 specialize (H2 _ _ Heqo).
 simpl in H2.
 destruct H2.
 constructor 2; auto.
 unfold filter_genv in H. destruct (Genv.find_symbol ge i); inv H.
 destruct H2 as [t' ?]. congruence.
 unfold eval_var. simpl.
 specialize (H2 _ _ Heqo).
 destruct H2. simpl in H2. unfold Map.get; rewrite H2.
 rewrite H. auto.
 destruct H2; congruence.

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
unfold tc_val in H3. if_tac in H3; contradiction H3.

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
destruct H2 as [b [? ?]]. destruct H10 as [base [ofs ?]].  simpl in *.
intuition. rewrite H11 in *. constructor. inv H8. auto.

* (*unop*)

simpl in *.
super_unfold_lift.
rewrite denote_tc_assert_andp in H3; destruct H3.
intuition. clear H2.
unfold eval_unop in *. unfold force_val1, force_val.
remember (sem_unary_operation u (typeof e) (eval_expr e rho)).
eapply Clight.eval_Eunop. eapply H5.  rewrite Heqo.

unfold sem_unary_operation. unfold Cop.sem_unary_operation.
apply typecheck_expr_sound in H4; auto.
destruct u; auto;
  simpl in H3;
  destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl;
  hnf in H4; try contradiction;
  try (simpl in H3; rewrite denote_tc_assert_andp in H3; destruct H3 as [H3 H6]);
  destruct (eval_expr e rho) eqn:?;
  try if_tac in H4; try contradiction; try reflexivity;
 unfold Cop.sem_notbool; simpl;
 unfold tc_test_eq in H6; simpl in H6;
 destruct (eval_expr e any_environ) eqn:?;
 simpl in H6; unfold_lift in H6;
  try solve [apply (eval_expr_any rho) in Heqv0; congruence];
  rewrite Heqv in H6;
  try (rewrite tc_test_eq0; auto).
* (*binop*)
  
simpl in *.
clear H4 H2. rename H3 into H7.
rewrite !denote_tc_assert_andp in H5.
destruct H5 as [[H2 H3] H4].
rename H7 into H5.
super_unfold_lift.
unfold eval_binop in *; super_unfold_lift; intuition. unfold force_val2, force_val.
remember (sem_binary_operation' b (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
destruct o.
  + eapply Clight.eval_Ebinop. eapply H6; eauto.
    eapply H1; assumption.
   rewrite Heqo. clear Heqo.
   rewrite Hcenv.
    eapply tc_binaryop_relate; eauto.
    admit. (* typeof e1 <> int_or_ptr_type *)
    admit. (* typeof e2 <> int_or_ptr_type *)
  +
    eapply eval_binop_relate_fail; eassumption.
* (*Cast*)
assert (TC := typecheck_expr_sound _ _ _ _ H0 H3).
simpl in *.
rewrite denote_tc_assert_andp in H3.
destruct H3.
unfold force_val1, force_val in *; super_unfold_lift; intuition.
eapply Clight.eval_Ecast.
eapply H5; auto.
revert TC.
rewrite  <- cop2_sem_cast' with (m0:=m); auto.
    2: admit. (* typeof e <> int_or_ptr_type *)
    2: admit. (* t2 <> int_or_ptr_type *)
intro.
destruct (Cop.sem_cast (eval_expr e rho) (typeof e) t (m_dry m)); auto.
exfalso; eapply tc_val_Vundef; eauto.
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
exists b. exists (Int.add ofs (Int.repr z)).
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
constructor.
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
Admitted.

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






