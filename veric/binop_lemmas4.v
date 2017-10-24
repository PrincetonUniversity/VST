Require Import VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.

Require Import VST.veric.juicy_mem.
Import Cop.
Import Cop2.


Lemma sameblock_eq_block:
 forall p q r s, 
  is_true (sameblock (Vptr p r) (Vptr q s)) -> p=q.
Proof.
 simpl; intros. destruct (peq p q); auto. inv H.
Qed.

Lemma denote_tc_test_eq_Vint_l': forall m i v,
  (denote_tc_test_eq (Vint i) v) m ->
  Int.eq i Int.zero = true.
Proof.
  intros.
  unfold denote_tc_test_eq in H; simpl in H.
  destruct v; try solve [inv H]; simpl in H; destruct H; subst;
   apply Int.eq_true.
Qed.

Lemma denote_tc_test_eq_Vint_r': forall m i v,
  (denote_tc_test_eq v (Vint i)) m ->
  Int.eq i Int.zero = true.
Proof.
  intros.
  unfold denote_tc_test_eq in H; simpl in H.
  destruct v; try solve [inv H]; simpl in H; destruct H; subst;
   apply Int.eq_true.
Qed.

Lemma denote_tc_test_order_eqblock:
  forall phi b0 i0 b i,
   app_pred (denote_tc_test_order (Vptr b0 i0) (Vptr b i)) phi ->
     b0 = b.
Proof.
intros.
unfold denote_tc_test_order in H; simpl in H.
unfold test_order_ptrs in H.
simpl in H. destruct (peq b0 b); auto. contradiction H.
Qed.

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

Lemma eval_binop_relate':
 forall {CS: compspecs} (ge: genv) te ve rho b e1 e2 t m
    (Hcenv: genv_cenv ge = @cenv_cs CS)
    (H1: Clight.eval_expr ge ve te (m_dry m) e1 (eval_expr e1 rho))
    (H2: Clight.eval_expr ge ve te (m_dry m) e2 (eval_expr e2 rho))
    (H3: app_pred (denote_tc_assert (isBinOpResultType b e1 e2 t) rho) (m_phi m))
    (TC1 : tc_val (typeof e1) (eval_expr e1 rho))
    (TC2 : tc_val (typeof e2) (eval_expr e2 rho)),
Clight.eval_expr ge ve te (m_dry m) (Ebinop b e1 e2 t)
  (force_val2 (sem_binary_operation' b (typeof e1) (typeof e2))
     (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
intros.
rewrite den_isBinOpR in H3.
simpl in H3.
forget (op_result_type (Ebinop b e1 e2 t)) as err.
forget (arg_type (Ebinop b e1 e2 t)) as err0.
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
try clear rho;
econstructor; eauto;
rewrite Hcenv; clear Hcenv;
unfold tc_val in *;
try abstract (
(*Ltac foo e1 e2 TC1 TC2 C v1 v2 := *)
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
 | H: negb false = true |- _ => clear H
 | H: andb _ _ = true |- _ => rewrite andb_true_iff in H; destruct H
 | H: isptr ?A |- _ => destruct A; simpl in H; try contradiction H
 | H: is_int _ _ ?A |- _ => unfold is_int in H; destruct A; try solve [contradiction H]
 | H: is_long ?A |- _ => unfold is_long in H; destruct A; try solve [contradiction H]
 | H: is_single ?A |- _ => unfold is_single in H; destruct A; try contradiction H
 | H: is_float ?A |- _ => unfold is_float in H; destruct A; try contradiction H
 end;
try match goal with
 | H: is_numeric_type _ = true |- _ => solve [inv H]
 end;
 try (destruct v2; inv TC2; try contradiction; try reflexivity);
 try (destruct v1; inv TC1; try contradiction; try reflexivity);
 cbv beta iota zeta delta [
  sem_binary_operation sem_binary_operation' 
   Cop.sem_add Cop.sem_sub sem_sub Cop.sem_div Cop.sem_cast
   Cop.sem_mod sem_mod Cop.sem_shl Cop.sem_shift sem_shl sem_shift
   Cop.sem_shr sem_shr Cop.sem_cmp sem_cmp
   sem_cmp_pp sem_cmp_pl sem_cmp_lp cast_out_long
   Cop.sem_binarith classify_cmp
   Cop.classify_cast binarith_type classify_binarith
   classify_shift sem_shift_ii sem_shift_ll sem_shift_il sem_shift_li
   classify_sub sem_sub_pp
   force_val2 typeconv remove_attributes change_attributes
 ];
 try (erewrite (if_true _ (eq_block _ _)) by (eapply sameblock_eq_block; eauto));
 rewrite ?sizeof_range_true by auto;
 try erewrite denote_tc_nodivover_e by eauto;
 try erewrite denote_tc_nonzero_e by eauto;
 try rewrite cast_int_long_nonzero 
       by (eapply denote_tc_nonzero_e; eauto);
 rewrite ?(proj2 (eqb_type_false _ _)) by auto 1;
 try reflexivity;
 try erewrite (denote_tc_nodivover_e64_li Signed) by eauto;
 try erewrite (denote_tc_nodivover_e64_il Signed) by eauto;
 try erewrite (denote_tc_nodivover_e64_li Unsigned) by eauto;
 try erewrite (denote_tc_nodivover_e64_il Unsigned) by eauto;
 try erewrite (denote_tc_nodivover_e64_ll) by eauto;
 try erewrite denote_tc_nonzero_e64 by eauto;
 try erewrite denote_tc_igt_e by eauto;
 try erewrite denote_tc_lgt_e by eauto;
 try (erewrite test_eq_relate by eauto; unfold sem_cmp_pp; simpl);
 try (erewrite test_order_relate by eauto; unfold sem_cmp_pp; simpl);
 erewrite ?denote_tc_test_eq_Vint_l' by eassumption;
 erewrite ?denote_tc_test_eq_Vint_r' by eassumption;
 rewrite ?(if_true _ (eq_block _ _))
         by (eapply denote_tc_test_order_eqblock; eauto);
 try solve [destruct (eq_block _ _); reflexivity];
 try reflexivity
).
Qed.

