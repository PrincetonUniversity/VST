Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.binop_lemmas5.
Require Import VST.veric.binop_lemmas6.

Section mpred.

Context `{!heapGS Σ}.

Lemma typecheck_binop_sound:
forall op {CS: compspecs} (rho : environ) (e1 e2 : expr) (t : type)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   denote_tc_assert (isBinOpResultType op e1 e2 t) rho ⊢
   ⌜tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
  intros.
  destruct op;
  first
    [ eapply typecheck_Oadd_sound; eauto
    | eapply typecheck_Osub_sound; eauto
    | eapply typecheck_Omul_sound; eauto
    | eapply typecheck_Odiv_sound; eauto
    | eapply typecheck_Omod_sound; eauto
    | eapply typecheck_Oshift_sound; solve [eauto]
    | eapply typecheck_Obin_sound; solve [eauto]
    | eapply typecheck_Otest_eq_sound; solve [eauto]
    | eapply typecheck_Otest_order_sound; solve [eauto]].
Qed.

Lemma force_val_Some : forall o v, o = Some v -> force_val o = v.
Proof. intros; subst; auto. Qed.

Lemma ints_to_64 : forall i, 0 <= Int.signed i <= Ptrofs.max_unsigned -> Ptrofs.to_int64 (Ptrofs.of_ints i) = Int64.repr (Int.signed i).
Proof.
  intros; rewrite /Ptrofs.to_int64 /Ptrofs.of_ints.
  rewrite Ptrofs.unsigned_repr; auto.
Qed.

Lemma intu_to_64 : forall i, 0 <= Int.unsigned i <= Ptrofs.max_unsigned -> Ptrofs.to_int64 (Ptrofs.of_intu i) = Int64.repr (Int.unsigned i).
Proof.
  intros; rewrite /Ptrofs.to_int64 /Ptrofs.of_intu /Ptrofs.of_int.
  rewrite Ptrofs.unsigned_repr; auto.
Qed.

Lemma sem_cmp_relate : forall {CS} b e1 e2 ty m rho
  (TC1 : tc_val (typeof e1) (eval_expr e1 rho))
  (TC2 : tc_val (typeof e2) (eval_expr e2 rho))
  (Hcmp : is_comparison b = true),
  mem_auth m ∗ denote_tc_assert (isBinOpResultType b e1 e2 ty) rho ⊢
  ⌜sem_binary_operation cenv_cs b (eval_expr(CS := CS) e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) m =
   Some (eval_binop b  (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
  intros.
  iIntros "[Hm H]"; iDestruct (typecheck_binop_sound b rho e1 e2 with "H") as %TC; [done..|].
  rewrite /eval_binop /force_val2 in TC |- *.
  destruct (sem_binary_operation' _ _ _ _ _) eqn: Heval; last by apply tc_val_Vundef in TC.
  rewrite /sem_binary_operation' in Heval.
  rewrite den_isBinOpR /= /sem_binary_operation -classify_cmp_eq.
  forget (op_result_type (Ebinop b e1 e2 ty)) as err.
  forget (arg_type (Ebinop b e1 e2 ty)) as err0.
  pose proof (classify_cmp_reflect (typeof e1) (typeof e2)) as Hclass; rewrite -classify_cmp_eq in Hclass.
  rewrite !tc_val_tc_val_PM' in TC1 TC2.
  rewrite -(force_val_Some _ _ Heval).
  inv Hclass.
  - destruct b; try discriminate; rewrite /Cop.sem_cmp /sem_cmp; simpl; rewrite -H0 /=; unfold_lift;
      rewrite /tc_int_or_ptr_type !tc_bool_e -?bi.pure_and ?negb_true_iff /=; iDestruct "H" as "([-> ->] & H & %)";
      ((iApply (test_eq_relate' with "[$]"); auto) || iApply (test_order_relate' with "[$]")).
  - inv TC2; rewrite Ht in Hty2; try discriminate.
    destruct (eval_expr e2 rho) eqn: Hv; try contradiction.
    destruct b; try discriminate; rewrite /Cop.sem_cmp /sem_cmp /sem_cmp_pi; simpl; rewrite -H0 /=; unfold_lift;
      rewrite Ht Hv sem_cast_int_intptr_lemma /tc_int_or_ptr_type !tc_bool_e ?negb_true_iff /=; iDestruct "H" as "(-> & H & %)";
      first [rewrite test_eq_fiddle_signed_xx; iApply (test_eq_relate' with "[$]"); auto |
       rewrite test_order_fiddle_signed_xx; iApply (test_order_relate' with "[$]")].
  - inv TC1; rewrite Ht in Hty1; try discriminate.
    destruct (eval_expr e1 rho) eqn: Hv; try contradiction.
    destruct b; try discriminate; rewrite /Cop.sem_cmp /sem_cmp /sem_cmp_ip; simpl; rewrite -H0 /=; unfold_lift;
      rewrite Ht Hv sem_cast_int_intptr_lemma /tc_int_or_ptr_type !tc_bool_e ?negb_true_iff /=; iDestruct "H" as "(-> & H & %)";
      first [rewrite test_eq_fiddle_signed_yy; iApply (test_eq_relate' with "[$]"); auto |
       rewrite test_order_fiddle_signed_yy; iApply (test_order_relate' with "[$]")].
  - inv TC2; rewrite Ht in Hty2; try destruct sz; inv Hty2.
    destruct (typeof e2) eqn: Ht2; try destruct i; inv Ht.
    destruct (eval_expr e2 rho) eqn: Hv; try contradiction.
    destruct b; try discriminate; rewrite /Cop.sem_cmp /sem_cmp /sem_cmp_pl; simpl; rewrite -H0 /=; unfold_lift;
      rewrite Ht2 Hv sem_cast_long_intptr_lemma /tc_int_or_ptr_type !tc_bool_e ?negb_true_iff /=; iDestruct "H" as "(-> & H & %)";
      ((iApply (test_eq_relate' with "[$]"); auto) || iApply (test_order_relate' with "[$]")).
  - inv TC1; rewrite Ht in Hty1; try destruct sz; inv Hty1.
    destruct (typeof e1) eqn: Ht1; try destruct i; inv Ht.
    destruct (eval_expr e1 rho) eqn: Hv; try contradiction.
    destruct b; try discriminate; rewrite /Cop.sem_cmp /sem_cmp /sem_cmp_pl; simpl; rewrite -H0 /=; unfold_lift;
      rewrite Ht1 Hv sem_cast_long_intptr_lemma /tc_int_or_ptr_type !tc_bool_e ?negb_true_iff /=; iDestruct "H" as "(-> & H & %)";
      ((iApply (test_eq_relate' with "[$]"); auto) || iApply (test_order_relate' with "[$]")).
  - rewrite Heval /=; rewrite -!tc_val_tc_val_PM' in TC1 TC2; destruct b; try discriminate; rewrite /Cop.sem_cmp /sem_cmp in Heval |- *; simpl; rewrite /= -!H0 /= in Heval |- *; unfold_lift;
      rewrite !tc_bool_e /=; iDestruct "H" as %?; iPureIntro;
      destruct (typeof e1); try discriminate; destruct (typeof e2); try discriminate;
      apply sem_binarith_relate; rewrite ?bool2val_eq; auto; simpl in *; try discriminate; try (destruct i; discriminate); try (destruct i0; discriminate).
Qed.

Lemma sem_div_relate : forall {CS} e1 e2 ty m rho
  (TC1 : tc_val (typeof e1) (eval_expr(CS := CS) e1 rho))
  (TC2 : tc_val (typeof e2) (eval_expr e2 rho)),
  denote_tc_assert (isBinOpResultType Odiv e1 e2 ty) rho ⊢
  ⌜sem_binary_operation cenv_cs Odiv (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) m =
   Some (eval_binop Odiv (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
  intros.
  iIntros "H"; iDestruct (typecheck_binop_sound with "H") as %TC; [done..|].
  rewrite /eval_binop /force_val2 in TC |- *.
  destruct (sem_binary_operation' _ _ _ _ _) eqn: Heval; last by apply tc_val_Vundef in TC.
  rewrite /sem_binary_operation' in Heval.
  rewrite den_isBinOpR /= /sem_binary_operation.
  forget (op_result_type (Ebinop Odiv e1 e2 ty)) as err.
  forget (arg_type (Ebinop Odiv e1 e2 ty)) as err0.
  pose proof (classify_binarith_reflect (typeof e1) (typeof e2)) as Hclass.
  rewrite !tc_val_tc_val_PM' in TC1 TC2.
  rewrite /Cop.sem_div /sem_div in Heval |- *.
  inv Hclass; try iDestruct "H" as "[]";
  repeat match goal with
  | H : stupid_typeconv ?t = Tint _ _ _, Hty : tc_val_PM' ?t _ |- _ => inv Hty; rewrite ?Ht ?Ht0 in H; inv H
  | H : stupid_typeconv ?t = Tlong _ _, Hty : tc_val_PM' ?t _ |- _ => destruct t eqn: ?Ht; try destruct i; inv H; inv Hty; try discriminate;
      try match goal with H: stupid_typeconv (Tlong _ _) = Tlong _ _ |- _ => inv H end
  | H : stupid_typeconv ?t = Tfloat _ _, Hty : tc_val_PM' ?t _ |- _ => destruct t eqn: ?Ht; try destruct i; inv H; inv Hty; try discriminate;
      try match goal with H: stupid_typeconv (Tfloat _ _) = Tfloat _ _ |- _ => inv H end
  | H : stupid_typeconv ?t = Tpointer _ _, Hty : tc_val_PM' ?t _ |- _ =>
      inv Hty; rewrite ?Ht ?Ht0 in H; simpl in H; try match goal with H : match ?sz with _ => _ end = Tpointer _ _ |- _=> destruct sz end; inv H
  end;
  rewrite ?Ht ?Ht0 in H0 |- *;
  repeat match goal with
  | H: eqb_type _ _ = _ |- _ => rewrite -> H in *; clear H
  | H: typecheck_error _ |- _ => contradiction H
  | H: andb _ _ = true |- _ => rewrite andb_true_iff in H; destruct H
  | H: isptr ?A |- _ => destruct (isptr_e H) as [?b [?ofs ?He]]; clear H
  | H: is_int _ _ ?A |- _ => destruct (is_int_e' H) as [?i ?He]; clear H
  | H: is_long ?A |- _ =>  destruct (is_long_e H) as [?i ?He]; clear H
  | H: is_single ?A |- _ => destruct (is_single_e H) as [?f ?He]; clear H
  | H: is_float ?A |- _ => destruct (is_float_e H) as [?f ?He]; clear H
  | H: is_true (sameblock _ _) |- _ => apply sameblock_eq_block in H; subst;
                                                          rewrite ?eq_block_lem'
  | H: is_numeric_type _ = true |- _  => inv H
  end; rewrite ?He ?He0; try destruct s; try destruct s1; try destruct s2; repeat rewrite -denote_tc_assert_andp' denote_tc_assert_andp; simpl; unfold_lift; rewrite ?He ?He0 ?denote_tc_nodivover_e' ?denote_tc_nonzero_e' ?(denote_tc_nodivover_e64_li' sg)
    ?denote_tc_nodivover_e64_ll' ?denote_tc_nonzero_e64' ?tc_bool_e /Cop.sem_binarith classify_binarith_eq;
  rewrite /sem_binarith classify_binarith_eq ?Ht ?Ht0 ?He ?He0 /both_int /both_long /both_single /both_float in Heval; rewrite -!H0 /binarith_type in Heval |- *; unfold_lift;
  destruct Archi.ptr64 eqn: Hp; try discriminate;
  rewrite -> ?sem_cast_relate, ?sem_cast_relate_long, ?sem_cast_relate_int_long;
  rewrite -> ?sem_cast_int_lemma, ?sem_cast_long_lemma, ?sem_cast_int_long_lemma;
  rewrite ?denote_tc_nodivover_e64_il';
  try (iDestruct "H" as %?; iPureIntro; repeat match goal with H : _ /\ _ |- _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2]; rewrite ?H1 ?H2 end;
    rewrite -> ?Int64_eq_repr_int_nonzero' by auto; auto).
Qed.

Lemma sem_mod_relate : forall {CS} e1 e2 ty m rho
  (TC1 : tc_val (typeof e1) (eval_expr(CS := CS) e1 rho))
  (TC2 : tc_val (typeof e2) (eval_expr e2 rho)),
  denote_tc_assert (isBinOpResultType Omod e1 e2 ty) rho ⊢
  ⌜sem_binary_operation cenv_cs Omod (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho) (typeof e2) m =
   Some (eval_binop Omod (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
  intros.
  iIntros "H"; iDestruct (typecheck_binop_sound with "H") as %TC; [done..|].
  rewrite /eval_binop /force_val2 in TC |- *.
  destruct (sem_binary_operation' _ _ _ _ _) eqn: Heval; last by apply tc_val_Vundef in TC.
  rewrite /sem_binary_operation' in Heval.
  rewrite den_isBinOpR /= /sem_binary_operation.
  forget (op_result_type (Ebinop Omod e1 e2 ty)) as err.
  forget (arg_type (Ebinop Omod e1 e2 ty)) as err0.
  pose proof (classify_binarith_reflect (typeof e1) (typeof e2)) as Hclass.
  rewrite !tc_val_tc_val_PM' in TC1 TC2.
  rewrite /Cop.sem_mod /sem_mod in Heval |- *.
  inv Hclass; try iDestruct "H" as "[]";
  repeat match goal with
  | H : stupid_typeconv ?t = Tint _ _ _, Hty : tc_val_PM' ?t _ |- _ => inv Hty; rewrite ?Ht ?Ht0 in H; inv H
  | H : stupid_typeconv ?t = Tlong _ _, Hty : tc_val_PM' ?t _ |- _ => destruct t eqn: ?Ht; try destruct i; inv H; inv Hty; try discriminate;
      try match goal with H: stupid_typeconv (Tlong _ _) = Tlong _ _ |- _ => inv H end
  | H : stupid_typeconv ?t = Tfloat _ _, Hty : tc_val_PM' ?t _ |- _ => destruct t eqn: ?Ht; try destruct i; inv H; inv Hty; try discriminate;
      try match goal with H: stupid_typeconv (Tfloat _ _) = Tfloat _ _ |- _ => inv H end
  | H : stupid_typeconv ?t = Tpointer _ _, Hty : tc_val_PM' ?t _ |- _ =>
      inv Hty; rewrite ?Ht ?Ht0 in H; simpl in H; try match goal with H : match ?sz with _ => _ end = Tpointer _ _ |- _=> destruct sz end; inv H
  end;
  rewrite ?Ht ?Ht0 in H0 |- *;
  repeat match goal with
  | H: eqb_type _ _ = _ |- _ => rewrite -> H in *; clear H
  | H: typecheck_error _ |- _ => contradiction H
  | H: andb _ _ = true |- _ => rewrite andb_true_iff in H; destruct H
  | H: isptr ?A |- _ => destruct (isptr_e H) as [?b [?ofs ?He]]; clear H
  | H: is_int _ _ ?A |- _ => destruct (is_int_e' H) as [?i ?He]; clear H
  | H: is_long ?A |- _ =>  destruct (is_long_e H) as [?i ?He]; clear H
  | H: is_single ?A |- _ => destruct (is_single_e H) as [?f ?He]; clear H
  | H: is_float ?A |- _ => destruct (is_float_e H) as [?f ?He]; clear H
  | H: is_true (sameblock _ _) |- _ => apply sameblock_eq_block in H; subst;
                                                          rewrite ?eq_block_lem'
  | H: is_numeric_type _ = true |- _  => inv H
  end; rewrite ?He ?He0; try destruct s; try destruct s1; try destruct s2; repeat rewrite -denote_tc_assert_andp' denote_tc_assert_andp; simpl; unfold_lift; rewrite ?He ?He0 ?denote_tc_nodivover_e' ?denote_tc_nonzero_e' ?(denote_tc_nodivover_e64_li' sg)
    ?denote_tc_nodivover_e64_ll' ?denote_tc_nonzero_e64' ?tc_bool_e /Cop.sem_binarith classify_binarith_eq;
  rewrite /sem_binarith classify_binarith_eq ?Ht ?Ht0 ?He ?He0 /both_int /both_long /both_single /both_float in Heval; rewrite -!H0 /binarith_type in Heval |- *; unfold_lift;
  destruct Archi.ptr64 eqn: Hp; try discriminate;
  rewrite -> ?sem_cast_relate, ?sem_cast_relate_long, ?sem_cast_relate_int_long;
  rewrite -> ?sem_cast_int_lemma, ?sem_cast_long_lemma, ?sem_cast_int_long_lemma;
  rewrite ?denote_tc_nodivover_e64_il';
  try (iDestruct "H" as %?; iPureIntro; repeat match goal with H : _ /\ _ |- _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2]; rewrite ?H1 ?H2 end;
    rewrite -> ?Int64_eq_repr_int_nonzero' by auto; auto).
Qed.

Global Instance binop_eq_dec : EqDec Cop.binary_operation.
Proof. hnf. decide equality. Qed.

Lemma eval_binop_relate':
 forall {CS: compspecs} (ge: genv) te ve rho b e1 e2 t m
    (Hcenv: cenv_sub (@cenv_cs CS) (genv_cenv ge))
    (H1: Clight.eval_expr ge ve te m e1 (eval_expr e1 rho))
    (H2: Clight.eval_expr ge ve te m e2 (eval_expr e2 rho))
    (TC1 : tc_val (typeof e1) (eval_expr e1 rho))
    (TC2 : tc_val (typeof e2) (eval_expr e2 rho)),
  mem_auth m ∗ denote_tc_assert (isBinOpResultType b e1 e2 t) rho ⊢
⌜Clight.eval_expr ge ve te m (Ebinop b e1 e2 t)
  (force_val2 (sem_binary_operation' b (typeof e1) (typeof e2))
     (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
intros; iIntros "[Hm H]".
iDestruct (sem_binary_operation_stable CS (genv_cenv ge) with "H") as %Hstable.
{ clear - Hcenv.
hnf in Hcenv.
intros.
specialize (Hcenv id). hnf in Hcenv. rewrite H in Hcenv. auto.
}
rewrite -bi.pure_mono'; [|econstructor; [apply H1 | apply H2 | apply Hstable; eassumption]].
clear - TC1 TC2.
destruct (is_comparison b) eqn: Hcmp.
{ by iApply (sem_cmp_relate with "[$]"). }
destruct (eq_dec b Odiv).
{ by subst; iApply (sem_div_relate with "H"). }
destruct (eq_dec b Omod).
{ by subst; iApply (sem_mod_relate with "H"). }
iDestruct (typecheck_binop_sound b rho e1 e2 with "H") as %TC; [done..|].
rewrite /eval_binop /force_val2 in TC |- *.
destruct (sem_binary_operation' _ _ _ _ _) eqn: Heval; last by apply tc_val_Vundef in TC.
rewrite /sem_binary_operation' in Heval.
rewrite -(force_val_Some _ _ Heval) /=.
rewrite den_isBinOpR /=.
forget (op_result_type (Ebinop b e1 e2 t)) as err.
forget (arg_type (Ebinop b e1 e2 t)) as err0.
cbv beta iota zeta delta [
  sem_binary_operation sem_binary_operation' 
   binarithType'
 ] in Heval |- *.
destruct b; try discriminate; try contradiction;
repeat lazymatch goal with
| |-context [classify_add'] => pose proof (classify_add_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_add' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into C end
| |-context [classify_sub'] => pose proof (classify_sub_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_sub' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into C end
| |-context [classify_binarith'] => 
   pose proof (classify_binarith_rel (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_binarith' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into C end;
   try destruct s
| |-context [classify_shift'] => pose proof (classify_shift_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_shift' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into C end
| |-context [classify_cmp'] => pose proof (classify_cmp_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_cmp' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into C end
| _ => idtac
end;
simpl; rewrite ?tc_andp_sound /=; super_unfold_lift;
unfold tc_int_or_ptr_type in *; rewrite ?tc_bool_e;
forget (eval_expr e1 rho) as v1;
forget (eval_expr e2 rho) as v2;
try clear rho;
try clear err err0;
try rewrite <- ?classify_add_eq, <- ?classify_sub_eq, <- ?classify_cmp_eq, <- ?classify_shift_eq, <- ?classify_binarith_eq in *;
 rewrite -> ?sem_cast_long_intptr_lemma in *;
 rewrite -> ?sem_cast_int_intptr_lemma in *;
  cbv beta iota zeta delta [
  sem_binary_operation sem_binary_operation' 
   Cop.sem_add sem_add Cop.sem_sub sem_sub Cop.sem_div
   Cop.sem_mod sem_mod Cop.sem_shl Cop.sem_shift 
   sem_shl sem_shift sem_add_ptr_long sem_add_ptr_int
   sem_add_long_ptr sem_add_int_ptr
   Cop.sem_shr sem_shr Cop.sem_cmp sem_cmp
   sem_cmp_pp sem_cmp_pl sem_cmp_lp
   binarith_type 
   sem_shift_ii sem_shift_ll sem_shift_il sem_shift_li
    sem_sub_pp sem_sub_pi sem_sub_pl 
   force_val2 typeconv remove_attributes change_attributes
   sem_add_ptr_int force_val both_int both_long force_val2
    Cop.sem_add_ptr_int
 ] in Heval |- *;
 try rewrite C in Heval |- *; try rewrite C0 in Heval |- *; try rewrite C1 in Heval |- *;
 try (iDestruct "H" as %?);
 repeat match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: complete_type _ _ = _ |- _ => rewrite H; clear H
            | H: negb (eqb_type ?A ?B) = true |- _ =>
                rewrite negb_true_iff in H; try rewrite H in *
            | H: eqb_type _ _ = _ |- _ => rewrite H
            end;
 try clear CS; try clear m;
 try contradiction;
 try solve [destruct (classify_binarith _ _) eqn: Hbin; rewrite Heval; try iDestruct "H" as "([] & _)";
     iPureIntro; apply sem_binarith_relate; auto; destruct (typeof e1); try discriminate; destruct (typeof e2); try discriminate;
     simpl in *; auto; try discriminate; try destruct s; try destruct s0; try discriminate; try (destruct i; discriminate); try (destruct i0; discriminate); try (destruct f; discriminate)];
(* unfold Cop.sem_binarith, sem_binarith in *;
 try match goal with
 | |-context [classify_binarith] => destruct (classify_binarith (typeof e1) (typeof e2)) eqn:?C; try destruct s
 end;
 simpl; super_unfold_lift; rewrite ?tc_bool_e; try (iDestruct "H" as "[H %]"); *)
 rewrite !tc_val_tc_val_PM' in TC1, TC2;
 try match goal with
 | H : stupid_typeconv ?t = Tint _ _ _, Hty : tc_val_PM' ?t _ |- _ => inv Hty; rewrite Ht in H; inv H
 | H : stupid_typeconv ?t = Tlong _ _, Hty : tc_val_PM' ?t _ |- _ => destruct t; try destruct i; inv H; inv Hty; try discriminate
 | H : stupid_typeconv ?t = Tpointer _ _, Hty : tc_val_PM' ?t _ |- _ =>
     inv Hty; rewrite Ht in H; simpl in H; try match goal with H : match ?sz with _ => _ end = Tpointer _ _ |- _ => destruct sz end; inv H
 end;
 try match goal with
 | H : stupid_typeconv ?t = Tint _ _ _, Hty : tc_val_PM' _ _ |- _ => inv Hty; rewrite Ht in H; inv H
 | H : stupid_typeconv ?t = Tlong _ _, Hty : tc_val_PM' _ _ |- _ => destruct t; try destruct i; inv H; inv Hty; try discriminate
 | H : stupid_typeconv ?t = Tpointer _ _, Hty : tc_val_PM' _ _ |- _ =>
     inv Hty; rewrite ?Ht ?Ht0 in H; simpl in H; try match goal with H : match ?sz with _ => _ end = Tpointer _ _ |- _=> destruct sz end; inv H
 end;
 rewrite ?Ht ?Ht0;
 repeat match goal with
 | H: eqb_type _ _ = _ |- _ => rewrite -> H in *; clear H
 | H: typecheck_error _ |- _ => contradiction H
 | H: andb _ _ = true |- _ => rewrite andb_true_iff in H; destruct H
 | H: isptr ?A |- _ => destruct (isptr_e H) as [?b [?ofs ?]]; clear H; subst A
 | H: is_int _ _ ?A |- _ => destruct (is_int_e' H) as [?i ?]; clear H; subst A
 | H: is_long ?A |- _ =>  destruct (is_long_e H) as [?i ?]; clear H; subst A
 | H: is_single ?A |- _ => destruct (is_single_e H) as [?f ?]; clear H; subst A
 | H: is_float ?A |- _ => destruct (is_float_e H) as [?f ?]; clear H; subst A
 | H: is_true (sameblock _ _) |- _ => apply sameblock_eq_block in H; subst;
                                                         rewrite ?eq_block_lem'
 | H: is_numeric_type _ = true |- _  => inv H
 end; try done;
 rewrite ?bool2val_eq;
 try done;
 rewrite -> ?sem_cast_long_intptr_lemma in *;
 rewrite -> ?sem_cast_int_intptr_lemma in *;
 rewrite -> ?sem_cast_relate, ?sem_cast_relate_long, ?sem_cast_relate_int_long;
 rewrite -> ?sem_cast_int_lemma, ?sem_cast_long_lemma, ?sem_cast_int_long_lemma;
 rewrite -> ?if_true by auto;
 rewrite -> ?sizeof_range_true by auto;
 rewrite ?denote_tc_igt_e' ?denote_tc_lgt_e';
 rewrite -> ?cast_int_long_nonzero by eassumption;
 rewrite -> ?(proj2 (eqb_type_false _ _)) by auto 1;
 repeat match goal with H: (if ?A then _ else _) = Some _ |- _ => destruct A eqn: ?Hcond; try discriminate end;
 try (iDestruct "H" as "(-> & %)"; iPureIntro);
 try done; try solve [destruct v1; inv Heval; auto].
Qed.

End mpred.
