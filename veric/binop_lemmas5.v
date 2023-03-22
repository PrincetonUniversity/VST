Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Clight_Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Import Cop.

Transparent intsize_eq.

Section mpred.

Context `{!heapGS Σ}.

(*Lemma test: ∀ (cmp : comparison) (v1 v2 v : val)
    sem_cmp_pp cmp v1 v2 = Some v*)

Lemma typecheck_Otest_eq_sound:
 forall op {CS: compspecs} (rho : environ) (e1 e2 : expr) (t : type)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho))
   (OP: op = Oeq \/ op = One),
   denote_tc_assert (isBinOpResultType op e1 e2 t) rho ⊢
   ⌜tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
  intros.
  trans (denote_tc_assert
           match classify_cmp' (typeof e1) (typeof e2) with
              | Cop.cmp_default =>
                           tc_bool (is_numeric_type (typeof e1)
                                         && is_numeric_type (typeof e2)
                                          && is_int_type t)
                                             (arg_type (Ebinop op e1 e2 t))
	            | Cop.cmp_case_pp => 
                     tc_andp' (tc_andp' (tc_int_or_ptr_type (typeof e1)) 
                                      (tc_int_or_ptr_type (typeof e2)))
                       (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_pi si =>
                     tc_andp' (tc_int_or_ptr_type (typeof e1))
                       (check_pp_int' e1 (Ecast e2 size_t) op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_ip si => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 size_t) e2 op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_pl => 
                     tc_andp' (tc_int_or_ptr_type (typeof e1))
                       (check_pp_int' e1 (Ecast e2 size_t) op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_lp => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 size_t) e2 op t (Ebinop op e1 e2 t))
           end rho);
  first by (rewrite den_isBinOpR; destruct OP as [|]; subst; auto).
  replace
    (tc_val t (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)))
  with
    (tc_val t
      (force_val
        (match classify_cmp' (typeof e1) (typeof e2) with
         | Cop.cmp_case_pp => if orb (eqb_type (typeof e1) int_or_ptr_type)
                                 (eqb_type (typeof e2) int_or_ptr_type) 
                      then (fun _ _ => None)
                      else sem_cmp_pp (op_to_cmp op)
         | cmp_case_pi si => if eqb_type (typeof e1) int_or_ptr_type
            then (fun _ _ => None)
            else sem_cmp_pi si (op_to_cmp op)
         | cmp_case_ip si => if eqb_type (typeof e2) int_or_ptr_type
            then (fun _ _ => None)
            else sem_cmp_ip si (op_to_cmp op)
         | cmp_case_pl => if eqb_type (typeof e1) int_or_ptr_type
            then (fun _ _ => None)
            else sem_cmp_pl (op_to_cmp op)
         | cmp_case_lp => if eqb_type (typeof e2) int_or_ptr_type
            then (fun _ _ => None)
            else sem_cmp_lp (op_to_cmp op)
         | cmp_default => sem_cmp_default (op_to_cmp op) (typeof e1) (typeof e2)
         end (eval_expr e1 rho) (eval_expr e2 rho))))
  by (destruct OP as [|]; subst; rewrite <- classify_cmp_eq; auto).
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_add.
  unfold force_val;
  rewrite !tc_val_tc_val_PM' in TV1,TV2.
  replace (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' e1 e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    by (unfold check_pp_int'; destruct OP; subst; auto).
  replace (check_pp_int' e1 (Ecast e2 size_t) op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' e1 (Ecast e2 size_t))
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    by (unfold check_pp_int'; destruct OP; subst; auto).
  replace (check_pp_int' (Ecast e1 size_t) e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' (Ecast e1 size_t) e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    by (unfold check_pp_int'; destruct OP; subst; auto).
  destruct Archi.ptr64 eqn:Hp; try discriminate;
  pose proof (classify_cmp_reflect (typeof e1) (typeof e2)) as Hcmp; inv Hcmp; simpl; unfold_lift;
    rewrite !tc_bool_e;
  last (by rewrite -!tc_val_tc_val_PM' in TV1,TV2; rewrite !andb_true_iff; iPureIntro; intros ((? & ?) & ?); apply tc_val_sem_cmp_binarith'; auto);
  try (destruct OP; subst op;
  iIntros "(% & H & %)";
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]
    | |-context[denote_tc_test_eq _ _] =>
           unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast, size_t, sem_cast_pointer;
           simpl; rewrite ?Hp; simpl
    end;
  unfold denote_tc_test_eq, sem_cast_i2l, sem_cast_l2l, cast_int_long, force_val;
  rewrite ?Hp; inv TV1; try (rewrite H in Hty1; try solve [destruct sz; inv Hty1]; try solve [destruct sz0; inv Hty1]; inv Hty1);
  inv TV2; try (rewrite H3 in Hty2; try solve [destruct sz; inv Hty2]; try solve [destruct sz0; inv Hty2]; inv Hty2);
  rewrite -> ?J, ?J0 in *;
  destruct (eval_expr e1 rho); try contradiction; try iDestruct "H" as "[]";
  destruct (eval_expr e2 rho); try iDestruct "H" as "[]"; try iDestruct "H" as "[-> ->]"; try iDestruct "H" as "[-> H]"; try done;
    repeat match goal with
    | H:  _ /\ _ |- _ => destruct H
    end; subst;
    simpl; unfold Vptrofs, sem_cmp_pi, sem_cmp_ip, sem_cmp_pl, sem_cmp_lp, sem_cmp_pp; simpl; rewrite ?Hp; simpl;
    rewrite ?Hp; simpl;
    try (rewrite (Ptrofs_to_of64_lemma Hp);
           unfold cast_int_int in H; rewrite Hii Int.eq_true);
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto);
   try match goal with
    | H: Int64.repr (Int.signed _) = Int64.zero |- _ => apply Int64repr_Intsigned_zero in H; subst
    | H: Int64.repr (Int.unsigned _) = Int64.zero |- _ => apply Int64repr_Intunsigned_zero in H; subst
    end;
  try match goal with
     | |- context [Int64.eq (Ptrofs.to_int64 (Ptrofs.of_ints Int.zero)) Int64.zero] =>
       change (Int64.eq (Ptrofs.to_int64 (Ptrofs.of_ints Int.zero)) Int64.zero) with true;
       simpl
     | |- context [Int64.eq (Ptrofs.to_int64 (Ptrofs.of_intu Int.zero)) Int64.zero] =>
       change (Int64.eq (Ptrofs.to_int64 (Ptrofs.of_intu Int.zero)) Int64.zero) with true;
       simpl
    end;
   try solve [iPureIntro; apply int_type_tc_val_of_bool; auto];
   try solve [iPureIntro; if_tac; apply int_type_tc_val_of_bool; auto];
   try solve [iPureIntro; apply int_type_tc_val_Vfalse; auto];
   try solve [iPureIntro; apply int_type_tc_val_Vtrue; auto]);
  match goal with |- context [match typeof e1 with _ => _ end] => destruct (typeof e1); try discriminate; try iDestruct "H" as "[]"
                | |- context [match typeof e2 with _ => _ end] => destruct (typeof e2); try discriminate; try iDestruct "H" as "[]" end;
  try iDestruct "H" as "[-> _]"; try (destruct s; iDestruct "H" as "[%Hs _]"; (apply Int64repr_Intsigned_zero in Hs as -> || apply Int64repr_Intunsigned_zero in Hs as ->); destruct si; simpl);
  try solve [iPureIntro; apply int_type_tc_val_of_bool; auto].
Qed.

End mpred.
