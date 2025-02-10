Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Clight_Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Import Cop.

Section mpred.

Context `{!heapGS Σ}.

Lemma typecheck_Otest_order_sound:
 forall op {CS: compspecs} (rho : environ) (e1 e2 : expr) (t : type)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho))
   (OP: op = Ole \/ op = Olt \/ op = Oge \/ op = Ogt),
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
  first by (rewrite den_isBinOpR; destruct OP as [| [| [|]]]; subst; auto).
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
  by (destruct OP as [| [| [|]]]; subst; rewrite <- classify_cmp_eq; auto).
  unfold tc_int_or_ptr_type.
  replace (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_order' e1 e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    by (unfold check_pp_int'; destruct OP as [| [| [|]]]; subst; auto).
  replace (check_pp_int' e1 (Ecast e2 size_t) op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_order' e1 (Ecast e2 size_t))
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    by (unfold check_pp_int'; destruct OP as [| [| [|]]]; subst; auto).
  replace (check_pp_int' (Ecast e1 size_t) e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_order' (Ecast e1 size_t) e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    by (unfold check_pp_int'; destruct OP as [| [| [|]]]; subst; auto).

  destruct Archi.ptr64 eqn:Hp; try discriminate;
  pose proof (classify_cmp_reflect (typeof e1) (typeof e2)) as Hbin; inv Hbin; try iIntros "[]";
    simpl; unfold_lift; rewrite !tc_bool_e;
  last (by rewrite !andb_true_iff; iPureIntro; intros ((? & ?) & ?); apply tc_val_sem_cmp_binarith'; auto);
  iIntros "(% & H & %)";
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]
    | |-context[denote_tc_test_eq _ _] =>
           simpl; super_unfold_lift; simpl;
            unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast, size_t, sem_cast_pointer;
            simpl; rewrite ?Hp; simpl
    | |-context[denote_tc_test_order _ _] =>
            simpl; unfold_lift; unfold denote_tc_test_order; rewrite ?Hp
(*    | |-context[denote_tc_assert match op with _ => _ end _] =>
          match type of H with ?A =>
             first [replace A with (app_pred (denote_tc_assert (tc_andp' (tc_test_order' e1 (Ecast e2 size_t))
              (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t)))) rho) m) in H
          by (clear - OP H; destruct OP as [| [| [|]]]; subst op; try contradiction; reflexivity)
         | replace A with (app_pred (denote_tc_assert (tc_andp' (tc_test_order' (Ecast e1 size_t) e2)
              (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t)))) rho) m) in H
          by (clear - OP H; destruct OP as [| [| [|]]]; subst op; try contradiction; reflexivity)]
         end*)
   end;
    simpl;
    unfold sem_cmp_pi, sem_cmp_ip, sem_cmp_pl, sem_cmp_lp,
                     sem_cmp_pp, Val.cmplu_bool, Val.cmpu_bool; rewrite ?Hp.

all: rewrite !tc_val_tc_val_PM' in TV1, TV2; inv TV1; try (rewrite Ht in Hty1; try solve [destruct sz; inv Hty1]; try solve [destruct sz0; inv Hty1]; inv Hty1);
  inv TV2; try (rewrite Ht0 in Hty2; try solve [destruct sz; inv Hty2]; try solve [destruct sz0; inv Hty2]; inv Hty2);
  rewrite -> ?J, ?J0 in *;
  destruct (eval_expr e1 rho); try contradiction; try iDestruct "H" as "[]";
  destruct (eval_expr e2 rho); try iDestruct "H" as "[]"; try iDestruct "H" as "[-> ->]"; try iDestruct "H" as "[-> H]"; try done;
    simpl; unfold Vptrofs, sem_cmp_pi, sem_cmp_ip, sem_cmp_pl, sem_cmp_lp,
                     sem_cmp_pp, Clight_Cop2.sem_cast, size_t; simpl; rewrite ?H ?H3 ?Hp; simpl;
    try iDestruct "H" as "[]";
    try (rewrite (Ptrofs_to_of64_lemma Hp); 
           unfold cast_int_int in H; rewrite H Int.eq_true);
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto);
    try solve [iPureIntro; apply int_type_tc_val_of_bool; auto];
    try solve [if_tac; iPureIntro; apply int_type_tc_val_of_bool; auto];

   try (simpl; unfold test_order_ptrs, sameblock;
   destruct (peq b b0); simpl; try iDestruct "H" as "[]"; subst b0; iPureIntro;
   rewrite -> if_true by auto; apply int_type_tc_val_of_bool; auto).
all: match goal with |- context [match typeof ?e with _ => _ end] => destruct (typeof e); try discriminate; try iDestruct "H" as "[]" end.
Qed.

End mpred.
