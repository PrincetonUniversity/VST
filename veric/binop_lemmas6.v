Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Clight_Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Import Cop.

Lemma typecheck_Otest_order_sound:
 forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho))
   (OP: op = Ole \/ op = Olt \/ op = Oge \/ op = Ogt),
   tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  replace
    ((denote_tc_assert (isBinOpResultType op e1 e2 t) rho) m)
  with
    ((denote_tc_assert
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
              end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP as [| [| [|]]]; subst; auto).
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
  unfold tc_int_or_ptr_type in IBR.
    replace (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_order' e1 e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP as [| [| [|]]]; subst; auto).
    replace (check_pp_int' e1 (Ecast e2 (Tint I32 Unsigned noattr)) op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_order' e1 (Ecast e2 (Tint I32 Unsigned noattr)))
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP as [| [| [|]]]; subst; auto).
    replace (check_pp_int' (Ecast e1 (Tint I32 Unsigned noattr)) e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_order' (Ecast e1 (Tint I32 Unsigned noattr)) e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP as [| [| [|]]]; subst; auto).

 destruct Archi.ptr64 eqn:Hp;
  destruct (classify_cmp' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR];
    repeat match goal with
    |  H: app_pred (denote_tc_assert  (tc_andp' _ _) _) _ |- _ => 
                                destruct H
    | H:  app_pred   (denote_tc_assert
          (check_pp_int' _ _ _ _ _) _) _ |- _ => unfold check_pp_int' in H
    | H: _ /\ _ |- _ => destruct H
    | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
                      apply tc_bool_e in H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]
    | H: app_pred (denote_tc_assert (tc_test_eq' _ _) _) _ |- _ =>
           simpl in H; super_unfold_lift; simpl in H;
            unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast, size_t, sem_cast_pointer in H;
            simpl in H; rewrite ?Hp in H; simpl in H
    | H: app_pred (denote_tc_assert (tc_test_order' _ _) _) _ |- _ =>
            simpl in H; unfold_lift in H; unfold denote_tc_test_order in H; rewrite ?Hp in H
    | H: app_pred (denote_tc_assert match op with _ => _ end _) m |- _ =>
          match type of H with ?A =>
             first [replace A with (app_pred (denote_tc_assert (tc_andp' (tc_test_order' e1 (Ecast e2 size_t))
              (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t)))) rho) m) in H
          by (clear - OP H; destruct OP as [| [| [|]]]; subst op; try contradiction; reflexivity)
         | replace A with (app_pred (denote_tc_assert (tc_andp' (tc_test_order' (Ecast e1 size_t) e2)
              (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t)))) rho) m) in H
          by (clear - OP H; destruct OP as [| [| [|]]]; subst op; try contradiction; reflexivity)]
         end
   end;
    simpl;
    unfold sem_cmp_pi, sem_cmp_ip, sem_cmp_pl, sem_cmp_lp,
                     sem_cmp_pp, Val.cmplu_bool, Val.cmpu_bool; rewrite ?Hp.
all: try abstract (
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |];
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |];
    simpl in H; inv H; hnf in TV1,TV2;
    try (rewrite J in *; clear J);
    try (rewrite J0 in *; clear J0);
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try contradiction;
    repeat match goal with
    | H: app_pred (denote_tc_test_eq _ _) _ |- _ => 
            destruct H as [? _]
    | H: app_pred (prop _) _ |- _ => do 3 red in H; subst
    end;
    simpl; unfold Vptrofs, sem_cmp_pi, sem_cmp_ip, sem_cmp_pl, sem_cmp_lp,
                     sem_cmp_pp; simpl; rewrite ?Hp; simpl;
    rewrite ?Hp; simpl;
    try (rewrite (Ptrofs_to_of64_lemma Hp); 
           unfold cast_int_int in H; rewrite H, Int.eq_true);
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto);
    try solve [if_tac; apply int_type_tc_val_of_bool; auto];
  
   simpl in H1; unfold test_order_ptrs, sameblock in H1;
   destruct (peq b b0); try contradiction; subst b0; clear H1;
   rewrite if_true by auto; apply int_type_tc_val_of_bool; auto).
 
all:
 repeat rewrite andb_true_iff in IBR; destruct IBR as [[? ?] ?];
 destruct (typeof e1) as [|  [| | |] [|] | [|] | [ | ] ? | | | | |]; inv H0;
 destruct (typeof e2) as [|  [| | |] [|] | [|] | [ | ] ? | | | | |]; inv H1;
 inv H;
 simpl; unfold both_int, both_long;
 destruct (eval_expr e1 rho); try contradiction; 
 destruct (eval_expr e2 rho); try contradiction;
 unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast; rewrite ?Hp; simpl; rewrite ?Hp; simpl;
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto).
Qed.
