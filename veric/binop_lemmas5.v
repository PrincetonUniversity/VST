Require Import VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Import Cop.

Lemma int_type_tc_val_Vtrue:
  forall t, is_int_type t = true -> tc_val t Vtrue.
Proof.
intros.
    destruct t as [| [| | |] [|] | | | | | | |]; 
 try discriminate; hnf; auto.
change (Int.signed Int.one) with 1.
change Byte.min_signed with (-128).
change Byte.max_signed with 127.
clear. omega.
clear.
simpl. 
change (Int.signed Int.one) with 1.
omega.
Qed.

Lemma int_type_tc_val_Vfalse:
  forall t, is_int_type t = true -> tc_val t Vfalse.
Proof.
intros.
    destruct t as [| [| | |] [|] | | | | | | |]; 
 try discriminate; hnf; auto;
change (Int.signed Int.zero) with 0.
change Byte.min_signed with (-128).
change Byte.max_signed with 127.
clear. omega.
clear. simpl. omega.
Qed.


Lemma int_type_tc_val_of_bool:
  forall t b, is_int_type t = true -> tc_val t (Val.of_bool b).
Proof.
intros.
    destruct t as [| [| | |] [|] | | | | | | |]; 
 try discriminate; hnf; auto; clear H;
 destruct b; simpl; auto;
change (Int.signed Int.one) with 1;
change (Int.signed Int.zero) with 0;
change (Int.unsigned Int.one) with 1;
change (Int.unsigned Int.zero) with 0;
change Byte.min_signed with (-128);
change Byte.max_signed with 127;
change Byte.max_unsigned with 255;
try omega.
Qed.

Lemma Ptrofs_to_of64_lemma:
 Archi.ptr64 = false -> 
 forall i, Ptrofs.to_int (Ptrofs.of_int64 i) = Int.repr (Int64.unsigned i).
Proof.
intros.
unfold Ptrofs.of_int64, Ptrofs.to_int.
pose proof (Ptrofs.agree32_repr H (Int64.unsigned i)).
red in H0.
rewrite H0.
apply Int.repr_unsigned.
Qed.

Lemma typecheck_Otest_eq_sound:
 forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho))
   (OP: op = Oeq \/ op = One),
   tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  assert (Hp: Archi.ptr64 = false) by reflexivity.  (* Archi.ptr64 DEPENDENCY *)
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
                       (check_pp_int' e1 (Ecast e2 intptr_t) op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_ip si => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 intptr_t) e2 op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_pl => 
                     tc_andp' (tc_int_or_ptr_type (typeof e1))
                       (check_pp_int' e1 (Ecast e2 intptr_t) op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_lp => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 intptr_t) e2 op t (Ebinop op e1 e2 t))
           end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP as [|]; subst; auto).
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
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_add in IBR |- *.
  unfold force_val;
  rewrite tc_val_tc_val_PM in TV1,TV2.
  replace (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' e1 e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP; subst; auto).
  replace (check_pp_int' e1 (Ecast e2 (Tint I32 Unsigned noattr)) op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' e1 (Ecast e2 (Tint I32 Unsigned noattr)))
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP; subst; auto).
  replace (check_pp_int' (Ecast e1 (Tint I32 Unsigned noattr)) e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' (Ecast e1 (Tint I32 Unsigned noattr)) e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP; subst; auto).
  destruct (classify_cmp' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].

1,2,3,4,5: abstract 
  (destruct OP; subst op;
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
            unfold Cop2.sem_cast, Cop2.classify_cast, intptr_t, sem_cast_pointer in H;
            simpl in H; rewrite ?Hp in H; simpl in H
   end;
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |]; inv TV1; 
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv TV2;
    simpl in H; inv H;
    try (rewrite J in *; clear J);
    try (rewrite J0 in *; clear J0);
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try contradiction;
    repeat match goal with
    | H: app_pred (denote_tc_test_eq _ _) _ |- _ => 
            destruct H as [? _]
    | H: app_pred (prop _) _ |- _ => do 3 red in H; subst
    end;
    simpl; unfold Vptrofs, sem_cmp_pp; simpl; rewrite ?Hp; simpl;
    rewrite ?Hp; simpl;
    try (rewrite (Ptrofs_to_of64_lemma Hp); 
           unfold cast_int_int in H; rewrite H, Int.eq_true);
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto);
    try solve [if_tac; apply int_type_tc_val_of_bool; auto]).

 apply tc_bool_e in IBR;
 repeat rewrite andb_true_iff in IBR; destruct IBR as [[? ?] ?];
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |]; inv TV1; inv H0;
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv TV2; inv H1;
    simpl in H; inv H;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try contradiction;
   destruct OP; subst op; try destruct s; try destruct s0;
  unfold sem_cmp_default, op_to_cmp,
 Cop2.sem_binarith, classify_binarith, both_int, Cop2.sem_cast,
  Cop2.classify_cast, binarith_type; rewrite ?Hp;
  simpl; rewrite ?Hp;
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto).
Qed.

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
  assert (Hp: Archi.ptr64 = false) by reflexivity.  (* Archi.ptr64 DEPENDENCY *)
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
                       (check_pp_int' e1 (Ecast e2 intptr_t) op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_ip si => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 intptr_t) e2 op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_pl => 
                     tc_andp' (tc_int_or_ptr_type (typeof e1))
                       (check_pp_int' e1 (Ecast e2 intptr_t) op t (Ebinop op e1 e2 t))
              | Cop.cmp_case_lp => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 intptr_t) e2 op t (Ebinop op e1 e2 t))
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
  destruct (classify_cmp' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].
1,2,3,4,5:
abstract (
destruct OP as [| [| [|]]]; subst op;
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
            unfold Cop2.sem_cast, Cop2.classify_cast, intptr_t, sem_cast_pointer in H;
            simpl in H; rewrite ?Hp in H; simpl in H
    | H: app_pred (denote_tc_assert (tc_test_order' _ _) _) _ |- _ =>
           simpl in H; super_unfold_lift; simpl in H;
            unfold Cop2.sem_cast, Cop2.classify_cast, intptr_t, sem_cast_pointer in H;
            simpl in H; rewrite ?Hp in H; simpl in H
   end;
    simpl;
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
    simpl; unfold Vptrofs, sem_cmp_pp; simpl; rewrite ?Hp; simpl;
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


 apply tc_bool_e in IBR;
 repeat rewrite andb_true_iff in IBR; destruct IBR as [[? ?] ?];
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |]; inv H0;
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv H1;
    simpl in H; inv H;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try contradiction.
all:
 destruct OP as [| [| [|]]]; subst op; try destruct s; try destruct s0;
   try destruct f; try destruct f0; try contradiction;
  unfold sem_cmp_default, op_to_cmp,
 Cop2.sem_binarith, classify_binarith, both_int, Cop2.sem_cast,
  Cop2.classify_cast, binarith_type; rewrite ?Hp;
  simpl; rewrite ?Hp;
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto).
Qed.
