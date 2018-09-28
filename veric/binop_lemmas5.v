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
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_add in IBR |- *.
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
  destruct Archi.ptr64 eqn:Hp;
  destruct (classify_cmp' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR];
try abstract (
  destruct OP; subst op;
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
   end;
  unfold denote_tc_test_eq, sem_cast_i2l, sem_cast_l2l, cast_int_long, force_val in H1;
  rewrite Hp in H1;

    destruct (typeof e1) as [| [| | |] [|] | | | | | | |]; inv TV1; 
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv TV2;
    simpl in H; inv H;
    try (rewrite J in *; clear J);
    try (rewrite J0 in *; clear J0);
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try contradiction;
    repeat match goal with
    | H: app_pred (andp _ _) _ |- _ => destruct H
    | H: app_pred (prop _) _ |- _ => do 3 red in H; subst
    end;
    simpl; unfold Vptrofs, sem_cmp_pi, sem_cmp_ip, sem_cmp_pl, sem_cmp_lp, sem_cmp_pp; simpl; rewrite ?Hp; simpl;
    rewrite ?Hp; simpl;
    try (rewrite (Ptrofs_to_of64_lemma Hp); 
           unfold cast_int_int in H; rewrite H, Int.eq_true);
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
    try solve [if_tac; apply int_type_tc_val_of_bool; auto];
   try solve [apply int_type_tc_val_Vfalse; auto];
   try solve [apply int_type_tc_val_Vtrue; auto]).

all: try (
 apply tc_bool_e in IBR;
 repeat rewrite andb_true_iff in IBR; destruct IBR as [[? ?] ?];
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |]; inv TV1; inv H0;
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv TV2; inv H1;
    simpl in H; inv H;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try contradiction;
   destruct OP; subst op; try destruct s; try destruct s0;
  unfold sem_cmp_default, op_to_cmp,
 Clight_Cop2.sem_binarith, classify_binarith, both_int, both_long, Clight_Cop2.sem_cast,
  Clight_Cop2.classify_cast, binarith_type; rewrite ?Hp;
  simpl; rewrite ?Hp;
    try (apply int_type_tc_val_Vtrue; auto);
    try (apply int_type_tc_val_Vfalse; auto);
    try (apply int_type_tc_val_of_bool; auto)).

all:
destruct IBR as [IBR ?];
apply tc_bool_e in IBR;
rewrite negb_true_iff in IBR;
unfold sem_cmp_pl, sem_cmp_lp, sem_cmp_pp, Val.cmplu_bool, Val.cmpu_bool;
rewrite IBR, Hp;
destruct (typeof e1) as [| [| | |] [|] | | | | | | |] eqn:He1;  inv TV1;
destruct (typeof e2) as [| [| | |] [|] | | | | | | |] eqn:He2; inv TV2; inv H;
try rewrite IBR in *;
unfold check_pp_int' in H0;
destruct OP; subst op; simpl; destruct H0 as [H0 H2]; apply tc_bool_e in H2;
simpl in H0; unfold_lift in H0;
unfold denote_tc_test_eq in H0;
unfold Vptrofs; rewrite Hp;
destruct (eval_expr e1 rho); try contradiction;
destruct (eval_expr e2 rho); try contradiction;
unfold size_t in H0; rewrite ?Hp,?He1,?He2 in H0; simpl in H0; destruct H0; subst; simpl;
try solve [apply int_type_tc_val_of_bool; auto].
all:
try solve [
rewrite Ptrofs_to_of64_lemma by assumption; rewrite  H; 
apply int_type_tc_val_of_bool; auto].
Qed.
