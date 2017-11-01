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

Ltac solve_tc_val H :=
  rewrite tc_val_tc_val_PM in H; inv H.

Ltac solve_tc_val' H :=
  rewrite tc_val_tc_val_PM' in H; inv H.

Lemma tc_val_sem_binarith': forall {CS: compspecs} sem_int sem_long sem_float sem_single t1 t2 t v1 v2 deferr reterr rho m
  (TV2: tc_val t2 v2)
  (TV1: tc_val t1 v1),
  (denote_tc_assert (binarithType' t1 t2 t deferr reterr) rho) m ->
  tc_val t
    (force_val
      (Cop2.sem_binarith
        (fun s n1 n2 => Some (Vint (sem_int s n1 n2)))
        (fun s n1 n2 => Some (Vlong (sem_long s n1 n2)))
        (fun n1 n2 => Some (Vfloat (sem_float n1 n2)))
        (fun n1 n2 => Some (Vsingle (sem_single n1 n2)))
        t1 t2 v1 v2)).
Proof.
  intros.
  unfold binarithType' in H.
  unfold Cop2.sem_binarith.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' t1 t2) eqn:?H;
  try solve [inv H]; apply tc_bool_e in H.
  + (* bin_case_i *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H0].
    destruct v1; try solve [inv H1].
    destruct v2; try solve [inv H2].
    destruct t as [| [| | |] ? ? | | | | | | |]; inv H; simpl; auto.
  + (* bin_case_l *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H0];
    destruct v1; try solve [inv H1];
    destruct v2; try solve [inv H2];
    destruct t as [| [| | |] ? ? | | | | | | |]; inv H; simpl; auto.
  + (* bin_case_f *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H0];
    destruct v1; try solve [inv H1];
    destruct v2; try solve [inv H2];
    destruct t as [| [| | |] ? ? | | [|] | | | | |]; inv H; simpl; auto.
  + (* bin_case_s *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H0];
    destruct v1; try solve [inv H1];
    destruct v2; try solve [inv H2];
    destruct t as [| [| | |] ? ? | | [|] | | | | |]; inv H; simpl; auto.
Qed.

Lemma tc_val_sem_cmp_binarith': forall sem_int sem_long sem_float sem_single t1 t2 t v1 v2
  (TV2: tc_val t2 v2)
  (TV1: tc_val t1 v1),
  is_numeric_type t1 = true ->
  is_numeric_type t2 = true ->
  is_int_type t = true ->
  tc_val t
    (force_val
      (Cop2.sem_binarith
        (fun s n1 n2 => Some (Val.of_bool (sem_int s n1 n2)))
        (fun s n1 n2 => Some (Val.of_bool (sem_long s n1 n2)))
        (fun n1 n2 => Some (Val.of_bool (sem_float n1 n2)))
        (fun n1 n2 => Some (Val.of_bool (sem_single n1 n2)))
        t1 t2 v1 v2)).
Proof.
  intros.
  destruct t; inv H1.
  unfold Cop2.sem_binarith.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' t1 t2) eqn:?H.
  + (* bin_case_i *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H1].
    destruct v1; try solve [inv H2];
    destruct v2; try solve [inv H3].
    apply tc_val_of_bool.
  + (* bin_case_l *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H1];
    destruct v1; try solve [inv H2];
    destruct v2; try solve [inv H3];
    apply tc_val_of_bool.
  + (* bin_case_f *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H1];
    destruct v1; try solve [inv H2];
    destruct v2; try solve [inv H3];
    apply tc_val_of_bool.
  + (* bin_case_s *)
    solve_tc_val TV1;
    solve_tc_val TV2;
    try solve [inv H1];
    destruct v1; try solve [inv H2];
    destruct v2; try solve [inv H3];
    apply tc_val_of_bool.
  + unfold classify_binarith' in H1.
    solve_tc_val TV1;
    solve_tc_val TV2;
    inv H1; inv H; inv H0.
Qed.

Lemma negb_true: forall a, negb a = true -> a = false.
Proof.  intros; destruct a; auto; inv H. Qed.

Lemma typecheck_Oadd_sound:
forall {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType Oadd e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop Oadd (typeof e1) (typeof e2)
       (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  rewrite den_isBinOpR in IBR. 
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_add in IBR |- *.
  rewrite classify_add_eq.
  destruct (classify_add' (typeof e1) (typeof e2)) eqn:?H;
  unfold force_val2, force_val;
  rewrite tc_val_tc_val_PM in TV1,TV2|-*;
  unfold classify_add' in H; simpl in IBR;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
                      apply tc_bool_e in H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]              
    end;
  try solve [
    unfold is_pointer_type in H1;
    destruct (typeof e1); inv TV1; destruct (typeof e2); inv TV2;
    simpl in H; inv H;
    try rewrite J in *; clear J;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
     simpl in *; try contradiction;
    destruct t; try solve [inv H1];
    try solve [constructor; try rewrite (negb_true _ H1); apply I]
  ].
  unfold sem_add_default.
  rewrite <- tc_val_tc_val_PM in TV1,TV2|-*.
  eapply tc_val_sem_binarith'; eauto.
Qed.

Lemma peq_eq_block:
   forall a b A (c d: A), is_true (peq a b) ->
       (if eq_block a b then c else d) = c.
 Proof.
  intros. rewrite if_true; auto.
   destruct (peq a b); auto. inv H.
 Qed.

Lemma typecheck_Osub_sound:
forall {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType Osub e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop Osub (typeof e1) (typeof e2)
       (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  rewrite den_isBinOpR in IBR. 
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_sub in IBR |- *.
  rewrite classify_sub_eq.
  destruct (classify_sub' (typeof e1) (typeof e2)) eqn:?H;
  unfold force_val2, force_val;
  rewrite tc_val_tc_val_PM in TV1,TV2|-*;
  unfold classify_sub' in H; simpl in IBR;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
                      apply tc_bool_e in H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]              
    end;
  try solve [
    unfold is_pointer_type in H1;
    destruct (typeof e1); inv TV1; destruct (typeof e2); inv TV2;
    simpl in H; inv H;
    try rewrite J in *; clear J;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
     simpl in *; try contradiction;
    destruct t; try solve [inv H1];
    try solve [constructor; try rewrite (negb_true _ H1); apply I]
  ].
 +
    destruct (typeof e1); inv TV1; destruct (typeof e2); inv TV2;
    simpl in H; inv H;
    rewrite ?J, ?J0 in *; clear J J0;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
     simpl in *; try contradiction;
    destruct t as [| [| | |] [|] | | | | | | |]; inv H4;
    simpl; constructor;
    try (rewrite peq_eq_block by auto; 
           rewrite sizeof_range_true by auto);
    try discriminate;
    try apply I.
 +
  rewrite <- tc_val_tc_val_PM in TV1,TV2|-*.
  eapply tc_val_sem_binarith'; eauto.
Qed.

Lemma typecheck_Omul_sound:
forall {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType Omul e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop Omul (typeof e1) (typeof e2)
       (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  rewrite den_isBinOpR in IBR.
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_mul in IBR |- *.
  unfold force_val2, force_val.
  eapply tc_val_sem_binarith'; eauto.
Qed.

Lemma typecheck_Odiv_sound:
forall {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType Odiv e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop Odiv (typeof e1) (typeof e2)
       (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  rewrite den_isBinOpR in IBR.
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_mul in IBR |- *.
  unfold force_val2, force_val.
  eapply (tc_val_sem_binarith' _ _ _ _ _ _ _ _ _ _ _ rho m); eauto.
  unfold binarithType'.
  destruct (classify_binarith' (typeof e1) (typeof e2)); eauto.
  + destruct s; destruct IBR; eauto.
  + destruct s; destruct IBR; eauto.
Qed.

Lemma typecheck_Omod_sound:
forall {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType Omod e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop Omod (typeof e1) (typeof e2)
       (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  rewrite den_isBinOpR in IBR.
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_mod in IBR |- *.
  unfold force_val2, force_val.
  unfold Cop2.sem_binarith.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' (typeof e1) (typeof e2)) eqn:?H.
  + solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H2, <- H0 in H;
    try solve [inv H].
    destruct s; destruct IBR as [?IBR ?IBR].
    - destruct IBR as [?IBR ?IBR].
      apply tc_bool_e in IBR0.
      simpl in IBR, IBR1 |- *; unfold_lift in IBR; unfold_lift in IBR1.
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3 | inv IBR].
      unfold both_int; simpl.
      apply denote_tc_nonzero_e in IBR; try rewrite IBR.
      apply denote_tc_nodivover_e in IBR1; try rewrite IBR1.
      simpl.
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
      simpl; auto.
    - apply tc_bool_e in IBR0.
      simpl in IBR |- *; unfold_lift in IBR.
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3 | inv IBR].
      unfold both_int; simpl.
      apply denote_tc_nonzero_e in IBR; try rewrite IBR.
      simpl.
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
      simpl; auto.
  + solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H2, <- H0 in H;
    try solve [inv H].
    - (* int long *)
      destruct s; destruct IBR as [?IBR ?IBR].
      * destruct IBR as [?IBR ?IBR].
        apply tc_bool_e in IBR0.
        simpl in IBR, IBR1 |- *; unfold_lift in IBR; unfold_lift in IBR1.
        destruct (eval_expr e1 rho), (eval_expr e2 rho);
          try solve [inv H1 | inv H3].
        unfold both_long; simpl.
        apply denote_tc_nonzero_e64 in IBR; try rewrite IBR.
        apply (denote_tc_nodivover_e64_il sg) in IBR1; try rewrite IBR1.
        simpl.
        destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
        simpl; auto.
      * apply tc_bool_e in IBR0.
        simpl in IBR |- *; unfold_lift in IBR.
        destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3 | inv IBR].
        unfold both_long; simpl.
        apply denote_tc_nonzero_e64 in IBR; try rewrite IBR.
        destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
        simpl; auto.
    - (* long int *)
      destruct s; destruct IBR as [?IBR ?IBR].
      * destruct IBR as [?IBR ?IBR].
        apply tc_bool_e in IBR0.
        simpl in IBR, IBR1 |- *; unfold_lift in IBR; unfold_lift in IBR1.
        destruct (eval_expr e1 rho), (eval_expr e2 rho);
          try solve [inv H1 | inv H3].
        unfold both_long; simpl.
        apply denote_tc_nonzero_e, (Int64_eq_repr_int_nonzero sg) in IBR; try rewrite IBR.
        apply (denote_tc_nodivover_e64_li sg) in IBR1; try rewrite IBR1.
        simpl.
        destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
        simpl; auto.
      * apply tc_bool_e in IBR0.
        simpl in IBR |- *; unfold_lift in IBR.
        destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3 | inv IBR].
        unfold both_long; simpl.
        apply denote_tc_nonzero_e, (Int64_eq_repr_int_nonzero sg) in IBR; try rewrite IBR.
        destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
        simpl; auto.
    - (* long long *)
      destruct s; destruct IBR as [?IBR ?IBR].
      * destruct IBR as [?IBR ?IBR].
        apply tc_bool_e in IBR0.
        simpl in IBR, IBR1 |- *; unfold_lift in IBR; unfold_lift in IBR1.
        destruct (eval_expr e1 rho), (eval_expr e2 rho);
          try solve [inv H1 | inv H3].
        unfold both_long; simpl.
        apply denote_tc_nonzero_e64 in IBR; try rewrite IBR.
        apply denote_tc_nodivover_e64_ll in IBR1; try rewrite IBR1.
        simpl.
        destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
        simpl; auto.
      * apply tc_bool_e in IBR0.
        simpl in IBR |- *; unfold_lift in IBR.
        destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3 | inv IBR].
        unfold both_long; simpl.
        apply denote_tc_nonzero_e64 in IBR; try rewrite IBR.
        destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
        simpl; auto.
  + inv IBR.
  + inv IBR.
  + inv IBR.
Qed.

Lemma typecheck_Oshift_sound:
 forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho))
   (OP: op = Oshl \/ op = Oshr),
   tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  replace
    ((denote_tc_assert (isBinOpResultType op e1 e2 t) rho) m)
  with
    ((denote_tc_assert
           match classify_shift' (typeof e1) (typeof e2) with
           | shift_case_ii _ =>
               tc_andp' (tc_ilt' e2 Int.iwordsize)
                 (tc_bool (is_int32_type t) (op_result_type (Ebinop op e1 e2 t)))
           | shift_case_il _ =>
               tc_andp' (tc_llt' e2 (Int64.repr 32))
                 (tc_bool (is_int32_type t) (op_result_type (Ebinop op e1 e2 t)))
           | shift_case_li _ =>
               tc_andp' (tc_ilt' e2 Int64.iwordsize')
                 (tc_bool (is_long_type t) (op_result_type (Ebinop op e1 e2 t)))
           | shift_case_ll _ =>
               tc_andp' (tc_llt' e2 Int64.iwordsize)
                 (tc_bool (is_long_type t) (op_result_type (Ebinop op e1 e2 t)))
           | _ => tc_FF (arg_type (Ebinop op e1 e2 t))
           end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP; subst; auto).
  destruct (classify_shift' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].
  + (* shift_ii *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl.
    - rewrite (denote_tc_igt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
    - rewrite (denote_tc_igt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
  + (* shift_ll *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl.
    - rewrite (denote_tc_lgt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
    - rewrite (denote_tc_lgt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
  + (* shift_il *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl.
    - rewrite (denote_tc_lgt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
    - rewrite (denote_tc_lgt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
  + (* shift_li *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl.
    - rewrite (denote_tc_igt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
    - rewrite (denote_tc_igt_e m) by assumption;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
Qed.

Lemma typecheck_Obin_sound:
 forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho))
   (OP: op = Oand \/ op = Oor \/ op = Oxor),
   tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
Proof.
  intros.
  replace
    ((denote_tc_assert (isBinOpResultType op e1 e2 t) rho) m)
  with
    ((denote_tc_assert
           match classify_binarith' (typeof e1) (typeof e2) with
           | bin_case_i _ => tc_bool (is_int32_type t) (op_result_type (Ebinop op e1 e2 t))
           | bin_case_l _ => tc_bool (is_long_type t) (op_result_type (Ebinop op e1 e2 t))
           | _ => tc_FF (arg_type (Ebinop op e1 e2 t))
           end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP as [| [ | ]]; subst; auto).
  destruct (classify_binarith' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].
  + (* bin_case_i *)
    apply tc_bool_e in IBR.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP as [| [|]]; subst; auto;
    simpl;
    unfold force_val, Cop2.sem_and, Cop2.sem_or, Cop2.sem_xor, Cop2.sem_binarith;
    rewrite classify_binarith_eq, H;
    simpl;
    destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
  + (* bin_case_l *)
    apply tc_bool_e in IBR.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H].
    - destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3].
      destruct OP as [| [|]]; subst; auto;
      simpl;
      unfold force_val, Cop2.sem_and, Cop2.sem_or, Cop2.sem_xor, Cop2.sem_binarith;
      rewrite classify_binarith_eq, H;
      simpl;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
    - destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3].
      destruct OP as [| [|]]; subst; auto;
      simpl;
      unfold force_val, Cop2.sem_and, Cop2.sem_or, Cop2.sem_xor, Cop2.sem_binarith;
      rewrite classify_binarith_eq, H;
      simpl;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
    - destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3].
      destruct OP as [| [|]]; subst; auto;
      simpl;
      unfold force_val, Cop2.sem_and, Cop2.sem_or, Cop2.sem_xor, Cop2.sem_binarith;
      rewrite classify_binarith_eq, H;
      simpl;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
Qed.

Lemma denote_tc_test_eq_Vint_l: forall m i v,
  (denote_tc_test_eq (Vint i) v) m ->
  i = Int.zero.
Proof.
  intros.
  unfold denote_tc_test_eq in H; simpl in H.
  destruct v; try solve [inv H]; simpl in H; tauto.
Qed.

Lemma denote_tc_test_eq_Vint_r: forall m i v,
  (denote_tc_test_eq v (Vint i)) m ->
  i = Int.zero.
Proof.
  intros.
  unfold denote_tc_test_eq in H; simpl in H.
  destruct v; try solve [inv H]; simpl in H; tauto.
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
  replace
    ((denote_tc_assert (isBinOpResultType op e1 e2 t) rho) m)
  with
    ((denote_tc_assert
           match classify_cmp' (typeof e1) (typeof e2) with
           | cmp_case_pp => tc_andp' (tc_andp' (tc_int_or_ptr_type (typeof e1)) 
                                      (tc_int_or_ptr_type (typeof e2)))
                                  (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
           | cmp_case_pl => 
                         tc_andp' (tc_int_or_ptr_type (typeof e1))
                            (check_pp_int' e1 (Ecast e2 (Tint I32 Unsigned noattr)) op t (Ebinop op e1 e2 t))
           | cmp_case_lp => 
                         tc_andp' (tc_int_or_ptr_type (typeof e2))
                            (check_pp_int' (Ecast e1 (Tint I32 Unsigned noattr)) e2 op t (Ebinop op e1 e2 t))
           | cmp_default =>
               tc_bool (is_numeric_type (typeof e1) && is_numeric_type (typeof e2) && is_int_type t)
                 (arg_type (Ebinop op e1 e2 t))
           end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP as [|]; subst; auto).
  replace
    (tc_val t (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)))
  with
    (tc_val t
      (force_val
        (match classify_cmp' (typeof e1) (typeof e2) with
         | cmp_case_pp => if orb (eqb_type (typeof e1) int_or_ptr_type)
                                 (eqb_type (typeof e2) int_or_ptr_type) 
            then (fun _ _ => None)
            else sem_cmp_pp (op_to_cmp op)
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
1,2,3:
  simpl in IBR; unfold_lift in IBR;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
                      apply tc_bool_e in H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]              
    end;
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |]; inv TV1; 
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv TV2;
    simpl in H; inv H;
    try (rewrite J in *; clear J);
    try (rewrite J0 in *; clear J0);
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
     simpl in *; try contradiction;
    repeat match goal with H: _ /\ _ |- _ => destruct H end;
    subst;
    destruct t as [| [| | |] [|] | | | | | | |];
    try solve [inv H2];
    try apply tc_val_of_bool;
    try solve [apply sem_cmp_pp_ip; auto; destruct OP; subst; auto];
    try solve [apply sem_cmp_pp_pi; auto; destruct OP; subst; auto];
    try solve [apply sem_cmp_pp_pp; auto; destruct OP; subst; auto].

  unfold sem_cmp_default.
  apply tc_bool_e in IBR.
  rewrite !andb_true_iff in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
  rewrite <- tc_val_tc_val_PM in TV1,TV2.
   apply tc_val_sem_cmp_binarith'; auto.
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
  replace
    ((denote_tc_assert (isBinOpResultType op e1 e2 t) rho) m)
  with
    ((denote_tc_assert
            match classify_cmp' (typeof e1) (typeof e2) with
              | cmp_default =>
                           tc_bool (is_numeric_type (typeof e1)
                                         && is_numeric_type (typeof e2)
                                          && is_int_type t)
                                             (arg_type (Ebinop op e1 e2 t))
	            | cmp_case_pp => 
                     tc_andp' (tc_andp' (tc_int_or_ptr_type (typeof e1)) 
                                      (tc_int_or_ptr_type (typeof e2)))
                       (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
              | cmp_case_pl => 
                     tc_andp' (tc_int_or_ptr_type (typeof e1))
                       (check_pp_int' e1 (Ecast e2 (Tint I32 Unsigned noattr)) op t (Ebinop op e1 e2 t))
              | cmp_case_lp => 
                     tc_andp' (tc_int_or_ptr_type (typeof e2))
                    (check_pp_int' (Ecast e1 (Tint I32 Unsigned noattr)) e2 op t (Ebinop op e1 e2 t))
              end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP as [| [| [|]]]; subst; auto).
  replace
    (tc_val t (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)))
  with
    (tc_val t
      (force_val
        (match classify_cmp' (typeof e1) (typeof e2) with
         | cmp_case_pp => if orb (eqb_type (typeof e1) int_or_ptr_type)
                                 (eqb_type (typeof e2) int_or_ptr_type) 
            then (fun _ _ => None)
            else sem_cmp_pp (op_to_cmp op)
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
1,2,3:  
    simpl in IBR; unfold_lift in IBR;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
                      apply tc_bool_e in H
    | H: negb (eqb_type ?A ?B) = true |- _ =>
             let J := fresh "J" in
              destruct (eqb_type A B) eqn:J; [inv H | clear H]              
    end;
    rewrite tc_val_tc_val_PM in TV1,TV2;
    destruct (typeof e1) as [| [| | |] [|] | | | | | | |];
    destruct (typeof e2) as [| [| | |] [|] | | | | | | |];
    simpl in H; inv H;
    inv TV1; inv TV2;
    try (rewrite J in *; clear J);
    try (rewrite J0 in *; clear J0);
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    simpl in *; try contradiction;
    repeat match goal with H: _ /\ _ |- _ => destruct H end;
    subst;
    destruct t as [| [| | |] [|] | | | | | | |];
    try solve [inv H2];
    try apply tc_val_of_bool;
    try solve [apply sem_cmp_pp_ip; auto; destruct OP as [| [| [|]]]; subst; auto];
    try solve [apply sem_cmp_pp_pi; auto; destruct OP as [| [| [|]]]; subst; auto];
    try solve [apply sem_cmp_pp_pp; auto; destruct OP as [| [| [|]]]; subst; auto];
    try solve [eapply sem_cmp_pp_pp'; eauto; destruct OP as [| [| [|]]]; subst; auto].

    unfold sem_cmp_default.
    apply tc_bool_e in IBR.
    rewrite !andb_true_iff in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_val_sem_cmp_binarith'; auto.
Qed.

Lemma typecheck_binop_sound:
forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: tc_val (typeof e2) (eval_expr e2 rho))
   (TV1: tc_val (typeof e1) (eval_expr e1 rho)),
   tc_val t
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho)).
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

