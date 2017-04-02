Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.Cop2.
Require Import veric.binop_lemmas2.
Import Cop.

Lemma denote_tc_nonzero_e:
 forall i m, app_pred (denote_tc_nonzero (Vint i)) m -> Int.eq i Int.zero = false.
Proof.
simpl; intros . destruct (Int.eq i Int.zero); auto; contradiction.
Qed.

Lemma denote_tc_nodivover_e:
 forall i j m, app_pred (denote_tc_nodivover (Vint i) (Vint j)) m ->
   Int.eq i (Int.repr Int.min_signed) && Int.eq j Int.mone = false.
Proof.
simpl; intros.
destruct (Int.eq i (Int.repr Int.min_signed) && Int.eq j Int.mone); try reflexivity; contradiction.
Qed.

Lemma denote_tc_nonzero_e64:
 forall i m, app_pred (denote_tc_nonzero (Vlong i)) m -> Int64.eq i Int64.zero = false.
Proof.
simpl; intros . destruct (Int64.eq i Int64.zero); auto; contradiction.
Qed.

Lemma denote_tc_nodivover_e64_ll:
 forall i j m, app_pred (denote_tc_nodivover (Vlong i) (Vlong j)) m ->
   Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone = false.
Proof.
simpl; intros.
destruct (Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone); try reflexivity; contradiction.
Qed.

Lemma denote_tc_nodivover_e64_il:
 forall s i j m, app_pred (denote_tc_nodivover (Vint i) (Vlong j)) m ->
   Int64.eq (cast_int_long s i) (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone = false.
Proof.
simpl; intros.
destruct (Int64.eq (cast_int_long s i) (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone); try reflexivity; contradiction.
Qed.

Lemma denote_tc_nodivover_e64_li:
 forall s i j m, app_pred (denote_tc_nodivover (Vlong i) (Vint j)) m ->
   Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq (cast_int_long s j) Int64.mone = false.
Proof.
simpl; intros.
destruct (Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq (cast_int_long s j) Int64.mone); try reflexivity; contradiction.
Qed.

Lemma Int64_eq_repr_signed32_nonzero:
  forall i, Int.eq i Int.zero = false ->
             Int64.eq (Int64.repr (Int.signed i)) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
rewrite Int64.eq_false; auto.
contradict H0.
unfold Int64.zero in H0.
assert (Int64.signed (Int64.repr (Int.signed i)) = Int64.signed (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.signed_repr in H.
rewrite Int64.signed_repr in H.
rewrite <- (Int.repr_signed i).
rewrite H. reflexivity.
pose proof (Int64.signed_range Int64.zero).
rewrite Int64.signed_zero in H1.
auto.
pose proof (Int.signed_range i).
clear - H1.
destruct H1.
split.
apply Z.le_trans with Int.min_signed; auto.
compute; congruence.
apply Z.le_trans with Int.max_signed; auto.
compute; congruence.
Qed.


Lemma Int64_eq_repr_unsigned32_nonzero:
  forall i, Int.eq i Int.zero = false ->
             Int64.eq (Int64.repr (Int.unsigned i)) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
rewrite Int64.eq_false; auto.
contradict H0.
unfold Int64.zero in H0.
assert (Int64.unsigned (Int64.repr (Int.unsigned i)) = Int64.unsigned (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.unsigned_repr in H.
rewrite Int64.unsigned_repr in H.
rewrite <- (Int.repr_unsigned i).
rewrite H. reflexivity.
split; compute; congruence.
pose proof (Int.unsigned_range i).
clear - H1.
destruct H1.
split; auto.
unfold Int64.max_unsigned.
apply Z.le_trans with Int.modulus.
omega.
compute; congruence.
Qed.

Lemma Int64_eq_repr_int_nonzero:
  forall s i, Int.eq i Int.zero = false ->
    Int64.eq (cast_int_long s i) Int64.zero = false.
Proof.
  intros.
  destruct s.
  + apply Int64_eq_repr_signed32_nonzero; auto.
  + apply Int64_eq_repr_unsigned32_nonzero; auto.
Qed.

Lemma denote_tc_igt_e:
  forall m i j, app_pred (denote_tc_igt j (Vint i)) m ->
        Int.ltu i j = true.
Proof.
intros.
hnf in H. destruct (Int.ltu i j); auto; contradiction.
Qed.

Lemma denote_tc_iszero_long_e:
 forall m i,
  app_pred (denote_tc_iszero (Vlong i)) m ->
  Int.eq (Int.repr (Int64.unsigned i)) Int.zero = true.
Proof.
intros.
hnf in H.
destruct (Int.eq (Int.repr (Int64.unsigned i)) Int.zero);
  auto; contradiction.
Qed.

Lemma sem_cmp_pp_pp:
  forall c b i b0 i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
    tc_val
      (Tint ii ss aa)
        match sem_cmp_pp c (Vptr b i) (Vptr b0 i0) with
        | Some v' => v'
        | None => Vundef
        end.
Proof.
intros; destruct OP; subst; unfold sem_cmp_pp; simpl.
+ destruct (eq_block b b0); [ destruct (Int.eq i i0) |];
  destruct ii,ss; simpl; try split; auto;
  rewrite <- Z.leb_le; reflexivity.
+ destruct (eq_block b b0); [ destruct (Int.eq i i0) |];
  destruct ii,ss; simpl; try split; auto;
  rewrite <- Z.leb_le; reflexivity.
Qed.

Lemma sem_cmp_pp_pp':
  forall c b i b0 i0 ii ss aa m
    (OP: c = Cle \/ c = Clt \/ c = Cge \/ c = Cgt),
    (denote_tc_test_order (Vptr b i) (Vptr b0 i0)) m ->
    tc_val (Tint ii ss aa)
      match sem_cmp_pp c (Vptr b i) (Vptr b0 i0) with
      | Some v' => v'
      | None => Vundef
      end.
Proof.
  intros; destruct OP as [| [| [|]]]; subst; unfold sem_cmp_pp; simpl;
  unfold denote_tc_test_order, test_order_ptrs in H; simpl in H.
  + unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i0 i);
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
  + unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i i0);
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
  + unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i i0);
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
  + unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i0 i);
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
Qed.

Lemma sem_cmp_pp_ip:
  forall c b i i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
  i = Int.zero ->
 tc_val (Tint ii ss aa)
  match sem_cmp_pp c (Vint i)  (Vptr b i0)  with
  | Some v' => v'
  | None => Vundef
  end.
Proof.
  intros; destruct OP; subst; unfold sem_cmp_pp; simpl.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
Qed.

Lemma sem_cmp_pp_pi:
  forall c b i i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
  i = Int.zero ->
 tc_val (Tint ii ss aa)
  match sem_cmp_pp c (Vptr b i0)  (Vint i)  with
  | Some v' => v'
  | None => Vundef
  end.
Proof.
  intros; destruct OP; subst; unfold sem_cmp_pp; simpl.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; try split; auto;
    rewrite <- Z.leb_le; reflexivity.
Qed.
(*
Lemma sem_cmp_pp_ppy:
  forall b i i0 ii ss aa,
  i = Int.zero ->
 tc_val (Tint ii ss aa)
  match sem_cmp_pp Ceq (Vptr b i0)  (Vint i)  with
  | Some v' => v'
  | None => Vundef
  end.
Proof.
intros; unfold sem_cmp_pp; simpl.
subst i. rewrite Int.eq_true.
destruct ii,ss; simpl; try split; auto;
rewrite <- Z.leb_le; reflexivity.
Qed.

Lemma sem_cmp_pp_ppy':
  forall b i i0 ii ss aa,
  i = Int.zero ->
 tc_val (Tint ii ss aa)
  match sem_cmp_pp Cne (Vptr b i0) (Vint i)  with
  | Some v' => v'
  | None => Vundef
  end.
Proof.
intros; unfold sem_cmp_pp; simpl.
subst i. rewrite Int.eq_true.
destruct ii,ss; simpl; try split; auto;
rewrite <- Z.leb_le; reflexivity.
Qed.
*)
Lemma eq_block_true: forall b1 b2 i1 i2 A (a b: A),
    is_true (sameblock (Vptr b1 i1) (Vptr b2 i2)) ->
    (if eq_block b1 b2 then a else b) = a.
Proof.
  unfold sameblock, eq_block.
  intros.
  apply is_true_e in H.
  destruct (peq b1 b2); auto.
  inv H.
Qed.

Lemma sizeof_range_true {CS: composite_env}: forall t A (a b: A),
    negb (Z.eqb (sizeof t) 0) = true ->
    Z.leb (sizeof t) Int.max_signed = true ->
    (if zlt 0 (sizeof t) && zle (sizeof t) Int.max_signed then a else b) = a.
Proof.
  intros.
  rewrite negb_true_iff in H.
  rewrite Z.eqb_neq in H.
  pose proof sizeof_pos t.
  rewrite <- Zle_is_le_bool in H0.
  destruct (zlt 0 (sizeof t)); [| omega].
  destruct (zle (sizeof t) Int.max_signed); [| omega]. 
  reflexivity.
Qed.

Inductive tc_val_PM: type -> val -> Prop :=
| tc_val_PM_Tint: forall sz sg a v, is_int sz sg v -> tc_val_PM (Tint sz sg a) v
| tc_val_PM_Tlong: forall s a v, is_long v -> tc_val_PM (Tlong s a) v
| tc_val_PM_Tfloat_single: forall a v, is_single v -> tc_val_PM (Tfloat F32 a) v
| tc_val_PM_Tfloat_double: forall a v, is_float v -> tc_val_PM (Tfloat F64 a) v
| tc_val_PM_Tpointer: forall t a v, is_pointer_or_null v -> tc_val_PM (Tpointer t a) v
| tc_val_PM_Tarray: forall t n a v, is_pointer_or_null v -> tc_val_PM (Tarray t n a) v
| tc_val_PM_Tfunction: forall ts t a v, is_pointer_or_null v -> tc_val_PM (Tfunction ts t a) v
| tc_val_PM_Tstruct: forall i a v, isptr v -> tc_val_PM (Tstruct i a) v
| tc_val_PM_Tunion: forall i a v, isptr v -> tc_val_PM (Tunion i a) v.

Lemma tc_val_tc_val_PM: forall t v, tc_val t v <-> tc_val_PM t v.
Proof.
  intros.
  split; intros.
  + destruct t as [| | | [ | ] ? | | | | |]; try (inv H); constructor; auto.
  + inversion H; subst; auto.
Qed.

Inductive tc_val_PM': type -> val -> Prop :=
| tc_val_PM'_Tint: forall t0 sz sg a v, stupid_typeconv t0 = Tint sz sg a -> is_int sz sg v -> tc_val_PM' t0 v
| tc_val_PM'_Tlong: forall t0 s a v, stupid_typeconv t0 = Tlong s a -> is_long v -> tc_val_PM' t0 v
| tc_val_PM'_Tfloat_single: forall t0 a v, stupid_typeconv t0 = Tfloat F32 a -> is_single v -> tc_val_PM' t0 v
| tc_val_PM'_Tfloat_double: forall t0 a v, stupid_typeconv t0 = Tfloat F64 a -> is_float v -> tc_val_PM' t0 v
| tc_val_PM'_Tpointer: forall t0 t a v, stupid_typeconv t0 = Tpointer t a -> is_pointer_or_null v -> tc_val_PM' t0 v
| tc_val_PM'_Tstruct: forall t0 i a v, stupid_typeconv t0 = Tstruct i a -> isptr v -> tc_val_PM' t0 v
| tc_val_PM'_Tunion: forall t0 i a v, stupid_typeconv t0 = Tunion i a -> isptr v -> tc_val_PM' t0 v.

Lemma tc_val_tc_val_PM': forall t v, tc_val t v <-> tc_val_PM' t v.
Proof.
  intros.
  split; intros.
  + destruct t as [| | | [ | ] ? | | | | |]; try (inv H).
    - eapply tc_val_PM'_Tint; eauto; reflexivity.
    - eapply tc_val_PM'_Tlong; eauto; reflexivity.
    - eapply tc_val_PM'_Tfloat_single; eauto; reflexivity.
    - eapply tc_val_PM'_Tfloat_double; eauto; reflexivity.
    - eapply tc_val_PM'_Tpointer; eauto; reflexivity.
    - eapply tc_val_PM'_Tpointer; eauto; reflexivity.
    - eapply tc_val_PM'_Tpointer; eauto; reflexivity.
    - eapply tc_val_PM'_Tstruct; eauto; reflexivity.
    - eapply tc_val_PM'_Tunion; eauto; reflexivity.
  + inversion H; subst;
    destruct t as [| | | [ | ] ? | | | | |]; try (inv H0);
    auto.
Qed.

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
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_add in IBR |- *.
  rewrite classify_add_eq.
  destruct (classify_add' (typeof e1) (typeof e2)) eqn:?H;
  unfold force_val2, force_val.
  + simpl in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_bool_e in IBR0.
    apply tc_bool_e in IBR1.
    unfold classify_add' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR].
    destruct t; try solve [inv IBR1]; simpl; auto.
  + simpl in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_bool_e in IBR0.
    apply tc_bool_e in IBR1.
    unfold classify_add' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR].
    destruct t; try solve [inv IBR1]; simpl; auto.
  + simpl in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_bool_e in IBR0.
    apply tc_bool_e in IBR1.
    unfold classify_add' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR];
    destruct t; try solve [inv IBR1]; simpl; auto.
  + simpl in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_bool_e in IBR0.
    apply tc_bool_e in IBR1.
    unfold classify_add' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR];
    destruct t; try solve [inv IBR1]; simpl; auto.
  + unfold sem_add_default.
    eapply tc_val_sem_binarith'; eauto.
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
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_sub in IBR |- *.
  rewrite classify_sub_eq.
  destruct (classify_sub' (typeof e1) (typeof e2)) eqn:?H;
  unfold force_val2, force_val.
  + simpl in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_bool_e in IBR0.
    apply tc_bool_e in IBR1.
    unfold classify_sub' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR].
    destruct t; try solve [inv IBR1]; simpl; auto.
  + simpl in IBR.
    destruct IBR as [[[[[[?IBR ?IBR] ?IBR] ?IBR] ?IBR] ?IBR] ?IBR].
    apply tc_bool_e in IBR2.
    apply tc_bool_e in IBR3.
    apply tc_bool_e in IBR4.
    apply tc_bool_e in IBR5.
    unfold classify_sub' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR].
    destruct t as [| [| | |] [|] | | | | | | |]; try solve [inv IBR2]; simpl;
    erewrite eq_block_true by eauto; rewrite sizeof_range_true by auto;
    simpl; auto.
  + simpl in IBR.
    destruct IBR as [[?IBR ?IBR] ?IBR].
    apply tc_bool_e in IBR0.
    apply tc_bool_e in IBR1.
    unfold classify_sub' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3 | inv IBR].
    destruct t; try solve [inv IBR1]; simpl; auto.
  + unfold sem_sub_default.
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
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Cop2.sem_div, Cop2.sem_binarith in IBR |- *.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' (typeof e1) (typeof e2)) eqn:?H;
  unfold force_val2, force_val.
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
  + apply tc_bool_e in IBR.
    destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR].
    destruct f; try solve [inv IBR].
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H2, <- H0 in H;
    try solve [inv H];
    unfold both_float;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    - destruct sg; simpl; auto.
    - destruct s; simpl; auto.
    - simpl; auto.
    - destruct sg; simpl; auto.
    - destruct s; simpl; auto.
    - simpl; auto.
    - simpl; auto.
  + apply tc_bool_e in IBR.
    destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR].
    destruct f; try solve [inv IBR].
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H2, <- H0 in H;
    try solve [inv H];
    unfold both_float;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    - destruct sg; simpl; auto.
    - destruct s; simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
  + inv IBR.
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
           | _ => tc_FF (arg_type (Ebinop op e1 e2 t))
           end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP; subst; auto).
  destruct (classify_shift' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].
  destruct IBR as [?IBR ?IBR].
  apply tc_bool_e in IBR0.
  simpl in IBR; unfold_lift in IBR.
  solve_tc_val TV1;
  solve_tc_val TV2;
  rewrite <- H0, <- H2 in H;
  try solve [inv H].
  + (* shift_ii *)
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
  (* TODO: Other shift cases to be added *)
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
           | _ => tc_FF (arg_type (Ebinop op e1 e2 t))
           end rho) m)
  in IBR
  by (rewrite den_isBinOpR; destruct OP as [| [ | ]]; subst; auto).
  destruct (classify_binarith' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].
  apply tc_bool_e in IBR.
  simpl in IBR; unfold_lift in IBR.
  solve_tc_val TV1;
  solve_tc_val TV2;
  rewrite <- H0, <- H2 in H;
  try solve [inv H].
  + (* bin_case_i *)
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP as [| [|]]; subst; auto;
    simpl;
    unfold force_val, Cop2.sem_and, Cop2.sem_or, Cop2.sem_xor, Cop2.sem_binarith;
    rewrite classify_binarith_eq, H;
    simpl;
    destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
  (* TODO: Other bin cases to be added *)
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
           | cmp_case_pp => check_pp_int' e1 e2 op t (Ebinop op e1 e2 t)
           | cmp_case_pl => check_pp_int' e1 (Ecast e2 (Tint I32 Unsigned noattr)) op t (Ebinop op e1 e2 t)
           | cmp_case_lp => check_pp_int' (Ecast e1 (Tint I32 Unsigned noattr)) e2 op t (Ebinop op e1 e2 t)
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
         | cmp_case_pp => sem_cmp_pp (op_to_cmp op)
         | cmp_case_pl => sem_cmp_pl (op_to_cmp op)
         | cmp_case_lp => sem_cmp_lp (op_to_cmp op)
         | cmp_default => sem_cmp_default (op_to_cmp op) (typeof e1) (typeof e2)
         end (eval_expr e1 rho) (eval_expr e2 rho))))
  by (destruct OP as [|]; subst; rewrite <- classify_cmp_eq; auto).
  destruct (classify_cmp' (typeof e1) (typeof e2)) eqn:?H; try solve [inv IBR].
  + (* cmp_case_pp *)
    replace (check_pp_int' e1 e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' e1 e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP; subst; auto).
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    unfold classify_cmp' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H];
    destruct OP as [|]; subst;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3];
    destruct t as [| | | | | | | |]; try solve [inv IBR0];
    unfold force_val, op_to_cmp;
    try pose proof denote_tc_test_eq_Vint_l _ _ _ IBR;
    try pose proof denote_tc_test_eq_Vint_r _ _ _ IBR;
    first [ apply sem_cmp_pp_pp; solve [auto]
          | apply sem_cmp_pp_ip; solve [auto]
          | apply sem_cmp_pp_pi; solve [auto]
          | subst; apply tc_val_of_bool].
  + (* cmp_case_pl *)
    replace (check_pp_int' e1 (Ecast e2 (Tint I32 Unsigned noattr)) op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' e1 (Ecast e2 (Tint I32 Unsigned noattr)))
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP; subst; auto).
    simpl in IBR.
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    unfold sem_cmp_pl.
    unfold classify_cmp' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (typeof e2); inv H2;
    simpl force_val1 in IBR.
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3];
    destruct t as [| | | | | | | |]; try solve [inv IBR0];
    unfold force_val, op_to_cmp;
    destruct OP as [|]; subst;
    try pose proof denote_tc_test_eq_Vint_l _ _ _ IBR;
    try pose proof denote_tc_test_eq_Vint_r _ _ _ IBR;
    first [ apply sem_cmp_pp_pp; solve [auto]
          | apply sem_cmp_pp_ip; solve [auto]
          | apply sem_cmp_pp_pi; solve [auto]
          | subst; apply tc_val_of_bool].
  + (* cmp_case_lp *)
    replace (check_pp_int' (Ecast e1 (Tint I32 Unsigned noattr)) e2 op t (Ebinop op e1 e2 t))
    with (tc_andp' (tc_test_eq' (Ecast e1 (Tint I32 Unsigned noattr)) e2)
                   (tc_bool (is_int_type t) (op_result_type (Ebinop op e1 e2 t))))
    in IBR
    by (unfold check_pp_int'; destruct OP; subst; auto).
    simpl in IBR.
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    unfold sem_cmp_lp.
    unfold classify_cmp' in H.
    solve_tc_val' TV1;
    solve_tc_val' TV2;
    rewrite ?H0, ?H2 in H;
    try solve [inv H].
    destruct (typeof e1); inv H0;
    simpl force_val1 in IBR.
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
    try solve [inv H1 | inv H3];
    destruct t as [| | | | | | | |]; try solve [inv IBR0];
    unfold force_val, op_to_cmp;
    destruct OP as [|]; subst;
    try pose proof denote_tc_test_eq_Vint_l _ _ _ IBR;
    try pose proof denote_tc_test_eq_Vint_r _ _ _ IBR;
    first [ apply sem_cmp_pp_pp; solve [auto]
          | apply sem_cmp_pp_ip; solve [auto]
          | apply sem_cmp_pp_pi; solve [auto]
          | subst; apply tc_val_of_bool].
  + unfold sem_cmp_default.
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
destruct op;
(*try abstract ( *)
  intros;
  rewrite den_isBinOpR in IBR; simpl in IBR;
 unfold binarithType in IBR;
 destruct (typeof e1) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ] eqn:TE1;
 try contradiction IBR;
 destruct (typeof e2) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ] eqn:TE2;
 simpl in IBR;
 rewrite ?TE1, ?TE2 in IBR; simpl in IBR; clear TE1 TE2;
 match type of IBR with context [@liftx] => unfold_lift in IBR | _ => idtac end;
 try contradiction IBR;
 try simple apply tc_bool_e in IBR;  try discriminate IBR;
 destruct (eval_expr e1 rho); try solve [contradiction TV1];
 destruct (eval_expr e2 rho); try solve [contradiction TV2].

 clear - IBR;
 destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction IBR; try discriminate IBR;
 simpl; unfold Cop2.sem_div, Cop2.sem_mod,
 Cop2.sem_binarith, Cop2.sem_cast, Cop2.sem_shift,
 force_val, sem_shift_ii, both_int, both_long, both_float,
 sem_cmp_lp, sem_cmp_pl, cast_out_long; simpl;
 repeat (let H := fresh in revert IBR; intros [IBR H];
                try contradiction IBR;
                try contradiction H;
                try (simple apply tc_bool_e in IBR; try discriminate IBR);
                try (simple apply denote_tc_nonzero_e in IBR; try rewrite IBR);
                try (simple apply denote_tc_nodivover_e in H; try rewrite H);
                try (simple apply denote_tc_nonzero_e64 in IBR; try rewrite IBR);
                try (simple apply denote_tc_nodivover_e64 in H; try rewrite H);
                try (simple apply tc_bool_e in H; try discriminate H));
    try simple apply eq_refl;
    try simple apply tc_val_of_bool;
    try (simple apply sem_cmp_pp_pp; solve [auto]);
    try (simple eapply sem_cmp_pp_pp'; solve [eauto]);
    try (simple apply sem_cmp_pp_ip; solve [eauto]);
    try (simple apply sem_cmp_pp_pi; solve [auto]);
    try (rewrite Int64_eq_repr_signed32_nonzero by assumption; reflexivity);
    try (rewrite Int64_eq_repr_unsigned32_nonzero by assumption; reflexivity);
    try (rewrite (denote_tc_igt_e m) by assumption; reflexivity);
    try (rewrite (denote_tc_iszero_long_e m) by assumption; reflexivity);
    try (unfold Cop2.sem_sub; simpl; erewrite eq_block_true by eauto; rewrite sizeof_range_true by auto; reflexivity
).
Time Qed. (* 61.5 sec *)





