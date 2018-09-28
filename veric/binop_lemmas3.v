Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Clight_Cop2.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.binop_lemmas2.

Lemma denote_tc_nonzero_e:
 forall i m, app_pred (denote_tc_nonzero (Vint i)) m -> i <> Int.zero.
Proof.
simpl; auto .
Qed.

Lemma denote_tc_nodivover_e:
 forall i j m, app_pred (denote_tc_nodivover (Vint i) (Vint j)) m ->
   ~ (i =Int.repr Int.min_signed /\ j = Int.mone).
Proof.
simpl; auto.
Qed.

Lemma denote_tc_nonzero_e64:
 forall i m, app_pred (denote_tc_nonzero (Vlong i)) m -> i <> Int64.zero.
Proof.
simpl; auto.
Qed.

Lemma denote_tc_nodivover_e64_ll:
 forall i j m, app_pred (denote_tc_nodivover (Vlong i) (Vlong j)) m ->
   ~ (i =Int64.repr Int64.min_signed /\ j = Int64.mone).
Proof.
simpl; auto.
Qed.

Lemma denote_tc_nodivover_e64_il:
  (* This is a rather vacuous lemma, since the premise is simply True *)
 forall s i j m, app_pred (denote_tc_nodivover (Vint i) (Vlong j)) m ->
   ~ (cast_int_long s i = Int64.repr Int64.min_signed /\ j = Int64.mone).
Proof.
simpl; intros.
intros [? ?].
subst.
destruct s; simpl in *.
*
pose proof (@f_equal _ _ Int64.signed _ _ H0).
rewrite Int64.signed_repr in H1.
rewrite Int64.signed_repr in H1.
pose proof (Int.signed_range i).
rewrite H1 in H2.
destruct H2.
compute in H2. apply H2; auto.
compute; split; congruence.
pose proof (Int.signed_range i).
clear - H2. forget (Int.signed i) as a.
destruct H2.
split; eapply Z.le_trans; try eassumption.
compute; congruence.
compute; congruence.
*
pose proof (@f_equal _ _ Int64.unsigned _ _ H0).
rewrite Int64.unsigned_repr in H1.
replace (Int64.repr Int64.min_signed) 
  with (Int64.repr (Int64.modulus + Int64.min_signed)) in H1.
rewrite Int64.unsigned_repr in H1.
pose proof (Int.unsigned_range i).
rewrite H1 in H2.
destruct H2.
compute in H2. apply H2; auto.
compute; split; congruence.
apply Int64.eqm_samerepr.
rewrite <- Z.add_0_l.
apply Int64.eqm_add.
unfold Int64.eqm.
exists 1. reflexivity.
apply Int64.eqm_refl.
clear.
pose proof (Int.unsigned_range i).
destruct H; split; auto.
assert (Int.modulus < Int64.max_unsigned).
compute; auto.
omega.
Qed.

Lemma denote_tc_nodivover_e64_li:
 forall s i j m, app_pred (denote_tc_nodivover (Vlong i) (Vint j)) m ->
   ~ (i = Int64.repr Int64.min_signed /\ cast_int_long s j = Int64.mone).
Proof.
simpl; intros.
contradict H.
destruct H; split; auto.
clear - H0.
destruct s; simpl in *.
*
unfold Int64.mone in H0.
pose proof (@f_equal _ _ Int64.signed _ _ H0).
clear H0.
rewrite Int64.signed_repr in H.
change (Int.signed j = -1) in H.
rewrite <- (Int.repr_signed j).
rewrite H. reflexivity.
clear H.
pose proof (Int.signed_range j).
destruct H.
split; eapply Z.le_trans; try eassumption.
compute. congruence. compute. congruence.
*
unfold Int64.mone in H0.
pose proof (@f_equal _ _ Int64.signed _ _ H0).
clear H0.
rewrite Int64.signed_repr in H.
change (Int.unsigned j = -1) in H.
pose proof (Int.unsigned_range j).
rewrite H in H0.
destruct H0. compute in H0. congruence.
pose proof (Int.unsigned_range j).
destruct H0.
split.
eapply Z.le_trans; try eassumption.
compute. congruence.
assert (Int.modulus < Int64.max_signed).
compute. auto.
omega.
Qed.

Lemma Int64_eq_repr_signed32_nonzero:
  forall i, i <> Int.zero ->
             Int64.repr (Int.signed i) <> Int64.zero.
Proof.
intros.
contradict H.
rename H into H0.
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

(*
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
*)

Lemma Int64_eq_repr_unsigned32_nonzero:
  forall i, i <> Int.zero ->
             Int64.repr (Int.unsigned i) <> Int64.zero.
Proof.
intros.
rename H into H0.
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

(*

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
*)

Lemma Int64_eq_repr_int_nonzero:
  forall s i, i <> Int.zero ->
    cast_int_long s i <> Int64.zero.
Proof.
  intros.
  destruct s.
  + apply Int64_eq_repr_signed32_nonzero; auto.
  + apply Int64_eq_repr_unsigned32_nonzero; auto.
Qed.

(*
Lemma Int64_eq_repr_int_nonzero:
  forall s i, Int.eq i Int.zero = false ->
    Int64.eq (cast_int_long s i) Int64.zero = false.
Proof.
  intros.
  destruct s.
  + apply Int64_eq_repr_signed32_nonzero; auto.
  + apply Int64_eq_repr_unsigned32_nonzero; auto.
Qed.
*)

Lemma denote_tc_igt_e:
  forall m i j, app_pred (denote_tc_igt j (Vint i)) m ->
        Int.unsigned i < Int.unsigned j.
Proof. auto. Qed.

Lemma denote_tc_lgt_e:
  forall m i j, app_pred (denote_tc_lgt j (Vlong i)) m ->
        Int64.unsigned i < Int64.unsigned j.
Proof. auto. Qed.

Lemma denote_tc_iszero_long_e:
 forall m i,
  app_pred (denote_tc_iszero (Vlong i)) m -> i = Int64.zero.
Proof.
intros.
hnf in H.
pose proof (Int64.eq_spec i Int64.zero).
destruct (Int64.eq i Int64.zero); try contradiction.
auto.
Qed.

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


Lemma Int64repr_Intsigned_zero:
  forall i, Int64.repr (Int.signed i) = Int64.zero -> i=Int.zero.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero).
destruct (Int.eq i Int.zero) eqn:?; auto.
apply Int64_eq_repr_signed32_nonzero in H0.
contradiction.
Qed.

Lemma Int64repr_Intunsigned_zero:
  forall i, Int64.repr (Int.unsigned i) = Int64.zero -> i=Int.zero.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero).
destruct (Int.eq i Int.zero) eqn:?; auto.
apply Int64_eq_repr_unsigned32_nonzero in H0.
contradiction.
Qed.

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

Lemma sizeof_range_true {CS: composite_env}: forall t A (a b: A) (max: Z),
    negb (Z.eqb (sizeof t) 0) = true ->
    Z.leb (sizeof t) max = true ->
    (if zlt 0 (sizeof t) && zle (sizeof t) max then a else b) = a.
Proof.
  intros.
  rewrite negb_true_iff in H.
  rewrite Z.eqb_neq in H.
  pose proof sizeof_pos t.
  rewrite <- Zle_is_le_bool in H0.
  destruct (zlt 0 (sizeof t)); [| omega].
  destruct (zle (sizeof t) max); [| omega]. 
  reflexivity.
Qed.

Inductive tc_val_PM: type -> val -> Prop :=
| tc_val_PM_Tint: forall sz sg a v, is_int sz sg v -> tc_val_PM (Tint sz sg a) v
| tc_val_PM_Tlong: forall s a v, is_long v -> tc_val_PM (Tlong s a) v
| tc_val_PM_Tfloat_single: forall a v, is_single v -> tc_val_PM (Tfloat F32 a) v
| tc_val_PM_Tfloat_double: forall a v, is_float v -> tc_val_PM (Tfloat F64 a) v
| tc_val_PM_Tpointer: forall t a v, 
          (if eqb_type (Tpointer t a) int_or_ptr_type
           then is_pointer_or_integer
           else is_pointer_or_null) v -> 
          tc_val_PM (Tpointer t a) v
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
| tc_val_PM'_Tint: forall t0 sz sg a v, t0 = Tint sz sg a -> is_int sz sg v -> tc_val_PM' t0 v
| tc_val_PM'_Tlong: forall t0 s a v, stupid_typeconv t0 = Tlong s a -> is_long v -> tc_val_PM' t0 v
| tc_val_PM'_Tfloat_single: forall t0 a v, stupid_typeconv t0 = Tfloat F32 a -> is_single v -> tc_val_PM' t0 v
| tc_val_PM'_Tfloat_double: forall t0 a v, stupid_typeconv t0 = Tfloat F64 a -> is_float v -> tc_val_PM' t0 v
| tc_val_PM'_Tpointer: forall t0 t a v, 
  stupid_typeconv t0 = Tpointer t a -> 
  (if eqb_type t0 int_or_ptr_type
           then is_pointer_or_integer
           else is_pointer_or_null) v -> 
  tc_val_PM' t0 v
| tc_val_PM'_Tstruct: forall t0 i a v, stupid_typeconv t0 = Tstruct i a -> isptr v -> tc_val_PM' t0 v
| tc_val_PM'_Tunion: forall t0 i a v, stupid_typeconv t0 = Tunion i a -> isptr v -> tc_val_PM' t0 v.

Lemma tc_val_tc_val_PM': forall t v, tc_val t v <-> tc_val_PM' t v.
Proof.
  intros.
  split; intros.
  + destruct t as [| | | [ | ] ? | | | | |]; try (inv H).
    - destruct s; eapply tc_val_PM'_Tint; eauto.
    - eapply tc_val_PM'_Tlong; eauto; reflexivity.
    - eapply tc_val_PM'_Tfloat_single; eauto; reflexivity.
    - eapply tc_val_PM'_Tfloat_double; eauto; reflexivity.
    - eapply tc_val_PM'_Tpointer; eauto; reflexivity.
    - eapply tc_val_PM'_Tpointer; eauto; reflexivity.
    - eapply tc_val_PM'_Tpointer; eauto; reflexivity.
    - eapply tc_val_PM'_Tstruct; eauto; reflexivity.
    - eapply tc_val_PM'_Tunion; eauto; reflexivity.
  + inversion H; subst; auto;
    destruct t as [| | | [ | ] ? | | | | |]; try (inv H0);
    auto.
    destruct i; inv H3.
    destruct i; inv H3.
    destruct i; inv H3.
    destruct i; inv H3.
    destruct i0; inv H3.
    destruct i0; inv H3.
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
      (Clight_Cop2.sem_binarith
        (fun s n1 n2 => Some (Vint (sem_int s n1 n2)))
        (fun s n1 n2 => Some (Vlong (sem_long s n1 n2)))
        (fun n1 n2 => Some (Vfloat (sem_float n1 n2)))
        (fun n1 n2 => Some (Vsingle (sem_single n1 n2)))
        t1 t2 v1 v2)).
Proof.
  intros.
  unfold binarithType' in H.
  unfold Clight_Cop2.sem_binarith.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' t1 t2) eqn:?H;
  try solve [inv H]; apply tc_bool_e in H;
  destruct t1 as [|  [| | |] [|] | | [ | ] ? | | | | |]; try discriminate H0;
  destruct t2 as [|  [| | |] [|] | | [ | ] ? | | | | |]; try inv H0;
  try contradiction;
  destruct v1; try solve [inv TV1];
  destruct v2; try solve [inv TV2];
  destruct t as [| [| | |] [|] ? | | [|] | | | | |]; inv H; simpl; auto; apply I.
Qed.

Lemma tc_val_sem_cmp_binarith': forall sem_int sem_long sem_float sem_single t1 t2 t v1 v2
  (TV2: tc_val t2 v2)
  (TV1: tc_val t1 v1),
  is_numeric_type t1 = true ->
  is_numeric_type t2 = true ->
  is_int_type t = true ->
  tc_val t
    (force_val
      (Clight_Cop2.sem_binarith
        (fun s n1 n2 => Some (Val.of_bool (sem_int s n1 n2)))
        (fun s n1 n2 => Some (Val.of_bool (sem_long s n1 n2)))
        (fun n1 n2 => Some (Val.of_bool (sem_float n1 n2)))
        (fun n1 n2 => Some (Val.of_bool (sem_single n1 n2)))
        t1 t2 v1 v2)).
Proof.
  intros.
  destruct t; inv H1.
  unfold Clight_Cop2.sem_binarith.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' t1 t2) eqn:?H.
1,2,3,4:
  destruct t1 as [|  [| | |] [|] | | [ | ] ? | | | | |]; try discriminate H0;
  destruct t2 as [|  [| | |] [|] | | [ | ] ? | | | | |]; try inv H0;
  try contradiction;
  destruct v1; try solve [inv TV1];
  destruct v2; try solve [inv TV2];
  inv H1;
  simpl;
  apply tc_val_of_bool; auto.
  destruct t1 as [|  [| | |] [|] | | [ | ] ? | | | | |]; inv H;
  destruct t2 as [|  [| | |] [|] | | [ | ] ? | | | | |]; inv H0;
  inv H1.
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
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_add in IBR |- *.
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
    destruct (typeof e1) as [| [| | |] ? ? | | [|] | | | | |]; inv TV1;
    destruct (typeof e2) as [| [| | |] ? ? | | [|] | | | | |]; inv TV2;
    simpl in H; inv H;
    try rewrite J in *; clear J;
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
     simpl in *; try contradiction;
    destruct t; try solve [inv H1];
    try solve [constructor; try rewrite (negb_true _ H1); apply I]
  ].
  rewrite denote_tc_assert_andp in IBR. destruct IBR.
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
  unfold tc_int_or_ptr_type, eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_sub in IBR |- *.
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
    destruct (typeof e1); inv TV1; destruct (typeof e2) as [| [| | |] [|] | | | | | | |]; inv TV2;
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
  rewrite denote_tc_assert_andp in IBR. destruct IBR.
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
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_mul in IBR |- *.
  rewrite denote_tc_assert_andp in IBR. destruct IBR.
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
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_mul in IBR |- *.
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
  unfold eval_binop, sem_binary_operation', isBinOpResultType, Clight_Cop2.sem_mod in IBR |- *.
  unfold force_val2, force_val.
  unfold Clight_Cop2.sem_binarith.
  rewrite classify_binarith_eq.
  destruct (classify_binarith' (typeof e1) (typeof e2)) eqn:?H.
  + solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H2, <- H0 in H;
    try solve [inv H];
    try solve [destruct sz,sg; inv H].
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
      unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast.
      unfold  sem_cast_pointer.
      destruct Archi.ptr64; reflexivity.
    - apply tc_bool_e in IBR0.
      simpl in IBR |- *; unfold_lift in IBR.
      destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3 | inv IBR].
      unfold both_int; simpl.
      apply denote_tc_nonzero_e in IBR; try rewrite IBR.
      simpl.
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0];
      simpl; auto.
      unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast.
      unfold  sem_cast_pointer.
      destruct Archi.ptr64; reflexivity.
  + solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H2, <- H0 in H;
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
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
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Clight_Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl.
    - destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
    - destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
  + (* shift_ll *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl; destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
  + (* shift_il *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Clight_Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl;
    destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR0]; simpl; auto.
  + (* shift_li *)
    destruct IBR as [?IBR ?IBR].
    apply tc_bool_e in IBR0.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
    destruct OP; subst; auto;
    simpl;
    unfold force_val, Clight_Cop2.sem_shift;
    rewrite classify_shift_eq, H;
    simpl;
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
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
    destruct (eval_expr e1 rho), (eval_expr e2 rho);
      try solve [inv H1 | inv H3].
   clear e1 e2 H0 H2.
    destruct OP as [| [|]]; subst; auto;
    simpl;
    unfold force_val, Clight_Cop2.sem_and, Clight_Cop2.sem_or, Clight_Cop2.sem_xor, Clight_Cop2.sem_binarith;
    rewrite classify_binarith_eq, H;
    simpl;
    destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto;
    unfold both_int, Clight_Cop2.sem_cast, Clight_Cop2.classify_cast, sem_cast_pointer;
   destruct Archi.ptr64; reflexivity.
  + (* bin_case_l *)
    apply tc_bool_e in IBR.
    simpl in IBR; unfold_lift in IBR.
    solve_tc_val TV1;
    solve_tc_val TV2;
    rewrite <- H0, <- H2 in H;
    try solve [inv H];
    try solve [destruct sz,sg; try destruct sz0,sg0; inv H].
    - destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3].
      destruct OP as [| [|]]; subst; auto;
      simpl;
      unfold force_val, Clight_Cop2.sem_and, Clight_Cop2.sem_or, Clight_Cop2.sem_xor, Clight_Cop2.sem_binarith;
      rewrite classify_binarith_eq, H;
      simpl;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
    - destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3].
      destruct OP as [| [|]]; subst; auto;
      simpl;
      unfold force_val, Clight_Cop2.sem_and, Clight_Cop2.sem_or, Clight_Cop2.sem_xor, Clight_Cop2.sem_binarith;
      rewrite classify_binarith_eq, H;
      simpl;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
    - destruct (eval_expr e1 rho), (eval_expr e2 rho);
        try solve [inv H1 | inv H3].
      destruct OP as [| [|]]; subst; auto;
      simpl;
      unfold force_val, Clight_Cop2.sem_and, Clight_Cop2.sem_or, Clight_Cop2.sem_xor, Clight_Cop2.sem_binarith;
      rewrite classify_binarith_eq, H;
      simpl;
      destruct t as [| [| | |] ? ? | | | | | | |]; try solve [inv IBR]; simpl; auto.
Qed.

