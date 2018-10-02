Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.tycontext.
Require Import VST.veric.Clight_lemmas.
Require Export VST.veric.expr.

Require Import VST.veric.mpred.

Lemma neutral_cast_lemma: forall t1 t2 v,
  is_neutral_cast t1 t2 = true ->
  tc_val t1 v -> eval_cast t1 t2 v = v.
Proof.
intros.
assert (- two_p (16-1) < Byte.min_signed) by (compute; congruence).
assert (two_p (16-1) > Byte.max_signed) by (compute; congruence).
assert (two_p 16 > Byte.max_unsigned) by (compute; congruence).
assert (- two_p (8-1) = Byte.min_signed) by reflexivity.
assert (two_p (8-1) - 1 = Byte.max_signed) by reflexivity.
assert (two_p 8 - 1 = Byte.max_unsigned) by reflexivity.
 destruct t1 as [ | [ | | | ] [ | ] | | [ | ] | | | | | ],
 t2 as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 unfold eval_cast, sem_cast, classify_cast,
  sem_cast_pointer, sem_cast_i2bool, sem_cast_l2bool;
try solve [
 try match goal with |- context [Archi.ptr64] => destruct Archi.ptr64 end;
 inversion H; clear H; try reflexivity;
 destruct v; unfold tc_val, is_int in H0; try contradiction;
 simpl; f_equal;
 try (first [apply sign_ext_inrange| apply zero_ext_inrange];
       try omega;
    match type of H0 with _ \/ _ =>
       destruct H0; subst i; simpl;
       try  rewrite Int.signed_zero;
       try  rewrite Int.unsigned_zero;
       try change (Int.signed Int.one) with 1;
       try change (Int.unsigned Int.one) with 1;
       clear; compute; split; congruence
    end);
 try (destruct H0; subst i; try rewrite Int.eq_true; auto)].
 unfold is_neutral_cast in H.
 rewrite orb_true_iff in H.
 destruct H.
 apply eqb_type_true in H. rewrite <- H in *.
 unfold tc_val in H0.
 rewrite eqb_reflx.
 destruct (eqb_type (Tpointer _ _) _); destruct v; inv H0; reflexivity.
 rewrite andb_true_iff in H. destruct H.
 destruct (eqb_type (Tpointer t1 a) int_or_ptr_type); inv H.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type); inv H7.
 simpl.
 unfold tc_val in H0.
 destruct (eqb_type (Tpointer _ _) _); destruct v; inv H0; reflexivity.
Qed.

Lemma neutral_cast_subsumption: forall t1 t2 v,
  is_neutral_cast t1 t2 = true ->
  tc_val t1 v -> tc_val t2 v.
Proof.
intros.
assert (- two_p (16-1) < Byte.min_signed) by (compute; congruence).
assert (two_p (16-1) > Byte.max_signed) by (compute; congruence).
assert (two_p 16 > Byte.max_unsigned) by (compute; congruence).
assert (- two_p (8-1) = Byte.min_signed) by reflexivity.
assert (two_p (8-1) - 1 = Byte.max_signed) by reflexivity.
assert (two_p 8 - 1 = Byte.max_unsigned) by reflexivity.
destruct t1 as [ | [ | | | ] [ | ] | | [ | ] | | | | | ],
 t2   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; inv H;
 destruct v; try solve [contradiction H0]; try apply I;
 unfold tc_val, is_int in *;
  auto;
 try omega;
 try
    match type of H0 with _ \/ _ =>
       destruct H0; subst i; simpl;
       try  rewrite Int.signed_zero;
       try  rewrite Int.unsigned_zero;
       try change (Int.signed Int.one) with 1;
       try change (Int.unsigned Int.one) with 1;
       clear; compute; try split; congruence
    end;
 try match type of H0 with context [if ?A then _ else _] => destruct A; contradiction H0 end.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type) eqn:?H.
 apply I.
 apply eqb_type_false in H.
 destruct (eqb_type (Tpointer t1 a) int_or_ptr_type) eqn:?H; auto.
 apply eqb_type_true in H7. inv H7. simpl in *.
 rewrite orb_false_r in H8. 
 rewrite andb_true_iff in H8. destruct H8.
 destruct t2; inv H7.
 destruct a0.
 destruct attr_volatile; try solve [inv H8].
 simpl in H8.
 destruct attr_alignas; try solve [inv H8].
 destruct n as [ | ]; try solve [inv H8].
 apply Peqb_true_eq in H8. subst p.
 contradiction H. reflexivity.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type) eqn:?H.
 apply I.
 apply I.
Qed.

Lemma neutral_cast_subsumption': forall t1 t2 v,
  is_neutral_cast (implicit_deref t1) t2 = true ->
  tc_val t1 v -> tc_val t2 v.
Proof.
intros.
assert (- two_p (16-1) < Byte.min_signed) by (compute; congruence).
assert (two_p (16-1) > Byte.max_signed) by (compute; congruence).
assert (two_p 16 > Byte.max_unsigned) by (compute; congruence).
assert (- two_p (8-1) = Byte.min_signed) by reflexivity.
assert (two_p (8-1) - 1 = Byte.max_signed) by reflexivity.
assert (two_p 8 - 1 = Byte.max_unsigned) by reflexivity.
destruct t1 as [ | [ | | | ] [ | ] | | [ | ] | | | | | ],
 t2   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; inv H;
 destruct v; try solve [contradiction H0]; try apply I;
 unfold tc_val, is_int in *;
  auto;
 try omega;
 try
    match type of H0 with _ \/ _ =>
       destruct H0; subst i; simpl;
       try  rewrite Int.signed_zero;
       try  rewrite Int.unsigned_zero;
       try change (Int.signed Int.one) with 1;
       try change (Int.unsigned Int.one) with 1;
       clear; compute; try split; congruence
    end;
 try match type of H0 with context [if ?A then _ else _] => destruct A; contradiction H0 end.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type) eqn:?H.
 apply I.
 apply eqb_type_false in H.
 destruct (eqb_type (Tpointer t1 a) int_or_ptr_type) eqn:?H; auto.
 apply eqb_type_true in H7. inv H7. simpl in *.
 rewrite orb_false_r in H8. 
 rewrite andb_true_iff in H8. destruct H8.
 destruct t2; inv H7.
 destruct a0.
 destruct attr_volatile; try solve [inv H8].
 simpl in H8.
 destruct attr_alignas; try solve [inv H8].
 destruct n as [ | ]; try solve [inv H8].
 apply Peqb_true_eq in H8. subst p.
 contradiction H. reflexivity.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type) eqn:?H.
 apply I.
 apply I.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type) eqn:?H.
 apply I.
 apply eqb_type_false in H.
 auto.
 destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type) eqn:?H.
 apply I.
 apply I.
Qed.

(** Denotation functions for each of the assertions that can be produced by the typechecker **)

Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => prop (is_true (Int.eq i Int.zero))
         | Vlong i => prop (is_true (Int64.eq i Int64.zero))
         | _ => FF
         end.

Definition denote_tc_nonzero v : mpred :=
         match v with
         | Vint i => prop (i <> Int.zero)
         | Vlong i =>prop (i <> Int64.zero)
         | _ => FF end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => prop (Int.unsigned i1 < Int.unsigned i)
     | _ => FF
     end.

Definition denote_tc_lgt l v : mpred :=
     match v with
     | Vlong l1 => prop (Int64.unsigned l1 < Int64.unsigned l)
     | _ => FF
     end.

Definition Zoffloat (f:float): option Z := (**r conversion to Z *)
  match f with
    | Fappli_IEEE.B754_finite s m (Zpos e) _ =>
       Some (Fcore_Zaux.cond_Zopp s (Zpos m) * Zpower_pos 2 e)
    | Fappli_IEEE.B754_finite s m 0 _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m))
    | Fappli_IEEE.B754_finite s m (Zneg e) _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m / Zpower_pos 2 e))
    | Fappli_IEEE.B754_zero _ => Some 0
    | _ => None
  end.  (* copied from CompCert 2.3, because it's missing in CompCert 2.4 *)

Definition Zofsingle (f: float32): option Z := (**r conversion to Z *)
  match f with
    | Fappli_IEEE.B754_finite s m (Zpos e) _ =>
       Some (Fcore_Zaux.cond_Zopp s (Zpos m) * Zpower_pos 2 e)
    | Fappli_IEEE.B754_finite s m 0 _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m))
    | Fappli_IEEE.B754_finite s m (Zneg e) _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m / Zpower_pos 2 e))
    | Fappli_IEEE.B754_zero _ => Some 0
    | _ => None
  end.  (* copied from CompCert 2.3, because it's missing in CompCert 2.4 *)


Definition denote_tc_Zge z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition denote_tc_Zle z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition sameblock v1 v2 : bool :=
         match v1, v2 with
          | Vptr b1 _, Vptr b2 _ => peq b1 b2
          | _, _ => false
         end.

Definition denote_tc_samebase v1 v2 : mpred :=
       prop (is_true (sameblock v1 v2)).

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => prop (~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone))
          | Vlong n1, Vlong n2 => prop (~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone))
          | Vint n1, Vlong n2 => TT
          | Vlong n1, Vint n2 => prop (~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone))
          | _ , _ => FF
        end.

Definition denote_tc_nosignedover (op: Z->Z->Z) v1 v2 : mpred :=
 match v1,v2 with
 | Vint n1, Vint n2 => 
   prop (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed)
 | Vlong n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vint n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vlong n1, Vint n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int.signed n2) <= Int64.max_signed)
 | _, _ => FF
 end.

Definition denote_tc_initialized id ty rho : mpred :=
    prop (exists v, Map.get (te_of rho) id = Some v
               /\ tc_val ty v).

Definition denote_tc_isptr v : mpred :=
  prop (isptr v).

Definition test_eq_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else (andp (valid_pointer v1) (valid_pointer v2)).

Definition test_order_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else FF.

Definition denote_tc_test_eq v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => 
     if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => 
     if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vint i, Vptr _ _ =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v2)
 | Vlong i, Vptr _ _ =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v2) else FF
 | Vptr _ _, Vint i =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v1)
 | Vptr _ _, Vlong i =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v1) else FF
 | Vptr _ _, Vptr _ _ =>
      test_eq_ptrs v1 v2
 | _, _ => FF
 end.

Definition denote_tc_test_order v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vptr _ _, Vptr _ _ =>
      test_order_ptrs v1 v2
 | _, _ => FF
 end.

Definition typecheck_error (e: tc_error) : Prop := False.

Fixpoint denote_tc_assert {CS: compspecs}(a: tc_assert) : environ -> mpred :=
  match a with
  | tc_FF msg => `(prop (typecheck_error msg))
  | tc_TT => `TT
  | tc_andp' b c => `andp (denote_tc_assert b) (denote_tc_assert c)
  | tc_orp' b c => `orp (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr e)
  | tc_isptr e => `denote_tc_isptr (eval_expr e)
  | tc_test_eq' e1 e2 => `denote_tc_test_eq (eval_expr e1) (eval_expr e2)
  | tc_test_order' e1 e2 => `denote_tc_test_order (eval_expr e1) (eval_expr e2)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr e)
  | tc_llt' e l => `(denote_tc_lgt l) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr e)
  | tc_nosignedover op e1 e2 => `(denote_tc_nosignedover op) (eval_expr e1) (eval_expr e2)
 end.

Lemma and_False: forall x, (x /\ False) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma and_True: forall x, (x /\ True) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma True_and: forall x, (True /\ x) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma False_and: forall x, (False /\ x) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma tc_andp_sound : forall {CS: compspecs} a1 a2 rho m,
    denote_tc_assert  (tc_andp a1 a2) rho m <->
    denote_tc_assert  (tc_andp' a1 a2) rho m.
Proof.
intros.
 unfold tc_andp.
 destruct a1; simpl; unfold_lift;
 repeat first [rewrite False_and | rewrite True_and
                    | rewrite and_False | rewrite and_True ];
  try apply iff_refl;
  destruct a2; simpl in *; unfold_lift;
 repeat first [rewrite False_and | rewrite True_and
                    | rewrite and_False | rewrite and_True ];
  try apply iff_refl.
Qed.

Lemma denote_tc_assert_andp:
  forall {CS: compspecs} a b rho, denote_tc_assert (tc_andp a b) rho =
             andp (denote_tc_assert a rho) (denote_tc_assert b rho).
Proof.
 intros.
 apply pred_ext.
 intro m. rewrite tc_andp_sound. intros [? ?]; split; auto.
 intros m [? ?]. rewrite tc_andp_sound; split; auto.
Qed.

Lemma neutral_isCastResultType:
  forall {CS: compspecs} t t' v rho,
   is_neutral_cast t' t = true ->
   forall m, denote_tc_assert (isCastResultType t' t v) rho m.
Proof.
intros.
  unfold isCastResultType.
  unfold is_neutral_cast in H; simpl classify_cast.
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |],
   t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
   try solve [inv H; try apply I; simpl; simple_if_tac; apply I];
  try (rewrite denote_tc_assert_andp; split);
  try solve [unfold eval_cast, sem_cast, classify_cast,
     sem_cast_pointer, sem_cast_i2bool, sem_cast_l2bool;
      destruct Archi.ptr64; simpl; try simple_if_tac; try apply I].
  apply orb_true_iff in H.
  unfold classify_cast.
  destruct (Bool.eqb (eqb_type (Tpointer t a0) int_or_ptr_type)
         (eqb_type (Tpointer t' a) int_or_ptr_type)) eqn:J.
  destruct (eqb_type (Tpointer t' a) (Tpointer t a0)) eqn:?H.
  apply I.
  destruct H. inv H.
  apply andb_true_iff in H. destruct H.
  rewrite eqb_true_iff in J.
  unfold is_pointer_type.
  rewrite <- J in *. apply eqb_type_false in H0.
  destruct (eqb_type (Tpointer t a0) int_or_ptr_type); inv H.
  apply I.
  destruct H.
  apply eqb_type_true in H. rewrite <- H in *.
  rewrite eqb_reflx in J. inv J.
  destruct (eqb_type (Tpointer t' a) int_or_ptr_type),
     (eqb_type (Tpointer t a0) int_or_ptr_type); inv H; inv J.
Qed.

Lemma is_true_e: forall b, is_true b -> b=true.
Proof. intros. destruct b; try contradiction; auto.
Qed.

Lemma tc_bool_e: forall {CS: compspecs} b a rho m,
  app_pred (denote_tc_assert (tc_bool b a) rho) m ->
  b = true.
Proof.
intros.
destruct b; simpl in H; auto.
Qed.
