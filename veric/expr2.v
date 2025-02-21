Require Import VST.veric.Clight_base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Require Import VST.veric.tycontext.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_lemmas.
Require Export VST.veric.expr.
Require Import VST.veric.mpred.
Require Export VST.veric.env.
Require Export VST.veric.lifting_expr.
Import LiftNotation.

Transparent intsize_eq.

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
       try lia;
    match type of H0 with _ \/ _ =>
       destruct H0; subst i; simpl;
       try  rewrite Int.signed_zero;
       try  rewrite Int.unsigned_zero;
       try change (Int.signed Int.one) with 1;
       try change (Int.unsigned Int.one) with 1;
       clear; compute; split; congruence
    end);
 try (destruct H0; subst i; try rewrite Int.eq_true; auto)].
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
 try lia;
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
 try lia;
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

Section mpred.

Context `{!heapGS Σ} `{!envGS Σ}.

(** Denotation functions for each of the assertions that can be produced by the typechecker **)

Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => ⌜is_true (Int.eq i Int.zero)⌝
         | Vlong i => ⌜is_true (Int64.eq i Int64.zero)⌝
         | _ => False
         end.

Definition denote_tc_nonzero v : mpred :=
         match v with
         | Vint i => ⌜i <> Int.zero⌝
         | Vlong i =>⌜i <> Int64.zero⌝
         | _ => False end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => ⌜Int.unsigned i1 < Int.unsigned i⌝
     | _ => False
     end.

Definition denote_tc_lgt l v : mpred :=
     match v with
     | Vlong l1 => ⌜Int64.unsigned l1 < Int64.unsigned l⌝
     | _ => False
     end.

Definition Zoffloat (f:float): option Z := (**r conversion to Z *)
  match f with
    | IEEE754.Binary.B754_finite s m (Zpos e) _ =>
       Some (Zaux.cond_Zopp s (Zpos m) * Zpower_pos 2 e)
    | IEEE754.Binary.B754_finite s m 0 _ => Some (Zaux.cond_Zopp s (Zpos m))
    | IEEE754.Binary.B754_finite s m (Zneg e) _ => Some (Zaux.cond_Zopp s (Zpos m / Zpower_pos 2 e))
    | IEEE754.Binary.B754_zero _ => Some 0
    | _ => None
  end.  (* copied from CompCert 2.3, because it's missing in CompCert 2.4,
             then adapted after CompCert 3.5 when Flocq was rearranged *)

Definition Zofsingle (f: float32): option Z := (**r conversion to Z *)
  match f with
    | IEEE754.Binary.B754_finite s m (Zpos e) _ =>
       Some (Zaux.cond_Zopp s (Zpos m) * Zpower_pos 2 e)
    | IEEE754.Binary.B754_finite s m 0 _ => Some (Zaux.cond_Zopp s (Zpos m))
    | IEEE754.Binary.B754_finite s m (Zneg e) _ => Some (Zaux.cond_Zopp s (Zpos m / Zpower_pos 2 e))
    | IEEE754.Binary.B754_zero _ => Some 0
    | _ => None
  end.  (* copied from CompCert 2.3, because it's missing in CompCert 2.4,
             then adapted after CompCert 3.5 when Flocq was rearranged *)

Definition denote_tc_Zge z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => ⌜z >= n⌝
                                    | None => False
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => ⌜z >= n⌝
                                    | None => False
                                   end
                     | _ => False
                  end.

Definition denote_tc_Zle z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => ⌜z <= n⌝
                                    | None => False
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => ⌜z <= n⌝
                                    | None => False
                                   end
                     | _ => False
                  end.

Definition sameblock v1 v2 : bool :=
         match v1, v2 with
          | Vptr b1 _, Vptr b2 _ => peq b1 b2
          | _, _ => false
         end.

Definition denote_tc_samebase v1 v2 : mpred :=
       ⌜is_true (sameblock v1 v2)⌝.

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => ⌜~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone)⌝
          | Vlong n1, Vlong n2 => ⌜~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone)⌝
          | Vint n1, Vlong n2 => True
          | Vlong n1, Vint n2 => ⌜~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone)⌝
          | _ , _ => False
        end.

Definition denote_tc_nosignedover (op: Z->Z->Z) (s: signedness) v1 v2 : mpred :=
 match v1,v2 with
 | Vint n1, Vint n2 => 
   ⌜Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed⌝
 | Vlong n1, Vlong n2 =>
   ⌜Int64.min_signed <= op (Int64.signed n1) (Int64.signed n2) <= Int64.max_signed⌝
 | Vint n1, Vlong n2 =>
   ⌜Int64.min_signed <= op ((if s then Int.signed else Int.unsigned) n1) (Int64.signed n2) <= Int64.max_signed⌝
 | Vlong n1, Vint n2 =>
   ⌜Int64.min_signed <= op (Int64.signed n1) ((if s then Int.signed else Int.unsigned)  n2) <= Int64.max_signed⌝
 | _, _ => False
 end.

Definition denote_tc_initialized id ty : assert :=
  ∃ v, temp id v ∧ ⌜tc_val ty v⌝.

Definition denote_tc_isptr v : mpred :=
  ⌜isptr v⌝.

Definition denote_tc_isint v : mpred :=
  ⌜is_int I32 Signed v⌝.

Definition denote_tc_islong v : mpred :=
  ⌜is_long v⌝.

Definition test_eq_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then ((weak_valid_pointer v1) ∧ (weak_valid_pointer v2))
  else ((valid_pointer v1) ∧ (valid_pointer v2)).

Definition test_order_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then ((weak_valid_pointer v1) ∧ (weak_valid_pointer v2))
  else False.

Definition denote_tc_test_eq v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => 
     if Archi.ptr64 then False else bi_and (⌜i = Int.zero⌝) (⌜j = Int.zero⌝)
 | Vlong i, Vlong j => 
     if Archi.ptr64 then bi_and (⌜i = Int64.zero⌝) (⌜j = Int64.zero⌝) else False
 | Vint i, Vptr _ _ =>
      if Archi.ptr64 then False else bi_and (⌜i = Int.zero⌝) (weak_valid_pointer v2)
 | Vlong i, Vptr _ _ =>
      if Archi.ptr64 then bi_and (⌜i = Int64.zero⌝) (weak_valid_pointer v2) else False
 | Vptr _ _, Vint i =>
      if Archi.ptr64 then False else bi_and (⌜i = Int.zero⌝) (weak_valid_pointer v1)
 | Vptr _ _, Vlong i =>
      if Archi.ptr64 then bi_and (⌜i = Int64.zero⌝) (weak_valid_pointer v1) else False
 | Vptr _ _, Vptr _ _ =>
      test_eq_ptrs v1 v2
 | _, _ => False
 end.

Definition denote_tc_test_order v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => if Archi.ptr64 then False else bi_and (⌜i = Int.zero⌝) (⌜j = Int.zero⌝)
 | Vlong i, Vlong j => if Archi.ptr64 then bi_and (⌜i = Int64.zero⌝) (⌜j = Int64.zero⌝) else False
 | Vptr _ _, Vptr _ _ =>
      test_order_ptrs v1 v2
 | _, _ => False
 end.

Definition typecheck_error (e: tc_error) : Prop := False.

(* The only place we use the environ here is in tc_initialized.
   Not quite true: a bunch of them use eval_expr, which needs the environment.
   Should we switch them to wps? *)
Fixpoint denote_tc_assert {CS: compspecs} f (a: tc_assert) : assert :=
  match a with
  | tc_FF msg => ⌜typecheck_error msg⌝
  | tc_TT => True
  | tc_andp' b c => bi_and (denote_tc_assert f b) (denote_tc_assert f c)
  | tc_orp' b c => bi_or (denote_tc_assert f b) (denote_tc_assert f c)
  | tc_nonzero' e => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_nonzero v⎤)
  | tc_isptr e => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_isptr v⎤)
  | tc_isint e => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_isint v⎤)
  | tc_islong e => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_islong v⎤)
  | tc_test_eq' e1 e2 => wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_test_eq v1 v2⎤))
  | tc_test_order' e1 e2 => wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_test_order v1 v2⎤))
  | tc_ilt' e i => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_igt i v⎤)
  | tc_llt' e l => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_lgt l v⎤)
  | tc_Zle e z => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_Zge z v⎤)
  | tc_Zge e z => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_Zle z v⎤)
  | tc_samebase e1 e2 => wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_samebase v1 v2⎤))
  | tc_nodivover' e1 e2 => wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_nodivover v1 v2⎤))
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => wp_expr cenv_cs ∅ f e (λ v, ⎡denote_tc_iszero v⎤)
  | tc_nosignedover op e1 e2 => 
     match typeof e1, typeof e2 with
     | Tlong _ _, Tint _ Unsigned _ => wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_nosignedover op Unsigned v1 v2⎤))
     | Tint _ Unsigned _, Tlong _ _ => wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_nosignedover op Unsigned v1 v2⎤))
     | _, _ =>  wp_expr cenv_cs ∅ f e1 (λ v1, wp_expr cenv_cs ∅ f e2 (λ v2, ⎡denote_tc_nosignedover op Signed v1 v2⎤))
     end
 end.

Lemma and_False: forall x, (x /\ False) = Logic.False.
Proof.
intros; apply Axioms.prop_ext; intuition.
Qed.

Lemma and_True: forall x, (x /\ True) = x.
Proof.
intros; apply Axioms.prop_ext; intuition.
Qed.

Lemma True_and: forall x, (True /\ x) = x.
Proof.
intros; apply Axioms.prop_ext; intuition.
Qed.

Lemma False_and: forall x, (False /\ x) = Logic.False.
Proof.
intros; apply Axioms.prop_ext; intuition.
Qed.

Lemma tc_andp_sound : forall {CS: compspecs} f a1 a2,
    denote_tc_assert f (tc_andp a1 a2) ⊣⊢
    denote_tc_assert f (tc_andp' a1 a2).
Proof.
intros.
 unfold tc_andp.
 destruct a1; simpl; unfold_lift;
 repeat first [rewrite bi.False_and | rewrite bi.True_and
                    | rewrite bi.and_False | rewrite bi.and_True ];
  try reflexivity;
  destruct a2; simpl in *; unfold_lift;
  repeat first [rewrite bi.False_and | rewrite bi.True_and
                    | rewrite bi.and_False | rewrite bi.and_True ];
  try reflexivity.
Qed.

Lemma denote_tc_assert_andp:
  forall {CS: compspecs} f a b, denote_tc_assert f (tc_andp a b) ⊣⊢
             bi_and (denote_tc_assert f a) (denote_tc_assert f b).
Proof. intros; apply tc_andp_sound. Qed.

Lemma neutral_isCastResultType:
  forall {CS: compspecs} f P t t' v,
   is_neutral_cast t' t = true ->
   P ⊢ denote_tc_assert f (isCastResultType t' t v).
Proof.
intros.
  unfold isCastResultType.
  unfold is_neutral_cast in H; simpl classify_cast.
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |],
   t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
   try solve [inv H; auto; simpl; simple_if_tac; auto];
  try (rewrite denote_tc_assert_bi_and; split);
  try solve [unfold eval_cast, sem_cast, classify_cast,
     sem_cast_pointer, sem_cast_i2bool, sem_cast_l2bool;
      destruct Archi.ptr64; simpl; try simple_if_tac; auto].
  apply orb_true_iff in H.
  unfold classify_cast.
  destruct (Bool.eqb (eqb_type (Tpointer t a0) int_or_ptr_type)
         (eqb_type (Tpointer t' a) int_or_ptr_type)) eqn:J.
  destruct (eqb_type (Tpointer t' a) (Tpointer t a0)) eqn:?H; first by auto.
  destruct H. inv H.
  apply andb_true_iff in H. destruct H.
  rewrite eqb_true_iff in J.
  unfold is_pointer_type.
  rewrite <- J in *. apply eqb_type_false in H0.
  destruct (eqb_type (Tpointer t a0) int_or_ptr_type); inv H; by auto.
  destruct H.
  apply eqb_type_true in H. rewrite <- H in *.
  rewrite eqb_reflx in J. inv J.
  destruct (eqb_type (Tpointer t' a) int_or_ptr_type),
     (eqb_type (Tpointer t a0) int_or_ptr_type); inv H; inv J.
Qed.

Lemma is_true_e: forall b, is_true b -> b=true.
Proof. intros. destruct b; try contradiction; auto.
Qed.

Lemma tc_bool_e: forall {CS: compspecs} f b a,
  denote_tc_assert f (tc_bool b a) ⊢
  ⌜b = true⌝.
Proof.
intros.
destruct b; simpl; auto.
Qed.

End mpred.
