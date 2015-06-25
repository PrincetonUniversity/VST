Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.tycontext.
Require Import veric.Clight_lemmas.
Require Export veric.expr.



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
 try (destruct H0; subst i; try rewrite Int.eq_true; auto).
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
    end.
Qed.

(** Denotation functions for each of the assertions that can be produced by the typechecker **)

Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => prop (is_true (Int.eq i Int.zero)) 
         | Vlong i => prop (is_true (Int.eq (Int.repr (Int64.unsigned i)) Int.zero))
         | _ => FF
         end.

Definition denote_tc_nonzero v : mpred := 
         match v with 
         | Vint i => if negb (Int.eq i Int.zero) then TT else FF
         | _ => FF end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => prop (is_true (Int.ltu i1 i))
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
                                    | Some n => prop (is_true (Zge_bool z n))
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (is_true (Zge_bool z n))
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition denote_tc_Zle z v : mpred := 
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (is_true (Zle_bool z n))
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (is_true (Zle_bool z n))
                                    | None => FF
                                   end
                     | _ => FF 
                  end.

Definition denote_tc_samebase v1 v2 : mpred :=
                         match v1, v2 with
                           | Vptr b1 _, Vptr b2 _ => prop (is_true (peq b1 b2))
                           | _, _ => FF
                         end.

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => prop (is_true (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone)))
          | _ , _ => FF
        end.

Definition denote_tc_initialized id ty rho : mpred := 
    prop (exists v, Map.get (te_of rho) id = Some v
               /\ is_true (typecheck_val v ty)).

Definition denote_tc_isptr v : mpred :=
  prop (isptr v).

Fixpoint denote_tc_assert (Delta: tycontext) (a: tc_assert) : environ -> mpred :=
  match a with
  | tc_FF _ => `FF
  | tc_noproof => `FF
  | tc_TT => `TT
  | tc_andp' b c => `andp (denote_tc_assert Delta b) (denote_tc_assert Delta c)
  | tc_orp' b c => `orp (denote_tc_assert Delta b) (denote_tc_assert Delta c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr Delta e)
  | tc_isptr e => `denote_tc_isptr (eval_expr Delta e)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr Delta e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr Delta e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr Delta e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr Delta e1) (eval_expr Delta e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr Delta v1) (eval_expr Delta v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr Delta e)
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


Lemma tc_andp_sound : forall Delta a1 a2 rho m, 
    denote_tc_assert Delta (tc_andp a1 a2) rho m <->  
    denote_tc_assert Delta (tc_andp' a1 a2) rho m. 
Proof.
intros.
 unfold tc_andp.
 destruct a1; simpl; unfold_lift;
 repeat first [rewrite False_and | rewrite True_and | rewrite and_False | rewrite and_True];
  try apply iff_refl;
  destruct a2; simpl in *; unfold_lift;
 repeat first [rewrite False_and | rewrite True_and | rewrite and_False | rewrite and_True];
  try apply iff_refl.
Qed. 

Lemma denote_tc_assert_andp: 
  forall Delta a b rho, denote_tc_assert Delta (tc_andp a b) rho =
             andp (denote_tc_assert Delta a rho) (denote_tc_assert Delta b rho).
Proof.
 intros.
 apply pred_ext.
 intro m. rewrite tc_andp_sound. intros [? ?]; split; auto.
 intros m [? ?]. rewrite tc_andp_sound; split; auto.
Qed.

Lemma neutral_isCastResultType:
  forall Delta t t' v rho,
   is_neutral_cast t' t = true ->
   forall m, denote_tc_assert Delta (isCastResultType Delta t' t v) rho m.
Proof.
intros.
  unfold isCastResultType;
  destruct t'  as [ | [ | | | ] [ | ] | | [ | ] | | | | |], t  as [ | [ | | | ] [ | ] | | [ | ] | | | | |];
     inv H; try apply I;
    simpl; if_tac; apply I.
Qed.
