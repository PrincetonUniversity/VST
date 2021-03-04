Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import Memdata.

Definition Gprog : funspecs :=
    ltac:(with_library prog (@nil(ident*funspec))).


Definition g_spec :=
 DECLARE _g
 WITH i: Z
 PRE [ size_t]
   PROP() PARAMS(Vptrofs (Ptrofs.repr i)) SEP()
 POST [ size_t ]
   PROP() RETURN (Vptrofs (Ptrofs.repr i)) SEP().

Lemma body_g: semax_body Vprog Gprog f_g g_spec.
Proof.
start_function.
forward.
forward.
forward.
cancel.
Qed.

Lemma decode_float32_int32:
  forall (bl: list memval) (x: float32),
 size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
 decode_val Mfloat32 bl = Vsingle x ->
 decode_val Mint32 bl = Vint (Float32.to_bits x).
Proof.
intros.
unfold decode_val,decode_int,rev_if_be in *.
destruct (proj_bytes bl) eqn:?H.
inv H0.
rewrite Float32.to_of_bits. auto.
inv H0.
Qed.

Lemma NOT_decode_int32_float32:
  Archi.ptr64=false ->
 ~ (forall (bl: list memval) (x: float32),
     size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
     decode_val Mint32 bl = Vint (Float32.to_bits x) ->
     decode_val Mfloat32 bl = Vsingle x).
(* This lemma illustrates a problem: it is NOT the case that
   if (bl: list memval) decodes to Vint (Float32.to_bits x) 
  then it also decodes to  Vsingle x.   
  See https://github.com/AbsInt/CompCert/issues/207  for a description
  of the problem; and see https://github.com/PrincetonUniversity/VST/issues/429
  for a description of the solution,  forward_store_union_hack  *)
Proof.
intro Hp.
intro.
set (x := Float32.zero). (* nothing special about zero, any value would do *)
set (i := Float32.to_bits x).
set (bl := [Fragment (Vint i) Q32 3; Fragment (Vint i) Q32 2; Fragment (Vint i) Q32 1; Fragment (Vint i) Q32 0]).
specialize (H bl x).
specialize (H (eq_refl _)).
assert (decode_val Mint32 bl = Vint (Float32.to_bits x)).
unfold decode_val, bl.
rewrite Hp.
simpl.
destruct (Val.eq (Vint i) (Vint i)); [ | congruence].
destruct (quantity_eq Q32 Q32); [ | congruence].
simpl.
reflexivity.
specialize (H H0).
clear - H. subst bl i.
unfold decode_val in H.
simpl in H. inversion H.
Qed.

Module FABS_STUFF.

Lemma shift_pos_succ:
  forall k j, (shift_pos (Pos.succ k) j = (shift_pos k j)~0)%positive.
Proof.
intros.
change ((shift_pos k j)~0)%positive
with (2 * (shift_pos k j))%positive.
apply Pos2Z.inj.
rewrite Pos2Z.inj_mul.
rewrite !shift_pos_correct.
rewrite Z.mul_assoc.
f_equal.
rewrite <- !two_power_pos_correct.
rewrite <- Pos.add_1_l.
rewrite two_power_pos_is_exp.
reflexivity.
Qed.

Lemma nan_pl_range:
 forall k p, Binary.nan_pl k p = true ->
 Z.pos p < 2 ^ (k-1).
Proof.
intros.
unfold Binary.nan_pl in H.
apply Z.ltb_lt in H.
revert k H; induction p; simpl; intros.
-
rewrite Pos2Z.inj_succ in H.
specialize (IHp (k-1)).
spec IHp; [lia | ].
replace (2^(k-1)) with (2^1 * 2^(k-1-1)).
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
rewrite Pos2Z.inj_xI.
lia.
-
rewrite Pos2Z.inj_succ in H.
specialize (IHp (k-1)).
spec IHp; [lia | ].
replace (2^(k-1)) with (2^1 * 2^(k-1-1)).
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
rewrite Pos2Z.inj_xO.
lia.
-
replace (2^(k-1)) with (2^1 * 2^(k-1-1)).
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
change (2^1) with 2.
assert (0 < 2 ^ (k-1-1)).
apply Z.pow_pos_nonneg; lia.
lia.
Qed.


Definition abs_nan (any_nan: {x : Bits.binary32 | Binary.is_nan 24 128 x = true}) (f: Binary.binary_float 24 128)   :=
match f with
| @Binary.B754_nan _ _ _ p H =>
    exist (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = true)
      (Binary.B754_nan 24 128 false p H) eq_refl
| _ => any_nan
end.

Lemma bounded_mantissa:
  forall prec emax m e, Binary.bounded prec emax m e = true ->
    Z.pos m < 2 ^ prec.
Proof.
intros.
unfold Binary.bounded in H.
rewrite andb_true_iff in H.
destruct H as [H H0].
apply Z.leb_le in H0.
unfold Binary.canonical_mantissa in H.
apply Zeq_bool_eq in H.
unfold FLT.FLT_exp in H.
rewrite Digits.Zpos_digits2_pos in H.
pose proof (Z.max_lub_l (Digits.Zdigits Zaux.radix2 (Z.pos m) + e - prec)
      (3 - emax - prec) e).
spec H1; [ lia | ].
clear H.
assert (Digits.Zdigits Zaux.radix2 (Z.pos m) <= prec) by lia.
clear - H.
apply Digits.Zpower_gt_Zdigits in H.
apply H.
Qed.

Lemma binary32_abs_lemma:
 forall (x : Bits.binary32)
      (any_nan : {x : Bits.binary32 | Binary.is_nan 24 128 x = true}),
  Bits.b32_of_bits (Bits.bits_of_b32 x mod 2 ^ 31) =
  Binary.Babs 24 128 (abs_nan any_nan) x.
Proof.
intros.
destruct x.
- (* B754_zero *)
destruct s; reflexivity.
- (* B754_infinity *)
destruct s; reflexivity.
- (* B754_nan *)
assert (Hpl := nan_pl_range _ _ e).
unfold Bits.b32_of_bits, Binary.Babs, Bits.bits_of_b32, Bits.bits_of_binary_float.
assert (Bits.join_bits 23 8 s (Z.pos pl) (2 ^ 8 - 1) mod 2 ^ 31 =
            Bits.join_bits 23 8 false (Z.pos pl) (2 ^ 8 - 1)).  {
 unfold Bits.join_bits.
rewrite !Z.shiftl_mul_pow2 by computable.
rewrite Z.add_0_l.
rewrite Z.mul_add_distr_r.
rewrite <- Z.add_assoc.
rewrite Z.add_mod by (compute; lia).
replace (((if s then 2 ^ 8 else 0) * 2 ^ 23) mod 2 ^ 31) with 0
  by (destruct s; reflexivity).
rewrite Z.add_0_l.
rewrite Z.mod_mod by lia.
apply Z.mod_small.
lia.
}
rewrite H; clear H.
transitivity (Binary.B754_nan 24 128 false pl e); [ | reflexivity].
clear.
replace (Bits.join_bits 23 8 false (Z.pos pl) (2 ^ 8 - 1))
   with (Bits.bits_of_binary_float 23 8 (Binary.B754_nan 24 128 false pl e)).
apply (Bits.binary_float_of_bits_of_binary_float 23 8 eq_refl eq_refl eq_refl).
reflexivity.
- (* B754_finite *)
unfold Binary.Babs.
clear.
unfold Bits.b32_of_bits, Binary.Babs, Bits.bits_of_b32, Bits.bits_of_binary_float.
pose proof (bounded_mantissa _ _ _ _ e0).
destruct (0 <=? Z.pos m - 2 ^ 23) eqn:?H.
+
apply Z.leb_le in H0.
assert (Z.pos m - 2^23 < 2^23) by lia.
replace (Bits.join_bits 23 8 s (Z.pos m - 2 ^ 23)
                 (e - (3 - 2 ^ (8 - 1) - (23 + 1)) + 1) mod  2 ^ 31)
   with (Bits.bits_of_binary_float 23 8 (Binary.B754_finite 24 128 false m e e0)).
apply (Bits.binary_float_of_bits_of_binary_float 23 8 eq_refl eq_refl eq_refl).
unfold Bits.bits_of_binary_float.
pose proof H0.
apply Z.leb_le in H2. rewrite H2. clear H2.
forget (Z.pos m - 2^23)  as i.
unfold Binary.bounded in e0.
rewrite andb_true_iff in e0.
destruct e0 as [H' ?H].
assert (-149 <= e). {
 clear - H'.
 unfold Binary.canonical_mantissa in H'.
apply Zeq_bool_eq in H'.
unfold FLT.FLT_exp in H'.
rewrite Digits.Zpos_digits2_pos in H'.
pose proof (Z.max_lub_r (Digits.Zdigits Zaux.radix2 (Z.pos m) + e - 24)
      (3 - 128 - 24) e).
spec H; lia.
}
clear H'.
apply Z.leb_le in H2.
simpl Z.sub.
replace (e - -149 + 1) with (e+150) by lia.
unfold Bits.join_bits.
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite Z.add_0_l.
set (e' := e+150).
rewrite Z.mul_add_distr_r.
rewrite <- Z.add_assoc.
rewrite Z.add_mod by (compute; lia).
replace (((if s then 2 ^ 8 else 0) * 2 ^ 23) mod 2 ^ 31)
  with 0 by (destruct s; reflexivity).
rewrite Z.add_0_l.
rewrite Z.mod_mod by lia.
rewrite (Z.mod_small); auto.
subst e'.
lia.
+
replace (Bits.join_bits 23 8 s (Z.pos m) 0 mod 2 ^ 31)
 with (Bits.join_bits 23 8 false (Z.pos m) 0).
replace (Bits.join_bits 23 8 false (Z.pos m) 0)
   with (Bits.bits_of_binary_float 23 8 (Binary.B754_finite 24 128 false m e e0)).
apply (Bits.binary_float_of_bits_of_binary_float 23 8 eq_refl eq_refl eq_refl).
unfold Bits.bits_of_binary_float.
rewrite H0. auto.
clear H0.
unfold Bits.join_bits.
rewrite Z.add_mod by (compute; lia).
rewrite (Z.mod_small (Z.pos m)) by lia.
rewrite !Z.add_0_r.
replace (Z.shiftl (if s then 2 ^ 8 else 0) 23 mod 2 ^ 31) with 0 by (destruct s; reflexivity).
simpl Z.shiftl.
symmetry.
apply Z.mod_small.
lia.
Qed.


Lemma fabs_float32_lemma:
  forall x: float32,
  Float32.of_bits (Int.and (Float32.to_bits x) (Int.repr 2147483647)) =
  Float32.abs x.
Proof.
intros.
Transparent Float32.of_bits.
Transparent Float32.to_bits.
Transparent Float32.abs.
unfold Float32.of_bits, Float32.to_bits, Float32.abs.
Opaque Float32.of_bits.
Opaque Float32.to_bits.
Opaque Float32.abs.
rewrite and_repr.
change 2147483647 with (Z.ones 31).
rewrite Z.land_ones by computable.
rewrite Int.unsigned_repr
 by (pose proof (Z_mod_lt (Bits.bits_of_b32 x) (2 ^ 31) (eq_refl _)); rep_lia).
apply binary32_abs_lemma.
Qed.

End FABS_STUFF.

Module Single.

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float32
 PRE [ Tfloat F32 noattr]
   PROP() PARAMS (Vsingle x) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() RETURN (Vsingle (Float32.abs x)) SEP().

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
entailer!.
f_equal.
apply FABS_STUFF.fabs_float32_lemma.
Qed.
End Single.

Module Float.

 (* This experiment shows what kind of error message you get
   if you put the wrong LOCAL precondition.
   In fact, Vfloat x is wrong, leading to an unsatisfying precondition,
   it must be Vsingle. *)

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float
 PRE [ Tfloat F32 noattr]
   PROP() PARAMS (Vfloat x) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() RETURN (Vfloat (Float.abs x)) SEP().

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
try (start_function; fail 99).
Abort.

End Float.
