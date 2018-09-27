Require Import Reals.
Require Export VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

(* This file contains lemmas regarding "superprecise",
and in principle, almost proving that "mapsto" is superprecise.

However, mapsto is not superprecise, because it's not quite true
that decode_val is injective.  The only reason is the treatment
of single-precision floating-point NaNs, where the conversion
from single-prec to double-prec loses one bit of information:
both quiet 32-bit NaNs and signalling 32-bit NaNs are quietly turned into
quite 64-bit NaNs.

If CompCert ever changes so that this does not happen, then
the lemmas in this file might become useful.

*)

Lemma int_of_bytes_uniq:
  forall i j, length i = length j -> int_of_bytes i = int_of_bytes j -> i = j.
Proof.
  induction i; intros.
 destruct j; inv H. auto.
 destruct j; inv H.
 specialize (IHi _ H2).
 simpl in H0.
do 2 rewrite (Z.add_comm (Byte.unsigned _)) in H0.
 remember (int_of_bytes j * 256 + Byte.unsigned i0) as v eqn:?H.
 symmetry in H0.
 rename i0 into b.
 pose proof (Zmod_unique _ _ _ _ H (Byte.unsigned_range _)).
 pose proof (Zmod_unique _ _ _ _ H0 (Byte.unsigned_range _)).
 assert (Byte.repr (Byte.unsigned a) = Byte.repr (Byte.unsigned b)) by congruence.
 repeat rewrite Byte.repr_unsigned in H4.
 subst b.
 f_equal. clear H1.
 apply IHi.
 omega.
Qed.

Lemma decode_int_uniq:
  forall i j, length i = length j -> decode_int i = decode_int j -> i=j.
Proof.
 unfold decode_int, rev_if_be.
 destruct Archi.big_endian.
 intros. rewrite <- (rev_involutive i). rewrite <- (rev_involutive j).
 f_equal.
 assert (length (rev i) = length (rev j)).
 repeat rewrite rev_length; auto.
 eapply int_of_bytes_uniq; eauto.
 apply int_of_bytes_uniq.
Qed.

Lemma decode_int_range:
  forall l N, N = two_p (8 * Z.of_nat (length l)) -> 0 <= decode_int l < N.
Proof.
intros; subst; revert l.
unfold decode_int.
assert (forall l, 0 <= int_of_bytes l < two_p (8 * Z.of_nat (length l))).
2: intros; rewrite <- rev_if_be_length; auto.
induction l.
simpl; omega.
simpl int_of_bytes. simpl length.
rewrite Nat2Z.inj_succ.
unfold Z.succ.
rewrite Z.mul_add_distr_l.
rewrite two_p_is_exp; try omega.
change (two_p (8*1)) with 256.
pose proof (Byte.unsigned_range a).
change Byte.modulus with 256 in H.
omega.
Qed.

Lemma sign_ext_injective:
 forall n i j,
    0 < n < Int.zwordsize ->
    0 <= i < two_p n ->
    0 <= j < two_p n ->
    Int.sign_ext n (Int.repr i) = Int.sign_ext n (Int.repr j) ->
    i=j.
Proof.
intros.
pose proof (Int.eqmod_sign_ext n (Int.repr i) H).
pose proof (Int.eqmod_sign_ext n (Int.repr j) H).
rewrite H2 in H3.
apply Int.eqmod_sym in H3.
pose proof (Int.eqmod_trans _ _ _ _ H3 H4).
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize);
   change Int.max_unsigned with (two_p Int.zwordsize - 1);
   omega.
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize);
   change Int.max_unsigned with (two_p Int.zwordsize - 1);
   omega.
apply Int.eqmod_small_eq in H5; auto.
Qed.


Lemma zero_ext_injective:
 forall n i j,
    0 <= n < Int.zwordsize ->
    0 <= i < two_p n ->
    0 <= j < two_p n ->
    Int.zero_ext n (Int.repr i) = Int.zero_ext n (Int.repr j) ->
    i=j.
Proof.
intros.
pose proof (Int.eqmod_zero_ext n (Int.repr i) H).
pose proof (Int.eqmod_zero_ext n (Int.repr j) H).
rewrite H2 in H3.
apply Int.eqmod_sym in H3.
pose proof (Int.eqmod_trans _ _ _ _ H3 H4).
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize);
   change Int.max_unsigned with (two_p Int.zwordsize - 1);
   omega.
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize);
   change Int.max_unsigned with (two_p Int.zwordsize - 1);
   omega.
apply Int.eqmod_small_eq in H5; auto.
Qed.

Lemma repr_decode_int_inj:
  forall l1 l2, length l1 = 4%nat -> length l2 = 4%nat ->
    Int.repr (decode_int l1) = Int.repr (decode_int l2) ->
    l1=l2.
Proof.
intros.
apply decode_int_uniq; [congruence | ].
rewrite <- (Int.unsigned_repr (decode_int l1)).
2:{
pose proof (decode_int_range l1 _ (eq_refl _)).
rewrite H in H2.
change (two_p (8 * Z.of_nat 4)) with (Int.max_unsigned + 1) in H2.
omega.
}
rewrite <- (Int.unsigned_repr (decode_int l2)).
2:{
pose proof (decode_int_range l2 _ (eq_refl _)).
rewrite H0 in H2.
change (two_p (8 * Z.of_nat 4)) with (Int.max_unsigned + 1) in H2.
omega.
}
congruence.
Qed.

Lemma repr_decode_int64_inj:
  forall l1 l2, length l1 = 8%nat -> length l2 = 8%nat ->
    Int64.repr (decode_int l1) = Int64.repr (decode_int l2) ->
    l1=l2.
Proof.
intros.
apply decode_int_uniq; [congruence | ].
rewrite <- (Int64.unsigned_repr (decode_int l1)).
2:{
pose proof (decode_int_range l1 _ (eq_refl _)).
rewrite H in H2.
change (two_p (8 * Z.of_nat 8)) with (Int64.max_unsigned + 1) in H2.
omega.
}
rewrite <- (Int64.unsigned_repr (decode_int l2)).
2:{
pose proof (decode_int_range l2 _ (eq_refl _)).
rewrite H0 in H2.
change (two_p (8 * Z.of_nat 8)) with (Int64.max_unsigned + 1) in H2.
omega.
}
congruence.
Qed.

Transparent Float.of_bits.
Transparent Float32.of_bits.

Lemma double_of_bits_inj:
  forall i j, Float.of_bits i = Float.of_bits j -> i=j.
Proof.
intros.
unfold Float.of_bits in H.
rewrite <- (Int64.repr_unsigned i).
rewrite <- (Int64.repr_unsigned j).
f_equal.
unfold Fappli_IEEE_bits.b64_of_bits in H.
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _) (Int64.unsigned i))
  by (apply Int64.unsigned_range).
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _) (Int64.unsigned j))
  by (apply Int64.unsigned_range).
f_equal; apply H.
Qed.

Require Import ZArith.
From compcert Require Import Fappli_IEEE Fcore_Zaux Fcore_generic_fmt.

Lemma binary_normalize_inj:
  forall s1 m1 e1 (h1 : bounded 24 128 m1 e1 = true),
  forall s2 m2 e2 (h2 : bounded 24 128 m2 e2 = true),
   binary_normalize 53 1024 (eq_refl _) (eq_refl _) mode_NE (cond_Zopp s1 (Zpos m1)) e1 s1 =
   binary_normalize 53 1024 (eq_refl _) (eq_refl _) mode_NE (cond_Zopp s2 (Zpos m2)) e2 s2 ->
  B754_finite 24 128 s1 m1 e1 h1 = B754_finite 24 128 s2 m2 e2 h2.
Proof.
intros s1 m1 e1 h1 s2 m2 e2 h2 Hn.
apply B2R_inj ; try easy.
assert (H: forall s m e h,
  B2R 24 128 (B754_finite 24 128 s m e h) =
  B2R 53 1024 (binary_normalize 53 1024 (eq_refl _) (eq_refl _) mode_NE (cond_Zopp s (Zpos m)) e s)).
2: now rewrite 2!H, Hn.
clear.
intros s m e h.
generalize (binary_normalize_correct 53 1024 (eq_refl _) (eq_refl _) mode_NE (cond_Zopp s (Zpos m)) e s).
rewrite round_generic ; auto with typeclass_instances.
rewrite  Fcore_Raux.Rlt_bool_true.
intros [-> _].
easy.
apply Raxioms.Rlt_trans with (1 := abs_B2R_lt_emax _ _ (B754_finite 24 128 s m e h)).
now apply Fcore_Raux.bpow_lt.
apply Fcore_FLT.generic_format_FLT.
assert (h' := generic_format_B2R 24 128 (B754_finite 24 128 s m e h)).
apply Fcore_FLT.FLT_format_generic in h'.
destruct h' as [f [H1 [H2 H3]]].
exists f.
rewrite <- H1.
repeat split.
apply Z.lt_trans with (1 := H2).
now apply Zpower_lt.
now apply Z.le_trans with (2 := H3).
easy.
Qed.

Lemma binary_normalize_finite:
  forall b m e,
  bounded (23 + 1) (2 ^ (8 - 1)) m e = true ->
 match
     binary_normalize 53 1024 eq_refl eq_refl mode_NE
          (cond_Zopp b (Z.pos m)) e b
 with B754_finite _ _ _ _ => True | _ => False
 end.
Proof.
intros s m e h.
generalize (binary_normalize_correct 53 1024 (eq_refl _) (eq_refl _) mode_NE (cond_Zopp s (Zpos m)) e s).
rewrite round_generic ; auto with typeclass_instances.
rewrite Fcore_Raux.Rlt_bool_true.
(****)
intros [H _].
assert (H': B2R 53 1024 (binary_normalize 53 1024 eq_refl eq_refl mode_NE (cond_Zopp s (Z.pos m)) e s) <> 0%R).
  rewrite H, <- (Fcore_float_prop.F2R_0 radix2 e).
  case s.
  now apply RIneq.Rlt_not_eq, Fcore_float_prop.F2R_lt_compat.
  now apply RIneq.Rgt_not_eq, Fcore_float_prop.F2R_lt_compat.
clear H.
destruct binary_normalize ; try easy ; now elim H'.
(****)
apply Raxioms.Rlt_trans with (1 := abs_B2R_lt_emax _ _ (B754_finite 24 128 s m e h)).
now apply Fcore_Raux.bpow_lt.
apply Fcore_FLT.generic_format_FLT.
assert (h' := generic_format_B2R 24 128 (B754_finite 24 128 s m e h)).
apply Fcore_FLT.FLT_format_generic in h'.
destruct h' as [f [H1 [H2 H3]]].
exists f.
rewrite <- H1.
repeat split.
apply Z.lt_trans with (1 := H2).
now apply Zpower_lt.
now apply Z.le_trans with (2 := H3).
easy.
Qed.

Lemma float32_preserves_payload:
 forall s pl,
    let '(s1,pl1) := Float.of_single_pl s pl in
      (s=s1 /\ (536870912 * (Pos.lor (proj1_sig pl) 4194304))%positive = proj1_sig pl1).
Proof.
 intros.
 unfold Float.of_single_pl.
 split; auto.
Qed.

Lemma pos_lor_inj:  (* not true *)
  forall k N (a b: nan_pl k),
     Zpower_nat 2 (Z.to_nat (k-2)) = Zpos N ->
     Pos.lor (proj1_sig a) N =  Pos.lor (proj1_sig b) N ->
    a=b.
Proof.
intros.
 destruct a as [a Ha]. destruct b as [b Hb].
 simpl in *.
 assert (a=b); [ | subst a; f_equal; apply Axioms.proof_irr].
Abort.

Inductive wishes_eq_horses := .

Lemma float32_payload_inj:
  wishes_eq_horses ->
  forall s1 pl1 s2 pl2,
    Float.of_single_pl s1 pl1= Float.of_single_pl s2 pl2 ->
    (s1,pl1) = (s2,pl2).
Proof.
intro WH; intros.
 pose proof (float32_preserves_payload s1 pl1).
 pose proof (float32_preserves_payload s2 pl2).
 rewrite H in H0. clear H.
 destruct (Float.of_single_pl s2 pl2).
 destruct H0,H1. subst.
 f_equal.
 rewrite <- H2 in H0; clear - WH H0.
 apply Pos.mul_reg_l in H0.
 contradiction WH.
Qed.

Lemma single_of_bits_inj:
  forall i j : Int.int, Float32.of_bits i = Float32.of_bits j -> i=j.
Proof.
intros.
unfold Float32.of_bits in H.
rewrite <- (Int.repr_unsigned i).
rewrite <- (Int.repr_unsigned j).
f_equal.
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _) (Int.unsigned i))
  by (apply Int.unsigned_range).
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _) (Int.unsigned j))
  by (apply Int.unsigned_range).
f_equal.
unfold Fappli_IEEE_bits.b32_of_bits in H.
match goal with |- ?A = ?B => remember A as u eqn:H9; remember B as v eqn:H10;
   clear H9 H10 end.
clear i j.

destruct u,v; auto; try congruence.
Qed.

Lemma Vint_inj: forall i j, Vint i = Vint j -> i=j.
Proof. congruence. Qed.

Lemma decode_val_uniq:
   (* Just not true any more, with Fragments *)
  forall ch b1 b2 v,
    v <> Vundef ->
    length b1 = size_chunk_nat ch ->
    length b2 = size_chunk_nat ch ->
    decode_val ch b1 = v ->
    decode_val ch b2 = v ->
    b1=b2.
Proof.
 intros.
 unfold size_chunk_nat in *.
 unfold decode_val in *.
 destruct (proj_bytes b1) eqn:B1.
subst v.
(*
unfold proj_pointer in H3.
destruct b1; try congruence.
destruct m; try congruence.
if_tac in H3; try congruence.
clear - H2 H3 H.
subst v.
unfold proj_pointer in *.
destruct b1; try congruence.
destruct m; try congruence.
destruct b2; try congruence. destruct m; try congruence.
destruct (check_pointer 4 b i (Pointer b i n :: b1)) eqn:?; try congruence.
destruct (check_pointer 4 b0 i0 (Pointer b0 i0 n0 :: b2)) eqn:?; try congruence.
inv H3.
clear H.
unfold check_pointer in *; simpl in *.
repeat match goal with
| H: ?A = true |- _ =>
  match A with
  | context [eq_block ?a ?b]  =>
     destruct (eq_block a b); simpl in *; try congruence
  | context [Int.eq_dec ?i ?j] =>
     destruct (Int.eq_dec i j); simpl in *; try congruence
  | context [match ?n with _ => _ end] =>
     destruct n; simpl in *; try congruence
  end
end.
} Unfocus.
destruct (proj_bytes b2) eqn:B2.
2:{
destruct ch; try congruence.
unfold proj_pointer in H3.
destruct b2; try congruence.
destruct m; try congruence.
if_tac in H3; try congruence.
}
pose proof (length_proj_bytes _ _ B1).
pose proof (length_proj_bytes _ _ B2).
rewrite <- H4 in *; rewrite <- H5 in *.
assert (l=l0).
2:{
clear - H6 B1 B2.
revert l0 b1 b2 B1 B2 H6; induction l; destruct l0; intros; inv H6.
destruct b1; inv B1. destruct b2; inv B2; auto.
destruct m; try congruence.
destruct (proj_bytes b2);  inv H0.
destruct m; inv H0.
destruct (proj_bytes b1);  inv H1.
destruct b1; inv B1.
destruct m; inv H0.
destruct (proj_bytes b1) eqn:?; inv H1.
destruct b2; inv B2.
destruct m; inv H0.
destruct (proj_bytes b2) eqn:?; inv H1.
specialize (IHl _ _ _ Heqo Heqo0).
f_equal; auto.
}
clear b1 b2 H4 H5 B1 B2.
clear H.
subst v.
destruct ch; try apply Vint_inj in H3;
simpl in H0,H1; unfold Pos.to_nat in H0,H1; simpl in H0,H1;
 (* this "try" takes care of all signed and unsigned bytes and shorts *)
try (apply decode_int_uniq; [ congruence | ];
(apply sign_ext_injective in H3 || apply zero_ext_injective in H3);
 [ congruence |  compute; split; congruence
 | apply decode_int_range; rewrite H1; reflexivity
 | apply decode_int_range; rewrite H0; reflexivity
 ]).

* (* Mint32 *)  apply repr_decode_int_inj; auto.
* (* Mint64 *) apply repr_decode_int64_inj; congruence.
* (* Mfloat32 *)
  inv H3.
  apply decode_int_uniq; [congruence | ].
  apply single_of_bits_inj in H2.
  apply repr_decode_int_inj in H2; auto.
  congruence.
  apply WH.
* (* Mfloat64 *)
  inv H3.
  apply decode_int_uniq; [congruence | ].
  apply double_of_bits_inj in H2.
  apply repr_decode_int64_inj in H2; auto.
  congruence.
Qed.
*)
Abort.


Lemma superprecise_ewand_lem1:
  forall S P: pred rmap, superprecise P ->
          S |-- P * TT ->
          S = (P * (ewand P S))%pred.
Proof.
intros.
apply pred_ext.
intros w ?. specialize (H0 w H1).
destruct H0 as [w1 [w2 [? [? _]]]].
exists w1; exists w2; split3; auto.
exists w1; exists w; split3; auto.
intros w [w1 [w2 [? [? ?]]]].
destruct H3 as [w3 [w4 [? [? ?]]]].
assert (w1=w3). eapply H; eauto.
apply join_core2 in H1; apply join_core2 in H3; unfold comparable; congruence.
subst w3.
pose proof (join_eq H1 H3); subst w4.
auto.
Qed.

(*Lemma superprecise_address_mapsto:
  wishes_eq_horses -> 
  forall ch v sh loc, 
   v<>Vundef -> superprecise (address_mapsto ch v sh loc).
Proof.
intro WH.
intros.
hnf; intros.
unfold address_mapsto in *.
destruct H0 as [b1 [[? [? ?]] ?]]; destruct H1 as [b2 [[? [? ?]] ?]].
(* just not true anymore, with Fragments *)
(*
assert (b1=b2) by (eapply decode_val_uniq; eauto).
subst b2.
assert (level w1 = level w2).
clear - H2; unfold comparable in H2.
rewrite <- level_core. rewrite <- (level_core w2).
congruence.
apply rmap_ext.
auto.
intro.
clear - H5 H8 H9 H2.
specialize (H5 l); specialize (H8 l).
hnf in H5,H8.
if_tac in H5.
destruct H5 as [p ?]. destruct H8 as [p' ?].
hnf in H0,H1.
rewrite H0,H1.
f_equal.
f_equal.
apply proof_irr.
congruence.
do 3 red in H5, H8.
unfold comparable in H2; clear - H5 H8 H2.
assert (core (w1 @ l) = core (w2 @ l)).
repeat rewrite core_resource_at.
congruence.
clear H2.
transitivity (core (w1 @ l)).
apply unit_core.
apply  identity_unit_equiv.
auto.
rewrite H.
symmetry.
apply unit_core.
apply  identity_unit_equiv.
auto.
Qed.

Require Import VST.veric.extend_tc. (-this line is in a comment-)
Require Import VST.veric.seplog. (-this line is in a comment-)

Lemma superprecise_mapsto:
 wishes_eq_horses ->
  forall sh t v1 v2,
    v2 <> Vundef ->
   superprecise (mapsto sh t v1 v2).
Proof.
intro WH.
assert (WH' := superprecise_address_mapsto WH); clear WH.
intros. rename H into Hv2.
hnf; intros.
unfold mapsto in *;
simpl in H,H0.
destruct (access_mode t); try contradiction.
destruct (type_is_volatile t); try contradiction.
destruct v1; try contradiction.
destruct H as [[_ H]|[Hz [u1 H]]]; try congruence.
destruct H0 as [[_ H0]|[Hz [u2 H0]]]; try congruence.
eapply WH'; eauto.
Qed.
*)
Abort.
*)
