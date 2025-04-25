Require Import Coq.Reals.Rdefinitions.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.expr_lemmas2.

Require Import VST.veric.seplog. (*For definition of typecheck_environ*)

Import Cop.
Import Cop2.
Import Clight_Cop2.
Import Ctypes.
Import Clight.

Lemma type_eq_true : forall a b, proj_sumbool (type_eq a b) = true -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.

(** Definitions of some environments **)
Definition empty_genv cenv := Build_genv (Globalenvs.Genv.empty_genv fundef type nil) cenv.
Definition empty_tenv := Maps.PTree.empty val.

Definition empty_environ cenv : environ :=
mkEnviron (filter_genv (empty_genv cenv)) (Map.empty _) (Map.empty _).

Lemma Zle_bool_rev: forall x y, Zle_bool x y = Zge_bool y x.
Proof.
intros. pose proof (Zle_cases x y). pose proof (Zge_cases y x).
destruct (Zle_bool x y); destruct (Zge_bool y x); auto;
exfalso; lia.
Qed.

(** Typechecking soundness **)

Transparent Float.to_int.
Transparent Float.to_intu.
Transparent Float32.to_int.
Transparent Float32.to_intu.

Section mpred.

Context `{!heapGS Σ}.

Lemma isCastR: forall {CS: compspecs} tfrom tto a,
  denote_tc_assert (isCastResultType tfrom tto a) =
 denote_tc_assert
match classify_cast tfrom tto with
| Cop.cast_case_default => tc_FF  (invalid_cast tfrom tto)
| Cop.cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_s2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_s2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_i2l _ =>
           tc_andp (tc_bool (is_int_type tfrom) (invalid_cast_result tfrom tto))
             (if is_pointer_type tto then tc_iszero a else tc_TT)
| Cop.cast_case_l2i _ _ => 
           tc_andp (tc_bool (is_long_type tfrom) (invalid_cast_result tfrom tto))
             (if is_pointer_type tto then tc_iszero a else tc_TT)
| Cop.cast_case_pointer  => 
           if eqb_type tfrom tto then tc_TT else
           if orb  (andb (is_pointer_type tto) (is_pointer_type tfrom))
                       (if Archi.ptr64
                        then (andb (is_long_type tto) (is_long_type tfrom)) 
                        else (andb (is_int_type tto) (is_int_type tfrom)))
           then tc_TT else 
           if (andb (eqb_type tto int_or_ptr_type) ((if Archi.ptr64 then is_long_type else is_int_type) tfrom))
           then tc_TT else
           if (andb (eqb_type tto int_or_ptr_type) (is_pointer_type tfrom))
           then tc_TT else
           if (andb (eqb_type tfrom int_or_ptr_type) (is_pointer_type tto))
           then tc_isptr a else
           if (andb (eqb_type tfrom int_or_ptr_type) ((if Archi.ptr64 then is_long_type else is_int_type) tto))
           then (if Archi.ptr64 then tc_islong else tc_isint) a
           else tc_iszero a
| Cop.cast_case_l2l => tc_bool (is_long_type tfrom && is_long_type tto) (invalid_cast_result tto tto)
| Cop.cast_case_f2bool => tc_bool (is_float_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_s2bool => tc_bool (is_single_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_l2bool => 
      if is_pointer_type tfrom
      then tc_test_eq a (Econst_long Int64.zero (Tlong Unsigned noattr))
      else tc_TT
| Cop.cast_case_i2bool =>
      if is_pointer_type tfrom
      then tc_test_eq a (Econst_int Int.zero (Tint I32 Unsigned noattr))
      else tc_TT
| Cop.cast_case_void => tc_noproof
| Cop.cast_case_i2s _ => tc_TT
| Cop.cast_case_i2f _ => tc_TT
| _ => match tto with
      | Tint _ _ _  => tc_bool (is_int_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F64 _  => tc_bool (is_anyfloat_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F32 _  => tc_bool (is_anyfloat_type tfrom) (invalid_cast_result tto tto)
      | _ => tc_FF (invalid_cast tfrom tto)
      end
end.
Proof. intros; extensionality rho.
 unfold isCastResultType.
 destruct (classify_cast tfrom tto) eqn:?; auto.
Qed.

Lemma IZR_pow_0_lt:
  forall e,
  0 <= e ->
  Rdefinitions.Rlt 0 (IZR (2 ^ e)).
Proof.
intros.
rewrite <- (Z2Nat.id e) by auto.
clear.
induction (Z.to_nat e).
simpl.
apply RIneq.Rlt_0_1.
rewrite inj_S.
rewrite -> Z.pow_succ_r by lia.
rewrite RIneq.mult_IZR.
apply RIneq.Rmult_lt_0_compat; auto.
simpl.
clear.
apply DiscrR.Rlt_R0_R2.
Qed.

Definition general_offloat (prec emax : Z)
    (f:  Binary.binary_float prec emax) : option Z :=
  match f with
  | Binary.B754_zero _ => Some 0
  | Binary.B754_infinity _ => None
  | Binary.B754_nan _ _ _ => None
  | Binary.B754_finite s m 0 _ => Some (Zaux.cond_Zopp s (Z.pos m))
  | Binary.B754_finite s m (Z.pos e) _ =>
      Some (Zaux.cond_Zopp s (Z.pos m) * Z.pow_pos 2 e)
  | Binary.B754_finite s m (Z.neg e) _ =>
      Some (Zaux.cond_Zopp s (Z.pos m / Z.pow_pos 2 e))
  end.

Definition general_float_to_int (prec emax : Z) (lo hi: Z) (f: Binary.binary_float prec emax) : option int :=
 option_map Int.repr
   (IEEE754_extra.ZofB_range prec emax f lo hi).

Goal Zoffloat = general_offloat 53 1024.
reflexivity.
Qed.

Goal Zofsingle = general_offloat 24 128.
reflexivity.
Qed.

Goal Float.to_int = general_float_to_int 53 1024 Int.min_signed Int.max_signed.
reflexivity.
Qed.

Goal Float.to_intu = general_float_to_int 53 1024 0 Int.max_unsigned.
reflexivity.
Qed.

Goal Float32.to_int = general_float_to_int 24 128 Int.min_signed Int.max_signed.
reflexivity.
Qed.

Goal Float32.to_intu = general_float_to_int 24 128 0 Int.max_unsigned.
reflexivity.
Qed.

Lemma IZR_pos_gt_0:
 forall m, (IZR (Z.pos m) > 0)%R.
Proof.
intros.
unfold IZR.
rewrite <- RIneq.INR_IPR.
apply RIneq.pos_INR_nat_of_P.
Qed.

Lemma general_float_to_int_ok:
  forall prec emax lo hi f z,
    general_offloat prec emax f = Some z ->
    lo <= z <= hi ->
    general_float_to_int prec emax lo hi f = Some (Int.repr z).
Proof.
intros.
unfold general_offloat in H.
unfold general_float_to_int.
destruct H0 as [H0 H1].
apply Z.leb_le in H0; apply Z.leb_le in H1.
destruct f; inv H.
{ (* zero case *)
rewrite IEEE754_extra.ZofB_range_correct. simpl.
unfold Raux.Ztrunc.
rewrite -> Raux.Rlt_bool_false by apply RIneq.Rle_refl.
replace (Raux.Zfloor 0) with 0.
rewrite H0 H1. reflexivity.
unfold Raux.Zfloor.
replace (Rdefinitions.up 0) with 1; [reflexivity |].
apply R_Ifp.tech_up; simpl.
apply RIneq.Rlt_0_1.
rewrite Raxioms.Rplus_comm.
rewrite RIneq.Rplus_0_r. apply RIneq.Rle_refl.
}
(* nonzero case *)
destruct (zle 0 e).
* (* 0 <= e *)
rename s into b.
assert (z = Zaux.cond_Zopp b (Z.pos m) * Z.pow 2 e). {
  destruct e; inv H3.
  rewrite Z.pow_0_r. rewrite Z.mul_1_r. auto.
  rewrite Zpower_pos_nat. rewrite Zpower_nat_Z.
  rewrite positive_nat_Z; auto.
  pose proof (Pos2Z.neg_is_neg p); lia.
}
clear H3. subst z.
rewrite IEEE754_extra.ZofB_range_correct.
replace
   (Raux.Ztrunc
      (Binary.B2R prec emax (Binary.B754_finite prec emax b m e e0)))
  with (Zaux.cond_Zopp b (Z.pos m) * 2^e).
rewrite H0 H1; clear H0 H1.
rewrite (IEEE754_extra.is_finite_strict_finite prec emax).
reflexivity.
reflexivity.
unfold Zaux.cond_Zopp.
unfold Raux.Ztrunc.
destruct b; [rewrite Raux.Rlt_bool_true | rewrite Raux.Rlt_bool_false].
+
unfold Binary.B2R.
unfold Zaux.cond_Zopp.
unfold Raux.Zceil.
unfold Raux.Zfloor.
symmetry; apply Raux.Zceil_imp; split.
eapply RIneq.Rlt_le_trans.
apply RIneq.IZR_lt.
instantiate (1 := - Z.pos m * 2 ^ e). lia.
unfold Defs.F2R.
rewrite RIneq.mult_IZR.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
f_equal.
simpl.
rewrite <- Raux.IZR_Zpower by auto.
reflexivity.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
unfold Defs.F2R.
rewrite RIneq.mult_IZR.
simpl.
rewrite <- Raux.IZR_Zpower by auto.
simpl.
auto.
+
simpl. unfold Defs.F2R.
simpl.
change (Z.neg m) with (- (Z.pos m)).
rewrite RIneq.opp_IZR.
rewrite RIneq.Ropp_mult_distr_l_reverse.
apply RIneq.Ropp_lt_gt_0_contravar.
apply RIneq.Rmult_gt_0_compat.
apply IZR_pos_gt_0.
apply RIneq.Rlt_gt.
apply Raux.bpow_gt_0.
+
unfold Binary.B2R.
unfold Zaux.cond_Zopp.
symmetry; apply Raux.Zfloor_imp; split.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
unfold Defs.F2R.
rewrite RIneq.mult_IZR.
simpl.
rewrite <- Raux.IZR_Zpower by auto.
simpl.
auto.
unfold Defs.F2R.
eapply RIneq.Rle_lt_trans.
instantiate (1:= (IZR (Z.pos m * 2 ^ e ))).
rewrite RIneq.mult_IZR.
simpl.
rewrite <- Raux.IZR_Zpower by auto.
(* rewrite !Fcore_Raux.P2R_INR. *)
simpl.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
f_equal.
(* symmetry; apply Fcore_Raux.P2R_INR. *)
rewrite RIneq.plus_IZR.
rewrite Raxioms.Rplus_comm.
rewrite <- RIneq.Rplus_0_r at 1.
rewrite -> Raxioms.Rplus_comm at 1.
apply RIneq.Rplus_lt_le_compat.
apply RIneq.Rlt_0_1.
apply RIneq.Req_le. auto.
+
unfold Binary.B2R.
unfold Zaux.cond_Zopp.
unfold Defs.F2R.
simpl.
apply RIneq.Rmult_le_pos.
left.
apply IZR_pos_gt_0.
apply Raux.bpow_ge_0.
* (* e < 0 *)
assert (HH: (IZR (2 ^ (- e))) <> Rdefinitions.R0). {
assert (Rdefinitions.R0 <> IZR (2 ^ (- e))); auto.
apply RIneq.Rlt_not_eq.
apply IZR_pow_0_lt.
lia.
}
rename s into b.
assert (z = Zaux.cond_Zopp b (Z.pos m / Z.pow 2 (- e))). {
  destruct e; inv H3.
  clear g.
  rewrite Zpower_pos_nat. rewrite Zpower_nat_Z.
  rewrite positive_nat_Z; auto.
}
clear H3. subst z.
rewrite IEEE754_extra.ZofB_range_correct.
replace
   (Raux.Ztrunc
      (Binary.B2R prec emax (Binary.B754_finite prec emax b m e e0)))
  with (Zaux.cond_Zopp b (Z.pos m / 2^(-e))).
rewrite H0 H1; clear H0 H1.
rewrite (IEEE754_extra.is_finite_strict_finite prec emax).
reflexivity.
reflexivity.
unfold Zaux.cond_Zopp.
unfold Raux.Ztrunc.
destruct b; [rewrite Raux.Rlt_bool_true | rewrite Raux.Rlt_bool_false].
+
clear - g.
unfold Binary.B2R.
unfold Zaux.cond_Zopp.
unfold Raux.Zceil.
f_equal.
unfold Defs.F2R.
simpl.
change (Z.neg m) with (- (Z.pos m)).
rewrite RIneq.opp_IZR.
rewrite RIneq.Ropp_mult_distr_l_reverse.
rewrite RIneq.Ropp_involutive.
rewrite <- Raux.Zfloor_div by (apply Z.pow_nonzero; lia).
rewrite <- (Z.opp_involutive e) at 2.
rewrite (Raux.bpow_opp _ (-e)).
symmetry.
rewrite <- Raux.IZR_Zpower by lia.
simpl.
unfold Rdefinitions.Rdiv.
auto.
+
simpl.
apply Float_prop.F2R_lt_0.
simpl. pose proof (Pos2Z.neg_is_neg m); lia.
+
simpl.
unfold Defs.F2R.
simpl.
rewrite <- (Z.opp_involutive e) at 2.
rewrite (Raux.bpow_opp _ (-e)).
rewrite <- Raux.IZR_Zpower by lia.
simpl.
rewrite <- Raux.Zfloor_div by (apply Z.pow_nonzero; lia).
reflexivity.
+
simpl.
unfold Defs.F2R.
simpl.
rewrite <- (Z.opp_involutive e).
rewrite (Raux.bpow_opp _ (-e)).
rewrite <- Raux.IZR_Zpower by lia.
simpl.
apply RIneq.Rmult_le_pos.
left. apply IZR_pos_gt_0. 
apply RIneq.Rlt_le.
apply RIneq.Rinv_0_lt_compat.
apply IZR_pow_0_lt. lia.
Qed.


Lemma float_to_int_ok:
  forall f z,
    Zoffloat f = Some z ->
    Int.min_signed <= z <= Int.max_signed ->
    Float.to_int f = Some (Int.repr z).
Proof.
apply general_float_to_int_ok.
Qed.

Lemma float_to_intu_ok:
  forall f z,
    Zoffloat f = Some z ->
    0 <= z <= Int.max_unsigned ->
    Float.to_intu f = Some (Int.repr z).
Proof.
apply general_float_to_int_ok.
Qed.

Lemma single_to_int_ok:
  forall f z,
    Zofsingle f = Some z ->
    Int.min_signed <= z <= Int.max_signed ->
    Float32.to_int f = Some (Int.repr z).
Proof.
apply general_float_to_int_ok.
Qed.

Lemma single_to_intu_ok:
  forall f z,
    Zofsingle f = Some z ->
    0 <= z <= Int.max_unsigned ->
    Float32.to_intu f = Some (Int.repr z).
Proof.
apply general_float_to_int_ok.
Qed.

(* not necessary if rewrite denote_tc_assert_andp *)
(*
Lemma denote_tc_assert_andp_e:
  forall a b rho, denote_tc_assert Delta (tc_andp a b) rho ->
         denote_tc_assert Delta a rho /\ denote_tc_assert Delta b rho.
Proof.
intros.
rewrite denote_tc_assert_andp in H; auto.
Qed.
*)
Lemma andb_zleb:
 forall i j k : Z,  i <= j <= k ->
      (i <=? j) && (j <=? k) = true.
Proof.
intros ? ? ? [? ?]; rewrite andb_true_iff; split;
 apply Z.leb_le; auto.
Qed.

Lemma sign_ext_range':
    forall n x, 0 < n < Int.zwordsize ->
      - two_p (n - 1) <= Int.signed (Int.sign_ext n x) <= two_p (n - 1) -1.
Proof.
intros.
pose proof (Int.sign_ext_range n x H).
lia.
Qed.

Lemma zero_ext_range':
  forall n x, 0 <= n < Int.zwordsize ->
     0 <= Int.unsigned (Int.zero_ext n x) <= two_p n - 1.
Proof.
intros.
 pose proof (Int.zero_ext_range n x H); lia.
Qed.

Lemma int64_eq_e: forall i, Int64.eq i Int64.zero = true -> i=Int64.zero.
Proof.
intros.
pose proof (Int64.eq_spec i Int64.zero). rewrite H in H0; auto.
Qed.

Lemma long_int_zero_lem:
  forall i, Int64.eq (Int64.repr (Int64.unsigned i)) Int64.zero = true ->
    Int.repr (Int64.unsigned i) = Int.zero.
Proof.
 intros.
 apply int64_eq_e in H.
unfold Int.zero.
rewrite Int64.repr_unsigned in H.
subst.
reflexivity.
Qed.

Lemma typecheck_cast_sound:
 forall {CS: compspecs} Delta rho e t,
 typecheck_environ Delta rho ->
 (denote_tc_assert (typecheck_expr Delta e) rho ⊢
  ⌜tc_val (typeof e) (expr.eval_expr e rho)⌝)  ->
denote_tc_assert (typecheck_expr Delta (Ecast e t)) rho ⊢
⌜tc_val (typeof (Ecast e t)) (expr.eval_expr (Ecast e t) rho)⌝.
Proof.
intros until t; intros H IH.
unfold typecheck_expr; fold typecheck_expr.
simpl in *. unfold_lift.
rewrite denote_tc_assert_andp.
rewrite IH; iIntros "[%H1 H]".
unfold sem_cast, force_val1.
rewrite isCastR.
destruct (classify_cast (typeof e) t)
     as [ | | | | | | | | sz [ | ] | sz [ | ] | | | | | | [ | ] | [ | ] | | | | | | | |  ]
   eqn:H3;
   try iIntros "[]";
 destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    try discriminate H3; try iIntros "[]";
 destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    try discriminate H3; try iIntros "[]";
  unfold classify_cast in H3;
  try replace (if Archi.ptr64 then false else false) with false by (destruct Archi.ptr64; auto);
(*  repeat (progress unfold_lift; simpl);  (* needed ? *) *)
  unfold tc_val, is_pointer_type in *;
  repeat match goal with |- context [eqb_type ?A ?B] =>
              let J := fresh "J" in 
              destruct (eqb_type A B) eqn:J;
             [apply eqb_type_true in J | apply eqb_type_false in J]
    end;
  repeat match goal with H: context [eqb_type ?A ?B] |- _ =>
              let J := fresh "J" in 
              destruct (eqb_type A B) eqn:J;
             [apply eqb_type_true in J | apply eqb_type_false in J]
    end;
   try discriminate;
   rewrite -> ?if_true in H3 by auto; rewrite -> ?if_false in H3 by (clear; congruence);
   try (destruct Archi.ptr64 eqn:?Hp; try discriminate; [idtac]);
   rewrite /= ?denote_tc_assert_andp ?denote_tc_assert_iszero ?tc_bool_e /denote_tc_assert /denote_tc_Zle /denote_tc_Zge; unfold_lift;
   destruct (expr.eval_expr e rho); try solve [contradiction H1];
   try ((destruct (Zoffloat f) eqn: Hf || destruct (Zofsingle f) eqn: Hf); try iDestruct "H" as "[[] []]");
   try iDestruct "H" as %?; iPureIntro;
   try apply I;
   try contradiction;
   unfold sem_cast_pointer, sem_cast_i2i, sem_cast_f2f, sem_cast_s2s,
   sem_cast_f2i, sem_cast_s2i, cast_float_int, is_pointer_or_null, force_val in *;
   rewrite -> ?Hp in *;
   repeat match goal with
        | H: is_true _ |- _ => apply is_true_e in H; 
                                      try (apply int_eq_e in H; subst);
                                      try (apply int64_eq_e in H; subst)
       end;
    auto;
    inv H3;
   try (simpl in H1|-*;
      match goal with
      | |- context[Int.sign_ext ?n ?x] =>
      apply (sign_ext_range' n x); compute; split; congruence
      | |- context[Int.zero_ext ?n ?x] =>
      apply (zero_ext_range' n x); compute; try split; congruence
     end);
   simpl;
    try match goal with |- (if ?A then _ else _) = _ \/ (if ?A then _ else _) = _ =>
      destruct A; solve [auto]
     end;
  repeat  match goal with
    | H: match ?A with Some _ => _ | None => _ end |- _ =>
         destruct A eqn:?; [  | contradiction H]
    | H: is_true _ |- _ => apply is_true_e in H;
           rewrite ?Z.leb_le ?Z.geb_le in H
          end.
all: try (simpl in *;
          first [ erewrite float_to_int_ok | erewrite float_to_intu_ok
          | erewrite single_to_int_ok | erewrite single_to_intu_ok];
          [ | eassumption | split; lia]).
all:   try match goal with
     | |- context[Int.sign_ext ?n ?x] =>
      apply (sign_ext_range' n x); compute; split; congruence
     | |- context[Int.zero_ext ?n ?x] =>
      apply (zero_ext_range' n x); compute; try split; congruence
   end.
all: try apply I.
all: rewrite ?Hp; hnf; auto.
Qed.

End mpred.
