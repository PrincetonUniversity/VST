Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Export veric.environ_lemmas.
Require Import veric.binop_lemmas2.
(*Require Import veric.binop_lemmas.*)
Require Import veric.expr_lemmas2.
Import Cop.
Import Cop2.

Opaque tc_andp. (* This is needed otherwise certain Qeds take
    forever in Coq 8.3.  *)

Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.

(** Definitions of some environments **)
Definition empty_genv cenv := Build_genv (Globalenvs.Genv.empty_genv fundef type nil) cenv.
Definition empty_tenv := PTree.empty val.

Definition empty_environ cenv : environ :=
mkEnviron (filter_genv (empty_genv cenv)) (Map.empty _) (Map.empty _).

Lemma Zle_bool_rev: forall x y, Zle_bool x y = Zge_bool y x.
Proof.
intros. pose proof (Zle_cases x y). pose proof (Zge_cases y x).
destruct (Zle_bool x y); destruct (Zge_bool y x); auto;
elimtype False; omega.
Qed.

(** Typechecking soundness **)

Transparent Float.to_int.
Transparent Float.to_intu.
Transparent Float32.to_int.
Transparent Float32.to_intu.


Lemma isCastR: forall {CS: compspecs} tfrom tto a,
  denote_tc_assert (isCastResultType tfrom tto a) =
 denote_tc_assert
match Cop.classify_cast tfrom tto with
| Cop.cast_case_default => tc_FF  (invalid_cast tfrom tto)
| Cop.cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_s2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_s2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_neutral  => if eqb_type tfrom tto then tc_TT else
                            (if orb  (andb (is_pointer_type tto) (is_pointer_type tfrom)) (andb (is_int_type tto) (is_int_type tfrom)) then tc_TT
                                else tc_iszero' a)
| Cop.cast_case_i2l _ => tc_bool (is_int_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_l2l => tc_bool (is_long_type tfrom && is_long_type tto) (invalid_cast_result tto tto)
| Cop.cast_case_f2bool => tc_bool (is_float_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_s2bool => tc_bool (is_single_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_p2bool =>tc_andp (tc_comparable a (Econst_int Int.zero (Tint I32 Signed noattr)))
                                                (tc_bool (orb (is_int_type tfrom) (is_pointer_type tfrom)) (invalid_cast_result tfrom tto))
| Cop.cast_case_l2bool => tc_bool (is_long_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_void => tc_noproof
| _ => match tto with
      | Tint _ _ _  => tc_bool (is_int_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F64 _  => tc_bool (is_float_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F32 _  => tc_bool (is_single_type tfrom) (invalid_cast_result tto tto)
      | _ => tc_FF (invalid_cast tfrom tto)
      end
end.
Proof. intros; extensionality rho.
 unfold isCastResultType.
 destruct (classify_cast tfrom tto) eqn:?; auto.
 destruct (eqb_type tfrom tto); auto.
 if_tac; auto. apply denote_tc_assert_iszero.
Qed.

Lemma Z2R_pow_0_lt:
  forall e,
  0 <= e ->
  Rdefinitions.Rlt 0 (Fcore_Raux.Z2R (2 ^ e)).
Proof.
intros.
rewrite <- (Z2Nat.id e) by auto.
clear.
induction (Z.to_nat e).
simpl.
apply RIneq.Rlt_0_1.
rewrite inj_S.
rewrite Z.pow_succ_r by omega.
rewrite Fcore_Raux.Z2R_mult.
apply RIneq.Rmult_lt_0_compat; auto.
simpl.
clear.
apply DiscrR.Rlt_R0_R2.
Qed.

Definition general_offloat (prec emax : Z)
    (f:  Fappli_IEEE.binary_float prec emax) : option Z :=
  match f with
  | Fappli_IEEE.B754_zero _ => Some 0
  | Fappli_IEEE.B754_infinity _ => None
  | Fappli_IEEE.B754_nan _ _ => None
  | Fappli_IEEE.B754_finite s m 0 _ => Some (Fcore_Zaux.cond_Zopp s (Z.pos m))
  | Fappli_IEEE.B754_finite s m (Z.pos e) _ =>
      Some (Fcore_Zaux.cond_Zopp s (Z.pos m) * Z.pow_pos 2 e)
  | Fappli_IEEE.B754_finite s m (Z.neg e) _ =>
      Some (Fcore_Zaux.cond_Zopp s (Z.pos m / Z.pow_pos 2 e))
  end.

Definition general_float_to_int (prec emax : Z) (lo hi: Z) (f: Fappli_IEEE.binary_float prec emax) : option int :=
 option_map Int.repr
   (Fappli_IEEE_extra.ZofB_range prec emax f lo hi).

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
rewrite Fappli_IEEE_extra.ZofB_range_correct. simpl.
unfold Fcore_Raux.Ztrunc.
rewrite Fcore_Raux.Rlt_bool_false by apply RIneq.Rle_refl.
replace (Fcore_Raux.Zfloor 0) with 0.
rewrite H0,H1. reflexivity.
unfold Fcore_Raux.Zfloor.
replace (Rdefinitions.up 0) with 1; [reflexivity |].
apply R_Ifp.tech_up; simpl.
apply RIneq.Rlt_0_1.
rewrite Raxioms.Rplus_comm.
rewrite RIneq.Rplus_0_r. apply RIneq.Rle_refl.
}
(* nonzero case *)
destruct (zle 0 e).
* (* 0 <= e *)
assert (z = Fcore_Zaux.cond_Zopp b (Z.pos m) * Z.pow 2 e). {
  destruct e; inv H3.
  rewrite Z.pow_0_r. rewrite Z.mul_1_r. auto.
  rewrite Zpower_pos_nat. rewrite Zpower_nat_Z.
  rewrite positive_nat_Z; auto.
  pose proof (Pos2Z.neg_is_neg p); omega.
}
clear H3. subst z.
rewrite Fappli_IEEE_extra.ZofB_range_correct.
replace
   (Fcore_Raux.Ztrunc
      (Fappli_IEEE.B2R prec emax (Fappli_IEEE.B754_finite prec emax b m e e0)))
  with (Fcore_Zaux.cond_Zopp b (Z.pos m) * 2^e).
rewrite H0,H1; clear H0 H1.
rewrite (Fappli_IEEE_extra.is_finite_strict_finite prec emax).
reflexivity.
reflexivity.
unfold Fcore_Zaux.cond_Zopp.
unfold Fcore_Raux.Ztrunc.
destruct b; [rewrite Fcore_Raux.Rlt_bool_true | rewrite Fcore_Raux.Rlt_bool_false].
+
unfold Fappli_IEEE.B2R.
unfold Fcore_Zaux.cond_Zopp.
unfold Fcore_Raux.Zceil.
unfold Fcore_Raux.Zfloor.
symmetry; apply Fcore_Raux.Zceil_imp; split.
eapply RIneq.Rlt_le_trans.
apply Fcore_Raux.Z2R_lt.
instantiate (1 := - Z.pos m * 2 ^ e). omega.
unfold Fcore_defs.F2R.
rewrite Fcore_Raux.Z2R_mult.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
f_equal.
simpl.
rewrite <- Fcore_Raux.Z2R_Zpower by auto.
reflexivity.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
unfold Fcore_defs.F2R.
rewrite Fcore_Raux.Z2R_mult.
simpl.
rewrite <- Fcore_Raux.Z2R_Zpower by auto.
simpl.
auto.
+
simpl. unfold Fcore_defs.F2R.
simpl.
rewrite RIneq.Ropp_mult_distr_l_reverse.
apply RIneq.Ropp_lt_gt_0_contravar.
unfold Rdefinitions.Rgt.
apply RIneq.Rmult_lt_0_compat.
clear.
rewrite Fcore_Raux.P2R_INR.
apply RIneq.lt_0_INR.
apply Pos2Nat.is_pos.
simpl.
rewrite <- Fcore_Raux.Z2R_Zpower by auto.
simpl.
apply Z2R_pow_0_lt; auto.
+
unfold Fappli_IEEE.B2R.
unfold Fcore_Zaux.cond_Zopp.
symmetry; apply Fcore_Raux.Zfloor_imp; split.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
unfold Fcore_defs.F2R.
rewrite Fcore_Raux.Z2R_mult.
simpl.
rewrite <- Fcore_Raux.Z2R_Zpower by auto.
simpl.
auto.
unfold Fcore_defs.F2R.
eapply RIneq.Rle_lt_trans.
instantiate (1:= (Fcore_Raux.Z2R (Z.pos m * 2 ^ e ))).
rewrite Fcore_Raux.Z2R_mult.
simpl.
rewrite !Fcore_Raux.P2R_INR.
rewrite <- Fcore_Raux.Z2R_Zpower by auto.
simpl.
match goal with |- _ ?A ?B => replace B with A; [apply RIneq.Rle_refl | ] end.
f_equal.
(* symmetry; apply Fcore_Raux.P2R_INR. *)
rewrite Fcore_Raux.Z2R_plus.
rewrite Raxioms.Rplus_comm.
rewrite <- RIneq.Rplus_0_r at 1.
rewrite Raxioms.Rplus_comm at 1.
apply RIneq.Rplus_lt_le_compat.
apply RIneq.Rlt_0_1.
apply RIneq.Req_le. auto.
+
unfold Fappli_IEEE.B2R.
unfold Fcore_Zaux.cond_Zopp.
unfold Fcore_defs.F2R.
simpl.
apply RIneq.Rmult_le_pos.
rewrite Fcore_Raux.P2R_INR.
apply RIneq.pos_INR.
rewrite <- Fcore_Raux.Z2R_Zpower by auto.
simpl.
apply RIneq.Rlt_le.
apply Z2R_pow_0_lt; auto.
* (* e < 0 *)
assert (HH: (Fcore_Raux.Z2R (2 ^ (- e))) <> Rdefinitions.R0). {
assert (Rdefinitions.R0 <> Fcore_Raux.Z2R (2 ^ (- e))); auto.
apply RIneq.Rlt_not_eq.
apply (Z2R_pow_0_lt (-e)).
omega.
}
assert (z = Fcore_Zaux.cond_Zopp b (Z.pos m / Z.pow 2 (- e))). {
  destruct e; inv H3.
  omega. pose proof (Zgt_pos_0 p); omega. clear g.
  rewrite Zpower_pos_nat. rewrite Zpower_nat_Z.
  rewrite positive_nat_Z; auto.
}
clear H3. subst z.
rewrite Fappli_IEEE_extra.ZofB_range_correct.
replace
   (Fcore_Raux.Ztrunc
      (Fappli_IEEE.B2R prec emax (Fappli_IEEE.B754_finite prec emax b m e e0)))
  with (Fcore_Zaux.cond_Zopp b (Z.pos m / 2^(-e))).
rewrite H0,H1; clear H0 H1.
rewrite (Fappli_IEEE_extra.is_finite_strict_finite prec emax).
reflexivity.
reflexivity.
unfold Fcore_Zaux.cond_Zopp.
unfold Fcore_Raux.Ztrunc.
destruct b; [rewrite Fcore_Raux.Rlt_bool_true | rewrite Fcore_Raux.Rlt_bool_false].
+
clear - g.
unfold Fappli_IEEE.B2R.
unfold Fcore_Zaux.cond_Zopp.
unfold Fcore_Raux.Zceil.
f_equal.
unfold Fcore_defs.F2R.
simpl.
rewrite RIneq.Ropp_mult_distr_l_reverse.
rewrite RIneq.Ropp_involutive.
rewrite <- Fcore_Raux.Zfloor_div by (apply Z.pow_nonzero; omega).
rewrite <- (Z.opp_involutive e) at 2.
rewrite (Fcore_Raux.bpow_opp _ (-e)).
symmetry.
rewrite <- Fcore_Raux.Z2R_Zpower by omega.
simpl.
unfold Rdefinitions.Rdiv.
auto.
+
simpl.
apply Fcore_float_prop.F2R_lt_0_compat.
simpl.  pose proof (Pos2Z.neg_is_neg m); omega.
+
simpl.
unfold Fcore_defs.F2R.
simpl.
rewrite <- (Z.opp_involutive e) at 2.
rewrite (Fcore_Raux.bpow_opp _ (-e)).
rewrite <- Fcore_Raux.Z2R_Zpower by omega.
simpl.
rewrite <- Fcore_Raux.Zfloor_div by (apply Z.pow_nonzero; omega).
reflexivity.
+
simpl.
unfold Fcore_defs.F2R.
simpl.
rewrite <- (Z.opp_involutive e).
rewrite (Fcore_Raux.bpow_opp _ (-e)).
rewrite <- Fcore_Raux.Z2R_Zpower by omega.
simpl.
apply RIneq.Rmult_le_pos.
rewrite Fcore_Raux.P2R_INR.
apply RIneq.pos_INR.
apply RIneq.Rlt_le.
apply RIneq.Rinv_0_lt_compat.
apply Z2R_pow_0_lt; omega.
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
omega.
Qed.

Lemma zero_ext_range':
  forall n x, 0 <= n < Int.zwordsize ->
     0 <= Int.unsigned (Int.zero_ext n x) <= two_p n - 1.
Proof.
intros.
 pose proof (Int.zero_ext_range n x H); omega.
Qed.

Lemma typecheck_cast_sound:
 forall {CS: compspecs} Delta rho m e t,
 typecheck_environ Delta rho ->
(denote_tc_assert (typecheck_expr Delta e) rho m ->
 typecheck_val (eval_expr e rho) (typeof e) = true) /\
(forall pt : type,
 denote_tc_assert (typecheck_lvalue Delta e) rho m ->
 is_pointer_type pt = true -> typecheck_val (eval_lvalue e rho) pt = true) ->
denote_tc_assert (typecheck_expr Delta (Ecast e t)) rho m ->
typecheck_val (eval_expr (Ecast e t) rho) (typeof (Ecast e t)) = true.
Proof.
intros until t; intros H IHe H0.
simpl in *. unfold_lift.
destruct IHe as [? _].
rewrite denote_tc_assert_andp in H0.
destruct H0.
specialize (H1 H0).
unfold  sem_cast, force_val1.
rewrite isCastR in H2.
destruct (classify_cast (typeof e) t)
     as [ | | | | | | | | sz [ | ] | sz [ | ] | | | | | | [ | ] | [ | ] | | | | | | | |  ]
   eqn:H3;
   try contradiction;
 destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in H3; try discriminate H3; try contradiction;
 destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in H3; try discriminate H3; try contradiction;
  simpl in H2; unfold_lift in H2; simpl in H2;
  try (rewrite denote_tc_assert_andp in H2;
        destruct H2 as [H2a H2b];
       unfold denote_tc_assert in H2a,H2b;
      unfold_lift in H2a; unfold_lift in H2b;
       simpl in H2a,H2b
    );
  destruct (eval_expr e rho); simpl in H1; try discriminate H1;
  try contradiction H2;
  try reflexivity; try assumption;
  try (apply (is_true_e _ H2));
  try (injection H3; clear H3; intros; subst);
  simpl;
  try solve [destruct (Int.eq i Int.zero); reflexivity];
  try (rewrite andb_true_iff in H1; destruct H1 as [H1 H1']);
  try rewrite Z.leb_le in H1;
  try rewrite Z.leb_le in H1';
  try (
   simpl in H2a,H2b;
    match type of H2a with app_pred match ?A with Some _ => _ | None => _ end _ =>
       destruct A eqn:H7; [ | contradiction];
      do 3 red in H2a,H2b;
       apply is_true_e in H2a; apply is_true_e in H2b;
       rewrite Z.leb_le in H2a; rewrite Z.geb_le in H2b
    end);
    try apply andb_zleb; try rewrite Z.leb_le;
   try match goal with
     | |- appcontext [Int.sign_ext ?n ?x] =>
      apply (sign_ext_range' n x); compute; split; congruence
     | |- appcontext [Int.zero_ext ?n ?x] =>
      apply (zero_ext_range' n x); compute; try split; congruence
   end;
  try (first [ erewrite float_to_int_ok | erewrite float_to_intu_ok
          | erewrite single_to_int_ok | erewrite single_to_intu_ok];
          [ | eassumption | split; assumption]);
 try match goal with |- Int.eq (if ?A then _ else _) _ || _ = _ =>
      destruct A; try reflexivity
  end;
  try (
    simpl;
    try reflexivity;
    try apply andb_zleb; try rewrite Z.leb_le;
    match goal with
     | |- appcontext [Int.sign_ext ?n ?x] =>
      apply (sign_ext_range' n x); compute; split; congruence
     | |- appcontext [Int.zero_ext ?n ?x] =>
      apply (zero_ext_range' n x); compute; try split; congruence
   end);
 try match goal with |- Int.eq (if ?A then _ else _) _ || _ = _ =>
      destruct A; try reflexivity
  end.
Qed.
