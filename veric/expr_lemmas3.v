Require Import Coq.Reals.Rdefinitions.
Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.expr_lemmas2.
Import Cop.
Import Cop2.
Import Clight_Cop2.

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
           (if orb  (andb (is_pointer_type tto) (is_pointer_type tfrom))
                       (if Archi.ptr64
                        then (andb (is_long_type tto) (is_long_type tfrom)) 
                        else (andb (is_int_type tto) (is_int_type tfrom)))
              then tc_TT
              else tc_iszero a)
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
 forall {CS: compspecs} Delta rho m e t,
 typecheck_environ Delta rho ->
 (denote_tc_assert (typecheck_expr Delta e) rho m ->
   tc_val (typeof e) (eval_expr e rho))  ->
denote_tc_assert (typecheck_expr Delta (Ecast e t)) rho m ->
tc_val (typeof (Ecast e t)) (eval_expr (Ecast e t) rho).
Proof.
intros until t; intros H H1 H0.
simpl in *. unfold_lift.
rewrite denote_tc_assert_andp in H0.
destruct H0.
specialize (H1 H0); clear H0.
unfold  sem_cast, force_val1.
rewrite isCastR in H2.
destruct (classify_cast (typeof e) t)
     as [ | | | | | | | | sz [ | ] | sz [ | ] | | | | | | [ | ] | [ | ] | | | | | | | |  ]
   eqn:H3;
   try contradiction;
 destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    try discriminate H3; try contradiction;
 destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    try discriminate H3; try contradiction;
  unfold classify_cast in H3;
  try replace (if Archi.ptr64 then false else false) with false in H2 by (destruct Archi.ptr64; auto);
  repeat (progress unfold_lift in H2; simpl in H2);  (* needed ? *)
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
   rewrite ?if_true in H3 by auto; rewrite ?if_false in H3 by (clear; congruence);
   try (destruct Archi.ptr64 eqn:?Hp; try discriminate; [idtac]);
  repeat match goal with
       | H: app_pred (denote_tc_assert (tc_andp _ _) _) _ |- _ => 
          rewrite denote_tc_assert_andp in H; destruct H
       | H: app_pred (denote_tc_assert (if ?A then _ else _) _) _ |- _ =>
           first [change A with false in H | change A with true in H]; cbv iota in H
       | H: app_pred (denote_tc_assert (tc_iszero _) _) _ |- _ =>
                   rewrite denote_tc_assert_iszero in H
       | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => apply tc_bool_e in H
       | H: app_pred (denote_tc_assert _ _) _ |- _ =>
             unfold denote_tc_assert, denote_tc_Zle, denote_tc_Zge in H;
             unfold_lift in H
       end;
   destruct (eval_expr e rho); try solve [contradiction H1];
   try apply I;
   try solve [contradiction];
   unfold sem_cast_pointer, sem_cast_i2i, sem_cast_f2f, sem_cast_s2s,
   sem_cast_f2i, sem_cast_s2i, cast_float_int, is_pointer_or_null, force_val in *;
   repeat rewrite Hp in *;
   repeat match goal with
        | H: app_pred (prop _) _ |- _ => apply is_true_e in H; 
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
    | H: app_pred match ?A with Some _ => _ | None => _ end _ |- _ =>
         destruct A eqn:?; [  | contradiction H]
    | H: app_pred (prop _) _ |- _ => apply is_true_e in H;
           rewrite ?Z.leb_le, ?Z.geb_le in H
   end.
all: try (simpl in H0,H2;
          first [ erewrite float_to_int_ok | erewrite float_to_intu_ok
          | erewrite single_to_int_ok | erewrite single_to_intu_ok];
          [ | eassumption | split; omega]).
all:   try match goal with
     | |- context[Int.sign_ext ?n ?x] =>
      apply (sign_ext_range' n x); compute; split; congruence
     | |- context[Int.zero_ext ?n ?x] =>
      apply (zero_ext_range' n x); compute; try split; congruence
   end.
all: try apply I.
all: rewrite ?Hp; hnf; auto.
all: apply long_int_zero_lem; auto.
Qed.
