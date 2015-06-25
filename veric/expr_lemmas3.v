Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Export veric.environ_lemmas. 
Require Import veric.binop_lemmas2.
Require Import veric.binop_lemmas.
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


Lemma isCastR: forall Delta tfrom tto a, 
  denote_tc_assert Delta (isCastResultType Delta tfrom tto a) =
 denote_tc_assert Delta
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
| Cop.cast_case_p2bool => tc_bool (orb (is_int_type tfrom) (is_pointer_type tfrom)) (invalid_cast_result tfrom tto)
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

Lemma float_to_int_ok:
  forall f z, 
    Zoffloat f = Some z ->
    Int.min_signed <= z <= Int.max_signed ->
    Float.to_int f = Some (Int.repr z).
Admitted.

Lemma float_to_intu_ok:
  forall f z, 
    Zoffloat f = Some z ->
    0 <= z <= Int.max_unsigned ->
    Float.to_intu f = Some (Int.repr z).
Admitted.

Lemma single_to_int_ok:
  forall f z, 
    Zofsingle f = Some z ->
    Int.min_signed <= z <= Int.max_signed ->
    Float32.to_int f = Some (Int.repr z).
Admitted.

Lemma single_to_intu_ok:
  forall f z, 
    Zofsingle f = Some z ->
    0 <= z <= Int.max_unsigned ->
    Float32.to_intu f = Some (Int.repr z).
Admitted.
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
 forall Delta rho m e t,
 typecheck_environ Delta rho ->
(denote_tc_assert Delta (typecheck_expr Delta e) rho m ->
 typecheck_val (eval_expr Delta e rho) (typeof e) = true) /\
(forall pt : type,
 denote_tc_assert Delta (typecheck_lvalue Delta e) rho m ->
 is_pointer_type pt = true -> typecheck_val (eval_lvalue Delta e rho) pt = true) ->
denote_tc_assert Delta (typecheck_expr Delta (Ecast e t)) rho m ->
typecheck_val (eval_expr Delta (Ecast e t) rho) (typeof (Ecast e t)) = true.
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
  destruct (eval_expr Delta e rho); simpl in H1; try discriminate H1;
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
