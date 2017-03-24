Require Import floyd.proofauto.
Require Import aes.aesutils.
Require Import aes.AES256.

Require Import Coqlib.
Require Import msl.Coqlib2.
Require Import floyd.coqlib3.
Require Import Integers.
Require Import List.
Require Import floyd.sublist.
Require Import sha.SHA256.
Require Import sha.general_lemmas.

(* works, but very slow!
Lemma exp_table_correct : forall a : nat, (a < 256)%nat ->
  nth a ff_exp_table Int.zero = exp3 a.
Proof.
  intros.
  do 256 (destruct a as [| a]; [reflexivity | ]).
  omega.
Qed.
*)

Lemma nth_cons_S: forall {T: Type} (n: nat) (h: T) (tl: list T),
  nth (S n) (h :: tl) = nth n tl.
Proof. reflexivity. Qed.

Tactic Notation "int_zero_case_if" constr(v) :=
  let E := fresh in
  destruct (Int.eq_dec v Int.zero) as [E | E];
  [ rewrite E in *; rewrite Int.eq_true in *
  | rewrite (Int.eq_false _  _ E) in *].

(* TODO put this into client_lemmas.v (contains already repable_signed, which is similar but does not
   know all of them *)

(* Equality proofs for all constants from the Compcert Int module: *)
Definition int_wordsize_eq : Int.wordsize = 32%nat := eq_refl.
Definition int_zwordsize_eq : Int.zwordsize = 32 := eq_refl.
Definition int_modulus_eq : Int.modulus = 4294967296 := eq_refl.
Definition int_half_modulus_eq : Int.half_modulus = 2147483648 := eq_refl.
Definition int_max_unsigned_eq : Int.max_unsigned = 4294967295 := eq_refl.
Definition int_max_signed_eq : Int.max_signed = 2147483647 := eq_refl.
Definition int_min_signed_eq : Int.min_signed = -2147483648 := eq_refl.

Ltac my_repable_signed :=
   pose proof int_wordsize_eq;
   pose proof int_zwordsize_eq;
   pose proof int_modulus_eq;
   pose proof int_half_modulus_eq;
   pose proof int_max_unsigned_eq;
   pose proof int_max_signed_eq;
   pose proof int_min_signed_eq;
   unfold repable_signed in *;
   omega.

Lemma xtime_zero: forall (i : int),
  0 <= (Int.unsigned i) < 256 ->
  xtime i = Int.zero -> i = Int.zero.
Proof.
  intros i B H. unfold xtime in H.
  erewrite Int.modu_and in H by reflexivity.
  replace (Int.sub (Int.repr 256) Int.one) with (Int.repr 255) in H by reflexivity.
  int_zero_case_if (Int.and i (Int.repr 128)).
  - apply Int.same_bits_eq. intros j ?. rewrite Int.bits_zero.
    assert (0 <= j <= 6 \/ j = 7 \/ 8 <= j < 32) as C by my_repable_signed.
    destruct C as [C | [C | C]].
    + subst. apply (f_equal (fun x => Int.testbit x (j + 1))) in H.
      rewrite Int.bits_and in H by my_repable_signed.
      assert (Int.testbit (Int.repr 255) (j+1) = true) as E. {
        assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6) as C1 by omega.
        repeat destruct C1 as [C1 | C1]; subst j; reflexivity.
      }
      rewrite E in H.
      rewrite andb_true_r in H.
      rewrite Int.bits_shl in H by my_repable_signed.
      rewrite Int.unsigned_one in H. replace (j + 1 - 1) with j in H by omega.
      destruct (zlt (j + 1) 1). omega. rewrite H. apply Int.bits_zero.
    + subst. apply (f_equal (fun x => Int.testbit x 7)) in H0.
      rewrite Int.bits_and in H0 by my_repable_signed.
      replace (Int.testbit (Int.repr 128) 7) with true in H0 by reflexivity.
      rewrite andb_true_r in H0. rewrite H0. reflexivity.
    + unfold Int.testbit.
      apply Z.testbit_false. omega.
      rewrite Z.div_small. reflexivity.
      assert (256 <= 2 ^ j). {
        replace 256 with (2 ^ 8) by reflexivity. apply Z.pow_le_mono_r_iff; omega.
      }
      omega.
  - apply (f_equal (fun x => Int.testbit x 0)) in H.
    rewrite Int.bits_xor in H by my_repable_signed.
    replace (Int.testbit (Int.repr 27) 0) with true in H by reflexivity.
    rewrite xorb_true_r in H.
    rewrite Int.bits_zero in H.
    rewrite Int.bits_and in H by my_repable_signed.
    replace (Int.testbit (Int.repr 255) 0) with true in H by reflexivity.
    rewrite andb_true_r in H.
    rewrite Int.bits_shl in H by my_repable_signed.
    destruct (zlt 0 (Int.unsigned Int.one)); discriminate.
Qed.

Lemma fast_times3: forall (i : int),
  0 <= (Int.unsigned i) < 256 ->
  Int.xor i (xtime i) = ff_mult (Int.repr 3) i.
Proof.
  intros. unfold ff_mult. simpl.
  int_zero_case_if i.
  - reflexivity.
  - int_zero_case_if (xtime i).
    + exfalso. apply H0. apply xtime_zero; assumption.
    + unfold ff_checkbit.
      simpl. rewrite Int.xor_zero_l. reflexivity.
Qed.

Lemma ff_exp_step: forall a e,
  0 <= Int.unsigned a < 256 ->
  0 <= e < Int.max_signed ->
  ff_exp a (Int.repr (1 + e)) = ff_mult a (ff_exp a (Int.repr e)).
Proof.
  intros. unfold ff_exp.
  do 2 rewrite (Int.unsigned_repr) by repable_signed.
  rewrite Z2Nat.inj_add by omega.
  replace (Z.to_nat 1 + Z.to_nat e)%nat with (S (Z.to_nat e)) by reflexivity.
  reflexivity.
Qed.

Lemma exp3_step: forall e,
  0 <= e < Int.max_signed ->
  ff_exp (Int.repr 3) (Int.repr (1 + e)) = ff_mult (Int.repr 3) (ff_exp (Int.repr 3) (Int.repr e)).
Proof.
  intros. apply ff_exp_step.
  rewrite (Int.unsigned_repr); repable_signed.
  repable_signed.
Qed.

(* 3^e in GF(2^8) *)
Definition exp3 (e: nat): int := ff_exp (Int.repr 3) (Int.repr (Z.of_nat e)).

Lemma exp3_S: forall n,
  (0 <= n <= 256)%nat -> (* even holds for bigger n, as long as no int overflow *)
  exp3 (S n) = ff_mult (Int.repr 3) (exp3 n).
Proof.
  intros. unfold exp3.
  rewrite <- exp3_step.
  - replace (Z.of_nat (S n)) with (1 + (Z.of_nat n)).
    + reflexivity.
    + replace 1 with (Z.of_nat (S O)) by reflexivity.
      rewrite <- Nat2Z.inj_add. reflexivity.
  - assert (Z.of_nat n <= 256). {
      replace 256 with (Z.of_nat 256) by reflexivity.
      apply Nat2Z.inj_le. omega.
    }
    repable_signed.
Qed.

Lemma exp3_S_slow: forall n,
  (0 <= n <= 256)%nat -> (* even holds for bigger n, as long as no int overflow *)
  exp3 (S n) = ff_mult (Int.repr 3) (exp3 n).
Proof.
  intros. unfold exp3. unfold ff_exp. unfold repeat_op at 1. fold repeat_op.
  rewrite (Int.unsigned_repr).  rewrite (Int.unsigned_repr).
  do 2 rewrite Nat2Z.id. reflexivity. repable_signed.
  assert (Z.of_nat (S n) <= 257). {
    replace 257 with (Z.of_nat 257) by reflexivity.
    apply Nat2Z.inj_le. omega.
  }
  repable_signed.
(* Qed. <-- this takes ages, but why?? *)
Abort.

Lemma ff_exp_range: forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Int.unsigned (ff_exp (Int.repr a) (Int.repr b)) < 256.
Proof.
Admitted.

Lemma gen_exp_table_correct : forall n : nat, (n <= 256)%nat ->
  forall i : nat, (i < n)%nat ->
    nth i (gen_exp_table n (exp3 (256-n))) Int.zero = exp3 (256+i-n).
Proof.
  intro n. induction n; intros. omega.
  destruct i as [|j].
  - unfold gen_exp_table. unfold nth. reflexivity.
  - unfold gen_exp_table. fold gen_exp_table. rewrite nth_cons_S.
    rewrite fast_times3.
    + replace (256 + S j - S n)%nat with (256 + j - n)%nat by omega.
      replace (256 - n)%nat with (S (256 - S n)) in IHn by omega.
      rewrite exp3_S in IHn by omega.
      apply IHn; omega.
    + apply ff_exp_range.
      * omega.
      * replace 256 with (Z.of_nat 256) by reflexivity. split.
        { apply Nat2Z.is_nonneg. }
        { apply Nat2Z.inj_lt. omega. }
Qed.

(* slow (minutes)
Lemma exp_table_correct : forall a : nat, (a < 256)%nat ->
  nth a ff_exp_table Int.zero = exp3 a.
Proof.
  specialize (gen_exp_table_correct 256). intros C a H.
  assert (256 <= 256)%nat as L by omega.
  specialize (C L a H).
  replace (256 - 256)%nat with O in C by omega.
  replace (256 + a - 256)%nat with a in C by omega.
  apply C.
Qed.
*)

(* slow (minutes)
Lemma log_table_correct : forall a : nat, (1 < a < 256)%nat ->
  let pow := nth a ff_log_table Int.zero in
  ff_exp (Int.repr 3) pow = Int.repr (Z.of_nat a).
Proof.
  intros.
  destruct a as [| a].
  omega.
  do 255 (destruct a as [| a]; [reflexivity | ]).
  omega.
Qed.
*)

(* unfeasibly slow (150 hours are not enough)
Lemma ff_mult_equiv : forall a b : nat,
  (a < 256)%nat -> (b < 256)%nat ->
  table_ff_mult (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat b))
  = ff_mult (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat b)).
Proof.
  intros.
  do 256 (destruct a as [| a]; [do 256 (destruct b as [| b]; [reflexivity | ]); omega | ]).
  omega.
Qed.
*)
