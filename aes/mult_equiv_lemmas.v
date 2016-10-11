Require Import floyd.proofauto.
Require Import aesutils.
Require Import AES256.

Require Import Coqlib.
Require Import msl.Coqlib2. 
Require Import floyd.coqlib3.
Require Import Integers.
Require Import List.
Require Import floyd.sublist.
Require Import sha.SHA256.
Require Import sha.general_lemmas.

(* 3^e in GF(2^8) *)
Definition exp3 (e: nat): int := ff_exp (Int.repr 3) (Int.repr (Z.of_nat e)).

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

(* TODO QQQ am I reinventing the wheel? *)
Ltac omega' := replace Int.zwordsize with 32 in * by reflexivity; omega.

Lemma xtime_zero: forall i,
  (* TODO what if i too big? *)
  xtime i = Int.zero -> i = Int.zero.
Proof.
  intros. unfold xtime in H.
  erewrite Int.modu_and in H by reflexivity.
  replace (Int.sub (Int.repr 256) Int.one) with (Int.repr 255) in H by reflexivity.
  int_zero_case_if (Int.and i (Int.repr 128)).
  - apply Int.same_bits_eq. intros j ?. rewrite Int.bits_zero.
    assert (0 <= j <= 6 \/ j = 7 \/ 8 <= j < 32) as C by omega'.
    destruct C as [C | [C | C]].
    + subst. apply (f_equal (fun x => Int.testbit x (j + 1))) in H.
      rewrite Int.bits_and in H by omega'.
      assert (Int.testbit (Int.repr 255) (j+1) = true) as E. {
        assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6) as C1 by omega.
        repeat destruct C1 as [C1 | C1]; subst j; reflexivity.
      }
      rewrite E in H.
      rewrite andb_true_r in H.
      rewrite Int.bits_shl in H by omega'.
      rewrite Int.unsigned_one in H. replace (j + 1 - 1) with j in H by omega.
      destruct (zlt (j + 1) 1). omega. rewrite H. apply Int.bits_zero.
    + subst. apply (f_equal (fun x => Int.testbit x 7)) in H0.
      rewrite Int.bits_and in H0 by omega'.
      replace (Int.testbit (Int.repr 128) 7) with true in H0 by reflexivity.
      rewrite andb_true_r in H0. rewrite H0. reflexivity.
    + admit.
  - apply (f_equal (fun x => Int.testbit x 0)) in H.
    rewrite Int.bits_xor in H by omega'.
    replace (Int.testbit (Int.repr 27) 0) with true in H by reflexivity.
    rewrite xorb_true_r in H.
    rewrite Int.bits_zero in H.
    rewrite Int.bits_and in H by omega'.
    replace (Int.testbit (Int.repr 255) 0) with true in H by reflexivity.
    rewrite andb_true_r in H.
    rewrite Int.bits_shl in H by omega'.
    destruct (zlt 0 (Int.unsigned Int.one)); discriminate.
Qed.

Lemma fast_times3: forall (i: int),
  Int.xor i (xtime i) = ff_mult (Int.repr 3) i.
Proof.
  intros. unfold ff_mult. simpl.
  int_zero_case_if i.
  - reflexivity.
  - int_zero_case_if (xtime i).
    + exfalso. apply H. apply xtime_zero. assumption.
    + unfold ff_checkbit.
      simpl. rewrite Int.xor_zero_l. reflexivity.
Qed.

Lemma xtime_step: forall (m: nat), 
  Int.xor (exp3 m) (xtime (exp3 m)) = exp3 (S m).
Proof.
  intro. unfold exp3. unfold ff_exp.
  assert (0 <= Z.of_nat (S m) <= Int.max_unsigned) by admit.
  assert (0 <= Z.of_nat    m  <= Int.max_unsigned) by admit.
  rewrite (Int.unsigned_repr _ H).
  rewrite (Int.unsigned_repr _ H0).
  do 2 rewrite Nat2Z.id.
  apply fast_times3.
Admitted.

Lemma gen_exp_table_correct : forall n : nat, (n <= 256)%nat -> 
  forall i : nat, (i < n)%nat ->
    nth i (gen_exp_table n (exp3 (256-n))) Int.zero = exp3 (256+i-n).
Proof.
  intro n. induction n; intros. omega.
  destruct i as [|j].
  - unfold gen_exp_table. unfold nth. reflexivity.
  - unfold gen_exp_table. fold gen_exp_table. rewrite nth_cons_S.
    rewrite xtime_step.
    replace (S (256 - S n)) with (256 - n)%nat by omega.
    replace (256 + S j - S n)%nat with (256 + j - n)%nat by omega.
    apply IHn; omega.
Qed.

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

Lemma ff_mult_equiv : forall a b : nat,
  (a < 256)%nat -> (b < 256)%nat ->
  table_ff_mult (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat b)) 
  = ff_mult (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat b)).
Proof.
  intros.
  do 256 (destruct a as [| a]; [do 256 (destruct b as [| b]; [reflexivity | ]); omega | ]).
  omega.
Qed.
