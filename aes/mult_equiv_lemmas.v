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

Lemma exp_table_correct : forall a : nat, (a < 256)%nat -> 
  nth a ff_exp_table Int.zero = ff_exp (Int.repr 3) (Int.repr (Z.of_nat a)).
Proof.
  intros.
  do 256 (destruct a as [| a]; [reflexivity | ]).
  omega.
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
