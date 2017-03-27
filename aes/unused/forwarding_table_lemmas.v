Require Import aes.aesutils.
Require Import aes.AES256.

Require Import Coqlib.
Require Import msl.Coqlib2.
Require Import floyd.coqlib3.
Require Import Integers.
Require Import List. Import ListNotations.
Require Import floyd.sublist.
Require Import sha.SHA256.
Require Import sha.general_lemmas.
Require Import Sorting.Mergesort.

Local Open Scope logic.
(* we want to prove forward table lemmas:
 * for byte i, FT0[i] = (2 * sbox[i], sbox[i], sbox[i], 3 * sbox[i]), where * is GF(256) mult;
 * FT1[i] is the same but a rotation, etc.
 *
 * This means that FT0 corresponds to the first column of the transformation matrix in figure 5.6
 * in the official spec; FT1 is the second column, etc.
 *)

Lemma ft0_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n sbox Int.zero in
  nth n FT0 Int.zero = word_to_int (ff_mult b (Int.repr 2),  b, b, ff_mult b (Int.repr 3)).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

Lemma ft1_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n sbox Int.zero in
  nth n FT1 Int.zero = word_to_int (ff_mult b (Int.repr 3), ff_mult b (Int.repr 2), b, b).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

Lemma ft2_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n sbox Int.zero in
  nth n FT2 Int.zero = word_to_int (b, ff_mult b (Int.repr 3), ff_mult b (Int.repr 2), b).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

Lemma ft3_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n sbox Int.zero in
  nth n FT3 Int.zero = word_to_int (b, b, ff_mult b (Int.repr 3), ff_mult b (Int.repr 2)).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

(* Analogous reverse table lemmas with figure 5.10 *)

Lemma rt0_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n inv_sbox Int.zero in
  (* (0x0e, 0x09, 0x0d, 0x0b) *)
  nth n RT0 Int.zero = word_to_int (ff_mult b (Int.repr 14), ff_mult b (Int.repr 9),
                                    ff_mult b (Int.repr 13), ff_mult b (Int.repr 11)).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

Lemma rt1_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n inv_sbox Int.zero in
  (* (0x0b, 0x0e, 0x09, 0x0d) *)
  nth n RT1 Int.zero = word_to_int (ff_mult b (Int.repr 11), ff_mult b (Int.repr 14),
                                    ff_mult b (Int.repr 9), ff_mult b (Int.repr 13)).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

Lemma rt2_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n inv_sbox Int.zero in
  (* (0x0d, 0x0b, 0x0e, 0x09) *)
  nth n RT2 Int.zero = word_to_int (ff_mult b (Int.repr 13), ff_mult b (Int.repr 11),
                                    ff_mult b (Int.repr 14), ff_mult b (Int.repr 9)).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.

Lemma rt3_equiv : forall n : nat,
  (n < 256)%nat ->
  let b := nth n inv_sbox Int.zero in
  (* (0x09, 0x0d, 0x0b, 0x0e) *)
  nth n RT3 Int.zero = word_to_int (ff_mult b (Int.repr 9), ff_mult b (Int.repr 13),
                                    ff_mult b (Int.repr 11), ff_mult b (Int.repr 14)).
Proof.
  intros.
  do 256 (destruct n as [ | n]; [reflexivity | ]).
  omega.
Qed.
