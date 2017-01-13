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

Local Open Scope logic.

Lemma extra_expansion_sublist : forall k : list word,
  Zlength k = Nk -> sublist 0 (Nb*(Nr+1)) (blocks_to_ints (extra_key_expansion k)) = blocks_to_ints (KeyExpansion k).
Proof.
  intros.
  simpl.
  unfold extra_key_expansion.
  unfold KeyExpansion.
  assert (length k = 8%nat).
    rewrite Zlength_correct in H.
    apply Nat2Z.inj.
    auto.
  do 9 (destruct k as [ | ?w k]; try (inv H0; rename H2 into H0)).
  reflexivity.
Qed.

(* FIPS 197 section 5.3.5 mentions that ShiftRows and SubBytes (or InvShiftRows and
 * InvSubBytes) can commute. Normally, we would stipulate that the blocks are in bounds,
 * but it actually turns out to be unnecessary for the proof. *)

Lemma subbytes_shiftrows_comm : forall b : block,
  ShiftRows (SubBytes b) = SubBytes (ShiftRows b).
Proof.
  intros.
  destruct b as [[[[[[? ?] ?] ?] [[[? ?] ?] ?]] [[[? ?] ?] ?]] [[[? ?] ?] ?]].
  reflexivity.
Qed.

Lemma invsubbytes_invshiftrows_comm : forall b : block,
    InvShiftRows (InvSubBytes b) = InvSubBytes (InvShiftRows b).
Proof.
  intros.
  destruct b as [[[[[[? ?] ?] ?] [[[? ?] ?] ?]] [[[? ?] ?] ?]] [[[? ?] ?] ?]].
  reflexivity.
Qed.

(* FIPS 197 section 5.3.5 mentions that MixColumns and InvMixColumns are linear over
 * XOR (i.e., AddRoundKey) *)

(*
Lemma mixcolumns_xor_linear: forall s : state, rk : block,
    block_in_bounds s -> block_in_bounds rk ->
    MixColumns (AddRoundKey s rk) = AddRoundKey (MixColumns s) (MixColumns rk)
*)

(*
Lemma invmixcolumns_xor_linear : forall s : state, rk : block,
    block_in_bounds s -> block_in_bounds rk ->
    InvMixColumns (AddRoundKey s rk) = AddRoundKey (InvMixColumns s) (InvMixColumns rk).
*)

(* To show correctness of the implementation of the AES ciper round,
 * we will need to take into account that the XOR of C ints also XORs the
 * individual bytes *)
(*
Lemma xor_bytes : forall x y : int,
  let x_bytes := map Int.repr (intlist_to_Zlist [x]) in
  let y_bytes := map Int.repr (intlist_to_Zlist [y]) in
  map Int.repr (intlist_to_Zlist [Int.xor x y]) = map2 Int.xor x_bytes y_bytes.
*)

(* This would show that the mbed TLS implementation of the encryption round is equivalent to
 * the one in the functional spec *)
(*
Lemma round_equiv : forall (s : state) (rk : block),
  block_in_bounds s -> block_in_bounds rk ->
  block_to_ints (transpose (round s rk)) = mbed_tls_fround (block_to_ints (transpose s)) (block_to_ints (transpose rk)).
*)

(* This would show that the reverse encryption round is equivalent to the one in the functional spec *)
(*
Lemma inv_round_equiv : forall (s : state) (rk : block),
  block_in_bounds s -> block_in_bounds rk ->
  block_to_ints (transpose (inv_round s rk)) = mbed_tls_rround (blocks_to_ints (transpose s)) (block_to_ints (transpose rk)).
*)

Lemma sbox_invsbox_inverse : forall a : nat, (a < 256)%nat ->
    let b := Z.to_nat (Int.unsigned (nth a sbox Int.zero)) in
    nth b inv_sbox Int.zero = Int.repr (Z.of_nat a).
Proof.
  intros.
  do 256 (destruct a as [| a]; [reflexivity | ]).
  omega.
Qed.

Lemma invsbox_sbox_inverse : forall a : nat, (a < 256)%nat ->
    let b := Z.to_nat (Int.unsigned (nth a inv_sbox Int.zero)) in
    nth b sbox Int.zero = Int.repr (Z.of_nat a).
Proof.
  intros.
  do 256 (destruct a as [| a]; [reflexivity | ]).
  omega.
Qed.
