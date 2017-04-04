Require Import floyd.proofauto.
Require Import aes.spec_AES256_HL.

Require Import Coqlib.
Require Import msl.Coqlib2.
Require Import floyd.coqlib3.
Require Import Integers.
Require Import List.
Require Import floyd.sublist.
Require Import sha.SHA256.
Require Import sha.general_lemmas.

Local Open Scope logic.

(* utility functions for convertin the funcational spec's data structures
 * into C data structures *)
Definition word_to_int (w : word) : int :=
  match w with (b0, b1, b2, b3) => little_endian_integer [b0; b1; b2; b3] end.

Definition words_to_ints (words : list word) : list int := map word_to_int words.

Definition block_to_ints (b : block) : list int :=
  match b with (w0, w1, w2, w3) => [word_to_int w0; word_to_int w1; word_to_int w2; word_to_int w3] end.

Definition blocks_to_ints (blocks : list block) : list int := flat_map block_to_ints blocks.

(* stipulate that the different ints used to represent bytes are indeed in range *)
Definition word_in_bounds (w : word) :=
  match w with
      (b0, b1, b2, b3) => (Int.unsigned b0 < 256 /\ Int.unsigned b1 < 256 /\ Int.unsigned b2 < 256 /\ Int.unsigned b3 < 256)
  end.
Definition block_in_bounds (b : block) :=
   match b with (w0, w1, w2, w3) => (word_in_bounds w0 /\ word_in_bounds w1 /\ word_in_bounds w2 /\ word_in_bounds w3) end.
Definition words_in_bounds (words : list word) := forall w : word, In w words -> word_in_bounds w.
Definition blocks_in_bounds (blocks : list block) := forall b : block, In b blocks -> block_in_bounds b.

(* Coq implementations of functions in the mbed TLS implementation, which we will
 * have to prove correspond to the spec *)

(* Implemenation's RCON table includes two constants not used in AES256 *)
Definition full_rcons := RCon ++ [
  (Int.repr 27 (* 0x1b *), Int.zero, Int.zero, Int.zero);
  (Int.repr 54 (* 0x36 *), Int.zero, Int.zero, Int.zero)
].

(* similar to grow_key in the functional specification, but always applies both an even
 * and an odd round instead of having a special case for the last round. This is not
 * called for in the functional specification, but this is what the program does, thus
 * producing an extra block *)
Fixpoint grow_key_extra (b1 b2: block) (rcs: list word) : list block :=
  match rcs with
  | hd :: tl =>
    let b3 := odd_round b1 b2 hd in
    let b4 := even_round b2 b3 in
    b3 :: b4 :: grow_key_extra b3 b4 tl
  | [] => []
  end.
Definition extra_key_expansion (k : list word) : list block :=
  match k with
  | [w1; w2; w3; w4; w5; w6; w7; w8] =>
    let b1 := (w1, w2, w3, w4) in
    let b2 := (w5, w6, w7, w8) in
    b1 :: b2 :: (grow_key_extra b1 b2 RCon)
  | l => [] (* should not happen *)
  end.

(* The implementation generates GF(256) exponentiation and logarithm tables,
 * both base 3. It uses these for multiplication *)
Fixpoint gen_exp_table (n : nat) (base : int) : list int :=
  match n with
  | O => []
    (* b XOR (xtime b) = 3*b in GF(256) *)
  | S n' => base :: gen_exp_table n' (Int.xor base (xtime base))
  end.

Fixpoint mapi_aux {A B : Type} (f : Z -> A -> B) (pos : Z) (l : list A) : list B :=
  match l with
  | [] => []
  | hd :: tl => f pos hd :: mapi_aux f (pos+1) tl
  end.

Definition mapi {A B : Type} (f : Z -> A -> B) (l : list A) : list B := mapi_aux f 0 l.

Fixpoint insert_idx {A : Type} (l : list (Z * A)) (p : (Z * A)) : list (Z * A) :=
  match p with (i, a) =>
    match l with
    | [] => p :: []
    | ((i', b) as hd) :: tl =>
      if i =? i' then p :: tl (* replace equal entries *)
      else if i <? i' then p :: hd :: tl
      else hd :: insert_idx tl p
    end
  end.

Definition sort_idx {A : Type} (l : list (Z * A)) : list (Z * A) :=
  fold_left insert_idx l [].

(* the implemenation generates the log table by actually computing
 * x = 3^i, then setting log[x] = i. This is not easy to do in Coq,
 * so instead we generate the power table, pair each entry with its
 * index, sort by entry, and return the indices *)
Definition gen_log_table (n : nat) (base : int) : list int :=
  let exp := gen_exp_table n base in
  let indexed := mapi (fun i e => (Int.unsigned e, Int.repr i)) exp in
  let sorted := sort_idx indexed in
  (* zero is an arbitrary entry at the beginning because log 0 is undefined *)
  Int.zero :: map snd sorted.

(* ith element is 3^i in GF(256) *)
Definition ff_exp_table := gen_exp_table 256 Int.one.
(* ith element is log base 3 of i in GF(256). Zeroth entry is arbitrarily 0 *)
Definition ff_log_table := gen_log_table 256 Int.one.

(* We will show that GF(256) arithmetic done by peasant multiplication
 * is equivalent to the method used by the implementation, namely using
 * log and exponentiation tables. The implementation takes log of a and b,
 * adds them mod 255 (not mod 256) and returns exp of that,
 * returning 0 if a or b is 0 *)
Definition table_ff_mult (a b: int) : int :=
  if Int.eq a Int.zero then Int.zero
  else if Int.eq b Int.zero then Int.zero
  else
    let log_a := Znth (Int.unsigned a) ff_log_table Int.zero in
    let log_b := Znth (Int.unsigned b) ff_log_table Int.zero in
    let idx := Int.modu (Int.add log_a log_b) (Int.repr 255) in
    Znth (Int.unsigned idx) ff_exp_table Int.zero.

Fixpoint repeat_op (op : int -> int) (times : nat) (arg : int) : int :=
  match times with
  | O => arg
  | S n => op (repeat_op op n arg)
  end.

(* implement exponentiation by repeated multiplication, which we will use
 * to verify correctness of our exp and log tables *)
Definition ff_exp (a b : int) := repeat_op (ff_mult a) (Z.to_nat (Int.unsigned b)) Int.one.

(* Forward and reverse table generation *)

(* The forward and reverse tables are used by the implementation to perform the
 * MixColumns and SubBytes step simply by XORing entries from a lookup table. *)
Fixpoint generate_forward_table (table : list int) : list word :=
  match table with
  | hd :: tl =>
    let x := hd in
    let y := xtime hd in
    let z := Int.xor y x in
    (y, x, x, z) :: generate_forward_table tl
  | [] => []
  end.

Definition ft_words := generate_forward_table (map Int.repr sbox).

(* opposite direction of RotWord, brings last byte to front. Applies
 * rotation n times *)
Fixpoint rotate (n : nat) (w : word) : word :=
  match n with
  | O => w
  | S n' => match w with (w0, w1, w2, w3) => (rotate n' (w3, w0, w1, w2)) end
  end.

Definition FT0 := words_to_ints ft_words.
Definition FT1 := words_to_ints (map (rotate 1%nat) ft_words).
Definition FT2 := words_to_ints (map (rotate 2%nat) ft_words).
Definition FT3 := words_to_ints (map (rotate 3%nat) ft_words).

Fixpoint generate_reverse_table (table : list int) : list word :=
  let c_e := Int.repr 14 in (* 0x0e *)
  let c_b := Int.repr 11 in (* 0x0b *)
  let c_d := Int.repr 13 in (* 0x0d *)
  let c_9 := Int.repr 9 in (* 0x09 *)
  match table with
  | hd :: tl =>
    (ff_mult c_e hd, ff_mult c_9 hd, ff_mult c_d hd, ff_mult c_b hd) :: generate_reverse_table tl
  | [] => []
  end.

Definition rt_words := generate_reverse_table (map Int.repr inv_sbox).

Definition RT0 := words_to_ints rt_words.
Definition RT1 := words_to_ints (map (rotate 1%nat) rt_words).
Definition RT2 := words_to_ints (map (rotate 2%nat) rt_words).
Definition RT3 := words_to_ints (map (rotate 3%nat) rt_words).

(* Using the forward and reverse tables to implement the AES round
 * and reverse round *)

Definition zlist_to_col (c : int) : (Z * Z * Z * Z) :=
  let bytes := intlist_to_Zlist [c] in
  match bytes with
  | b3 :: b2 :: b1 :: b0 :: [] => (b0, b1, b2, b3)
  | _ => (0, 0, 0, 0) (* should not happen *)
  end.

Definition mbed_tls_fround_col (b0 b1 b2 b3 : Z) (rk : int) : int :=
  let f0 := Znth b0 FT0 Int.zero in
  let f1 := Znth b1 FT1 Int.zero in
  let f2 := Znth b2 FT2 Int.zero in
  let f3 := Znth b3 FT3 Int.zero in
  fold_left Int.xor [f0; f1; f2; f3] rk.

(* we want to represent a round using the mbed TLS implementation's representation of the data structures
 * and show that this maps back to our functional specification. Corresponds to
 * the AES_FROUND macro *)
Definition mbed_tls_fround (cols : list int) (rk : list int) : list int :=
  match (cols, rk) with
  | (c3 :: c2 :: c1 :: c0 :: [], k3 :: k2 :: k1 :: k0 :: []) =>
      match (zlist_to_col c0, zlist_to_col c1, zlist_to_col c2, zlist_to_col c3) with
            ((c00, c01, c02, c03), (c10, c11, c12, c13),
             (c20, c21, c22, c23), (c30, c31, c32, c33)) =>
       [mbed_tls_fround_col c00 c11 c22 c33 k0;
        mbed_tls_fround_col c10 c21 c32 c03 k1;
        mbed_tls_fround_col c20 c31 c02 c13 k2;
        mbed_tls_fround_col c30 c01 c12 c23 k3]
      end
  | _ => [] (* should not happen *)
  end.

Definition mbed_tls_rround_col (b0 b1 b2 b3 : Z) (rk : int) : int :=
  let r0 := Znth b0 RT0 Int.zero in
  let r1 := Znth b1 RT1 Int.zero in
  let r2 := Znth b2 RT2 Int.zero in
  let r3 := Znth b3 RT3 Int.zero in
  fold_left Int.xor [r0; r1; r2; r3] rk.

(* Corresponds to the AES_RROUND macro *)
Definition mbed_tls_rround (cols : list int) (rk : list int) : list int :=
  match (cols, rk) with
  | (c3 :: c2 :: c1 :: c0 :: [], k3 :: k2 :: k1 :: k0 :: []) =>
      match (zlist_to_col c0, zlist_to_col c1, zlist_to_col c2, zlist_to_col c3) with
            ((c00, c01, c02, c03), (c10, c11, c12, c13),
             (c20, c21, c22, c23), (c30, c31, c32, c33)) =>
      (* note that column positions differ from the forward round *)
       [mbed_tls_rround_col c00 c31 c22 c13 k0;
        mbed_tls_rround_col c10 c01 c32 c23 k1;
        mbed_tls_rround_col c20 c11 c02 c33 k2;
        mbed_tls_rround_col c30 c21 c12 c03 k3]
      end
  | _ => [] (* should not happen *)
  end.
