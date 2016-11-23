Require Import List. Import ListNotations.
Require Import ZArith.
Local Open Scope Z_scope.
Require Import Integers.
Require Import floyd.sublist.
Require Import aes.sbox.

(* TODO replace these definitions by low-level definitions which match exactly the C-code *)

(* xtime operation from section 4.2.1. Corresponds to multiplying by 2 in GF(256) *)
Definition xtime (b: int) : int :=
  let b' := Int.modu (Int.shl b (Int.one)) (Int.repr 256) in (* shift left by one, mod 256 *)
  let c_1b := Int.repr 27 in (* 0x1b *)
  let c_80 := Int.repr 128 in (* 0x80 *)
  (* test if highest bit of b is one. If so, then XOR b' with 0x1b, otherwise return b' *)
  if Int.eq (Int.and b c_80) Int.zero then b'
  else Int.xor b' c_1b.

(* Finite field multiplication using xtime operation and xor for finite field addition
 * (Russian peasant multiplication), not described directly but suggested in section 4.2.1. *)
 
(* Repeatedly double b using xtime as per Russian peasant multiplication. Add b to accumulator
 * if there is a "remainder," i.e., the tested bit of a is 1 *)
Definition ff_checkbit (a b : int) (acc : int) : int :=
  (* if lowest bit of a is one, add (xor) b to acc. Otherwise do nothing *)
  if Int.eq (Int.and a Int.one) Int.zero then acc
  else Int.xor acc b.

Fixpoint xtime_test (a b : int) (acc : int) (shifts : nat) : int :=
  if Int.eq a Int.zero then acc (* if a or b are zero, nothing to do *)
  else if Int.eq b Int.zero then acc
  else 
    (* check lowest bit of a, add b to acc if it is positive. Shift a
     * right for next iteration unless we're finished *)
    match shifts with
    | S n =>
      let acc' := ff_checkbit a b acc in
      (* shift a right and double b *)
      let a' := Int.shru a Int.one in
      let b' := xtime b in
      xtime_test a' b' acc' n
    | O => acc
    end.

Definition ff_mult (a b : int) : int := xtime_test a b Int.zero 8%nat.

(* Defining words and state as they are considered in the specification, using tuples
 * to enforce the length requirement -- a word is 4 bytes, while a state is 4 words,
 * illustrated as 4 rows of 4 bytes *)
Definition word := (int * int * int * int) % type.
(*
Definition state := (word * word * word * word) % type.
Definition block := state%type. (* Used synonymously with state in the spec, aliased here for readability *)
*)

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

Fixpoint little_endian_integer (contents: list int) : int :=
 match contents with 
 | nil => Int.zero
 | c::cr => Int.or (Int.shl (little_endian_integer cr) (Int.repr 8)) c
end.

(* utility functions for convertin the funcational spec's data structures
 * into C data structures *)
Definition word_to_int (w : word) : int :=
  match w with (b0, b1, b2, b3) => little_endian_integer [b0; b1; b2; b3] end.

Definition words_to_ints (words : list word) : list int := map word_to_int words.

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

Definition RCON : list int := words_to_ints [
  (* 0x01000000 *) (Int.repr 1, Int.zero, Int.zero, Int.zero);
  (* 0x02000000 *) (Int.repr 2, Int.zero, Int.zero, Int.zero);
  (* 0x04000000 *) (Int.repr 4, Int.zero, Int.zero, Int.zero);
  (* 0x08000000 *) (Int.repr 8, Int.zero, Int.zero, Int.zero);
  (* 0x10000000 *) (Int.repr 16, Int.zero, Int.zero, Int.zero);
  (* 0x20000000 *) (Int.repr 32, Int.zero, Int.zero, Int.zero);
  (* 0x40000000 *) (Int.repr 64, Int.zero, Int.zero, Int.zero);
  (* 0x1b000000 *) (Int.repr 27, Int.zero, Int.zero, Int.zero);
  (* 0x36000000 *) (Int.repr 54, Int.zero, Int.zero, Int.zero)
].

Definition FSb := map Int.repr sbox.
Definition RSb := map Int.repr inv_sbox.

(* matches aes_tables_struct *)
Definition tables_content := (FSb, (FT0, (FT1, (FT2, (FT3, (RSb, (RT0, (RT1, (RT2, (RT3, RCON)))))))))).

