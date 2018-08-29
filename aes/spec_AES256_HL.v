Require Export VST.floyd.sublist.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Coqlib.
Require Export List. Import ListNotations.
Require Export aes.sbox.

(* substitute b for its counterpart in the sbox *)
Definition look_sbox (b: int) : int :=
  (* All possible values of b are covered in the sbox so the default should never be returned *)
  Int.repr (Znth (Int.unsigned b) sbox).

(* substitute b for its counterpart in the inverse sbox *)
Definition look_inv_sbox (b: int) : int :=
  Int.repr (Znth (Int.unsigned b) inv_sbox).

(********************* GF(256) arithmetic *******************)

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

(******************************************************************************************)


(* Defining words and state as they are considered in the specification, using tuples
 * to enforce the length requirement -- a word is 4 bytes, while a state is 4 words,
 * illustrated as 4 rows of 4 bytes *)
Definition word := (int * int * int * int) % type.
Definition state := (word * word * word * word) % type.
Definition block := state%type. (* Used synonymously with state in the spec, aliased here for readability *)

(* SubBytes() transformation described in section 5.1.1 *)
Definition sub_word (w: word) : word :=
  match w with (b1, b2, b3, b4) => (look_sbox b1, look_sbox b2, look_sbox b3, look_sbox b4) end.
Definition SubBytes (s: state) : state :=
  match s with (w1, w2, w3, w4) => (sub_word w1, sub_word w2, sub_word w3, sub_word w4) end.

(* ShiftRows() transformation described in section 5.1.2 *)
Definition ShiftRows (s : state) : state :=
  match s with
  ((b11, b12, b13, b14),
   (b21, b22, b23, b24),
   (b31, b32, b33, b34),
   (b41, b42, b43, b44)) =>

  ((b11, b12, b13, b14),
   (b22, b23, b24, b21),
   (b33, b34, b31, b32),
   (b44, b41, b42, b43))
  end.

(* MixColumns() transformation described in section 5.1.3 *)

Definition transform_column (col: word) : word :=
  match col with (b1, b2, b3, b4) =>
    let two := Int.repr 2 in
    let three := Int.repr 3 in
    (* (2*b1)^(3*b2)^b3^b4 *)
    let c0 := Int.xor (Int.xor (ff_mult two b1) (ff_mult three b2)) (Int.xor b3 b4) in
    (* b1^(2*b2)^(3*b3)^b4 *)
    let c1 := Int.xor (Int.xor b1 (ff_mult two b2)) (Int.xor (ff_mult three b3) b4) in
    (* b1^b2^(2*b3)^(3*b4)*)
    let c2 := Int.xor (Int.xor b1 b2) (Int.xor (ff_mult two b3) (ff_mult three b4)) in
    (* (3*b1)^b2^b3^(2*b4)*)
    let c3 := Int.xor (Int.xor (ff_mult three b1) b2) (Int.xor b3 (ff_mult two b4)) in
    (c0, c1, c2, c3)
  end.

(* lets us treat state by columns rather than rows *)
Definition transpose (s: state) : state :=
  match s with
   ((b11, b12, b13, b14),
    (b21, b22, b23, b24),
    (b31, b32, b33, b34),
    (b41, b42, b43, b44)) =>

   ((b11, b21, b31, b41),
    (b12, b22, b32, b42),
    (b13, b23, b33, b43),
    (b14, b24, b34, b44))
end.

(* apply column transformation to each column in the state *)
Definition MixColumns (s: state) : state :=
  let cols := transpose s in
  match cols with (c1, c2, c3, c4) =>
    transpose (transform_column c1, transform_column c2, transform_column c3, transform_column c4)
  end.

(* Key expansion functions, section 5.2 *)

(* SubWord function from section 5.2: apply S-box to each byte in a word *)
Definition SubWord (w: word) : word :=
  match w with (b1, b2, b3, b4) => (look_sbox b1, look_sbox b2, look_sbox b3, look_sbox b4) end.

(* RotWord function from section 5.2: rotate bytes left, wrapping around *)
Definition RotWord (w: word) : word :=
  match w with (b1, b2, b3, b4) => (b2, b3, b4, b1) end.

(* round constant (RCon) array, described in section 5.2 and explicitly written
 * out in appendix A.3 (256-bit key expansion example) *)
Definition RCon : list word := [
  (* 0x01000000 *) (Int.repr 1, Int.zero, Int.zero, Int.zero);
  (* 0x02000000 *) (Int.repr 2, Int.zero, Int.zero, Int.zero);
  (* 0x04000000 *) (Int.repr 4, Int.zero, Int.zero, Int.zero);
  (* 0x08000000 *) (Int.repr 8, Int.zero, Int.zero, Int.zero);
  (* 0x10000000 *) (Int.repr 16, Int.zero, Int.zero, Int.zero);
  (* 0x20000000 *) (Int.repr 32, Int.zero, Int.zero, Int.zero);
  (* 0x40000000 *) (Int.repr 64, Int.zero, Int.zero, Int.zero)
].

(* For AES-256, figure 4 fixes the key length in words at 8 and the number
 * of rounds at 14 *)
Definition Nk := 8. (* number of words in key *)
Definition Nr := 14. (* number of cipher rounds *)
Definition Nb := 4. (* number of words in a block (state) *)

(* xor two words together, i.e., apply xor byte by byte *)
Definition xor_word (w1 w2 : word) : word :=
  match w1, w2 with (b1, b2, b3, b4), (b1', b2', b3', b4') =>
    (Int.xor b1 b1', Int.xor b2 b2', Int.xor b3 b3', Int.xor b4 b4')
  end.

(* Expanded key is Nb*(Nr+1) words, or Nr+1 blocks *)
Definition extended_key_blocks := Nr+1.

(* Based on Figure 11 and diagram in appendex A.3 *)

(* Note that "even" and "odd" are if you start counting blocks at 1, rather than 0 *)
(* b1 and b2 are the two blocks generated before this round. *)
Definition odd_round (b1 b2 : block) (rcon: word) : block :=
  match b1, b2 with (w1, w2, w3, w4), (_, _, _, w8) =>
    let w1' := xor_word w1 (xor_word (SubWord (RotWord w8)) rcon) in
    let w2' := xor_word w2 w1' in
    let w3' := xor_word w3 w2' in
    let w4' := xor_word w4 w3' in
    (w1', w2', w3', w4')
  end.
Definition even_round (b1 b2: block) : block :=
  match b1, b2 with (w1, w2, w3, w4), (_, _, _, w8) =>
    let w1' := xor_word w1 (SubWord w8) in
    let w2' := xor_word w2 w1' in
    let w3' := xor_word w3 w2' in
    let w4' := xor_word w4 w3' in
    (w1', w2', w3', w4')
  end.

Fixpoint grow_key (b1 b2: block) (rcs: list word) : list block :=
  match rcs with
  | rc :: [] =>
    (* for the last round constant, only apply an odd round *)
    (odd_round b1 b2 rc) :: []
  | rc :: tl =>
    (* generate a block with an odd round, use it in the next even round and keep going *)
    let b3 := odd_round b1 b2 rc in
	let b4 := even_round b2 b3 in
	b3 :: b4 :: (grow_key b3 b4 tl)
  | [] => [] (* should not happen *)
  end.

(* Note that RCon list (round constants) is described in section 5.2 and its values are given in A.3.
 * k should be a list of words of length Nk. Returns a list of blocks of length Nr+1 *)
Definition KeyExpansion (k : list word) : list block :=
  match k with
  | [w1; w2; w3; w4; w5; w6; w7; w8] =>
    let b1 := (w1, w2, w3, w4) in
	let b2 := (w5, w6, w7, w8) in
	b1 :: b2 :: (grow_key b1 b2 RCon)
  | l => [] (* should not happen *)
  end.

(* AddRoundKey() described in section 5.1.4: it uses a block from the expanded key, xoring
 * each word from the expanded key block with a column from the state *)
Definition AddRoundKey (s : state) (kb : block) : state :=
  let cols := transpose s in
  match cols, kb with (c1,c2,c3,c4), (k1,k2,k3,k4) =>
    transpose (xor_word c1 k1, xor_word c2 k2, xor_word c3 k3, xor_word c4 k4)
  end.

(* Based on figure 5, description of the cipher *)
Definition round (s : state) (kb: block) : state :=
  AddRoundKey (MixColumns (ShiftRows (SubBytes s))) kb.
(* omits mix columns step *)
Definition last_round (s : state) (kb : block) : state :=
  AddRoundKey (ShiftRows (SubBytes s)) kb.

(* Applies cipher rounds given an expanded key *)
Fixpoint apply_rounds (s : state) (ek: list block) : state :=
  match ek with
  | rk :: [] => last_round s rk (* last round *)
  | rk :: tl => apply_rounds (round s rk) tl
  | [] => s (* should not happen *)
  end.

(* exp_key should be length Nr+1 blocks, produced by applying KeyExpansion on a valid key. *)
Definition Cipher (exp_key : list block) (init : state) : state :=
  match exp_key with
  | k1 :: tl =>
    let r1 := AddRoundKey init k1 in
	apply_rounds r1 tl
  | [] => init (* should not happen *)
  end.

(* Inverse cipher and inverse operations -- section 5.3 *)

(* InvShiftRows in section 5.3.1 *)
Definition InvShiftRows (s: state) : state :=
  match s with
    ((b11, b12, b13, b14),
     (b21, b22, b23, b24),
	 (b31, b32, b33, b34),
	 (b41, b42, b43, b44)) =>
	
	((b11, b12, b13, b14),
	 (b24, b21, b22, b23),
	 (b33, b34, b31, b32),
	 (b42, b43, b44, b41))
  end.

(* InvSubBytes in section 5.3.2 *)
Definition inv_sub_word (w: word) : word :=
  match w with (b1, b2, b3, b4) =>
    (look_inv_sbox b1, look_inv_sbox b2, look_inv_sbox b3, look_inv_sbox b4)
  end.

Definition InvSubBytes (s : state) : state :=
  match s with (w1, w2, w3, w4) =>
    (inv_sub_word w1, inv_sub_word w2, inv_sub_word w3, inv_sub_word w4)
  end.

(* InvMixColumns in 5.3.3 *)
Definition inv_transform_column (w: word) : word :=
  let c_e := Int.repr 14 in (* 0x0e *)
  let c_b := Int.repr 11 in (* 0x0b *)
  let c_d := Int.repr 13 in (* 0x0d *)
  let c_9 := Int.repr 9 in (* 0x09 *)
  match w with (b1, b2, b3, b4) =>
    (* (0x0e * b1) ^ (0x0b * b2) ^ (0x0d * b3) ^ (0x09 * b4) *)
    let b1' := Int.xor (Int.xor (ff_mult c_e b1) (ff_mult c_b b2)) (Int.xor (ff_mult c_d b3) (ff_mult c_9 b4)) in
    (* (0x09 * b1) ^ (0x0e * b2) ^ (0x0b * b3) ^ (0x0d * b4) *)
    let b2' := Int.xor (Int.xor (ff_mult c_9 b1) (ff_mult c_e b2)) (Int.xor (ff_mult c_b b3) (ff_mult c_d b4)) in
    (* (0x0d * b1) ^ (0x09 * b2) ^ (0x0e * b3) ^ (0x0b * b4) *)
    let b3' := Int.xor (Int.xor (ff_mult c_d b1) (ff_mult c_9 b2)) (Int.xor (ff_mult c_e b3) (ff_mult c_b b4)) in
    (* (0x0b * b1) ^ (0x0d * b2) ^ (0x09 * b3) ^ (0x0e * b4) *)
    let b4' := Int.xor (Int.xor (ff_mult c_b b1) (ff_mult c_d b2)) (Int.xor (ff_mult c_9 b3) (ff_mult c_e b4)) in
    (b1', b2', b3', b4')
  end.

Definition InvMixColumns (s : state) : state :=
  let cols := transpose s in
  match cols with (c1, c2, c3, c4) =>
    transpose (inv_transform_column c1, inv_transform_column c2, inv_transform_column c3, inv_transform_column c4)
  end.

(* applies InvMixColumns to all members of expanded key but the last *)
Fixpoint grow_inv_key (ek : list block) : list block :=
  match ek with
  | rk :: [] => rk :: [] (* don't do anything to last one *)
  | rk :: tl => InvMixColumns rk :: grow_inv_key tl
  | [] => [] (* should not happen *)
  end.

(* Inverse key expansion briefly described at end of figure 15. k should be of length Nk. *)
Definition InverseKeyExpansion (k : list word) : list block :=
  let exp_key := KeyExpansion k in
  match exp_key with
  (* don't apply inv mix columns to first round key either *)
  | k1 :: tl => k1 :: grow_inv_key tl
  | ek => [] (* should not happen *)
  end.

(* Inverse cipher described in figure 15 *)
Definition inv_round (s : state) (kb : block) : state :=
  AddRoundKey (InvMixColumns (InvShiftRows (InvSubBytes s))) kb.
(* omits mix columns *)
Definition inv_last_round (s : state) (kb : block) : state :=
  AddRoundKey (InvShiftRows (InvSubBytes s)) kb.

Fixpoint apply_inv_rounds (s: state) (ek: list block) : state :=
  match ek with
  | kb :: [] => inv_last_round s kb
  | kb :: tl => apply_inv_rounds (inv_round s kb) tl
  | [] => s (* should not happen *)
  end.

(* exp_key should be length Nr+1 blocks, produced by applying InverseKeyExpansion on a valid
 * key and reversing the result, since the round keys are supposed to be applied starting with
 * the last. (We pass the key in this way for simplifying verification, since the implementation's
 * key expansion process also reverses the key, whereas the specification reverses it during the
 * decryption process) *)
Definition EqInvCipher (exp_key: list block) (init: state) : state :=
  match exp_key with
  | kb :: tl => apply_inv_rounds (AddRoundKey init kb) tl
  | l => init (* should not happen *)
  end.
