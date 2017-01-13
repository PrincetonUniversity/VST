Require Export floyd.sublist.
Require Export Integers.
Require Export Coqlib.
Require Export List.

Import ListNotations.

(* We will use integers constrained to represent values less than 256 and greater than 0
 * to represent bytes in order to be consistent with the lemmas of the SHA-256 verification *)

(* forward s-box, figure 7 in NIST specification *)
Definition sbox := map Int.repr [
  (* 0x00 through 0x0f: (hexadecimal) 63 7c 77 7b f2 6b 6f c5 30 01 67 2b fe d7 ab 76 *)
  99; 124; 119; 123; 242; 107; 111; 197; 48; 1; 103; 43; 254; 215; 171; 118;
  (* 0x10 through 0x1f: ca 82 c9 7d fa 59 47 f0 ad d4 a2 af 9c a4 72 c0 *)
  202; 130; 201; 125; 250; 89; 71; 240; 173; 212; 162; 175; 156; 164; 114; 192;
  (* 0x20 through 0x2f: b7 fd 93 26 36 3f f7 cc 34 a5 e5 f1 71 d8 31 15 *)
  183; 253; 147; 38; 54; 63; 247; 204; 52; 165; 229; 241; 113; 216; 49; 21;
  (* 0x30 through 0x3f: 04 c7 23 c3 18 96 05 9a 07 12 80 e2 eb 27 b2 75 *)
  4; 199; 35; 195; 24; 150; 5; 154; 7; 18; 128; 226; 235; 39; 178; 117;
  (* 0x40 through 0x4f: 09 83 2c 1a 1b 6e 5a a0 52 3b d6 b3 29 e3 2f 84 *)
  9; 131; 44; 26; 27; 110; 90; 160; 82; 59; 214; 179; 41; 227; 47; 132;
  (* 0x50 through 0x5f: 53 d1 00 ed 20 fc b1 5b 6a cb be 39 4a 4c 58 cf *)
  83; 209; 0; 237; 32; 252; 177; 91; 106; 203; 190; 57; 74; 76; 88; 207;
  (* 0x60 through 0x6f: d0 ef aa fb 43 4d 33 85 45 f9 02 7f 50 3c 9f a8 *)
  208; 239; 170; 251; 67; 77; 51; 133; 69; 249; 2; 127; 80; 60; 159; 168;
  (* 0x70 through 0x7f: 51 a3 40 8f 92 9d 38 f5 bc b6 da 21 10 ff f3 d2 *)
  81; 163; 64; 143; 146; 157; 56; 245; 188; 182; 218; 33; 16; 255; 243; 210;
  (* 0x80 through 0x8f: cd 0c 13 ec 5f 97 44 17 c4 a7 7e 3d 64 5d 19 73 *)
  205; 12; 19; 236; 95; 151; 68; 23; 196; 167; 126; 61; 100; 93; 25; 115;
  (* 0x90 through 0x9f: 60 81 4f dc 22 2a 90 88 46 ee b8 14 de 5e 0b db *)
  96; 129; 79; 220; 34; 42; 144; 136; 70; 238; 184; 20; 222; 94; 11; 219;
  (* 0xa0 through 0xaf: e0 32 3a 0a 49 06 24 5c c2 d3 ac 62 91 95 e4 79 *)
  224; 50; 58; 10; 73; 6; 36; 92; 194; 211; 172; 98; 145; 149; 228; 121;
  (* 0xb0 through 0xbf: e7 c8 37 6d 8d d5 4e a9 6c 56 f4 ea 65 7a ae 08 *)
  231; 200; 55; 109; 141; 213; 78; 169; 108; 86; 244; 234; 101; 122; 174; 8;
  (* 0xc0 through 0xcf: ba 78 25 2e 1c a6 b4 c6 e8 dd 74 1f 4b bd 8b 8a *)
  186; 120; 37; 46; 28; 166; 180; 198; 232; 221; 116; 31; 75; 189; 139; 138;
  (* 0xd0 through 0xdf: 70 3e b5 66 48 03 f6 0e 61 35 57 b9 86 c1 1d 9e *)
  112; 62; 181; 102; 72; 3; 246; 14; 97; 53; 87; 185; 134; 193; 29; 158;
  (* 0xe0 through 0xef: e1 f8 98 11 69 d9 8e 94 9b 1e 87 e9 ce 55 28 df *)
  225; 248; 152; 17; 105; 217; 142; 148; 155; 30; 135; 233; 206; 85; 40; 223;
  (* 0xf0 through 0xff: 8c a1 89 0d bf e6 42 68 41 99 2d 0f b0 54 bb 16 *)
  140; 161; 137; 13; 191; 230; 66; 104; 65; 153; 45; 15; 176; 84; 187; 22
].

(* Inverse s-box, figure 14 in NIST specification *)
Definition inv_sbox := map Int.repr [
  (* 0x00 through 0x0f (in hexadecimal) : 52 09 6a d5 30 36 a5 38 bf 40 a3 9e 81 f3 d7 fb *)
  82; 9; 106; 213; 48; 54; 165; 56; 191; 64; 163; 158; 129; 243; 215; 251;
  (* 0x10 through 0x1f: 7c e3 39 82 9b 2f ff 87 34 8e 43 44 c4 de e9 cb *)
  124; 227; 57; 130; 155; 47; 255; 135; 52; 142; 67; 68; 196; 222; 233; 203;
  (* 0x20 through 0x2f: 54 7b 94 32 a6 c2 23 3d ee 4c 95 0b 42 fa c3 4e *)
  84; 123; 148; 50; 166; 194; 35; 61; 238; 76; 149; 11; 66; 250; 195; 78;
  (* 0x30 through 0x3f: 08 2e a1 66 28 d9 24 b2 76 5b a2 49 6d 8b d1 25 *)
  8; 46; 161; 102; 40; 217; 36; 178; 118; 91; 162; 73; 109; 139; 209; 37;
  (* 0x40 through 0x4f: 72 f8 f6 64 86 68 98 16 d4 a4 5c cc 5d 65 b6 92 *)
  114; 248; 246; 100; 134; 104; 152; 22; 212; 164; 92; 204; 93; 101; 182; 146;
  (* 0x50 through 0x5f: 6c 70 48 50 fd ed b9 da 5e 15 46 57 a7 8d 9d 84 *)
  108; 112; 72; 80; 253; 237; 185; 218; 94; 21; 70; 87; 167; 141; 157; 132;
  (* 0x60 through 0x6f: 90 d8 ab 00 8c bc d3 0a f7 e4 58 05 b8 b3 45 06 *)
  144; 216; 171; 0; 140; 188; 211; 10; 247; 228; 88; 5; 184; 179; 69; 6;
  (* 0x70 through 0x7f: d0 2c 1e 8f ca 3f 0f 02 c1 af bd 03 01 13 8a 6b *)
  208; 44; 30; 143; 202; 63; 15; 2; 193; 175; 189; 3; 1; 19; 138; 107;
  (* 0x80 through 0x8f: 3a 91 11 41 4f 67 dc ea 97 f2 cf ce f0 b4 e6 73 *)
  58; 145; 17; 65; 79; 103; 220; 234; 151; 242; 207; 206; 240; 180; 230; 115;
  (* 0x90 through 0x9f: 96 ac 74 22 e7 ad 35 85 e2 f9 37 e8 1c 75 df 6e *)
  150; 172; 116; 34; 231; 173; 53; 133; 226; 249; 55; 232; 28; 117; 223; 110;
  (* 0xa0 through 0xaf: 47 f1 1a 71 1d 29 c5 89 6f b7 62 0e aa 18 be 1b *)
  71; 241; 26; 113; 29; 41; 197; 137; 111; 183; 98; 14; 170; 24; 190; 27;
  (* 0xb0 through 0xbf: fc 56 3e 4b c6 d2 79 20 9a db c0 fe 78 cd 5a f4 *)
  252; 86; 62; 75; 198; 210; 121; 32; 154; 219; 192; 254; 120; 205; 90; 244;
  (* 0xc0 through 0xcf: 1f dd a8 33 88 07 c7 31 b1 12 10 59 27 80 ec 5f *)
  31; 221; 168; 51; 136; 7; 199; 49; 177; 18; 16; 89; 39; 128; 236; 95;
  (* 0xd0 through 0xdf: 60 51 7f a9 19 b5 4a 0d 2d e5 7a 9f 93 c9 9c ef *)
  96; 81; 127; 169; 25; 181; 74; 13; 45; 229; 122; 159; 147; 201; 156; 239;
  (* 0xe0 through 0xef: a0 e0 3b 4d ae 2a f5 b0 c8 eb bb 3c 83 53 99 61 *)
  160; 224; 59; 77; 174; 42; 245; 176; 200; 235; 187; 60; 131; 83; 153; 97;
  (* 0xf0 through 0xff: 17 2b 04 7e ba 77 d6 26 e1 69 14 63 55 21 0c 7d *)
  23; 43; 4; 126; 186; 119; 214; 38; 225; 105; 20; 99; 85; 33; 12; 125
].

(* substitute b for its counterpart in the sbox *)
Definition look_sbox (b: int) : int :=
  (* All possible values of b are covered in the sbox so the default should never be returned *)
  Znth (Int.unsigned b) sbox Int.zero.

(* substitute b for its counterpart in the inverse sbox *)
Definition look_inv_sbox (b: int) : int :=
  Znth (Int.unsigned b) inv_sbox Int.zero.

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
    let w1' := xor_word w1 (SubWord (xor_word (RotWord w8) rcon)) in
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
