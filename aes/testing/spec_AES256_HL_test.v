Require Import aes.spec_AES256_HL.
Require Import List. Import ListNotations.

(* The hex values of this sample key are copied from C.3 of FIPS-197, and were converted to decimal
   in the Python repl with the following command:
   '; '.join([str(ord(c)) for c in '00112233445566778899aabbccddeeff'.decode('hex')])
*)
Definition sample_plaintext_Z := [0; 17; 34; 51; 68; 85; 102; 119; 136; 153; 170; 187; 204; 221; 238; 255].

(* The hex values of this sample key are copied from C.3 of FIPS-197, and were converted to decimal
   in the Python repl with the following command:
   '; '.join([str(ord(c)) for c in '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f'.decode('hex')])
*)
Definition sample_key_Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Fixpoint byte_list_to_word_list(l: list Z): list word := match l with
| b0 :: b1 :: b2 :: b3 :: tl =>
  (Int.repr b0, Int.repr b1, Int.repr b2, Int.repr b3) :: byte_list_to_word_list tl
| _ => nil
end.

(* Note: In the standard, the 4x4 matrix is filled with bytes column-wise, but the
   high-level spec fills it row-wise, so we have to transpose in the right spots *)

Definition list_to_state (l : list Z) : state := transpose
  match (map Int.repr l) with
  | [ b11; b12; b13; b14 ;  b21; b22; b23; b24 ;  b31; b32; b33; b34 ;  b41; b42; b43; b44 ] =>
    ((b11, b12, b13, b14), (b21, b22, b23, b24), (b31, b32, b33, b34), (b41, b42, b43, b44))
  (* should not happen: *)
  | _ => let z4 := (Int.zero, Int.zero, Int.zero, Int.zero) in
         (z4, z4, z4, z4)
  end.

Tactic Notation "calc" constr(x) := let r := eval cbv in x in exact r.

Definition sample_key : list word := ltac:(calc (byte_list_to_word_list sample_key_Z)).

Definition exp_sample_key : list block := KeyExpansion sample_key.

Definition sample_plaintext : state := ltac:(calc (list_to_state sample_plaintext_Z)).

Definition word0 : word := (Int.zero, Int.zero, Int.zero, Int.zero).
Definition state0 : state := (word0, word0, word0, word0).
Definition key0 : list word := ltac:(calc (repeat word0 8)).

(* stepping through encryption algorithm: *)
Definition s1 := (AddRoundKey sample_plaintext (Znth 0 exp_sample_key state0)).
Definition s11 := (SubBytes s1).
Definition s12 := (ShiftRows s11).
Definition s13 := (MixColumns s12).
Definition s14 := AddRoundKey s13 (Znth 1 exp_sample_key state0).
Definition s2 := (round s1 (Znth 1 exp_sample_key state0)).

Definition trace1 := map transpose [s1; s11; s12; s13; s14; s2].

Extraction "aes/extracted/trace1.ml" trace1.

Definition sample_ciphertext := transpose (Cipher exp_sample_key sample_plaintext).

Extraction "aes/extracted/c.ml" sample_ciphertext.

(* The hex values of this sample key are copied from A.3 of FIPS-197, and were converted to decimal
   in the Python repl with the following command:
   '; '.join([str(ord(c)) for c in '603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4'.decode('hex')]) 
*)
Definition test_keyZ := [96; 61; 235; 16; 21; 202; 113; 190; 43; 115; 174; 240; 133; 125; 119; 129; 31; 53; 44; 7; 59; 97; 8; 215; 45; 152; 16; 163; 9; 20; 223; 244].

Definition test_key : list word := ltac:(calc (byte_list_to_word_list test_keyZ)).

Definition exp_test_key := KeyExpansion test_key.

Extraction "aes/extracted/exp_test_key.ml" exp_test_key.

(*Definition exp_key0 : list block := ltac:(calc (repeat state0 15)).*)
Definition exp_key0 : list block := KeyExpansion key0.

Definition ciphertext1 := (Cipher exp_key0 state0).

Extraction "aes/extracted/ciphertext1.ml" ciphertext1.

Require Import aes.aes.

Definition aes_test_ecb_enc : list int := ltac:(
  let r := eval cbv in (let (_, v, _, _) := v_aes_test_ecb_enc in (map (fun data => match data with
  | AST.Init_int8 i => i
  | _ => Int.repr Int.max_signed
  end) v))
  in exact r).

Definition test1 := ltac:(
  let r := eval cbv in (sublist 0 16 aes_test_ecb_enc)
  in exact r).

Definition test2 := ltac:(
  let r := eval cbv in (sublist 16 24 aes_test_ecb_enc)
  in exact r).

Definition test3 := ltac:(
  let r := eval cbv in (sublist 24 48 aes_test_ecb_enc)
  in exact r).
