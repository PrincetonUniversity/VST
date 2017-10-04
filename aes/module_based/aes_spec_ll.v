Require Import List. Import ListNotations.
Require Import ZArith.
Local Open Scope Z_scope.
Require Import Integers.
Require Import floyd.sublist.
Require Import aes.tablesLL.

Definition four_ints := (int * (int * (int * int)))%type.

Definition col (i : Z) (s : four_ints) : int := match i with
| 0 => fst s
| 1 => fst (snd s)
| 2 => fst (snd (snd s))
| 3 => snd (snd (snd s))
| _ => Int.zero (* should not happen *)
end.

Lemma split_four_ints: forall (S: four_ints),
  S = (col 0 S, (col 1 S, (col 2 S, col 3 S))).
Proof.
  intros. destruct S as [c1 [c2 [c3 c4]]]. reflexivity.
Qed.

Lemma split_four_ints_eq: forall S c0 c1 c2 c3,
  S = (c0, (c1, (c2, c3))) -> c0 = col 0 S /\ c1 = col 1 S /\ c2 = col 2 S /\ c3 = col 3 S.
Proof.
  intros. destruct S as [d0 [d1 [d2 d3]]]. inversion H. auto.
Qed.



Module Type AES_LL_Spec_Type.

(* arr: list of 4 bytes *)
Parameter get_uint32_le: list Z -> Z -> int.
Axiom get_uint32_le_def: get_uint32_le = fun (arr: list Z) (i: Z) =>
 (Int.or (Int.or (Int.or
            (Int.repr (Znth  i    arr 0))
   (Int.shl (Int.repr (Znth (i+1) arr 0)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth (i+2) arr 0)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth (i+3) arr 0)) (Int.repr 24))).

(* outputs a list of 4 bytes *)
Parameter put_uint32_le: int -> list int.
Axiom put_uint32_le_def: put_uint32_le = fun (x : int) =>
  [ (Int.and           x                (Int.repr 255));
    (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255)) ].

Parameter output_four_ints_as_bytes: four_ints -> list int.
Axiom output_four_ints_as_bytes_def: output_four_ints_as_bytes = fun (s : four_ints) =>
  (put_uint32_le (col 0 s)) ++
  (put_uint32_le (col 1 s)) ++
  (put_uint32_le (col 2 s)) ++
  (put_uint32_le (col 3 s)).

Parameter byte0: int -> Z.
Axiom byte0_def: byte0 = fun (x : int) =>
  (Z.land (Int.unsigned x) (Int.unsigned (Int.repr 255))).
Parameter byte1: int -> Z.
Axiom byte1_def: byte1 = fun (x : int) =>
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).
Parameter byte2: int -> Z.
Axiom byte2_def: byte2 = fun (x : int) =>
  (Z.land (Int.unsigned (Int.shru x (Int.repr 16))) (Int.unsigned (Int.repr 255))).
Parameter byte3: int -> Z.
Axiom byte3_def: byte3 = fun (x : int) =>
  (Z.land (Int.unsigned (Int.shru x (Int.repr 24))) (Int.unsigned (Int.repr 255))).

Parameter mbed_tls_fround_col: int -> int -> int -> int -> Z -> int.
Axiom mbed_tls_fround_col_def: mbed_tls_fround_col = fun (col0 col1 col2 col3 : int) (rk : Z) =>
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
    (Znth (byte0 col0) FT0 Int.zero))
    (Znth (byte1 col1) FT1 Int.zero))
    (Znth (byte2 col2) FT2 Int.zero))
    (Znth (byte3 col3) FT3 Int.zero)).

Parameter mbed_tls_final_fround_col: int -> int -> int -> int -> Z -> int.
Axiom mbed_tls_final_fround_col_def: mbed_tls_final_fround_col =
fun (col0 col1 col2 col3 : int) (rk : Z) =>
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
             (Znth (byte0 col0) FSb Int.zero)              )
    (Int.shl (Znth (byte1 col1) FSb Int.zero) (Int.repr 8)))
    (Int.shl (Znth (byte2 col2) FSb Int.zero) (Int.repr 16)))
    (Int.shl (Znth (byte3 col3) FSb Int.zero) (Int.repr 24))).

Parameter mbed_tls_initial_add_round_key_col: Z -> list Z -> list Z -> int.
Axiom mbed_tls_initial_add_round_key_col_def: mbed_tls_initial_add_round_key_col =
fun (col_id : Z) (plaintext : list Z) (rks : list Z) =>
  Int.xor (get_uint32_le plaintext (col_id * 4)) (Int.repr (Znth col_id rks 0)).

Parameter mbed_tls_fround: four_ints -> list Z -> Z -> four_ints.
Axiom mbed_tls_fround_def: mbed_tls_fround =
fun (cols : four_ints) (rks : list Z) (i : Z) =>
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_fround_col col0 col1 col2 col3 (Znth  i    rks 0)),
  ((mbed_tls_fround_col col1 col2 col3 col0 (Znth (i+1) rks 0)),
  ((mbed_tls_fround_col col2 col3 col0 col1 (Znth (i+2) rks 0)),
   (mbed_tls_fround_col col3 col0 col1 col2 (Znth (i+3) rks 0)))))
end.

Parameter mbed_tls_final_fround: four_ints -> list Z -> Z -> four_ints.
Axiom mbed_tls_final_fround_def: mbed_tls_final_fround =
fun (cols : four_ints) (rks : list Z) (i : Z) =>
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_final_fround_col col0 col1 col2 col3 (Znth  i    rks 0)),
  ((mbed_tls_final_fround_col col1 col2 col3 col0 (Znth (i+1) rks 0)),
  ((mbed_tls_final_fround_col col2 col3 col0 col1 (Znth (i+2) rks 0)),
   (mbed_tls_final_fround_col col3 col0 col1 col2 (Znth (i+3) rks 0)))))
end.

Parameter mbed_tls_enc_rounds: nat -> four_ints -> list Z -> Z -> four_ints.
Axiom mbed_tls_enc_rounds_def: mbed_tls_enc_rounds =
fix mbed_tls_enc_rounds (n : nat) (state : four_ints) (rks : list Z) (i : Z) :=
match n with
| O => state
| S m => mbed_tls_fround (mbed_tls_enc_rounds m state rks i) rks (i+4*Z.of_nat m)
end.

(* plaintext: array of bytes
   rks: expanded round keys, array of Int32 *)
Parameter mbed_tls_initial_add_round_key: list Z -> list Z -> four_ints.
Axiom mbed_tls_initial_add_round_key_def: mbed_tls_initial_add_round_key =
fun (plaintext : list Z) (rks : list Z) =>
((mbed_tls_initial_add_round_key_col 0 plaintext rks),
((mbed_tls_initial_add_round_key_col 1 plaintext rks),
((mbed_tls_initial_add_round_key_col 2 plaintext rks),
((mbed_tls_initial_add_round_key_col 3 plaintext rks))))).

Parameter mbed_tls_aes_enc: list Z -> list Z -> list int.
Axiom mbed_tls_aes_enc_def: mbed_tls_aes_enc = fun (plaintext : list Z) (rks : list Z) =>
  let state0  := mbed_tls_initial_add_round_key plaintext rks in
  let state13 := mbed_tls_enc_rounds 13 state0 rks 4 in
  let state14 := mbed_tls_final_fround state13 rks 56 in
  output_four_ints_as_bytes state14.

End AES_LL_Spec_Type.


Module Export AES_LL_Spec : AES_LL_Spec_Type.

(* arr: list of 4 bytes *)
Definition get_uint32_le (arr: list Z) (i: Z) : int :=
 (Int.or (Int.or (Int.or
            (Int.repr (Znth  i    arr 0))
   (Int.shl (Int.repr (Znth (i+1) arr 0)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth (i+2) arr 0)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth (i+3) arr 0)) (Int.repr 24))).
Lemma get_uint32_le_def: get_uint32_le = fun (arr: list Z) (i: Z) =>
 (Int.or (Int.or (Int.or
            (Int.repr (Znth  i    arr 0))
   (Int.shl (Int.repr (Znth (i+1) arr 0)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth (i+2) arr 0)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth (i+3) arr 0)) (Int.repr 24))).
Proof. reflexivity. Qed.

(* outputs a list of 4 bytes *)
Definition put_uint32_le (x : int) : list int :=
  [ (Int.and           x                (Int.repr 255));
    (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255)) ].
Lemma put_uint32_le_def: put_uint32_le = fun (x : int) =>
  [ (Int.and           x                (Int.repr 255));
    (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255)) ].
Proof. reflexivity. Qed.

Definition output_four_ints_as_bytes (s : four_ints) :=
  (put_uint32_le (col 0 s)) ++
  (put_uint32_le (col 1 s)) ++
  (put_uint32_le (col 2 s)) ++
  (put_uint32_le (col 3 s)).
Lemma output_four_ints_as_bytes_def: output_four_ints_as_bytes = fun (s : four_ints) =>
  (put_uint32_le (col 0 s)) ++
  (put_uint32_le (col 1 s)) ++
  (put_uint32_le (col 2 s)) ++
  (put_uint32_le (col 3 s)).
Proof. reflexivity. Qed.

Definition byte0 (x : int) : Z :=
  (Z.land (Int.unsigned x) (Int.unsigned (Int.repr 255))).
Lemma byte0_def: byte0 = fun (x : int) =>
  (Z.land (Int.unsigned x) (Int.unsigned (Int.repr 255))).
Proof. reflexivity. Qed.

Definition byte1 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).
Lemma byte1_def: byte1 = fun (x : int) =>
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).
Proof. reflexivity. Qed.

Definition byte2 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 16))) (Int.unsigned (Int.repr 255))).
Lemma byte2_def: byte2 = fun (x : int) =>
  (Z.land (Int.unsigned (Int.shru x (Int.repr 16))) (Int.unsigned (Int.repr 255))).
Proof. reflexivity. Qed.

Definition byte3 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 24))) (Int.unsigned (Int.repr 255))).
Lemma byte3_def: byte3 = fun (x : int) =>
  (Z.land (Int.unsigned (Int.shru x (Int.repr 24))) (Int.unsigned (Int.repr 255))).
Proof. reflexivity. Qed.

Definition mbed_tls_fround_col (col0 col1 col2 col3 : int) (rk : Z) : int :=
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
    (Znth (byte0 col0) FT0 Int.zero))
    (Znth (byte1 col1) FT1 Int.zero))
    (Znth (byte2 col2) FT2 Int.zero))
    (Znth (byte3 col3) FT3 Int.zero)).
Lemma mbed_tls_fround_col_def: mbed_tls_fround_col = fun (col0 col1 col2 col3 : int) (rk : Z) =>
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
    (Znth (byte0 col0) FT0 Int.zero))
    (Znth (byte1 col1) FT1 Int.zero))
    (Znth (byte2 col2) FT2 Int.zero))
    (Znth (byte3 col3) FT3 Int.zero)).
Proof. reflexivity. Qed.

Definition mbed_tls_final_fround_col (col0 col1 col2 col3 : int) (rk : Z) : int :=
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
             (Znth (byte0 col0) FSb Int.zero)              )
    (Int.shl (Znth (byte1 col1) FSb Int.zero) (Int.repr 8)))
    (Int.shl (Znth (byte2 col2) FSb Int.zero) (Int.repr 16)))
    (Int.shl (Znth (byte3 col3) FSb Int.zero) (Int.repr 24))).
Lemma mbed_tls_final_fround_col_def: mbed_tls_final_fround_col =
fun (col0 col1 col2 col3 : int) (rk : Z) =>
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
             (Znth (byte0 col0) FSb Int.zero)              )
    (Int.shl (Znth (byte1 col1) FSb Int.zero) (Int.repr 8)))
    (Int.shl (Znth (byte2 col2) FSb Int.zero) (Int.repr 16)))
    (Int.shl (Znth (byte3 col3) FSb Int.zero) (Int.repr 24))).
Proof. reflexivity. Qed.

Definition mbed_tls_initial_add_round_key_col (col_id : Z) (plaintext : list Z) (rks : list Z) :=
  Int.xor (get_uint32_le plaintext (col_id * 4)) (Int.repr (Znth col_id rks 0)).
Lemma mbed_tls_initial_add_round_key_col_def: mbed_tls_initial_add_round_key_col =
fun (col_id : Z) (plaintext : list Z) (rks : list Z) =>
  Int.xor (get_uint32_le plaintext (col_id * 4)) (Int.repr (Znth col_id rks 0)).
Proof. reflexivity. Qed.

Definition mbed_tls_fround (cols : four_ints) (rks : list Z) (i : Z) : four_ints :=
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_fround_col col0 col1 col2 col3 (Znth  i    rks 0)),
  ((mbed_tls_fround_col col1 col2 col3 col0 (Znth (i+1) rks 0)),
  ((mbed_tls_fround_col col2 col3 col0 col1 (Znth (i+2) rks 0)),
   (mbed_tls_fround_col col3 col0 col1 col2 (Znth (i+3) rks 0)))))
end.
Lemma mbed_tls_fround_def: mbed_tls_fround =
fun (cols : four_ints) (rks : list Z) (i : Z) =>
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_fround_col col0 col1 col2 col3 (Znth  i    rks 0)),
  ((mbed_tls_fround_col col1 col2 col3 col0 (Znth (i+1) rks 0)),
  ((mbed_tls_fround_col col2 col3 col0 col1 (Znth (i+2) rks 0)),
   (mbed_tls_fround_col col3 col0 col1 col2 (Znth (i+3) rks 0)))))
end.
Proof. reflexivity. Qed.

Definition mbed_tls_final_fround (cols : four_ints) (rks : list Z) (i : Z) : four_ints :=
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_final_fround_col col0 col1 col2 col3 (Znth  i    rks 0)),
  ((mbed_tls_final_fround_col col1 col2 col3 col0 (Znth (i+1) rks 0)),
  ((mbed_tls_final_fround_col col2 col3 col0 col1 (Znth (i+2) rks 0)),
   (mbed_tls_final_fround_col col3 col0 col1 col2 (Znth (i+3) rks 0)))))
end.
Lemma mbed_tls_final_fround_def: mbed_tls_final_fround =
fun (cols : four_ints) (rks : list Z) (i : Z) =>
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_final_fround_col col0 col1 col2 col3 (Znth  i    rks 0)),
  ((mbed_tls_final_fround_col col1 col2 col3 col0 (Znth (i+1) rks 0)),
  ((mbed_tls_final_fround_col col2 col3 col0 col1 (Znth (i+2) rks 0)),
   (mbed_tls_final_fround_col col3 col0 col1 col2 (Znth (i+3) rks 0)))))
end.
Proof. reflexivity. Qed.

Fixpoint mbed_tls_enc_rounds (n : nat) (state : four_ints) (rks : list Z) (i : Z) : four_ints :=
match n with
| O => state
| S m => mbed_tls_fround (mbed_tls_enc_rounds m state rks i) rks (i+4*Z.of_nat m)
end.
Lemma mbed_tls_enc_rounds_def: mbed_tls_enc_rounds =
fix mbed_tls_enc_rounds (n : nat) (state : four_ints) (rks : list Z) (i : Z) :=
match n with
| O => state
| S m => mbed_tls_fround (mbed_tls_enc_rounds m state rks i) rks (i+4*Z.of_nat m)
end.
Proof. reflexivity. Qed.

(* plaintext: array of bytes
   rks: expanded round keys, array of Int32 *)
Definition mbed_tls_initial_add_round_key (plaintext : list Z) (rks : list Z) : four_ints :=
((mbed_tls_initial_add_round_key_col 0 plaintext rks),
((mbed_tls_initial_add_round_key_col 1 plaintext rks),
((mbed_tls_initial_add_round_key_col 2 plaintext rks),
((mbed_tls_initial_add_round_key_col 3 plaintext rks))))).
Lemma mbed_tls_initial_add_round_key_def: mbed_tls_initial_add_round_key =
fun (plaintext : list Z) (rks : list Z) =>
((mbed_tls_initial_add_round_key_col 0 plaintext rks),
((mbed_tls_initial_add_round_key_col 1 plaintext rks),
((mbed_tls_initial_add_round_key_col 2 plaintext rks),
((mbed_tls_initial_add_round_key_col 3 plaintext rks))))).
Proof. reflexivity. Qed.

Definition mbed_tls_aes_enc (plaintext : list Z) (rks : list Z) : list int :=
  let state0  := mbed_tls_initial_add_round_key plaintext rks in
  let state13 := mbed_tls_enc_rounds 13 state0 rks 4 in
  let state14 := mbed_tls_final_fround state13 rks 56 in
  (put_uint32_le (col 0 state14)) ++
  (put_uint32_le (col 1 state14)) ++
  (put_uint32_le (col 2 state14)) ++
  (put_uint32_le (col 3 state14)).
Lemma mbed_tls_aes_enc_def: mbed_tls_aes_enc = fun (plaintext : list Z) (rks : list Z) =>
  let state0  := mbed_tls_initial_add_round_key plaintext rks in
  let state13 := mbed_tls_enc_rounds 13 state0 rks 4 in
  let state14 := mbed_tls_final_fround state13 rks 56 in
  output_four_ints_as_bytes state14.
Proof. reflexivity. Qed.

End AES_LL_Spec.

