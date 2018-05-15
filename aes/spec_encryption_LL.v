Require Export aes.spec_utils_LL.
Require Export aes.tablesLL.
Local Open Scope Z.

Definition mbed_tls_fround_col (col0 col1 col2 col3 : int) (rk : Z) : int :=
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
    (Znth (byte0 col0) FT0))
    (Znth (byte1 col1) FT1))
    (Znth (byte2 col2) FT2))
    (Znth (byte3 col3) FT3)).

Definition mbed_tls_final_fround_col (col0 col1 col2 col3 : int) (rk : Z) : int :=
  (Int.xor (Int.xor (Int.xor (Int.xor (Int.repr rk)
             (Znth (byte0 col0) FSb)              )
    (Int.shl (Znth (byte1 col1) FSb) (Int.repr 8)))
    (Int.shl (Znth (byte2 col2) FSb) (Int.repr 16)))
    (Int.shl (Znth (byte3 col3) FSb) (Int.repr 24))).

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

Definition mbed_tls_initial_add_round_key_col (col_id : Z) (plaintext : list Z) (rks : list Z) :=
  Int.xor (get_uint32_le plaintext (col_id * 4)) (Int.repr (Znth col_id rks)).

Definition mbed_tls_fround (cols : four_ints) (rks : list Z) (i : Z) : four_ints :=
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_fround_col col0 col1 col2 col3 (Znth  i    rks)),
  ((mbed_tls_fround_col col1 col2 col3 col0 (Znth (i+1) rks)),
  ((mbed_tls_fround_col col2 col3 col0 col1 (Znth (i+2) rks)),
   (mbed_tls_fround_col col3 col0 col1 col2 (Znth (i+3) rks)))))
end.

Definition mbed_tls_final_fround (cols : four_ints) (rks : list Z) (i : Z) : four_ints :=
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_final_fround_col col0 col1 col2 col3 (Znth  i    rks)),
  ((mbed_tls_final_fround_col col1 col2 col3 col0 (Znth (i+1) rks)),
  ((mbed_tls_final_fround_col col2 col3 col0 col1 (Znth (i+2) rks)),
   (mbed_tls_final_fround_col col3 col0 col1 col2 (Znth (i+3) rks)))))
end.

Fixpoint mbed_tls_enc_rounds (n : nat) (state : four_ints) (rks : list Z) (i : Z) : four_ints :=
match n with
| O => state
| S m => mbed_tls_fround (mbed_tls_enc_rounds m state rks i) rks (i+4*Z.of_nat m)
end.

(* plaintext: array of bytes
   rks: expanded round keys, array of Int32 *)
Definition mbed_tls_initial_add_round_key (plaintext : list Z) (rks : list Z) : four_ints :=
((mbed_tls_initial_add_round_key_col 0 plaintext rks),
((mbed_tls_initial_add_round_key_col 1 plaintext rks),
((mbed_tls_initial_add_round_key_col 2 plaintext rks),
((mbed_tls_initial_add_round_key_col 3 plaintext rks))))).

Definition output_four_ints_as_bytes (s : four_ints) :=
  (put_uint32_le (col 0 s)) ++
  (put_uint32_le (col 1 s)) ++
  (put_uint32_le (col 2 s)) ++
  (put_uint32_le (col 3 s)).

Definition mbed_tls_aes_enc (plaintext : list Z) (rks : list Z) : list int :=
  let state0  := mbed_tls_initial_add_round_key plaintext rks in
  let state13 := mbed_tls_enc_rounds 13 state0 rks 4 in
  let state14 := mbed_tls_final_fround state13 rks 56 in
  output_four_ints_as_bytes state14.
