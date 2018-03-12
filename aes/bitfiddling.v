Require Export aes.conv_HL_to_LL.
Local Open Scope Z.

Lemma byte0_word_to_int: forall b0 b1 b2 b3,
  byte0 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b0.
Admitted.

Lemma byte1_word_to_int: forall b0 b1 b2 b3,
  byte1 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b1.
Admitted.

Lemma byte2_word_to_int: forall b0 b1 b2 b3,
  byte2 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b2.
Admitted.

Lemma byte3_word_to_int: forall b0 b1 b2 b3,
  byte3 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b3.
Admitted.

Lemma xor_byte0_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Znth i tablesLL.FSb)
  = word_to_int ((Int.xor b0 (Znth i tablesLL.FSb)), b1, b2, b3).
Admitted.

Lemma xor_byte1_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Int.shl (Znth i tablesLL.FSb) (Int.repr 8))
  = word_to_int (b0, (Int.xor b1 (Znth i tablesLL.FSb)), b2, b3).
Admitted.

Lemma xor_byte2_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Int.shl (Znth i tablesLL.FSb) (Int.repr 16))
  = word_to_int (b0, b1, (Int.xor b2 (Znth i tablesLL.FSb)), b3).
Admitted.

Lemma xor_byte3_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Int.shl (Znth i tablesLL.FSb) (Int.repr 24))
  = word_to_int (b0, b1, b2, (Int.xor b3 (Znth i tablesLL.FSb))).
Admitted.

Lemma equiv_sbox: forall b,
  Znth (Int.unsigned b) tablesLL.FSb = look_sbox b.
Admitted.

Lemma xor_word_to_int: forall a0 a1 a2 a3 b0 b1 b2 b3,
  Int.xor (word_to_int (a0, a1, a2, a3)) (word_to_int (b0, b1, b2, b3))
  = word_to_int ((Int.xor a0 b0), (Int.xor a1 b1), (Int.xor a2 b2), (Int.xor a3 b3)).
Admitted.

Lemma rot8_word_to_int: forall b0 b1 b2 b3,
  rot8 (word_to_int (b0, b1, b2, b3)) = word_to_int (b3, b0, b1, b2).
Admitted.

Lemma mask_byte_nop: forall i,
  0 <= Int.unsigned i < 256 ->
  Int.and i (Int.repr 255) = i.
Admitted.

Lemma FSb_range: forall i,
  0 <= Int.unsigned (Znth i FSb) < 256.
Admitted.

Lemma zero_ext_nop: forall i,
  0 <= (Int.unsigned i) < 256 ->
  Int.zero_ext 8 i = i.
Admitted.

Lemma FSb_inj: forall i j,
  0 <= i < 256 ->
  0 <= j < 256 ->
  Znth i FSb = Znth j FSb ->
  i = j.
Admitted.

Lemma FSb_RSb_id: forall j,
  0 <= j < 256 ->
  j = Int.unsigned (Znth (Int.unsigned (Znth j RSb)) FSb).
Admitted.

Lemma RSb_inj: forall i j,
  0 <= i < 256 ->
  0 <= j < 256 ->
  Znth i RSb = Znth j RSb ->
  i = j.
Admitted.

Lemma RSb_range: forall i,
  0 <= Int.unsigned (Znth i RSb) < 256.
Admitted.


(* TODO also requires that 0 <= b0, b1, b2, b3 < 256 *)
Lemma xor_is_or_4_bytes: forall b0 b1 b2 b3,
  (Int.xor (Int.xor (Int.xor b0
                    (Int.shl b1 (Int.repr 8)))
                    (Int.shl b2 (Int.repr 16)))
                    (Int.shl b3 (Int.repr 24))) =
  (Int.or  (Int.or  (Int.or  b0 
                    (Int.shl b1 (Int.repr 8)))
                    (Int.shl b2 (Int.repr 16)))
                    (Int.shl b3 (Int.repr 24))).
Admitted.

Lemma masked_byte_range: forall i,
  0 <= Z.land i 255 < 256.
Admitted.

Lemma zero_ext_mask: forall i,
  Int.zero_ext 8 i = Int.and i (Int.repr 255).
Admitted.
