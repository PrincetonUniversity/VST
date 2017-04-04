Require Import aes.spec_AES256_HL.
Require Import aes.GF_ops_LL.

Lemma times2_equiv: forall b,
  0 <= Int.unsigned b < 256 ->
  times2 b = ff_mult (Int.repr 2) b.
Admitted.

Lemma times3_equiv: forall b,
  0 <= Int.unsigned b < 256 ->
  times3 b = ff_mult (Int.repr 3) b.
Admitted.

