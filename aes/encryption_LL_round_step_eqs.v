(* This file contains highly trivial proofs, but they are carefully engineered
   in such a way that the Qed is fast. This is tricky because we have to avoid
   that constants such as 12 or 13 are unfolded by the typechecker while unifying
   two terms. *)

Require Import aes.spec_encryption_LL.
Require Import compcert.common.Values.
Local Open Scope Z.

Lemma round13eq: forall buf S12 S13,
       S13 = mbed_tls_fround S12 buf 52 ->
       Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 52 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 0 S12))
                        (Int.unsigned (Int.repr 255))) FT0))
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 1 S12) (Int.repr 8)))
                     (Int.unsigned (Int.repr 255))) FT1))
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 2 S12) (Int.repr 16)))
                  (Int.unsigned (Int.repr 255))) FT2))
         (Znth
            (Z.land (Int.unsigned (Int.shru (col 3 S12) (Int.repr 24)))
               (Int.unsigned (Int.repr 255))) FT3) = col 0 S13
   /\  Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 53 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 1 S12))
                        (Int.unsigned (Int.repr 255))) FT0))
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 2 S12) (Int.repr 8)))
                     (Int.unsigned (Int.repr 255))) FT1))
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 3 S12) (Int.repr 16)))
                  (Int.unsigned (Int.repr 255))) FT2))
         (Znth
            (Z.land (Int.unsigned (Int.shru (col 0 S12) (Int.repr 24)))
               (Int.unsigned (Int.repr 255))) FT3) = col 1 S13
   /\  Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 54 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 2 S12))
                        (Int.unsigned (Int.repr 255))) FT0))
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 3 S12) (Int.repr 8)))
                     (Int.unsigned (Int.repr 255))) FT1))
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 0 S12) (Int.repr 16)))
                  (Int.unsigned (Int.repr 255))) FT2))
         (Znth
            (Z.land (Int.unsigned (Int.shru (col 1 S12) (Int.repr 24)))
               (Int.unsigned (Int.repr 255))) FT3) = col 2 S13
   /\  Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 55 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 3 S12))
                        (Int.unsigned (Int.repr 255))) FT0))
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 0 S12) (Int.repr 8)))
                     (Int.unsigned (Int.repr 255))) FT1))
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 1 S12) (Int.repr 16)))
                  (Int.unsigned (Int.repr 255))) FT2))
         (Znth
            (Z.land (Int.unsigned (Int.shru (col 2 S12) (Int.repr 24)))
               (Int.unsigned (Int.repr 255))) FT3) = col 3 S13.
Proof.
  intros. subst S13. destruct S12 as [c0 [c1 [c2 c3]]]. repeat split.
Qed.

Lemma round14eq: forall buf S13 S14,
       S14 = mbed_tls_final_fround S13 buf 56 ->
       Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 56 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 0 S13))
                        (Int.unsigned (Int.repr 255))) FSb))
               (Int.shl
                  (Znth
                     (Z.land
                        (Int.unsigned (Int.shru (col 1 S13) (Int.repr 8)))
                        (Int.unsigned (Int.repr 255))) FSb)
                  (Int.repr 8)))
            (Int.shl
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 2 S13) (Int.repr 16)))
                     (Int.unsigned (Int.repr 255))) FSb)
               (Int.repr 16)))
         (Int.shl
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 3 S13) (Int.repr 24)))
                  (Int.unsigned (Int.repr 255))) FSb) (Int.repr 24)) =
       col 0 S14
    /\ Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 57 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 1 S13))
                        (Int.unsigned (Int.repr 255))) FSb))
               (Int.shl
                  (Znth
                     (Z.land
                        (Int.unsigned (Int.shru (col 2 S13) (Int.repr 8)))
                        (Int.unsigned (Int.repr 255))) FSb)
                  (Int.repr 8)))
            (Int.shl
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 3 S13) (Int.repr 16)))
                     (Int.unsigned (Int.repr 255))) FSb)
               (Int.repr 16)))
         (Int.shl
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 0 S13) (Int.repr 24)))
                  (Int.unsigned (Int.repr 255))) FSb) (Int.repr 24)) =
       col 1 S14
    /\ Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 58 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 2 S13))
                        (Int.unsigned (Int.repr 255))) FSb))
               (Int.shl
                  (Znth
                     (Z.land
                        (Int.unsigned (Int.shru (col 3 S13) (Int.repr 8)))
                        (Int.unsigned (Int.repr 255))) FSb)
                  (Int.repr 8)))
            (Int.shl
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 0 S13) (Int.repr 16)))
                     (Int.unsigned (Int.repr 255))) FSb)
               (Int.repr 16)))
         (Int.shl
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 1 S13) (Int.repr 24)))
                  (Int.unsigned (Int.repr 255))) FSb) (Int.repr 24)) =
       col 2 S14
    /\ Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (Int.repr (Znth 59 buf))
                  (Znth
                     (Z.land (Int.unsigned (col 3 S13))
                        (Int.unsigned (Int.repr 255))) FSb))
               (Int.shl
                  (Znth
                     (Z.land
                        (Int.unsigned (Int.shru (col 0 S13) (Int.repr 8)))
                        (Int.unsigned (Int.repr 255))) FSb)
                  (Int.repr 8)))
            (Int.shl
               (Znth
                  (Z.land (Int.unsigned (Int.shru (col 1 S13) (Int.repr 16)))
                     (Int.unsigned (Int.repr 255))) FSb)
               (Int.repr 16)))
         (Int.shl
            (Znth
               (Z.land (Int.unsigned (Int.shru (col 2 S13) (Int.repr 24)))
                  (Int.unsigned (Int.repr 255))) FSb) (Int.repr 24)) =
       col 3 S14.
Proof.
  intros. subst S14. destruct S13 as [c0 [c1 [c2 c3]]]. repeat split.
Qed.

Lemma map_append_eq_4x4:
  forall (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15: int)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15: int),
  a0  = b0  -> a1  = b1  ->  a2 = b2  -> a3  = b3  ->
  a4  = b4  -> a5  = b5  ->  a6 = b6  -> a7  = b7  ->
  a8  = b8  -> a9  = b9  -> a10 = b10 -> a11 = b11 ->
  a12 = b12 -> a13 = b13 -> a14 = b14 -> a15 = b15 ->
  map Vint ([a0; a1; a2; a3] ++ [a4; a5; a6; a7] ++ [a8; a9; a10; a11] ++ [a12; a13; a14; a15])
= [Vint b0; Vint b1; Vint b2; Vint b3; Vint b4; Vint b5; Vint b6; Vint b7;
   Vint b8; Vint b9; Vint b10; Vint b11; Vint b12; Vint b13; Vint b14; Vint b15].
Proof.
  intros. subst. reflexivity.
Qed.

(* This is more general than what we need (we only need it for i=12), but if we prove it for i=12
   directly, the Qed takes forever. *)
Lemma round13_eq_assemble_general: forall i buf plaintext S0 S12 S13,
  S0 = mbed_tls_initial_add_round_key plaintext buf ->
  S12 = mbed_tls_enc_rounds i S0 buf 4 ->
  S13 = mbed_tls_fround S12 buf (4 + 4 * Z.of_nat i) ->
  S13 = mbed_tls_enc_rounds (S i) (mbed_tls_initial_add_round_key plaintext buf) buf 4.
Proof.
  intros.
  progress (unfold mbed_tls_enc_rounds; fold mbed_tls_enc_rounds).
  subst S0 S12 S13. reflexivity.
Qed.

Lemma round13_eq_assemble: forall buf plaintext S0 S12 S13,
  S0 = mbed_tls_initial_add_round_key plaintext buf ->
  S12 = mbed_tls_enc_rounds 12 S0 buf 4 ->
  S13 = mbed_tls_fround S12 buf 52 ->
  S13 = mbed_tls_enc_rounds 13 (mbed_tls_initial_add_round_key plaintext buf) buf 4.
Proof.
  intros. eapply round13_eq_assemble_general; eassumption.
Qed.

Lemma final_aes_eq: forall buf plaintext S0 S12 S13,
  S0 = mbed_tls_initial_add_round_key plaintext buf ->
  S12 = mbed_tls_enc_rounds 12 S0 buf 4 ->
  S13 = mbed_tls_fround S12 buf 52 ->
  [Vint (Int.and           (col 0 (mbed_tls_final_fround S13 buf 56))                (Int.repr 255));
   Vint (Int.and (Int.shru (col 0 (mbed_tls_final_fround S13 buf 56)) (Int.repr  8)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 0 (mbed_tls_final_fround S13 buf 56)) (Int.repr 16)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 0 (mbed_tls_final_fround S13 buf 56)) (Int.repr 24)) (Int.repr 255));
   Vint (Int.and           (col 1 (mbed_tls_final_fround S13 buf 56)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 1 (mbed_tls_final_fround S13 buf 56)) (Int.repr  8)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 1 (mbed_tls_final_fround S13 buf 56)) (Int.repr 16)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 1 (mbed_tls_final_fround S13 buf 56)) (Int.repr 24)) (Int.repr 255));
   Vint (Int.and           (col 2 (mbed_tls_final_fround S13 buf 56))                (Int.repr 255));
   Vint (Int.and (Int.shru (col 2 (mbed_tls_final_fround S13 buf 56)) (Int.repr  8)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 2 (mbed_tls_final_fround S13 buf 56)) (Int.repr 16)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 2 (mbed_tls_final_fround S13 buf 56)) (Int.repr 24)) (Int.repr 255));
   Vint (Int.and           (col 3 (mbed_tls_final_fround S13 buf 56))                (Int.repr 255));
   Vint (Int.and (Int.shru (col 3 (mbed_tls_final_fround S13 buf 56)) (Int.repr  8)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 3 (mbed_tls_final_fround S13 buf 56)) (Int.repr 16)) (Int.repr 255));
   Vint (Int.and (Int.shru (col 3 (mbed_tls_final_fround S13 buf 56)) (Int.repr 24)) (Int.repr 255))]
= map Vint (mbed_tls_aes_enc plaintext buf).
Proof.
  intros.
  unfold mbed_tls_aes_enc. progress unfold output_four_ints_as_bytes. progress unfold put_uint32_le.
  pose proof (round13_eq_assemble buf plaintext S0 S12 S13) as E.
  specialize (E H H0 H1).
  apply map_append_eq_4x4; repeat f_equal; exact E.
Qed.
