Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import Coq.Lists.List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.Snuffle.
Require Import tweetnacl20140427.spec_salsa. Opaque Snuffle.Snuffle.
Require Import tweetnacl20140427.verif_crypto_stream_salsa20_xor.

Lemma crypto_stream_salsa20_tweet_ok: semax_body SalsaVarSpecs (*(crypto_stream_salsa20_xor_spec::*)SalsaFunSpecs
      f_crypto_stream_salsa20_tweet
      f_crypto_stream_salsa20_tweet_spec.
Proof.
start_function.
abbreviate_semax.
forward_call (c, k, nullval, nonce, d, Nonce, K, list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero, gv).
{ simpl; entailer!. }
apply Zlength_list_repeat. apply Int64.unsigned_range.

forward.
Qed.

(*The crypto_stream function*)
Lemma crypto_stream_xsalsa20_tweet_ok:
      semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_xsalsa20_tweet
      f_crypto_stream_xsalsa20_tweet_spec.
Proof.
start_function. unfold data_at_, field_at_. simpl.
unfold Sigma_vector.
forward_call (gv _sigma, k, nonce, v_s,
        default_val (tarray tuchar 32),
        ((Nonce, SIGMA), K)).
{ unfold CoreInSEP, SByte. cancel. }
Intros v.
unfold CoreInSEP, SByte, Sigma_vector. normalize.
assert_PROP (isptr nonce) as PN by entailer!.
assert (exists HSalsaRes, hSalsaOut v =
   match HSalsaRes with (q1, q2) =>
     SixteenByte2ValList q1 ++ SixteenByte2ValList q2
   end).
{ unfold hSalsaOut.
  exists ((littleendian_invert (Znth 0 v),
           littleendian_invert (Znth 5 v),
           littleendian_invert (Znth 10 v),
           littleendian_invert (Znth 15 v)),
          (littleendian_invert (Znth 6 v),
           littleendian_invert (Znth 7 v),
           littleendian_invert (Znth 8 v),
           littleendian_invert (Znth 9 v))).
  do 2 rewrite SixteenByte2ValList_char. repeat rewrite <- app_assoc. trivial. }
destruct H0 as [HSalsaRes HS]. rewrite HS.
forward_call (c, v_s, offset_val 16 nonce, d, Nonce2, HSalsaRes, gv).
{ unfold SByte, Sigma_vector, ThirtyTwoByte.
  destruct HSalsaRes as [q1 q2]. cancel.
  unfold data_at_. cancel. }
forward.
unfold ThirtyTwoByte. entailer.
 Exists HSalsaRes. entailer. cancel.
destruct HSalsaRes as [q1 q2]. cancel.
Qed.

(*The crypto_stream_xor function*)
Lemma crypto_stream_xsalsa20_tweet_xor_ok:
      semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_xsalsa20_tweet_xor
      f_crypto_stream_xsalsa20_tweet_xor_spec.
Proof.
start_function.
rename v_s into s. rename H into mLen. unfold data_at_, field_at_. simpl.
unfold Sigma_vector.
forward_call (gv _sigma, k, nonce, s,
        default_val (tarray tuchar 32),
        ((Nonce, SIGMA), K)).
{ unfold CoreInSEP, SByte. cancel. }
Intros v.
unfold CoreInSEP, SByte, Sigma_vector. normalize.
assert_PROP (isptr nonce) as PN by entailer!.
assert (exists HSalsaRes, hSalsaOut v =
   match HSalsaRes with (q1, q2) =>
     SixteenByte2ValList q1 ++ SixteenByte2ValList q2
   end).
{ exists ((littleendian_invert (Znth 0 v),
           littleendian_invert (Znth 5 v),
           littleendian_invert (Znth 10 v),
           littleendian_invert (Znth 15 v)),
          (littleendian_invert (Znth 6 v),
           littleendian_invert (Znth 7 v),
           littleendian_invert (Znth 8 v),
           littleendian_invert (Znth 9 v))).
  do 2 rewrite SixteenByte2ValList_char. repeat rewrite <- app_assoc. trivial. }
destruct H0 as [[q1 q2] HS]. rewrite HS. 
forward_call (c, s, m, offset_val 16 nonce, d, Nonce2, (q1,q2), mCont, gv).
{ unfold SByte, Sigma_vector, data_at_. unfold ThirtyTwoByte at 2. cancel. }
forward.
Exists (q1, q2). unfold ThirtyTwoByte. entailer!.
Qed.