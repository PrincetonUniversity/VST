Require Import floyd.proofauto.
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

(*TODO: support the following part of the tetxual spec:
      m and c can point to the same address (in-place encryption/decryption). 
     If they don't, the regions should not overlap.*)
Definition f_crypto_stream_salsa20_tweet_spec := 
  DECLARE _crypto_stream_salsa20_tweet
   WITH c : val, k:val, nonce:val, d:int64,
        Nonce : SixteenByte, K: SixteenByte * SixteenByte,
        (*mCont: list byte, *) SV:val
   PRE [ _c OF tptr tuchar, (*_m OF tptr tuchar,*) _d OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP ((*Zlength mCont = Int64.unsigned b*))
      LOCAL (temp _c c; (*temp _m m;*) temp _d (Vlong d);
             temp _n nonce; temp _k k; gvar _sigma SV)
      SEP ( SByte Nonce nonce;
            data_at_ Tsh (Tarray tuchar (Int64.unsigned d) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector SV
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ] 
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector SV; 
            ThirtyTwoByte K k;
            crypto_stream_xor_postsep d Nonce K (list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero) (Int64.unsigned d) nonce c nullval). 

Lemma crypto_stream_salsa20_tweet_ok: semax_body SalsaVarSpecs (crypto_stream_salsa20_xor_spec::SalsaFunSpecs)
      f_crypto_stream_salsa20_tweet
      f_crypto_stream_salsa20_tweet_spec.
Proof. 
start_function.
abbreviate_semax.
forward_call (c, k, nullval, nonce, d, Nonce, K, list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero, SV).
{ simpl; entailer!. }
apply Zlength_list_repeat. apply Int64.unsigned_range.

forward.
Qed.

Definition f_crypto_stream_xsalsa20_tweet_spec := 
  DECLARE _crypto_stream_xsalsa20_tweet
   WITH c : val, k:val, nonce:val, d:int64,
        Nonce : SixteenByte, Nonce2 : SixteenByte, K: SixteenByte * SixteenByte,
        SV:val
   PRE [ _c OF tptr tuchar,  _d OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP ()
      LOCAL (temp _c c; (*temp _m m;*) temp _d (Vlong d);
             temp _n nonce; temp _k k; gvar _sigma SV)
      SEP ( SByte Nonce nonce; SByte Nonce2 (offset_val 16 nonce);
            data_at_ Tsh (Tarray tuchar (Int64.unsigned d) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector SV
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ] 
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector SV; 
            EX HSalsaRes:_, crypto_stream_xor_postsep d Nonce2 HSalsaRes
              (list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero) (Int64.unsigned d)
              (offset_val 16 nonce) c nullval;
            data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
            ThirtyTwoByte K k).
(*            crypto_stream_xor_postsep d Nonce K (list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero) (Int64.unsigned d) nonce c k nullval). *)

(*The crypto_stream function*)
Lemma crypto_stream_xsalsa20_tweet_ok: 
      semax_body SalsaVarSpecs (crypto_stream_salsa20_xor_spec::f_crypto_stream_salsa20_tweet_spec::SalsaFunSpecs)
      f_crypto_stream_xsalsa20_tweet
      f_crypto_stream_xsalsa20_tweet_spec.
Proof. 
start_function.
abbreviate_semax.
rename lvar0 into s. unfold data_at_, field_at_. simpl.
unfold Sigma_vector.
forward_call (SV, k, nonce, s, 
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
  exists ((littleendian_invert (Znth 0 v Int.zero),
           littleendian_invert (Znth 5 v Int.zero),
           littleendian_invert (Znth 10 v Int.zero),
           littleendian_invert (Znth 15 v Int.zero)),
          (littleendian_invert (Znth 6 v Int.zero),
           littleendian_invert (Znth 7 v Int.zero),
           littleendian_invert (Znth 8 v Int.zero),
           littleendian_invert (Znth 9 v Int.zero))).
  do 2 rewrite SixteenByte2ValList_char. repeat rewrite <- app_assoc. trivial. }
destruct H0 as [HSalsaRes HS]. rewrite HS. 
forward_call (c, s, offset_val 16 nonce, d, Nonce2, HSalsaRes, SV).
{ unfold SByte, Sigma_vector, ThirtyTwoByte.
  destruct HSalsaRes as [q1 q2]. cancel.
  unfold data_at_. cancel. }
forward.
simpl. Exists s. unfold ThirtyTwoByte. entailer.
 Exists HSalsaRes. entailer. cancel.
destruct HSalsaRes as [q1 q2]. cancel.
Qed.

Definition f_crypto_stream_xsalsa20_tweet_xor_spec := 
  DECLARE _crypto_stream_salsa20_tweet_xor
   WITH c : val, k:val, nonce:val, m:val, d:int64, mCont: list byte,
        Nonce : SixteenByte, Nonce2 : SixteenByte, K: SixteenByte * SixteenByte,
        SV:val
   PRE [ _c OF tptr tuchar, _m OF tptr tuchar,  _d OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP (Zlength mCont = Int64.unsigned d)
      LOCAL (temp _c c; temp _m m; temp _d (Vlong d);
             temp _n nonce; temp _k k; gvar _sigma SV)
      SEP ( SByte Nonce nonce; SByte Nonce2 (offset_val 16 nonce);
            data_at_ Tsh (Tarray tuchar (Int64.unsigned d) noattr) c;
            ThirtyTwoByte K k;
            message_at mCont m;
            Sigma_vector SV
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ] 
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector SV; 
            EX HSalsaRes:_, crypto_stream_xor_postsep d Nonce2 HSalsaRes
              mCont (Int64.unsigned d)
              (offset_val 16 nonce) c m;
            data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
            ThirtyTwoByte K k).

(*The crypto_stream_xor function*)
Lemma crypto_stream_xsalsa20_tweet_xor_ok: 
      semax_body SalsaVarSpecs (crypto_stream_salsa20_xor_spec::f_crypto_stream_salsa20_tweet_spec::SalsaFunSpecs)
      f_crypto_stream_xsalsa20_tweet_xor
      f_crypto_stream_xsalsa20_tweet_xor_spec.
Proof. 
start_function.
abbreviate_semax.
rename lvar0 into s. rename H into mLen. unfold data_at_, field_at_. simpl.
unfold Sigma_vector.
forward_call (SV, k, nonce, s, 
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
{ exists ((littleendian_invert (Znth 0 v Int.zero),
           littleendian_invert (Znth 5 v Int.zero),
           littleendian_invert (Znth 10 v Int.zero),
           littleendian_invert (Znth 15 v Int.zero)),
          (littleendian_invert (Znth 6 v Int.zero),
           littleendian_invert (Znth 7 v Int.zero),
           littleendian_invert (Znth 8 v Int.zero),
           littleendian_invert (Znth 9 v Int.zero))).
  do 2 rewrite SixteenByte2ValList_char. repeat rewrite <- app_assoc. trivial. }
destruct H0 as [HSalsaRes HS]. rewrite HS. 
forward_call (c, s, m, offset_val 16 nonce, d, Nonce2, HSalsaRes, mCont, SV).
{ unfold SByte, Sigma_vector. unfold ThirtyTwoByte at 2. 
  destruct HSalsaRes as [q1 q2]. cancel.
  unfold data_at_. cancel. }
forward.
simpl. Exists s. entailer.
 unfold ThirtyTwoByte.
 Exists HSalsaRes. entailer. cancel.
 destruct HSalsaRes as [q1 q2]. cancel.
Qed.
