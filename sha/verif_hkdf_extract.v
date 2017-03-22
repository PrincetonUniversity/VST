Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.hmac_common_lemmas.

Require Import sha.hkdf.
Require Import sha.spec_hmac.
Require Import sha.spec_hkdf.
Require Import sha.hkdf_functional_prog.

Lemma body_hkdf_extract: semax_body Hkdf_VarSpecs Hkdf_FunSpecs 
       f_HKDF_extract HKDF_extract_spec.
Proof.
start_function.
rename H into LenSalt. rename H0 into LenSecret.
freeze [0;2;3;4] FR1.
assert_PROP (isptr salt) as Ptr_salt.
{ unfold data_block. normalize. rewrite data_at_isptr. entailer!. }
apply vst_lemmas.isptrD in Ptr_salt. destruct Ptr_salt as [sb [si SLT]]. subst salt.
thaw FR1.
idtac "Timing the call to HMAC".
Time forward_call (out, SALT, secret, SECRET, kv, shmd, sb, si).
apply extract_exists_pre. intros Hmac.
idtac "Timing the Intros". Time Intros. (*Coq8.6: 146s*) (*Coq8.5: 77.468 secs (77.25u,0.015s)*)
rename H into HypHmac. rename H0 into HypHmacBits. rename H1 into HmacCrypto.

assert_PROP (isptr out) as Ptr_out.
{ unfold data_block. normalize. rewrite data_at_isptr. entailer!. }
forward_if (PROP ( )
   LOCAL (temp _t'1 out; temp _out_key out; 
   temp _out_len olen; temp _salt (Vptr sb si); temp _salt_len (Vint (Int.repr (LEN SALT)));
   temp _secret secret; temp _secret_len (Vint (Int.repr (LEN SECRET)));
   gvar sha._K256 kv)
   SEP (K_vector kv; data_block shmd Hmac out; initPostKey (Vptr sb si) (CONT SALT);
   data_block Tsh (CONT SECRET) secret; data_at_ Tsh tuint olen)).
{ apply denote_tc_comparable_split.
  + unfold data_block. normalize.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2. apply data_at_valid_ptr.
    apply readable_nonidentity. apply writable_readable; trivial.
    rewrite HMAC_Zlength; simpl; omega.
  + apply valid_pointer_zero. }
{ subst out; contradiction. }
{ clear H; forward. entailer!. }

forward. forward. 
unfold HKDF_extract. cancel. 
Time Qed.
(*Coq 8.6: 2.5 secs*)
(*Feb 23rd 2017 (Coq8.5pl2): Finished transaction in 24.859 secs (17.937u,0.s) (successful)*)
 (*earlier: Finished transaction in 5.781 secs (4.89u,0.s) (successful)*)