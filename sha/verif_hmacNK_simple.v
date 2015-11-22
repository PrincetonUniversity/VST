Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac_NK.

Require Import sha.spec_hmacNK.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sublist.

Lemma body_hmac_simple: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC HMAC_spec.
Proof.
start_function.
name key' _key.
name keylen' _key_len.
name d' _d.
name n' _n.
name md' _md.
rename lvar0 into c.
rename keyVal into k. rename msgVal into d.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl in *.
rename H into KL. rename H0 into DL. 
assert_PROP (isptr md) as isPtrMD by entailer!.
forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvar sha._K256 kv)
   SEP  (data_at_ Tsh t_struct_hmac_ctx_st c; data_block Tsh key k;
   data_block Tsh data d; K_vector kv;
   memory_block shmd 32 md)).
  { apply denote_tc_comparable_split. 
    apply sepcon_valid_pointer2. apply memory_block_valid_ptr. auto. omega.
    apply valid_pointer_zero. }
  { (*Branch1*) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. } 
normalize.
assert_PROP (isptr k). { unfold data_block. normalize. rewrite data_at_isptr with (p:=k). entailer!. (*Issue: need to do unfold data_block. normalize. rewrite data_at_isptr with (p:=k). here is NEW*) }
rename H into isPtrK. 
forward_call (c, k, kl, key, kv, HMACabs nil nil nil). 
 { apply isptrD in isPtrK. destruct isPtrK as [kb [kofs HK]]. rewrite HK.
   unfold initPre. Time entailer!. (*1.1*)
 }
assert_PROP (s256a_len (absCtxt (hmacInit key)) = 512).
  { unfold hmacstate_. Intros r. apply prop_right. apply H. } 
rename H into H0_len512.
forward_call (hmacInit key, c, d, dl, data, kv).
  { rewrite H0_len512. assumption. } 

assert_PROP (field_compatible (Tstruct _hmac_ctx_st noattr) [] c).
{ unfold hmacstate_; entailer. }
rename H into FC_c.
remember  (hmacInit key) as h0.
forward_call ((hmacUpdate data h0), c, md, shmd, kv).
forward_call (fst (hmacFinal (hmacUpdate data h0)), c). 
(*VST Issue: 
remember (hmacFinal (hmacUpdate data h0)) as h2.  
forward_call (h2,c). does not work*)

forward.

assert_PROP (field_compatible (tarray tuchar (sizeof cenv_cs t_struct_hmac_ctx_st)) [] c).
{ unfold data_block at 1. unfold Zlength. simpl. rewrite data_at_data_at'. normalize. }
Exists c. entailer!.
rewrite <- (hmac_sound key data). unfold hmac.
cancel.  clear H3.
unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; trivial.
normalize.
  rewrite (memory_block_data_at_ Tsh (tarray tuchar (sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st))).
  2: trivial.
  eapply derives_trans. apply data_at_data_at_. apply derives_refl.
Qed.
