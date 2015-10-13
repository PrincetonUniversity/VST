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
assert_PROP (isptr md). entailer.
rename H into isPtrMD. 
forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st c); `(data_block Tsh key k);
   `(data_block Tsh data d); `(K_vector kv);
   `(memory_block shmd 32 md))).
  { apply denote_tc_comparable_split. 2: apply valid_pointer_zero. admit. (*TODO: is new side condition*) }
  { (*Branch1*) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. } 
normalize.
remember (HMACabs init_s256abs init_s256abs init_s256abs) as dummyHMA.
assert_PROP (isptr k). entailer. 
rename H into isPtrK. 
forward_call (c, k, kl, key, kv, dummyHMA) h0. 
 { apply isptrD in isPtrK. destruct isPtrK as [kb [kofs HK]]. rewrite HK.
   unfold initPre. cancel.
 }
normalize. rename H into HmacInit. 
assert_PROP (s256a_len (absCtxt h0) = 512).
  { unfold hmacstate_. entailer. apply prop_right. 
    destruct h0; simpl in *.  
    destruct H3 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion HmacInit; clear HmacInit.
    destruct H3 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
  }
rename H into H0_len512.
forward_call (h0, c, d, dl, data, kv) h1.
  { rewrite H0_len512. assumption. } 
rename H into HmacUpdate. 

assert_PROP (field_compatible (Tstruct _hmac_ctx_st noattr) [] c).
{ unfold hmacstate_; entailer. }
rename H into FC_c.

forward_call (h1, c, md, shmd, kv) [dig h2]. 
simpl in H; rename H into HmacFinalSimple. 

forward_call (h2,c). 
forward.

assert_PROP (field_compatible (tarray tuchar (sizeof cenv_cs t_struct_hmac_ctx_st)) [] c).
{ unfold data_block at 1. unfold Zlength. simpl. rewrite data_at_data_at'. normalize. }
Exists c. entailer. cancel.
assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; trivial.
apply hmacSimple_sound in HS. subst dig.
cancel. 
simpl in H5.

unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; trivial.
normalize.
  rewrite (memory_block_data_at_ Tsh (tarray tuchar (sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st))).
  2: trivial.
  eapply derives_trans. apply data_at_data_at_. apply derives_refl.
Qed.
