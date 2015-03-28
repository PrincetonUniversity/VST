Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.

Require Import sha.hmac091c.

Require Import sha.spec_hmac.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Lemma body_hmac_simple: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC HMAC_spec.
Proof.
start_function.
name key' _key.
name keylen' _key_len.
name d' _d.
name n' _n.
name md' _md.
simpl_stackframe_of. fixup_local_var; intro c. 

rename keyVal into k. rename msgVal into d.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl in *.
rename H into WrshMD.
assert_PROP (isptr md). entailer. 
rename H into isPtrMD. rename H0 into KL. rename H1 into DL. 
forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st c); `(data_block Tsh key k);
   `(data_block Tsh data d); `(K_vector kv);
   `(memory_block shmd (Int.repr 32) md))).
  { (*Branch1*) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. } 
normalize. rename H into isptrC.
remember (HMACabs init_s256abs init_s256abs init_s256abs Z0 nil) as dummyHMA.
assert_PROP (isptr k). entailer. 
rename H into isPtrK. 
forward_call' (c, k, kl, key, kv, dummyHMA) h0.
 { apply isptrD in isPtrK. destruct isPtrK as [kb [kofs HK]]. rewrite HK.
   unfold initPre. cancel.
 }
normalize. rename H into HmacInit.

assert_PROP (s256a_len (absCtxt h0) = 512).
  { unfold hmacstate_. entailer. apply prop_right. 
    destruct h0; simpl in *.  
    destruct H3 as [reprMD [reprI [reprO [iShaLen [oShaLen [K [ii [KL1 [KL2 KL3]]]]]]]]].
    inversion HmacInit; clear HmacInit.
    destruct H3 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
  }
rename H into H0_len512.
forward_call' (h0, c, d, dl, data, kv) h1.
  { rewrite H0_len512. assumption. } 
rename H into HmacUpdate. 

(*TODO: forward_call' fails if the postcondition of 
  HMAC_final starts with two existentials EX dig:_, EX h2:_, ... 
  instead of the current EX digh2:_, ... *)
forward_call' (h1, c, md, shmd, kv) [dig h2].

simpl in H; rename H into HmacFinalSimple.

forward_call' (h2,c). destruct H as [SCc ACc].
forward.
simpl_stackframe_of. normalize.
assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; trivial.
assert (Size: sizeof t_struct_hmac_ctx_st <= Int.max_unsigned).
  rewrite int_max_unsigned_eq; simpl. omega.
  rewrite hmac_hmacSimple in HS. destruct HS. 
eapply hmac_sound in H5. subst dig.
cancel.
unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; try reflexivity.
2: rewrite lvar_eval_lvar with (v:=c); trivial. 

normalize. rewrite lvar_eval_lvar with (v:=c); trivial. 
  rewrite (memory_block_data_at_ Tsh (tarray tuchar (sizeof t_struct_hmac_ctx_st))).
  apply data_at_data_at_.
  trivial.
  trivial.
  trivial. 
  destruct c; trivial. unfold align_compatible. simpl. apply Z.divide_1_l. 
  simpl. rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
Qed.
