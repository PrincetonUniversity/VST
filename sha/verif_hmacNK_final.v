Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac_NK.
Require Import sha.spec_hmacNK.
Require Import sha.vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Lemma body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Final HMAC_Final_spec.
Proof.
start_function.
name ctx' _ctx.
name md' _md.
simpl_stackframe_of. fixup_local_var; intro buf.

rename H into WrshMD. 
rewrite memory_block_isptr. unfold hmacstate_. normalize.
rename H into isptrMD.
intros ST. normalize.
destruct h1; simpl in *.
destruct H as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

unfold_data_at 1%nat.
rewrite field_at_data_at with (gfs:=[StructField _md_ctx]).
assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
  { entailer!. } 
rename H into FC.
make_Vptr c. 
unfold field_address; rewrite if_true by auto.
normalize.
rewrite <- memory_block_data_at_ ; try reflexivity.
Focus 2. red. destruct buf; trivial. simpl. apply Z.divide_1_l.

(*Call Sha_Final*)
forward_call' (ctx, buf, Vptr b i, Tsh, kv).
  { unfold sha256state_. normalize. apply (exp_right (mdCtx ST)). entailer!. }
normalize. 

eapply semax_pre with (P':=(PROP  ()
   LOCAL  (lvar _buf (tarray tuchar 32) buf; temp _md md;
   temp _ctx (Vptr b i); gvar sha._K256 kv)
   SEP  (`(K_vector kv); 
   `(data_at Tsh t_struct_hmac_ctx_st (default_val sha.t_struct_SHA256state_st, snd ST) (Vptr b i));
   `(data_block Tsh (sha_finish ctx) buf);
   `(memory_block shmd (Int.repr 32) md)))).
{ entailer!. 
  unfold_data_at 1%nat. unfold data_at_.
  rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity. 
  unfold nested_field_type2, nested_field_offset2, field_address; simpl.
  rewrite if_true by eauto. entailer!. 
}

unfold_data_at 1%nat.
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i)).
  { entailer!. } 
rename H into FCO.
replace_SEP 2 `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx]))) ((Vptr b i))).
  { entailer!. rewrite field_at_data_at. unfold nested_field_type2, field_address; simpl.
    rewrite if_true by eauto. entailer!. } 

destruct ST as [MD [iCTX oCTX]]. simpl in *.
forward_call' (Tsh, Tsh, Vptr b i,
               field_address t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i),
              (mkTrep t_struct_SHA256state_st oCTX)) rv.
  { unfold field_address; simpl. rewrite if_true by eauto. entailer!. }
subst rv; simpl. 

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. trivial.

(*Call sha256Update*)
Opaque firstn.
forward_call' (oSha, sha_finish ctx, Vptr b i, buf, Tsh, Z.of_nat SHA256.DigestLength, kv) updSha.
  { unfold sha256state_. normalize. apply (exp_right oCTX). entailer!. }
  { unfold SHA256.DigestLength. 
    rewrite oShaLen. simpl. simpl. split. omega. split. 
    rewrite int_max_unsigned_eq. omega.
    rewrite two_power_pos_equiv; simpl. unfold Z.pow_pos. simpl. omega.
  }
Transparent firstn.
simpl.
rename H into UPDSHA.
rewrite firstn_precise in UPDSHA. 
Focus 2. eapply Zlength_length in SFL. apply SFL. omega.  
unfold sha256state_. normalize. intros updShaST. normalize. rename H into updShaREL. 

(*Call SHA_Final*)
forward_call' (updSha, md, Vptr b i, shmd, kv).
  { unfold sha256state_. normalize. 
    apply (exp_right updShaST). entailer!.
  }
simpl.

forward.
unfold data_at_.
apply (exp_right (sha_finish updSha, HMACabs updSha iSha oSha)).
simpl_stackframe_of. simpl. normalize.
apply andp_right. apply prop_right. split; trivial.
  exists updSha; eauto.
  auto.
cancel.
unfold data_block.
normalize.
apply derives_trans with (Q:= hmacstate_PostFinal (HMACabs updSha iSha oSha)
      (Vptr b i) *
    data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr (sha_finish ctx)))
  (eval_lvar _buf (tarray tuchar 32) rho)).
2: cancel.
rewrite SFL in *. 
rewrite lvar_eval_lvar with (v:=buf); trivial. cancel.
unfold hmacstate_PostFinal, hmac_relate_PostFinal. 
apply (exp_right (updShaST, (iCTX, oCTX))).
simpl. normalize.
unfold_data_at 3%nat.
cancel.
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
rewrite (field_at_data_at _ _ [StructField _md_ctx]); try reflexivity.
unfold nested_field_type2, field_address; simpl. 
do 2 rewrite if_true by eauto. entailer!. 
Qed.
