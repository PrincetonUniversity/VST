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
Require Import sha.spec_hmacADT.
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
assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _md_ctx] c)).
{ entailer!. }
apply isptrD in H; destruct H as [cb [coff COff]]. rewrite COff in *.
unfold field_address in COff.
remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
             c) as s.
destruct s; simpl in *; inversion COff. simpl in *. rewrite COff. clear H0.

unfold nested_field_offset2, offset_val in COff. simpl in  COff. 
destruct c; inversion COff; clear COff. rewrite Int.add_zero in H1. subst cb coff.

rewrite <- memory_block_data_at_ ; try reflexivity.
Focus 2. red. destruct buf; trivial. simpl. apply Z.divide_1_l.

(*Call Sha_Final*)
forward_call' (ctx, buf, Vptr b i, Tsh, kv).
  { assert (FR: Frame = [
     (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
       (snd (snd ST))  (Vptr b i));
     (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd ST)) (Vptr b i));
       (memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    entailer!. cancel.
    unfold sha256state_. apply (exp_right (mdCtx ST)). entailer!.
  }
normalize. simpl.

eapply semax_pre with (P':=(PROP  ()
   LOCAL (lvar _buf (tarray tuchar 32) buf; temp _md md;
   temp _ctx (Vptr b i); gvar sha._K256 kv)
   SEP  (`(K_vector kv); 
   `(data_at Tsh t_struct_hmac_ctx_st (default_val sha.t_struct_SHA256state_st, snd ST) (Vptr b i));
   `(data_block Tsh (sha_finish ctx) buf);
   `(memory_block shmd (Int.repr 32) md)))).
{ entailer!. 
      unfold_data_at 1%nat. simpl. cancel. unfold data_at_.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      unfold nested_field_type2, nested_field_offset2, field_address; simpl. rewrite <- Heqs. simpl. entailer!.
}

unfold_data_at 1%nat.
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i))).
  entailer!.
apply isptrD in H; destruct H as [? [? OCTX]]; rewrite OCTX.
unfold field_address in OCTX.
destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i));
   inversion OCTX; clear OCTX. 
subst x x0.
rename f0 into FCO.
rewrite (field_at_data_at _ _ [StructField _md_ctx]); try reflexivity.
unfold field_address. simpl. rewrite <- Heqs.
unfold nested_field_type2; simpl.
unfold nested_field_offset2; simpl. 

replace_SEP 2 `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx]))) ((Vptr b i))).
  { entailer!. 
    eapply derives_trans. apply data_at_data_at_.
    rewrite <- (memory_block_data_at_ Tsh (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])).
    unfold nested_field_type2; simpl. cancel.
    reflexivity. reflexivity. reflexivity.
    unfold nested_field_offset2; simpl. apply f. 
    unfold nested_field_offset2; simpl. rewrite <- initialize.max_unsigned_modulus.
       rewrite int_max_unsigned_eq. omega. 
  }

destruct ST as [MD [iCTX oCTX]]. simpl in *.
forward_call' (Tsh, Tsh, Vptr b i, offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b i), 
          (mkTrep t_struct_SHA256state_st oCTX)) rv.
subst rv; simpl. 

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. trivial.

(*Call sha256Update*)
Opaque firstn.
forward_call' (oSha, sha_finish ctx, Vptr b i, buf, Tsh, Z.of_nat SHA256.DigestLength, kv) updSha.
  { assert (FR: Frame = [
       (data_at Tsh t_struct_SHA256state_st oCTX
           (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b i)));
       (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b i));
       (memory_block shmd (Int.repr 32) md)]).
       subst Frame; reflexivity.
    rewrite FR; clear FR Frame. 
    entailer!. cancel.
    unfold sha256state_. apply (exp_right oCTX).
    entailer!.
  }
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
  { assert (FR: Frame = [ (data_block Tsh (sha_finish ctx) buf);
      (data_at Tsh t_struct_SHA256state_st oCTX
         (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b i)));
      (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b i))]).
       subst Frame; reflexivity.
    rewrite FR; clear FR Frame. 
    entailer!. 
    cancel.
    unfold sha256state_. 
    apply (exp_right updShaST). entailer!.
  }
simpl.

forward.
unfold data_at_. 
apply (exp_right (sha_finish updSha, HMACabs updSha iSha oSha)).
simpl_stackframe_of. unfold data_block.
simpl; normalize.
apply andp_right. apply prop_right.
  split; eauto.
cancel.
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
entailer!. unfold nested_field_type2; simpl.
unfold field_address. rewrite <- Heqs.
destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
            (Vptr b i)); try contradiction.
unfold nested_field_offset2; simpl. rewrite Int.add_zero. entailer!.
Qed.