Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac091c.
Require Import sha.spec_hmac.
Require Import sha.vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Lemma withspacer_refl: forall sh a P, withspacer sh a a P = P.
Proof. intros. unfold withspacer. 
  rewrite <- Zminus_diag_reverse. trivial.
Qed.

Lemma body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Final HMAC_Final_spec.
Proof.
start_function.
name ctx' _ctx.
name md' _md.
simpl_stackframe_of. fixup_local_var; intro b.

rename H into WrshMD. 
rewrite memory_block_isptr. unfold hmacstate_. normalize.
rename H into isptrMD.
intros ST. normalize.
destruct h1; simpl in *.
destruct H as [reprMD [reprI [reprO [iShaLen [oShaLen [KeyST [l [KeylenST [KL ZLen]]]]]]]]].
rewrite KL in *.

(*erewrite (field_except_at_lemma _ _ _md_ctx nil); try reflexivity.*)
(*By rewriting with field_at_data_at here instead of inside the forward_call,
  we remember facts SCc and ACc which are necessary for performing the
  "inverse" conversion at the end of this proof*)  
(*XXX: Before Qinxiang's updgrate to nested structures, we could do this:
  rewrite field_at_data_at; try reflexivity. simpl. normalize. simpl. 
  rename H into SCc. rename H0 into ACc.*)
unfold_data_at 1%nat.
rewrite field_at_data_at with (gfs:=[StructField _md_ctx]).
simpl. 
rewrite data_at_isptr. normalize. rename H into isPtr_mdCtxt_c. 
apply isptrD in isPtr_mdCtxt_c. destruct isPtr_mdCtxt_c as [cb [coff COff]]. rewrite COff in *.
unfold field_address in COff.
remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
             c) as s.
destruct s; simpl in *; inversion COff. simpl in *. rewrite COff. clear H0.

unfold nested_field_offset2, offset_val in COff. simpl in  COff. 
destruct c; inversion COff; clear COff. rewrite Int.add_zero in H1. subst cb coff.

rewrite <- memory_block_data_at_ ; try reflexivity.
Focus 2. red. destruct b; trivial. simpl. apply Z.divide_1_l.

(*XXX: rename H into ACb.*)
forward_call' (ctx, b, Vptr b0 i, Tsh, kv).
  { assert (FR: Frame = [(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
        (fst (snd (snd (snd ST)))) (Vptr b0 i));
   (field_at Tsh t_struct_hmac_ctx_st [StructField _key]
       (snd (snd (snd (snd ST))))  (Vptr b0 i));
   (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
       (fst (snd (snd ST))) (Vptr b0 i));
   (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd ST)) (Vptr b0 i));
   (memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR; clear FR Frame. 
    entailer. 
    cancel.
    unfold sha256state_. entailer. apply exp_right with (x:= mdCtx ST). entailer. 
  }
normalize. simpl. 

eapply semax_pre with (P':=(PROP  ()
   LOCAL  (lvar _buf (tarray tuchar 32) b; temp _md md;
   temp _ctx (Vptr b0 i); gvar sha._K256 kv)
   SEP  (`(K_vector kv); 
   `(data_at Tsh t_struct_hmac_ctx_st (default_val sha.t_struct_SHA256state_st, snd ST) (Vptr b0 i));
   `(data_block Tsh (sha_finish ctx) b);
   `(memory_block shmd (Int.repr 32) md)))).
{ entailer. 
      unfold_data_at 1%nat. simpl. cancel. unfold data_at_.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      unfold nested_field_type2, nested_field_offset2, field_address; simpl. rewrite <- Heqs. simpl. entailer.
}

unfold_data_at 1%nat.
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
(*new: extract info from field_address as early as possible*)
assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b0 i))).
  entailer.
apply isptrD in H; destruct H as [? [? OCTX]]; rewrite OCTX.
      unfold field_address in OCTX.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b0 i)); inversion OCTX. 
      subst x x0. 
      rename f0 into FCO.
rewrite (field_at_data_at _ _ [StructField _md_ctx]); try reflexivity.
unfold field_address. rewrite <- Heqs.
unfold nested_field_type2; simpl.
unfold nested_field_offset2; simpl. clear OCTX.

replace_SEP 4 `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx]))) ((Vptr b0 i))).
   entailer!.

destruct ST as [MD [iCTX [oCTX [KEYLENST KEYST]]]]. simpl in *.
forward_call' (Tsh, Tsh, Vptr b0 i, offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i), 
          (mkTrep t_struct_SHA256state_st oCTX)) rv.
subst rv; simpl.

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. trivial.

(*Call sha256Update*)
Opaque firstn.
forward_call' (oSha, sha_finish ctx, Vptr b0 i, b, Tsh, Z.of_nat SHA256.DigestLength, kv) updSha. 
  { assert (FR: Frame = [
       (data_at Tsh t_struct_SHA256state_st oCTX
           (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i)));
       (field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] KEYLENST (Vptr b0 i));
       (field_at Tsh t_struct_hmac_ctx_st [StructField _key] KEYST (Vptr b0 i));
       (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b0 i));
       (memory_block shmd (Int.repr 32) md)]).
       subst Frame; reflexivity.
    rewrite FR; clear FR Frame. 
    entailer. cancel.
    unfold sha256state_. apply (exp_right oCTX).
    entailer.
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
forward_call'  (updSha, md, Vptr b0 i, shmd, kv). (*TODO: This line now takes > 5mins. In the corresponding place in verif_hmacNK_final, it takes about 30secs*)
  { assert (FR: Frame = [ (data_block Tsh (sha_finish ctx) b);
      (data_at Tsh t_struct_SHA256state_st oCTX
         (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i)));
      (field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] KEYLENST (Vptr b0 i));
      (field_at Tsh t_struct_hmac_ctx_st [StructField _key] KEYST (Vptr b0 i));
      (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b0 i))]).
       subst Frame; reflexivity.
    rewrite FR; clear FR Frame. 
    entailer. 
    cancel.
    unfold sha256state_. 
    apply (exp_right updShaST). entailer.
  }
simpl.

forward.
unfold data_at_. 
apply (exp_right (sha_finish updSha, HMACabs updSha iSha oSha (Int.unsigned l) key)).
simpl_stackframe_of. simpl. normalize.
apply andp_right. apply prop_right. split; trivial.
  exists updSha; eauto.
  auto.
cancel. (*TODO: this cancel now takes > 5mins. Again in verif_hmacNK_final it's much faster*)
unfold data_block.
normalize.
apply derives_trans with (Q:= hmacstate_PostFinal (HMACabs updSha iSha oSha (Int.unsigned l) key)
      (Vptr b0 i) *
    data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr (sha_finish ctx)))
  (eval_lvar _buf (tarray tuchar 32) rho)).
2: cancel.
rewrite SFL in *.  
rewrite lvar_eval_lvar with (v:=b); trivial. cancel.   
unfold hmacstate_PostFinal, hmac_relate_PostFinal. entailer.
apply exp_right with (x:=(updShaST, 
                         (iCTX, (oCTX, (Vint l,map Vint (map Int.repr (HMAC_SHA256.mkKey key))))))).
simpl. normalize.
apply andp_right. apply prop_right. exists l; auto.
unfold_data_at 3%nat.
cancel.
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
rewrite (field_at_data_at _ _ [StructField _md_ctx]); try reflexivity.
entailer. unfold nested_field_type2; simpl.
unfold field_address. rewrite <- Heqs.
destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
            (Vptr b0 i)); try contradiction.
unfold nested_field_offset2; simpl. rewrite Int.add_zero. entailer.
Qed.