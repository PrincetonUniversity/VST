Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_NK.
Require Import sha.spec_hmacNK.
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
simpl_stackframe_of. normalize. rename H into WrshMD. 
eapply semax_pre with (P':=PROP  ()
   LOCAL  (`(eq md) (eval_id _md); `(eq c) (eval_id _ctx);
     `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   ((EX b:_, local (`(eq b) (eval_var _buf (tarray tuchar 32)))
             && `(data_at_ Tsh (tarray tuchar 32) b));
   `(hmacstate_ h1 c); `(K_vector KV); `(memory_block shmd (Int.repr 32) md))).
  entailer. apply exp_right with (x:=eval_var _buf (tarray tuchar 32) rho).
  entailer.
normalize. intros b. normalize.
rewrite memory_block_isptr. unfold hmacstate_. normalize.
rename H into isptrMD.
intros ST. normalize.
destruct h1; simpl in *.
destruct H as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
(*rewrite KL in *.*)

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
rewrite data_at_isptr. normalize. 
apply isptrD in H. destruct H as [cb [coff COff]]. rewrite COff in *.
unfold field_address in COff.
remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
             c) as s.
destruct s; simpl in *; inversion COff. simpl in *. rewrite COff. clear H0.

rewrite <- memory_block_data_at_ ; try reflexivity.
(*XXX: rename H into ACb.*)

remember (ctx, b, c, Tsh, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
       (snd (snd ST)) c);
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd ST)) c);
      `(memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. 
    cancel.
    unfold sha256state_. apply exp_right with (x:= mdCtx ST). entailer.
    unfold offset_val in COff. destruct ctx'; inversion COff; clear COff. subst cb coff.
    simpl. unfold nested_field_offset2, nested_field_type2. simpl. rewrite Int.add_zero. cancel.
  }
after_call. subst WITNESS. normalize. simpl. 

eapply semax_pre with (P':=(PROP  ()
   LOCAL  (`(eq b) (eval_var _buf (tarray tuchar 32));
   `(eq md) (eval_id _md); `(eq c) (eval_id _ctx);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))

   SEP  (`(K_vector KV); 
   `(data_at Tsh t_struct_hmac_ctx_st (default_val sha.t_struct_SHA256state_st, snd ST) c);
   `(data_block Tsh (sha_finish ctx) b);
   `(memory_block shmd (Int.repr 32) md)))).
{ entailer. cancel. 
      unfold_data_at 1%nat. simpl. cancel. unfold data_at_. 
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      unfold nested_field_type2; simpl. unfold field_address. rewrite COff.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx] ctx'); try contradiction.
      unfold offset_val in COff. destruct ctx'; inversion COff. subst cb coff. clear f0 COff Heqs.
      unfold nested_field_offset2; simpl. rewrite Int.add_zero. entailer. 
}

unfold_data_at 1%nat. (*qinxiang told me about this tactic - we need a list of all tactics!!!*)
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
(*new: extract info from field_address as early as possible*)
  rewrite data_at_isptr. normalize.
  apply isptrD in H; destruct H as [? [? OCTX]]; rewrite OCTX.
      unfold field_address in OCTX.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx] c); inversion OCTX. 
      clear H0.
      rename f0 into FCO.
rewrite (field_at_data_at _ _ [StructField _md_ctx]); try reflexivity.
(*new: extract info from field_address as early as possible*)
  rewrite data_at_isptr with (p:=  (field_address t_struct_hmac_ctx_st [StructField _md_ctx] c)). normalize.
  apply isptrD in H; destruct H as [? [? MDCTX]]; rewrite MDCTX.
      unfold field_address in MDCTX.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx] c); inversion MDCTX. 
      clear H0. rewrite COff in MDCTX. apply eq_sym in MDCTX. inversion MDCTX. subst x1 x2; clear f0 Heqs MDCTX.

rewrite OCTX, COff. unfold nested_field_type2; simpl.
(*normalize. simpl.
rewrite at_offset_data_at. *)
    unfold offset_val in COff. destruct c; inversion COff. clear COff. subst cb coff.
    unfold offset_val in OCTX. inversion OCTX. clear OCTX. subst x x0.
unfold nested_field_offset2; simpl.

eapply semax_pre with (P':=
  (PROP  ()
   LOCAL  (`(eq b) (eval_var _buf (tarray tuchar 32));
   `(eq md) (eval_id _md); `(eq (Vptr b0 i)) (eval_id _ctx);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at Tsh
       (Tstruct _struct_SHA256state_st
          (Fcons _h (tarray tuint 8)
             (Fcons _Nl tuint
                (Fcons _Nh tuint
                   (Fcons _data (tarray tuchar 64) (Fcons _num tuint Fnil)))))
          noattr) (snd (snd ST)) (Vptr b0 (Int.add i (Int.repr 216))));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd ST)) (Vptr b0 i));
   `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx]))) ((Vptr b0 i)));
   `(K_vector KV); `(data_block Tsh (sha_finish ctx) b);
   `(memory_block shmd (Int.repr 32) md)))).
  { entailer. cancel.
    eapply derives_trans. apply data_at_data_at_.
    rewrite <- (memory_block_data_at_ Tsh (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])).
    unfold nested_field_type2; simpl. cancel.
    reflexivity. reflexivity. reflexivity.
    unfold nested_field_offset2; simpl. apply f. 
    unfold nested_field_offset2; simpl. rewrite <- initialize.max_unsigned_modulus.
       rewrite int_max_unsigned_eq. omega. 
  }

destruct ST as [MD [iCTX oCTX]]. simpl in *.
remember (Tsh, Tsh, Vptr b0 i, offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i), 
          (mkTrep t_struct_SHA256state_st oCTX)) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [
      `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b0 i));
      `(K_vector KV); `(data_block Tsh (sha_finish ctx) b);
      `(memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. cancel.
  }
after_call. subst WITNESS. normalize. subst retval0. simpl. 

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. trivial.

(*Call sha256Update*)
(*apply seq_assoc.*)
(*eapply semax_seq'.
frame_SEP 0 5 6.
*)
remember (oSha, sha_finish ctx, Vptr b0 i, b, Tsh, Z.of_nat SHA256.DigestLength, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [
       `(data_at Tsh t_struct_SHA256state_st oCTX
           (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i)));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b0 i));
       `(memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. 
    apply andp_right. (*rewrite SFL.*) unfold SHA256.DigestLength. entailer.
     rewrite oShaLen. simpl. entailer.
    cancel.
    unfold sha256state_. apply exp_right with (x:=oCTX).
    entailer.
  }
after_call. subst WITNESS. normalize. remember (sha_finish ctx) as SF. 
apply semax_pre with (P':=EX  x : s256abs,
  (PROP  (update_abs (firstn SHA256.DigestLength SF) oSha x)
   LOCAL  (`(eq b) (eval_var _buf (tarray tuchar 32));
   `(eq md) (eval_id _md); `(eq (Vptr b0 i)) (eval_id _ctx);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(K_vector KV); `(sha256state_ x (Vptr b0 i)); `(data_block Tsh SF b);
   `(data_at Tsh t_struct_SHA256state_st oCTX
       (offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i)));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b0 i));
   `(memory_block shmd (Int.repr 32) md)))).
  { entailer. apply (exp_right x). entailer. }
  normalize.
  apply extract_exists_pre. intros updSha. 
  rewrite firstn_precise. 
  Focus 2. unfold  SHA256.DigestLength. simpl. subst SF. 
        unfold sha_finish. destruct ctx.
        rewrite <- functional_prog.SHA_256'_eq,length_SHA256'. trivial.
  unfold sha256state_. normalize. intros updShaST. normalize. rename H into UPDSHA; rename H0 into updShaREL.
  
remember (updSha, md, Vptr b0 i, shmd, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [ `(data_block Tsh SF b);
      `(data_at Tsh t_struct_SHA256state_st oCTX
         (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])) (Vptr b0 i)));
      `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iCTX (Vptr b0 i))]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. 
    cancel.
    unfold sha256state_. 
    apply exp_right with (x:=updShaST). entailer.
  }
after_call. subst WITNESS. normalize. simpl.

forward.
unfold data_at_.
apply exp_right with (x:=sha_finish updSha).
simpl_stackframe_of. simpl. normalize.
apply exp_right with (x:=HMACabs updSha iSha oSha).
unfold data_block.
normalize.
apply andp_right. apply prop_right. split; trivial.
  exists updSha; eauto.
cancel. 
rewrite SFL in *.
apply derives_trans with (Q:= hmacstate_PostFinal (HMACabs updSha iSha oSha)
      (Vptr b0 i) *
    data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr (sha_finish ctx)))
  (eval_var _buf (tarray tuchar 32) rho)).
Focus 2. cancel. 
cancel.  
unfold hmacstate_PostFinal, hmac_relate_PostFinal.
apply (exp_right (updShaST, (iCTX, oCTX))).
simpl. normalize.
unfold_data_at 3%nat.
cancel.
rewrite (field_at_data_at _ _ [StructField _o_ctx]); try reflexivity.
rewrite (field_at_data_at _ _ [StructField _md_ctx]); try reflexivity.
entailer. unfold nested_field_type2; simpl.
unfold field_address.
destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
            (Vptr b0 i)); try contradiction. 
destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
            (Vptr b0 i)); try contradiction.
unfold nested_field_offset2; simpl. rewrite Int.add_zero. entailer.

red.  destruct b; trivial. simpl. apply Z.divide_1_l.
Qed.
