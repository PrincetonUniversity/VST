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
Require Import HMAC_lemmas.

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
erewrite (field_except_at_lemma _ _ _md_ctx nil); try reflexivity.
simpl. 

(*By rewriting with field_at_data_at here instead of inside the forward_call,
  we remember facts SCc and ACc which are necessary for performing the
  "inverse" conversion at the end of this proof*)  
rewrite field_at_data_at; try reflexivity. simpl. normalize. simpl. 
rename H into SCc. rename H0 into ACc.

rewrite <- memory_block_data_at_ ; try reflexivity. normalize.
rename H into ACb.
remember (ctx, b, c, Tsh, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [
      `(field_except_at Tsh t_struct_hmac_ctx_st _md_ctx [] (snd ST) c);
      `(memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. 
    cancel.
    unfold sha256state_. apply exp_right with (x:= mdCtx ST). entailer.
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
  entailer. cancel. 
  erewrite (field_except_at_lemma _ _ _md_ctx nil); try reflexivity. simpl.
  rewrite field_at_data_at; try reflexivity. simpl. normalize.

unfold_data_at 1%nat. (*qinxiang told me about this tactic - we need a list of all tactics!!!*)
rewrite (field_at_data_at _ _ [_o_ctx]); try reflexivity.
rewrite (field_at_data_at _ _ [_md_ctx]); try reflexivity.
normalize. simpl.
rewrite at_offset_data_at. 

eapply semax_pre with (P':=
  (PROP  ()
   LOCAL  (`(eq b) (eval_var _buf (tarray tuchar 32));
   `(eq md) (eval_id _md); `(eq c) (eval_id _ctx);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx])
       (snd (snd ST))
       (offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])) c));
   `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] (fst (snd ST)) c);
   `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [_md_ctx]))) c);
   `(K_vector KV);
   `(data_block Tsh (sha_finish ctx) b);
   `(memory_block shmd (Int.repr 32) md)))).
  entailer. cancel.
  eapply derives_trans. apply data_at_data_at_. reflexivity.
  rewrite <- (memory_block_data_at_ Tsh (nested_field_type2 t_struct_hmac_ctx_st [_md_ctx]) (eq_refl _) (eq_refl _)).
  entailer.

destruct ST as [MD [iCTX oCTX]]. simpl in *.
remember (Tsh, Tsh, c, offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])) c, 
          (mkTrep t_struct_SHA256state_st oCTX)) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [
      `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] iCTX c);
      `(K_vector KV); `(data_block Tsh (sha_finish ctx) b);
      `(memory_block shmd (Int.repr 32) md)]).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. cancel.
  }
after_call. subst WITNESS. normalize. subst retval0. simpl. 

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256' (*, Z2Nat.id*). trivial.
  (*unfold SHA256_DIGEST_LENGTH; omega.*)

(*Call sha256Update*)
(*apply seq_assoc.*)
(*eapply semax_seq'.
frame_SEP 0 5 6.
*)
remember (oSha, sha_finish ctx, c, b, Tsh, Z.of_nat SHA256.DigestLength, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [
       `(data_at Tsh t_struct_SHA256state_st oCTX
           (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])) c));
       `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] iCTX c);
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
  (PROP  ()
   LOCAL  (`(eq b) (eval_var _buf (tarray tuchar 32));
   `(eq md) (eval_id _md); `(eq c) (eval_id _ctx);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP  (update_abs (firstn SHA256.DigestLength SF) oSha x)
       LOCAL ()
       SEP  (`(K_vector KV); `(sha256state_ x c); `(data_block Tsh SF b))) a)
      globals_only;
   `(data_at Tsh t_struct_SHA256state_st oCTX
       (offset_val
          (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])) c));
   `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] iCTX c);
   `(memory_block shmd (Int.repr 32) md)))).
   entailer. rename x into a. apply exp_right with (x:=a).
     entailer.
  normalize.
  apply extract_exists_pre. intros updSha. normalize.
  rewrite firstn_precise. 
  Focus 2. unfold  SHA256.DigestLength. simpl. subst SF. 
        unfold sha_finish. destruct ctx.
        rewrite <- functional_prog.SHA_256'_eq,length_SHA256'. trivial.
  simpl.
  unfold sha256state_. normalize. intros updShaST. normalize.
  
remember (updSha, md, c, shmd, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame = [ `(data_block Tsh SF b);
      `(data_at Tsh t_struct_SHA256state_st oCTX
         (offset_val (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])) c));
      `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] iCTX c)]).
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
erewrite (data_at__array_at_ Tsh tuchar 32 noattr). cancel.
  2: omega. 2: reflexivity. 
unfold hmacstate_PostFinal, hmac_relate_PostFinal.
apply exp_right with (x:=(updShaST, (iCTX, oCTX))).
simpl. normalize.
(*apply andp_right.
  apply prop_right. exists l; auto.*)
unfold_data_at 3%nat.
cancel.
rewrite (field_at_data_at _ _ [_o_ctx]); try reflexivity.
rewrite (field_at_data_at _ _ [_md_ctx]); try reflexivity.
entailer.
Qed.