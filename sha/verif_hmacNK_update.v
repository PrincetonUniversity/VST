Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac_NK.
Require Import sha.spec_hmacNK.

Lemma body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Update HMAC_Update_spec.
Proof.
start_function.
name ctx' _ctx.
name data' _data.
name len' _len.
unfold hmacstate_. normalize. intros ST. normalize.
destruct H as [DL1 [DL2 DL3]].
destruct h1; simpl in *.
destruct H0 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
(*rewrite KL in *.*)
(*erewrite (field_except_at_lemma _ _ _md_ctx nil); try reflexivity.*)
simpl. 

(*By rewriting with field_at_data_at here instead of inside the forward_call,
  we remember facts SCc and ACc which are necessary for performing the
  "inverse" conversion at the end of this proof*)  
(*Before Qinxiang's updgrate to nested structures, we could do this (cf svn directoory):
rewrite field_at_data_at; try reflexivity. simpl. normalize. 
rename H into SCc. rename H0 into ACc.
*)
(*Instead, now we need to do the following 8 lines to achieve roughly the same:*)
unfold_data_at 1%nat.
rewrite field_at_data_at with (gfs:=[StructField _md_ctx]).
rewrite data_at_isptr. normalize. 
apply isptrD in H. destruct H as [b [off BOff]]. rewrite BOff in *.
unfold field_address in BOff.
remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
             c) as s.
destruct s; simpl in *; inversion BOff. simpl in *. clear BOff.

eapply semax_seq'. 
myframe_SEP'' [2; 3; 4].
remember (ctx, data, c, d, Tsh, len, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame =nil).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer.
    cancel. 
    unfold sha256state_. apply exp_right with (x:= mdCtx ST). entailer.
    (*rewrite field_at_data_at; try reflexivity. simpl. entailer.*)
  }
after_call. subst WITNESS. normalize. simpl. (* normalize.*)

assert (FF: firstn (Z.to_nat len) data = data). 
    rewrite DL1 in *. 
    apply firstn_same. rewrite Zlength_correct, Nat2Z.id. omega.
rewrite FF in *. 

(**** Again, distribute EX over lift*)
apply semax_pre with (P' :=EX  x : s256abs,
  (PROP  (update_abs data ctx x)
   LOCAL  (tc_environ Delta; `(eq c) (eval_id _ctx); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr len))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(K_vector KV); `(sha256state_ x c); `(data_block Tsh data d);
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd ST)) c);
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] (snd (snd ST)) c)))).
  entailer. apply (exp_right x). entailer.
apply extract_exists_pre. intros s. normalize.
(********************************************************)
rename H into HmacUpdate.

(*WHY IS THIS NEEDED?*) unfold MORE_COMMANDS, abbreviate.
forward.
apply (exp_right (HMACabs s iSha oSha)). entailer.
apply andp_right. apply prop_right. exists s; eauto.
cancel. 
unfold hmacstate_, sha256state_, hmac_relate. normalize.
apply (exp_right (r, (iCtx ST, oCtx ST))). 
simpl. entailer.
(*apply andp_right. apply prop_right. exists l; eauto.*)

unfold_data_at 2%nat.
destruct ST as [ST1 [ST2 ST3]]. simpl in *. cancel.
rewrite field_at_data_at. 
    unfold nested_field_type2, field_address; simpl.
    rewrite <- Heqs. entailer. 
Qed.