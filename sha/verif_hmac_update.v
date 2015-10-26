Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.

Require Import sha.hmac091c.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmac.

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
destruct H0 as [reprMD [reprI [reprO [iShaLen [oShaLen [KeyST [l [KeylenST [KL ZLen]]]]]]]]].
rewrite KL in *.
(*erewrite (field_except_at_lemma _ _ [StructField _md_ctx] nil); try reflexivity.*)
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

forward_call' (ctx, data, c, d, Tsh, len, kv) s.
  { unfold sha256state_. normalize. apply (exp_right (mdCtx ST)). 
    assert (FR: Frame = (field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
           (fst (snd (snd (snd ST)))) c) ::
        (field_at Tsh t_struct_hmac_ctx_st [StructField _key]
           (snd (snd (snd (snd ST)))) c) ::
        (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] (fst (snd (snd ST))) c) ::
        (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd ST)) c) :: nil).
       subst Frame. reflexivity.
    rewrite FR; clear FR Frame. entailer. cancel. 
  }
  { intuition. }
(*(*TODO: make sure the following pattern also works instead of the forward_call' above*)
eapply semax_seq'.
myframe_SEP'' [4; 5; 6].
apply semax_seq_skip.
forward_call' (ctx, data, c, d, Tsh, len, kv) s.
  { assert (FR: Frame =nil).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    entailer. unfold sha256state_.
    apply (exp_right (mdCtx ST)). entailer.
  }
  { intuition. }
  { (*of course we'd like to discharge this by entailer. But this fails.
     To see why, let's do it by hand:*)
    apply andp_derives. apply derives_refl.
    apply andp_derives. apply derives_refl.
    apply derives_refl. (*Ah, we want to instantiate with sth that mentions s, the 
       name we introduced in forward_call'. But the ? was introduced by the
       semax_seq' three lines earlier, so may not depend on s! So the pattern
       semax_seq'; myframeSEP; semax_seq_skip; forward_call'
       is  not quite right. *)}*)

rename H into HmacUpdate.
normalize. simpl. 
assert (FF: firstn (Z.to_nat len) data = data). 
    rewrite DL1 in *. 
    apply firstn_same. rewrite Zlength_correct, Nat2Z.id. omega.
rewrite FF in *. 

forward.
apply (exp_right (HMACabs s iSha oSha (Int.unsigned l) key)). entailer.
apply andp_right. apply prop_right. exists s; eauto.
unfold hmacstate_, sha256state_, hmac_relate. normalize.
apply (exp_right (r, (iCtx ST, (oCtx ST, (Vint l, Key ST))))). 
simpl. entailer.
apply andp_right. apply prop_right. exists l; eauto.

unfold_data_at 2%nat.
destruct ST as [ST1 [ST2 [ST3 [ST4 ST5]]]]. simpl in *. subst ST4. cancel.
rewrite field_at_data_at. 
    unfold nested_field_type2, field_address; simpl.
    rewrite <- Heqs. entailer. 
