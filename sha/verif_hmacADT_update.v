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
Require Import sha.spec_hmacADT.

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
assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
  { entailer!. } 
rename H into FC.
make_Vptr c. 

forward_call' (ctx, data, Vptr b i, d, Tsh, len, kv) s.
  { unfold sha256state_, field_address; normalize.
    rewrite if_true by eauto. apply (exp_right (mdCtx ST)). entailer!. }
  { intuition. }

rename H into HmacUpdate.
normalize. simpl. 
assert (FF: firstn (Z.to_nat len) data = data). 
    rewrite DL1 in *. 
    apply firstn_same. rewrite Zlength_correct, Nat2Z.id. omega.
rewrite FF in *. 

forward.
apply (exp_right (HMACabs s iSha oSha)). entailer!.
  exists s; eauto.
cancel. 
unfold hmacstate_, sha256state_, hmac_relate. normalize.
apply (exp_right (r, (iCtx ST, oCtx ST))). 
simpl. entailer!.
(*apply andp_right. apply prop_right. exists l; eauto.*)
unfold_data_at 2%nat.
destruct ST as [ST1 [ST2 ST3]]. simpl in *. cancel.
rewrite field_at_data_at. 
unfold nested_field_type2, field_address; simpl.
rewrite if_true by eauto. entailer!.
Qed.