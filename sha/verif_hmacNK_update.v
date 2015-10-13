Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.
Require Import sublist.

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

assert_PROP (isptr c /\ field_compatible t_struct_hmac_ctx_st [] c). entailer.
destruct H as [isptr_c FC_c].
assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
  { apply prop_right. red in FC_c. red. intuition.
    constructor. trivial. constructor. reflexivity. }
rename H into FC_mdCtx.
unfold data_at. unfold_field_at 1%nat. normalize. rename H into VF_ST.
apply isptrD in isptr_c. destruct isptr_c as [b [i Cptr]]. rewrite Cptr in *.
rewrite field_at_data_at at 1. unfold field_address; normalize.
rewrite if_true by eauto.
forward_call (ctx, data, Vptr b i, d, Tsh, len, kv) s. 
 (*Issue: the forward_call takes ca 50secs in newComCert, instead of 6secs in Master, 
   no matter wther the field_at_data_at stuff s done outside of the call or inside*)
  { (* rewrite field_at_data_at at 1.*)
    unfold sha256state_ (*, field_address*); normalize.
    (*rewrite if_true by eauto.*) Exists (fst ST). entailer!. }
  { intuition. }

rename H into HmacUpdate.
normalize.
rewrite sublist_same in HmacUpdate; trivial.
forward. (*Issue: leaves RHS in less normalized shape than previously*)
Exists (HMACabs s iSha oSha). entailer.
apply andp_right. apply prop_right. exists s; eauto.
cancel. 
unfold hmacstate_, sha256state_, hmac_relate. normalize.
Exists (r, (iCtx ST, oCtx ST)). 
simpl. entailer. 
unfold data_at at 2. unfold_field_at 3%nat. 
destruct ST as [ST1 [ST2 ST3]]. simpl in *. normalize.
apply andp_right. admit. (*TODO: Issue: how to establish value_fits for structs her ? entailer/normalize don't terminmate, andp_right; constructor, don't seem to wotrk either*)
repeat rewrite sepcon_assoc.
apply sepcon_derives. 2: cancel.
rewrite field_at_data_at.
unfold field_address. rewrite if_true by eauto. rewrite offset_val_zero_Vptr.
apply derives_refl.
Qed.