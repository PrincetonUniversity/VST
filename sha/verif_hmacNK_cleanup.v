Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.

Require Import sha.hmac_NK.

Require Import sha.spec_hmacNK.
Require Import sha.hmac_common_lemmas.

Lemma body_hmac_cleanup: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_cleanup HMAC_Cleanup_spec.
Proof.
start_function.
name ctx' _ctx.
unfold hmacstate_PostFinal, hmac_relate_PostFinal. normalize. intros hst. normalize.
assert_PROP (size_compatible t_struct_hmac_ctx_st c /\
        align_compatible t_struct_hmac_ctx_st c).
{ unfold data_at. entailer. } 
destruct H0 as [SC AC].

forward_call' (Tsh, c, sizeof t_struct_hmac_ctx_st, Int.zero) rv.
  { assert (FR: Frame = nil).  
      subst Frame. reflexivity.
    rewrite FR. clear FR Frame.
    entailer.
    eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity.
    entailer.
    assumption. 
  }
forward.
unfold data_block. rewrite Zlength_correct; simpl. entailer. 
apply prop_right.
assert (isByte0:  isbyteZ 0). unfold isbyteZ; omega.
apply (Forall_list_repeat _ _ (Z.to_nat (sizeof t_struct_hmac_ctx_st)) _ isByte0). 
Qed.
