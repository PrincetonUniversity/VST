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
assert_PROP (field_compatible t_struct_hmac_ctx_st [] c). entailer.
forward_call (Tsh, c, sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st, Int.zero) rv.
  { eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity. cancel.
    trivial. }
subst rv.
forward.
unfold data_block. rewrite Zlength_correct; simpl.
apply andp_right.
  apply prop_right. 
  assert (isByte0:  isbyteZ 0). unfold isbyteZ; omega.
  apply (Forall_list_repeat _ (Z.to_nat (sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st)) _ isByte0). 
cancel.
Qed.

(*Here's the proof for the alternative specification:*)
Lemma body_hmac_cleanup1: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_cleanup HMAC_Cleanup_spec1.
Proof.
start_function.
name ctx' _ctx.
unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
normalize. intros key.
unfold hmacstate_PreInitNull, hmac_relate_PreInitNull. normalize. intros hst. normalize.
intros X; normalize.
assert_PROP (field_compatible t_struct_hmac_ctx_st [] c). entailer.
forward_call (Tsh, c, sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st, Int.zero) rv.
  { eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity. cancel.
    trivial. }
subst rv.
forward.
unfold data_block. rewrite Zlength_correct; simpl.
apply andp_right.
  apply prop_right. 
  assert (isByte0:  isbyteZ 0). unfold isbyteZ; omega.
  apply (Forall_list_repeat _ (Z.to_nat (sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st)) _ isByte0). 
cancel.
Qed.
