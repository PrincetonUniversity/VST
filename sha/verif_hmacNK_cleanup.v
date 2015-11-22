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
unfold hmacstate_PostFinal, hmac_relate_PostFinal.
Intros hst.
Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] c) as FCc by entailer!. (*8.7*)
forward_call (Tsh, c, sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st, Int.zero).
  { eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity. cancel.
    trivial. }
Intros rv; subst rv.
subst POSTCONDITION; unfold abbreviate.
pose proof (sizeof_pos cenv_cs t_struct_hmac_ctx_st).
forget (sizeof cenv_cs t_struct_hmac_ctx_st) as NN.
forward.
unfold data_block. simpl. rewrite Zlength_list_repeat by omega.
rewrite !map_list_repeat.
 entailer!.
apply Forall_list_repeat; hnf; clear; omega.
Qed.

(*Here's the proof for the alternative specification:*)
Lemma body_hmac_cleanup1: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_cleanup HMAC_Cleanup_spec1.
Proof.
start_function.
name ctx' _ctx.
unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
Intros key.
unfold hmacstate_PreInitNull, hmac_relate_PreInitNull.
Intros hst X.
Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] c) as FCc by entailer!. (*8.9*)
forward_call (Tsh, c, sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st, Int.zero).
  { eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity. cancel.
    trivial. }
Intros rv; subst rv.
subst POSTCONDITION; unfold abbreviate.
pose proof (sizeof_pos cenv_cs t_struct_hmac_ctx_st).
forget (sizeof cenv_cs t_struct_hmac_ctx_st) as NN.
forward.
unfold data_block. simpl. rewrite Zlength_list_repeat by omega.
rewrite !map_list_repeat.
 entailer!.
apply Forall_list_repeat; hnf; clear; omega.
Qed.
