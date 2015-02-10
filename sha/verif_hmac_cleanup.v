Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.

Require Import sha.hmac091c.

Require Import sha.spec_hmac.
Require Import sha.hmac_common_lemmas.

Lemma body_hmac_cleanup: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_cleanup HMAC_Cleanup_spec.
Proof.
start_function.
name ctx' _ctx.
unfold hmacstate_PostFinal, hmac_relate_PostFinal. normalize. intros hst. normalize. 
apply semax_pre with (P':=
  PROP (size_compatible t_struct_hmac_ctx_st c /\
        align_compatible t_struct_hmac_ctx_st c)
   LOCAL  (`(eq c) (eval_id _ctx))
   SEP 
   (`(data_at Tsh t_struct_hmac_ctx_st
        (upd_reptype t_struct_hmac_ctx_st [StructField _md_ctx] hst
           (default_val t_struct_SHA256state_st)) c))).
  entailer. unfold data_at. simpl. normalize.
normalize.

forward_call (Tsh, c, sizeof t_struct_hmac_ctx_st, Int.zero).
  { assert (FR: Frame = nil).  
      subst Frame. reflexivity.
    rewrite FR. clear FR Frame.
    entailer.
    eapply derives_trans. apply data_at_data_at_.
       (*reflexivity.*)
    rewrite <- memory_block_data_at_; try reflexivity.
    entailer. 
    assumption.
  }
after_call. subst retval0.
forward.
assert (isByte0:  isbyteZ 0). unfold isbyteZ. omega.
specialize (isbyte_list_repeat 0 (Z.to_nat (sizeof t_struct_hmac_ctx_st)) isByte0). 
unfold data_block. rewrite Zlength_correct; simpl. intros.
entailer. 
Qed.