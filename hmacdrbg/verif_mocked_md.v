Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.floyd.sublist.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import VST.floyd.library.

Lemma body_md_free: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_free md_free_spec.
Proof.
  start_function. rewrite data_at_isptr. Intros.
  unfold_data_at 1%nat. destruct r as [r1 [r2 r3]]. simpl.
  rewrite EMPTY_isptr. Intros. 
  forward. 
freeze [0;1;2] FR1.
 forward_call (Tstruct _hmac_ctx_st noattr, r3).
{ rewrite sepcon_comm. apply sepcon_derives.
  eapply derives_trans. apply UNDER_SPEC.EmptyDissolve.
  fix_hmacdrbg_compspecs.
  apply derives_refl.
  cancel.
}
forward. thaw FR1. 
  unfold_data_at 1%nat. cancel.
Qed.

Lemma body_md_get_size: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_get_size md_get_size_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_md_start: semax_body HmacDrbgVarSpecs (HmacDrbgFunSpecs)
       f_mbedtls_md_hmac_starts md_starts_spec.
Proof.
  start_function.

  destruct r as [r1 [r2 r3]]. simpl.
  rewrite EMPTY_isptr; Intros.
  unfold_data_at 1%nat.
  forward.
  forward_call (@inr (val * Z * list Z * globals) _ (r3, l, key, b, i, gv)).
  { unfold spec_sha.data_block. normalize. cancel. }
  forward.
  cancel. unfold md_relate; simpl. cancel.
  unfold spec_sha.data_block; normalize. cancel.
  unfold_data_at 1%nat. cancel.
Qed.

Lemma body_md_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_update md_update_spec.
Proof.
  start_function.

  unfold md_relate(*; unfold convert_abs*).
  destruct r as [r1 [r2 internal_r]].
  simpl.
  rewrite REP_isptr; Intros.

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.

  (* HMAC_Update(hmac_ctx, input, ilen); *)
  rewrite data_at_isptr with (p:=d); Intros.
  destruct d; try contradiction.

  forward_call (key, internal_r, Vptr b i, data, data1, gv).
  {
    unfold spec_sha.data_block.
    entailer!. 
    change_compspecs hmac_drbg_compspecs.CompSpecs.  (* TODO: This should not be necessary *)
    entailer!.
  }

  (* return 0 *)
  forward.

  (* prove the post condition *)
  unfold spec_sha.data_block.
  unfold md_relate (*; unfold convert_abs*).
  change_compspecs hmac_drbg_compspecs.CompSpecs.  (* TODO: This should not be necessary *)
  entailer!.
Qed.

Lemma body_md_final: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_finish md_final_spec.
Proof.
  start_function.

  unfold md_relate(*; unfold convert_abs*).
  destruct r as [r1 [r2 internal_r]].
  simpl.
  rewrite REP_isptr; Intros.

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.

  (* HMAC_Final(hmac_ctx, output); *)
  forward_call (data, key, internal_r, md, shmd, gv).

  (* return 0 *)
  unfold spec_sha.data_block.
  forward.
  change_compspecs hmac_drbg_compspecs.CompSpecs.  (* TODO: This should not be necessary *)
  cancel.
Qed.

Lemma body_md_reset: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_reset md_reset_spec.
Proof.
  start_function.

  destruct r as [r1 [r2 internal_r]].
  simpl.
  rewrite FULL_isptr; Intros.

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward. 
  forward_call (@inl _ (val * Z * list Z * block * Ptrofs.int * globals) (internal_r, 32, key, gv)). 
  forward.

  unfold md_relate; simpl. cancel.
(*  unfold convert_abs.*)
Qed.

Lemma body_md_setup: semax_body HmacDrbgVarSpecs ((*malloc_spec::*)HmacDrbgFunSpecs)
       f_mbedtls_md_setup md_setup_spec.
Proof.
  start_function.

  forward_call (Tstruct _hmac_ctx_st noattr).
  Intros vret.

  forward_if.
  { destruct (Memory.EqDec_val vret nullval).
    + subst vret; entailer!.
    + normalize. eapply derives_trans; try apply valid_pointer_weak.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer2.
      apply data_at_valid_ptr. apply top_share_nonidentity. compute. auto.
      entailer!.
  }
  { (*null*)
    subst vret. simpl. forward.
    Exists (-20864).
    rewrite if_false by omega.
    entailer!.
  }
  destruct (eq_dec vret nullval); subst. elim H; trivial. clear n.
  Intros.
  unfold_data_at 1%nat.
  forward. forward. forward. forward. Exists 0. simpl. entailer!.
  Exists vret. unfold_data_at 1%nat. entailer!.
Qed.
