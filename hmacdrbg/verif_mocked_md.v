Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.floyd.sublist.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.vst_lemmas.
Require Import VST.floyd.library.

Lemma body_md_free: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_free md_free_spec.
Proof.
  start_function.
  destruct r as [r1 [r2 r3]].
  assert_PROP (isptr r3) by (unfold md_empty; entailer!).
  forward.
 forward_call (Tstruct _hmac_ctx_st noattr, r3).
 { rewrite md_empty_unfold. simpl. cancel. }
 forward.
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
  destruct r as [r1 [r2 r3]].
  assert_PROP (isptr r3) by (unfold md_empty; entailer!).
  forward.
  forward_call (@inr (val * share * Z * list byte * globals) _ (r3, Ews, l, key, b, i, shk, gv)).
 { rewrite md_empty_unfold. simpl. unfold data_block.
   sep_apply (UNDER_SPEC.mkEmpty Ews r3). cancel.
 }
  forward.
  unfold md_relate.
  unfold data_block. simpl. cancel.
Qed.

Hint Extern 2 (@data_at ?cs1 ?sh _ _ ?p |-- @data_at ?cs2 ?sh _ _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel; 
       [ reflexivity | reflexivity | apply JMeq_refl]) : cancel.

Lemma body_md_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_update md_update_spec.
Proof.
  start_function.
  assert_PROP (0 <= Zlength data1 <= Ptrofs.max_unsigned) as H0. {
    entailer!. clear - H2. destruct H2 as [? [_ [? _]]].
    destruct d; try contradiction.
    red in H0. simpl in H0. rewrite Z.max_r in H0 by list_solve.
    rep_omega.
  }

  unfold md_relate(*; unfold convert_abs*).
  destruct r as [r1 [r2 internal_r]].
  simpl. Intros.
  assert_PROP (isptr internal_r) by entailer!.

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.
  assert_PROP (isptr d) by entailer!.
  (* HMAC_Update(hmac_ctx, input, ilen); *)
  destruct d; try contradiction.

  forward_call (key, internal_r, Ews, Vptr b i, sh, data, data1, gv).
  { unfold data_block.
    entailer!.
  }

  (* return 0 *)
  forward.

  (* prove the post condition *)
  unfold data_block.
  unfold md_relate (*; unfold convert_abs*).
  simpl.
  cancel.
Qed.

Lemma body_md_final: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_finish md_final_spec.
Proof.
  start_function.

  unfold md_relate(*; unfold convert_abs*).
  destruct r as [r1 [r2 internal_r]].
  simpl. Intros.
  assert_PROP (isptr internal_r) by entailer!.

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.

  (* HMAC_Final(hmac_ctx, output); *)
  forward_call (data, key, internal_r, Ews, md, shmd, gv).
   sep_apply (data_at__memory_block_cancel shmd (tarray tuchar 32) md).
   simpl sizeof. cancel.
   
  (* return 0 *)
  unfold data_block.
  forward.
  unfold md_full; simpl.
  rewrite hmac_common_lemmas.HMAC_Zlength.
  cancel.
Qed.

Lemma body_md_reset: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_reset md_reset_spec.
Proof.
  start_function.

  destruct r as [r1 [r2 internal_r]].
  unfold md_full. Intros.
  simpl.
  assert_PROP (isptr internal_r) by entailer!.

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward. 
  forward_call (@inl _ (val * share * Z * list byte * block * Ptrofs.int * share * globals)
                             (internal_r, Ews, 32, key, gv)). 
  forward.

  unfold md_relate; simpl. cancel.
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
    + entailer!.
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
  forward. forward. forward. Exists 0. simpl.
  Exists vret.
  rewrite md_empty_unfold.
 unfold_data_at 1%nat. entailer!.
Qed.
