Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg.

Lemma body_md_get_size: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_get_size md_get_size_spec.
Proof. 
  start_function.
  forward.
Qed.

Lemma derive_helper4: forall A B C D P, A  |-- !!P -> (A * B * C * D) |-- !!P.
Proof.
  intros.
  specialize (saturate_aux20 A (B * C * D) P True).
  intros.
  eapply derives_trans with (Q:=!!(P /\ True)).
  do 2 rewrite <- sepcon_assoc in H0.
  apply H0. assumption. entailer!. entailer.
Qed.

Lemma body_md_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_update md_update_spec.
Proof.
  start_function.

  name ctx' _ctx.
  name input' _input.
  name ilen' _ilen.
  
  unfold md_relate; unfold convert_abs.
  destruct r as [r1 [r2 internal_r]].
  simpl.
  assert_PROP (isptr internal_r) as Hisptr_r.
  {
    entailer.
    apply derive_helper4.
    apply UNDER_SPEC.REP_isptr.
  }

  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.

  (* HMAC_Update(hmac_ctx, input, ilen); *)
  forward_call (key, internal_r, d, data, data1, kv).
  {
    entailer!.
    destruct input'; try solve [inversion TC1]; reflexivity.
  }
  {
    unfold spec_sha.data_block.
    entailer!.
    (* TODO this should not be needed *)
    change
      (@data_at spec_hmacNK.CompSpecs Tsh (tarray tuchar (@Zlength Z data1))
                (@map int val Vint (@map Z int Int.repr data1)) d) with
    (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z data1))
         (@map int val Vint (@map Z int Int.repr data1)) d).
    cancel.
  }

  (* return 0 *)
  forward.

  (* prove the post condition *)
  unfold spec_sha.data_block.
  unfold md_relate; unfold convert_abs.
  entailer!.
Qed.

Lemma body_md_final: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_finish md_final_spec.
Proof.
  start_function.

  name ctx' _ctx.
  name output' _output.
  
  unfold md_relate; unfold convert_abs.
  destruct r as [r1 [r2 internal_r]].
  simpl.
  assert_PROP (isptr internal_r) as Hisptr_r.
  {
    entailer.
    apply derive_helper4.
    apply UNDER_SPEC.REP_isptr.
  }
  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.

  (* HMAC_Final(hmac_ctx, output); *)
  forward_call (data, key, internal_r, md, shmd, kv).

  (* return 0 *)
  unfold spec_sha.data_block.
  forward.
Qed.

Lemma body_md_reset: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_md_hmac_reset md_reset_spec.
Proof.
  start_function.

  name ctx' _ctx.

  destruct r as [r1 [r2 internal_r]].
  simpl.
  assert_PROP (isptr internal_r) as Hisptr_r.
  {
    entailer.
    replace (spec_sha.K_vector kv) with (emp * (spec_sha.K_vector kv)) by (apply emp_sepcon).
    rewrite <- sepcon_assoc.
    apply derive_helper4.
    apply UNDER_SPEC.FULL_isptr.
  }
  (* HMAC_CTX * hmac_ctx = ctx->hmac_ctx; *)
  forward.

  forward_call (internal_r, 32, key, kv).
  forward.
  unfold md_relate.
  unfold convert_abs.
  entailer!.
Qed.