Require Import VST.floyd.proofauto.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.spec_hmac_drbg.

Lemma ReseedRes: forall X r v, @return_value_relate_result X r (Vint v) -> Int.eq v (Int.repr (-20864)) = false.
Proof. intros.
  unfold return_value_relate_result in H.
  destruct r. inversion H; reflexivity.
  destruct e; inversion H; try reflexivity.
  apply Int.eq_false. eapply ENT_GenErrAx.
Qed.

Lemma hmac_interp_empty sh d r: hmac_interp sh d r |-- md_empty sh r.
destruct d; simpl. auto.
+ destruct h. simpl.
  eapply derives_trans.
  apply UNDER_SPEC.REP_FULL.
  apply UNDER_SPEC.FULL_EMPTY.
+ apply UNDER_SPEC.FULL_EMPTY.
Qed.

Lemma instantiate256_reseed d s pr_flag rc ri (ZLc'256F : (Zlength d >? 256) = false):
      instantiate_function_256 s pr_flag  d =
      mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs initial_key initial_value rc 48 pr_flag ri) d.
Proof. intros.
  unfold instantiate_function_256; simpl.
  rewrite ZLc'256F, andb_negb_r.
  assert (MaxString': Zlength d >? max_personalization_string_length = false).
  { apply Zgt_is_gt_bool_f. apply Zgt_is_gt_bool_f in ZLc'256F.
    unfold max_personalization_string_length. omega. }
  rewrite MaxString' in *; trivial.
Qed.