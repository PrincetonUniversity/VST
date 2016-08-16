Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.entropy.
Require Import sha.general_lemmas.

Lemma body_hmac_drbg_random: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_random hmac_drbg_random_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  rename H into ASS1. rename H0 into ASS2. rename H1 into ASS3.
  rename H2 into ASS4. rename H3 into ASS5. rename H4 into ASS6.
  forward. 
  forward_call (@nil Z, nullval, Z0, output, out_len, ctx, initial_state, 
                initial_state_abs, kv, info_contents, s).
  { rewrite da_emp_null; trivial. cancel. }
  { rewrite Zlength_nil.
    repeat (split; try assumption; try omega).
    constructor. }
  Intros v. forward. simpl. Exists (Vint v). entailer!.
Qed.

Lemma body_hmac_drbg_init: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_init hmac_drbg_init_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  forward_call (Tsh,c,size_of_HMACDRBGCTX, Int.zero).
  forward.
Qed.

Lemma body_zeroize: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
      f_mbedtls_zeroize mbedtls_zeroize_spec. 
Proof. 
  start_function. 
  abbreviate_semax. rename H into N.
  rewrite data_at__isptr. Intros. destruct v; try contradiction. clear Pv.
  assert_PROP (field_compatible (tarray tuchar n) [] (Vptr b i)) as FC by entailer!.
  forward.
  apply semax_pre with (P':= EX k:Z,
  (PROP (0<=k<=n )
   LOCAL (temp _p (offset_val k (Vptr b i)); temp _n (Vint (Int.repr (n-k))); 
          temp _v (Vptr b i))
   SEP (data_at_ Tsh (tarray tuchar (n-k)) (offset_val k (Vptr b i));
        data_at Tsh (tarray tuchar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) (Vptr b i)))).
  { Exists 0. rewrite Zminus_0_r. entailer. cancel. unfold tarray.
    apply Tarray_0_emp'. eapply field_compatible_array_smaller0. eassumption. omega. }
  Intros k. rename H into K. 
  eapply semax_seq with (Q:=
         PROP ( )
         LOCAL ()
         SEP (data_block Tsh (list_repeat (Z.to_nat n) 0) (Vptr b i))).
  2: solve [unfold MORE_COMMANDS, abbreviate; forward]. 
  apply semax_loop with (Q':=
     (PROP ( )
      LOCAL (temp _p (offset_val k (Vptr b i)); temp _n (Vint (Int.repr (n - k))); 
      temp _v (Vptr b i))
      SEP (data_at_ Tsh (tarray tuchar (n - k)) (offset_val k (Vptr b i));
      data_at Tsh (tarray tuchar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) (Vptr b i)))).
  + forward. forward. 
    forward_if 
     (PROP ( n-k<>0)
      LOCAL (temp _n (Vint (Int.sub (Int.repr (n - k)) (Int.repr 1)));
        temp 222%positive (Vint (Int.repr (n - k))); temp _p (offset_val k (Vptr b i)); 
        temp _v (Vptr b i))
      SEP (data_at_ Tsh (tarray tuchar (n - k)) (offset_val k (Vptr b i));
           data_at Tsh (tarray tuchar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) (Vptr b i))).
    - inv H. forward. apply negb_true_iff in H1. apply int_eq_false_e in H1.
      entailer. apply prop_right. intros NN; rewrite NN in *. elim H1; trivial.
    - inv H. apply negb_false_iff in H1. apply int_eq_e in H1. rewrite H1.
      forward.
      entailer. unfold data_block.
      (*FLOYD: WHY DOES NORMALIZE HERE YIELD A NONSENSICAL GOAL (Vptr as additional argument to "!!" ???*) simpl.  
      apply andp_right. apply prop_right. apply Forall_list_repeat. split; omega. 
      assert (NK: n = k).
      { apply f_equal with (f:=Int.unsigned) in H1. unfold Int.zero in H1.
        do 2 rewrite Int.unsigned_repr in H1; try omega. }
      subst k. rewrite Zminus_diag, Zlength_list_repeat; try omega. 
      repeat rewrite general_lemmas.map_list_repeat. cancel.
      rewrite data_at__memory_block. normalize.
    - forward. forward. admit. (*we don't seem to have proof rule for Sbuiltin EF_vstore*)
  + forward. entailer.
Admitted. (*Proof contains one admit, for the missing proof rule for volatile stores*)

Lemma body_hmac_drbg_setPredictionResistance: 
      semax_body HmacDrbgVarSpecs (md_free_spec::mbedtls_zeroize_spec::HmacDrbgFunSpecs) 
      f_mbedtls_hmac_drbg_set_prediction_resistance hmac_drbg_setPredictionResistance_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  destruct CTX as [md_ctx [V [rc [el [pr ri]]]]].
  destruct ABS as [K VV RC EL PR RI].
  unfold hmac256drbg_relate. normalize.
  rewrite data_at_isptr. Intros. destruct ctx; try contradiction.
  unfold_data_at 1%nat. forward. forward.
  unfold_data_at 1%nat. cancel.
Qed. 

Lemma body_hmac_drbg_setEntropyLen: 
      semax_body HmacDrbgVarSpecs (md_free_spec::mbedtls_zeroize_spec::HmacDrbgFunSpecs) 
      f_mbedtls_hmac_drbg_set_entropy_len hmac_drbg_setEntropyLen_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  destruct CTX as [md_ctx [V [rc [el [pr ri]]]]].
  destruct ABS as [K VV RC EL PR RI].
  unfold hmac256drbg_relate. normalize.
  rewrite data_at_isptr. Intros. destruct ctx; try contradiction.
  unfold_data_at 1%nat. forward. forward.
  unfold_data_at 1%nat. cancel.
Qed. 

Lemma body_hmac_drbg_setReseedInterval: 
      semax_body HmacDrbgVarSpecs (md_free_spec::mbedtls_zeroize_spec::HmacDrbgFunSpecs) 
      f_mbedtls_hmac_drbg_set_reseed_interval hmac_drbg_setReseedInterval_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  destruct CTX as [md_ctx [V [rc [el [pr ri]]]]].
  destruct ABS as [K VV RC EL PR RI].
  unfold hmac256drbg_relate. normalize.
  rewrite data_at_isptr. Intros. destruct ctx; try contradiction.
  unfold_data_at 1%nat. forward. forward.
  unfold_data_at 1%nat. cancel.
Qed. 
Lemma body_hmac_drbg_free: semax_body HmacDrbgVarSpecs (md_free_spec::mbedtls_zeroize_spec::HmacDrbgFunSpecs) 
      f_mbedtls_hmac_drbg_free hmac_drbg_free_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  rewrite da_emp_isptrornull. Intros.
  destruct ctx; try contradiction.
  { (*ctx==null*)
    simpl in *; subst i. rewrite da_emp_null; trivial.
    forward_if (`FF).
    + forward.
    + inv H.
    + apply semax_ff. 
  }
  { (*isptr ctx*)
    rewrite da_emp_ptr. clear PNctx. Intros. simpl. rewrite if_false; try discriminate.
    forward_if (PROP ( )
       LOCAL (temp _ctx (Vptr b i))
       SEP (data_at Tsh t_struct_hmac256drbg_context_st CTX (Vptr b i);
            hmac256drbg_relate ABS CTX)).
    + inv H.
    + forward. entailer!.
    + unfold_data_at 1%nat. destruct CTX as [C1 [C2 [C3 [C4 [C5 C6]]]]]. simpl.
      freeze [1;2;3;4;5] FR. unfold hmac256drbg_relate. destruct ABS. normalize.
      destruct C1 as [? [? ?]]. unfold md_full. simpl. 
Admitted. (*TODO: COMPLETE FREE*)

