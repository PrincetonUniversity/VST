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
Require Import sha.general_lemmas.

Lemma body_hmac_drbg_free: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_free hmac_drbg_free_spec. 
Proof. 
  start_function. 
  abbreviate_semax.
  rewrite da_emp_isptrornull. Intros.
  destruct ctx; try contradiction.
  { (*ctx==null*)
    simpl in *; subst i. rewrite da_emp_null; trivial.
    forward_if (`FF).
    + forward. apply tt. 
    + inv H.
    + apply semax_ff. 
  }
  { (*isptr ctx*)
    rewrite da_emp_ptr. clear PNctx. Intros. simpl. rewrite if_false; try discriminate.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st
                   [StructField _md_ctx] (Vptr b i)) as FC_mdctx. 
    { entailer. unfold_data_at 1%nat. simpl. entailer. }
    forward_if (PROP ( )
       LOCAL (temp _ctx (Vptr b i))
       SEP (data_at Tsh t_struct_hmac256drbg_context_st CTX (Vptr b i);
            hmac256drbg_relate ABS CTX; FreeBLK 324 (snd (snd (fst CTX))))).
    + inv H.
    + forward. entailer!.
    + destruct CTX as [C1 [C2 [C3 [C4 [C5 C6]]]]]. simpl.
      assert_PROP (field_compatible t_struct_hmac256drbg_context_st [] (Vptr b i)) as FC by entailer!.
      unfold_data_at 1%nat.
      freeze [1;2;3;4;5] FR. unfold hmac256drbg_relate. destruct ABS. normalize.
      destruct C1 as [? [? ?]]. rewrite field_at_data_at. simpl.
      unfold field_address. rewrite if_true. simpl. rewrite Int.add_zero. 2: trivial.
      unfold md_full; simpl. replace_SEP 2 (UNDER_SPEC.EMPTY v1).
      { entailer. apply UNDER_SPEC.FULL_EMPTY. } 
      assert (exists xx:reptype t_struct_md_ctx_st, xx = (v, (v0, v1))). eexists; reflexivity.
      destruct  H1 as [xx XX]. 
      forward_seq.
        forward_seq.
          { eapply (semax_call_id00_wow (Vptr b i, (v, (v0, v1))) [FRZL FR]) 
             with (B:= (Prop*mpred)%type)(Ppost:=fun x => [fst x])(Rpost:=fun x => [data_at Tsh t_struct_md_ctx_st xx (Vptr b i)]); trivial; try reflexivity.
            + entailer!.  
            + entailer!. constructor. constructor. constructor. 
            + entailer!. constructor. 
            + simpl. cancel.
            + extensionality x. apply pred_ext; simpl.
              - Exists (True, emp). simpl.
                unfold PROPx, LOCALx, SEPx. simpl. entailer.
              - Intros z. destruct z as [P M]. simpl. 
                unfold PROPx, LOCALx, SEPx. simpl. entailer.
          }
          { Intros q. destruct q as [P M]. simpl. Intros. 
            replace_SEP 0 (memory_block Tsh 12 (Vptr b i)).
            { specialize (data_at_memory_block Tsh t_struct_md_ctx_st xx); simpl; intros.
              entailer. apply andp_left2. unfold PROPx, LOCALx, SEPx. simpl. normalize.
              apply andp_left2. apply H2. } 
            freeze [0;1] FR1.
            replace_SEP 0 (data_at_ Tsh (tarray tuchar (sizeof (Tstruct _mbedtls_hmac_drbg_context noattr))) (Vptr b i)).
            { thaw FR1.
              entailer. rewrite data_at__memory_block.
              apply andp_right. apply prop_right. unfold field_compatible in *; simpl in *.
                 repeat split; trivial. omega.
                 unfold align_attr . simpl. apply Z.divide_1_l.
              simpl. specialize (memory_block_split Tsh b (Int.unsigned i) 12 48); simpl.
              rewrite Int.repr_unsigned; intros XX; rewrite XX; clear XX; try omega. 
              cancel. 2: rewrite <- hmac_pure_lemmas.max_unsigned_modulus, int_max_unsigned_eq; omega. 
              Focus 2. unfold field_compatible in *. simpl in *.
                destruct (Int.unsigned_range i). omega.
              thaw FR. destruct (Int.unsigned_range i).  eapply derives_trans.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_. apply derives_refl.
               repeat rewrite field_at__memory_block. simpl.
               unfold field_address. repeat rewrite if_true. simpl. rewrite  <- add_repr. 
               specialize (memory_block_split Tsh b (Int.unsigned i + 12) 32 16); simpl.  rewrite <- add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Int.repr_unsigned. cancel. rewrite <- (Zplus_assoc _ 12). simpl.
               specialize (memory_block_split Tsh b (Int.unsigned i + 44) 4 12); simpl. rewrite <- add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Int.repr_unsigned. cancel. rewrite <- (Zplus_assoc _ 44). simpl.
               specialize (memory_block_split Tsh b (Int.unsigned i + 48) 4 8); simpl. rewrite <- add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Int.repr_unsigned. cancel. rewrite <- (Zplus_assoc _ 48). simpl.
               specialize (memory_block_split Tsh b (Int.unsigned i + 52) 4 4); simpl. rewrite <- add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Int.repr_unsigned. cancel.
               rewrite <- (Zplus_assoc _ 52). simpl. rewrite <- add_repr. rewrite Int.repr_unsigned. cancel.
               rewrite <- hmac_pure_lemmas.max_unsigned_modulus, int_max_unsigned_eq; omega. 
               destruct FC; simpl in *; omega.
               rewrite <- hmac_pure_lemmas.max_unsigned_modulus, int_max_unsigned_eq; omega. 
               destruct FC; simpl in *; omega.
               rewrite <- hmac_pure_lemmas.max_unsigned_modulus, int_max_unsigned_eq; omega. 
               destruct FC; simpl in *; omega.
               rewrite <- hmac_pure_lemmas.max_unsigned_modulus, int_max_unsigned_eq; omega. 
               destruct FC; simpl in *; omega.
               destruct FC; repeat split; trivial; simpl in *; try omega. apply H5.
               right; simpl. right; right; right. right; left; trivial. 
               destruct FC; repeat split; trivial; simpl in *; try omega. apply H5.
               right; simpl. right; right; right. left; trivial. 
               destruct FC; repeat split; trivial; simpl in *; try omega. apply H5.
               right; simpl. right; right; left; trivial. 
               destruct FC; repeat split; trivial; simpl in *; try omega. apply H5.
               right; simpl. right; left; trivial. 
               destruct FC; repeat split; trivial; simpl in *; try omega. apply H5.
               right; simpl. left; trivial.
            } 
            clear FR1. clear FR.
            eapply (semax_call_id00_wow (sizeof (Tstruct _mbedtls_hmac_drbg_context noattr), Vptr b i) nil)
             with (B:= (Prop*mpred)%type)(Ppost:=fun x => [fst x])
                  (Rpost:=fun x => [data_block Tsh (list_repeat 60 0) (Vptr b i)]); trivial; try reflexivity.
            + entailer!. 
            + entailer!. repeat constructor. 
            + entailer!. constructor. 
            + simpl. cancel. 
            + extensionality x. apply pred_ext; simpl.
              - Exists (True, emp). simpl.
                unfold PROPx, LOCALx, SEPx. simpl. entailer.
              - Intros z. destruct z as [PP MM]. simpl. 
                unfold PROPx, LOCALx, SEPx. simpl. entailer.
            + simpl; split; trivial. rewrite int_max_unsigned_eq. omega. 
          }
          normalize. apply extract_exists_pre. intros z. destruct z as [PP MM]. simpl.
          forward. apply tt. 
        }
Qed. 

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
        temp _t'1 (Vint (Int.repr (n - k))); temp _p (offset_val k (Vptr b i)); 
        temp _v (Vptr b i))
      SEP (data_at_ Tsh (tarray tuchar (n - k)) (offset_val k (Vptr b i));
           data_at Tsh (tarray tuchar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) (Vptr b i))).
    - inv H. forward. apply negb_true_iff in H1. apply int_eq_false_e in H1.
      entailer. apply prop_right. intros NN; rewrite NN in *. elim H1; trivial.
    - inv H. apply negb_false_iff in H1. apply int_eq_e in H1. rewrite H1.
      forward.
      entailer. unfold data_block. normalize. simpl.
      apply andp_right. apply prop_right. apply Forall_list_repeat. split; omega. 
      assert (NK: n = k).
      { apply f_equal with (f:=Int.unsigned) in H1. unfold Int.zero in H1.
        do 2 rewrite Int.unsigned_repr in H1; try omega. }
      subst k. rewrite Zminus_diag, Zlength_list_repeat; try omega. 
      repeat rewrite general_lemmas.map_list_repeat. cancel.
      rewrite data_at__memory_block. normalize.
    - unfold MORE_COMMANDS, abbreviate. forward. forward.
      unfold offset_val; simpl.
      replace_SEP 0  (data_at Tsh (tarray tuchar (n - k)) (list_repeat (Z.to_nat (n-k)) Vundef) (Vptr b (Int.add i (Int.repr k)))).
      { entailer. }
      admit. (*TODO erewrite (data_at_complete_split [Vundef] (list_repeat (Z.to_nat (n-k-1)) Vundef)); try reflexivity.
      * normalize. unfold Zlength. simpl. freeze [1;2;3] FR6. unfold tarray, tuchar, tint in *.
assert (Econst_int (Int.repr 0) tint = Ecast (Econst_int (Int.repr 0) tint) tuchar). admit.
rewrite H0. forward.
        admit.
      * assert (ZZ: [Vundef] = list_repeat (Z.to_nat 1) Vundef) by reflexivity.
        rewrite ZZ; repeat rewrite Zlength_list_repeat; try omega.
        assert (QQ: 1 + (n - k - 1) = n-k) by omega. rewrite QQ; clear QQ ZZ.
        destruct (@field_compatible_Tarray_split hmac_drbg_compspecs.CompSpecs tuchar k n (Vptr b i)) as [FC' _]. omega.
        destruct (FC' FC) as [_ FFC]; clear FC'.
        unfold field_address0 in FFC. rewrite if_true in FFC. 
        2: auto with field_compatible.
        simpl in FFC. rewrite Z.add_0_l, Z.mul_1_l in FFC. apply FFC. 
      * rewrite Zlength_list_repeat. unfold Zlength; simpl. omega. omega.
      * assert (ZZ: [Vundef] = list_repeat (Z.to_nat 1) Vundef) by reflexivity.
        rewrite ZZ, list_repeat_app, <- Z2Nat.inj_add; try omega. f_equal. f_equal. omega. *)
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

