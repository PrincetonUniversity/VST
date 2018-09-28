Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import sha.vst_lemmas.
Require Import VST.floyd.library.

Lemma body_hmac_drbg_free: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_free hmac_drbg_free_spec.
Proof.
  start_function.
  abbreviate_semax.
  assert_PROP (is_pointer_or_null ctx) as PNctx by entailer.
  destruct ctx; try contradiction.
  - (*ctx==null*)
    simpl in PNctx; subst i. rewrite da_emp_null; trivial.
    forward_if (`FF).
    + forward. apply tt.
    + inv H.
    + apply semax_ff.
  - (*isptr ctx*)
    rewrite if_false; try discriminate.
    rewrite da_emp_ptr.  Intros. 
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st
                   [StructField _md_ctx] (Vptr b i)) as FC_mdctx.
        entailer!.
    forward_if.
    + elim H; trivial.
    + clear H. Intros.
      destruct CTX as [C1 [C2 [C3 [C4 [C5 C6]]]]]. simpl.
      assert_PROP (field_compatible t_struct_hmac256drbg_context_st [] (Vptr b i)) as FC by entailer!.
      unfold_data_at 1%nat.
      freeze [1;2;3;4;5] FR. unfold hmac256drbg_relate. destruct ABS. normalize.
      destruct C1 as [? [? ?]]. rewrite field_at_data_at. simpl.
      unfold field_address. rewrite if_true. simpl. rewrite Ptrofs.add_zero. 2: trivial.
      unfold md_full; simpl. Intros.
      sep_apply (UNDER_SPEC.FULL_EMPTY Ews key v1).
      assert (exists xx:reptype t_struct_md_ctx_st, xx = (v, (v0, v1))). eexists; reflexivity.
      destruct  H0 as [xx XX]. 
      forward_call (Vptr b i, (v, (v0, v1)), shc). {
         unfold md_empty. simpl. cancel. } 
      replace_SEP 0 (memory_block shc 12 (Vptr b i)).
            { entailer!. apply @data_at_memory_block. }
      freeze [0;1] FR1.
      replace_SEP 0 (data_at_ shc (tarray tuchar (sizeof (Tstruct _mbedtls_hmac_drbg_context noattr))) (Vptr b i)).
            { thaw FR1.
              entailer. rewrite data_at__memory_block.
              apply andp_right. apply prop_right.
              hnf in FC_mdctx, FC |- *.
              decompose [and] FC_mdctx; clear FC_mdctx FC.
               split3; auto. split3; auto.
              apply align_compatible_rec_Tarray. intros.
              eapply align_compatible_rec_by_value. reflexivity. simpl. apply Z.divide_1_l.
              simpl. specialize (memory_block_split shc b (Ptrofs.unsigned i) 12 48); simpl.
              rewrite Ptrofs.repr_unsigned; intros XX; rewrite XX; clear XX; try omega.
              cancel.
              2:{ unfold field_compatible in *. simpl in *.
                  destruct (Ptrofs.unsigned_range i). omega. }
              thaw FR.
               destruct (Ptrofs.unsigned_range i).  eapply derives_trans.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_.
               eapply sepcon_derives. apply field_at_field_at_. apply derives_refl.
               repeat rewrite field_at__memory_block. simpl.
               unfold field_address. repeat rewrite if_true. simpl. rewrite  <- ptrofs_add_repr.
               specialize (memory_block_split shc b (Ptrofs.unsigned i + 12) 32 16); simpl.  rewrite <- ptrofs_add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Ptrofs.repr_unsigned. cancel. rewrite <- (Zplus_assoc _ 12). simpl.
               specialize (memory_block_split shc b (Ptrofs.unsigned i + 44) 4 12); simpl. rewrite <- ptrofs_add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Ptrofs.repr_unsigned. cancel. rewrite <- (Zplus_assoc _ 44). simpl.
               specialize (memory_block_split shc b (Ptrofs.unsigned i + 48) 4 8); simpl. rewrite <- ptrofs_add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Ptrofs.repr_unsigned. cancel. rewrite <- (Zplus_assoc _ 48). simpl.
               specialize (memory_block_split shc b (Ptrofs.unsigned i + 52) 4 4); simpl. rewrite <- ptrofs_add_repr.
               intros XX; rewrite XX; clear XX; try omega. rewrite Ptrofs.repr_unsigned. cancel.
               rewrite <- (Zplus_assoc _ 52). simpl. rewrite <- ptrofs_add_repr. rewrite Ptrofs.repr_unsigned. cancel.
               destruct FC; simpl in *; omega.
               destruct FC; simpl in *; omega.
               destruct FC; simpl in *; omega.
               destruct FC; simpl in *; omega.
               all: hnf in FC; decompose [and] FC; clear FC; split3; auto; split3; auto; split; auto;
                       repeat first [left; solve [trivial] | right].
            }
      clear FR1. clear FR.
      forward_call (sizeof (Tstruct _mbedtls_hmac_drbg_context noattr), Vptr b i, shc).
      forward. apply tt.
Qed.

Lemma body_hmac_drbg_random: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_random hmac_drbg_random_spec.
Proof.
  start_function.
  abbreviate_semax.
  rename H into ASS1. rename H0 into ASS2. rename H1 into ASS3.
  rename H2 into ASS4. rename H3 into ASS5.
  forward.  
  forward_call (@nil byte, nullval, Tsh, Z0, output, sho, out_len, ctx, shc, initial_state,
               I, info_contents, s, gv).
  { rewrite da_emp_null; trivial. cancel. }
  { rewrite Zlength_nil.
    repeat (split; auto; try omega). }
  Intros v. forward. simpl. Exists (Vint v). entailer!.
Qed.

Definition WF (I:hmac256drbgabs):=
         Zlength (hmac256drbgabs_value I) = 32 /\ 
         0 < hmac256drbgabs_entropy_len I <= 384 /\
         RI_range (hmac256drbgabs_reseed_interval I)  /\
         0 <= hmac256drbgabs_reseed_counter I < Int.max_signed.

Definition hmac_drbg_random_spec_simple :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, n: Z,
        ctx: val, i: hmac256drbgstate,
        I: hmac256drbgabs,
        info: md_info_state,
        s: ENTROPY.stream, bytes:_, J:_, ss:_, gv: globals
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP ( WF I;
         0 <= n <= 1024;
         mbedtls_HMAC256_DRBG_generate_function s I n [] = ENTROPY.success (bytes, J) ss)
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr n)); gvars gv)
       SEP (
         data_at_ Ews (tarray tuchar n) output;
         data_at Ews t_struct_hmac256drbg_context_st i ctx;
         hmac256drbg_relate I i;
         data_at Ews t_struct_mbedtls_md_info info (hmac256drbgstate_md_info_pointer i);
         Stream s;
         K_vector gv)
    POST [ tint ] EX F: hmac256drbgabs, EX f: hmac256drbgstate, 
       PROP (F = match J with ((((VV, KK), RC), _), PR) =>
                   HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                        (hmac256drbgabs_reseed_interval I)
                      end) 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at Ews (tarray tuchar n) (map Vubyte bytes) output;
            data_at Ews t_struct_hmac256drbg_context_st f ctx;
         hmac256drbg_relate F f;
         data_at Ews t_struct_mbedtls_md_info info (hmac256drbgstate_md_info_pointer f);
        Stream ss; K_vector gv).

Lemma AUX s I n bytes J ss: mbedtls_HMAC256_DRBG_generate_function s I n [] =
  ENTROPY.success (bytes, J) ss ->
  hmac256drbgabs_generate I s n [] = 
  match J with ((((VV, KK), RC), _), PR) =>
     HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                    (hmac256drbgabs_reseed_interval I)
  end.
Proof. unfold hmac256drbgabs_generate. intros H; rewrite H.
  destruct I. simpl. destruct J. destruct p. destruct d. destruct p. f_equal.
Qed. 
Opaque hmac256drbgabs_generate.

Lemma body_hmac_drbg_random_simple: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_random hmac_drbg_random_spec_simple.
Proof.
  start_function.
  abbreviate_semax. 
  destruct H as [ASS1 [ASS2 [ASS3 [ASS4 ASS5]]]].
  destruct H0 as [ASS6 ASS7]. rename H1 into ASS8.
  forward.
  forward_call (@nil byte, nullval, Tsh, Z0, output, Ews, n, ctx, Ews, i,
                I, info, s, gv).
  { rewrite da_emp_null; trivial. cancel. }
  { rewrite Zlength_nil.
    repeat (split; auto; try rep_omega). }
  Intros v. forward. unfold hmac256drbgabs_common_mpreds.
  unfold generatePOST, contents_with_add; simpl. 
  apply Zgt_is_gt_bool_f in ASS7. rewrite ASS7 in *.
  rewrite ASS8 in *.
  unfold return_value_relate_result, da_emp; simpl. (* entailer!.*)
  Exists (hmac256drbgabs_generate I s
            (Zlength (map Vubyte bytes)) []).
  Exists (hmac256drbgabs_to_state (hmac256drbgabs_generate I s
            (Zlength (map Vubyte bytes)) []) i).
  apply AUX in ASS8. rewrite <- ASS8; clear ASS8. 
  entailer!. 
  unfold hmac256drbgabs_common_mpreds; simpl.
  cancel.
  eapply derives_trans.
  + instantiate (1:=emp).  
    apply orp_left; [ auto | normalize; apply derives_refl].
  + cancel.
Qed.
(*
Definition myProp s n I (i F:hmac256drbgstate): Prop :=
  F = (hmac256drbgabs_to_state (hmac256drbgabs_generate I s n []) i).

Definition hmac_drbg_random_spec_simple :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, out_len: Z,
        ctx: val, i: hmac256drbgstate,
        I: hmac256drbgabs,
        kv: val, info: md_info_state,
        s: ENTROPY.stream, bytes:_, J:_, ss:_
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP ( WF I;
         0 <= out_len <= 1024;
         mbedtls_HMAC256_DRBG_generate_function s I out_len [] = ENTROPY.success (bytes, J) ss)
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr out_len)); gvar sha._K256 kv)
       SEP (
         data_at_ Ews (tarray tuchar out_len) output;
         data_at Ews t_struct_hmac256drbg_context_st i ctx;
         hmac256drbg_relate I i;
         data_at Ews t_struct_mbedtls_md_info info (hmac256drbgstate_md_info_pointer i);
         Stream s;
         K_vector kv)
    POST [ tint ] EX final_state: hmac256drbgstate,
       PROP (final_state = hmac256drbgabs_to_state (hmac256drbgabs_generate I s out_len []) i)
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at Ews (tarray tuchar out_len) (map Vint (map Int.repr bytes)) output;
            data_at Ews t_struct_hmac256drbg_context_st final_state ctx;
         hmac256drbg_relate (hmac256drbgabs_generate I s out_len []) final_state;
         data_at Ews t_struct_mbedtls_md_info info (hmac256drbgstate_md_info_pointer final_state);
        Stream ss; K_vector kv).
(*
generatePOST (Vint Int.zero) nil nullval 0 output out_len ctx initial_state I kv info_contents s).
*)

Lemma AUX s I n bytes J ss: mbedtls_HMAC256_DRBG_generate_function s I n [] =
  ENTROPY.success (bytes, J) ss ->
  hmac256drbgabs_generate I s n [] = 
  match J with ((((VV, KK), RC), _), PR) =>
     HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                    (hmac256drbgabs_reseed_interval I)
  end.
Proof. unfold hmac256drbgabs_generate. intros H; rewrite H.
  destruct I. simpl. trivial. 
Qed. 

Opaque hmac256drbgabs_generate.

Lemma body_hmac_drbg_random_simple: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_random hmac_drbg_random_spec_simple.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [ASS1 [ASS2 [ASS3 [ASS4 ASS5]]]].
  destruct H0 as [ASS6 ASS7]. rename H1 into ASS8.
  forward.
  forward_call (@nil Z, nullval, Z0, output, out_len, ctx, i,
                I, kv, info, s).
  { rewrite da_emp_null; trivial. cancel. }
  { rewrite Zlength_nil.
    repeat (split; try assumption; try rewrite int_max_unsigned_eq; try omega).
    constructor. }
  Intros v. forward. unfold hmac256drbgabs_common_mpreds.
  unfold generatePOST, contents_with_add; simpl. 
  apply Zgt_is_gt_bool_f in ASS7. rewrite ASS7 in *.
  rewrite ASS8 in *.
  unfold return_value_relate_result, da_emp; simpl. entailer!.
  Exists (hmac256drbgabs_to_state (hmac256drbgabs_generate I s
            (Zlength (map Vint (map Int.repr bytes))) []) i).
  apply andp_right. 
  + entailer!. 
  + entailer!.
  unfold hmac256drbgabs_common_mpreds; simpl.
  cancel.
  eapply derives_trans. apply sepcon_derives. apply derives_refl.
  instantiate (1:=emp). 
  apply orp_left. trivial. normalize. cancel. 
Qed.
 unfold hmac256drbgabs_generate.
  remember  (@Zlength (@reptype hmac_drbg_compspecs.CompSpecs tuchar)
                       (@map Int.int val Vint (@map Z Int.int Int.repr bytes))) as len. 
  remember (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
        reseed_interval) as A. 
  remember (HMAC256DRBGabs l0 l z entropy_len b reseed_interval) as B. 
  assert (HB: B = (hmac256drbgabs_generate A s len [])).
  { clear - Heqlen ASS8 H0. rewrte . rewrite ASS8 in H0.  subst.  subst. rewrite ASS8 in H0. unfold hmac256drbgabs_generate,  mbedtls_HMAC256_DRBG_generate_function. simpl in H0. rewrite H0.
  rewrite <- HB.
  cancel.
  remember (hmac256drbgabs_generate
     (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
        reseed_interval) s (Zlength (map Vint (map Int.repr bytes))) (@nil Z)) as hh; clear Heqhh. 
  destruct initial_state as [? ? ? ? ?]. simpl.
  unfold hmac256drbgabs_to_state.
  remember (mbedtls_HMAC256_DRBG_generate_function s I
               (Zlength (map Vint (map Int.repr bytes))) []). 
  assert (r=ENTROPY.success (bytes, J) ss).
  { subst r. apply ASS8. } clear Heqr. cancel.
  remember (hmac256drbgabs_generate I s
            (Zlength (map Vint (map Int.repr bytes))) []) as h.
  unfold hmac256drbgabs_generate in Heqh. 
  unfold hmac256drbgabs_common_mpreds; simpl.
  remember (mbedtls_HMAC256_DRBG_generate_function s I
               (Zlength (map Vint (map Int.repr bytes))) []). 
  assert (r=ENTROPY.success (bytes, J) ss).
  { subst r. apply ASS8. } clear Heqr.
  Exists (hmac256drbgabs_to_state h initial_state). 
  apply andp_right. 
  admit. OK, is on comment
  entailer. 
  cancel.
  destruct I. destruct J as [[[[? ?] ?] ?] ?].
  eapply derives_trans. apply sepcon_derives. apply derives_refl.
  instantiate (1:=emp). 
  apply orp_left. trivial. normalize. unfold hmac256drbgabs_generate.
  remember  (@Zlength (@reptype hmac_drbg_compspecs.CompSpecs tuchar)
                       (@map Int.int val Vint (@map Z Int.int Int.repr bytes))) as len. 
  remember (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
        reseed_interval) as A. 
  remember (HMAC256DRBGabs l0 l z entropy_len b reseed_interval) as B. 
  assert (HB: B = (hmac256drbgabs_generate A s len [])).
  { clear - Heqlen ASS8 H0. rewrte . rewrite ASS8 in H0.  subst.  subst. rewrite ASS8 in H0. unfold hmac256drbgabs_generate,  mbedtls_HMAC256_DRBG_generate_function. simpl in H0. rewrite H0.
  rewrite <- HB.
  cancel.
  remember (hmac256drbgabs_generate
     (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
        reseed_interval) s (Zlength (map Vint (map Int.repr bytes))) (@nil Z)) as hh; clear Heqhh. 
  destruct initial_state as [? ? ? ? ?]. simpl.
  unfold hmac256drbgabs_to_state.
Print hmac256drbgstate. cancel. simpl.
  remember ().
  unfold hmac256drbgabs_generate.
  normalize. cancel.
Qed. 
  remember (hmac256drbgabs_generate I s (Zlength (map Vint (map Int.repr bytes)))
         []). 
  unfold hmac256drbgabs_generate. rewrite ASS8. clear ASS8. 
  destruct I as [K V RC EL PR RI]. simpl in *. 
  destruct J as [[[[VAL KEY] RCC] SecStr] PRflag]. simpl. rewrite ASS7. subst h; simpl.
  destruct I (hmac256drbgabs_generate I s (Zlength (map Vint (map Int.repr bytes))) []).
  unfold hmac256drbgabs_common_mpreds. simpl.
  unfold hmac256drbgabs_generate in Heqh. rewrite ASS8 in Heqh.
  subst h. entailer.
Locate hmac256drbgabs.
  destruct I as [K V RC EL PR RI]. simpl in *. 
Print DRBG_functions.DRBG_state_handle. destruct J as [[[[VAL KEY] RCC] SecStr] PRflag]. subst h; simpl.
  unfold return_value_relate_result, da_emp; simpl. entailer!.
  unfold hmac256drbgabs_common_mpreds. simpl.
  cancel.
  eapply derives_trans. apply sepcon_derives. apply derives_refl.
  instantiate (1:=emp). 2: cancel. 
  apply orp_left. trivial. normalize. 
Qed. ntailer.
 normalize. cancel. destruct (
  destruct I. simpl in *. 
  apply Zgt_is_gt_bool_f in ASS7. rewrite ASS7 in *.
  rewrite ASS8 in *; clear ASS8.  unfold return_value_relate_result in *. simpl in *. 
  unfold da_emp; simpl. unfold hmac256drbgabs_common_mpreds; simpl. unfold hmac256drbgabs_to_state. simpl.
  destruct xx as [[[[V' key'] rc'] x']pr']. 
  destruct initial_state. simpl.
  unfold hmac256drbgstate_md_info_pointer. simpl.
  unfold hmac256drbgabs_common_mpreds. simpl. 
  unfold hmac256drbgabs_to_state, hmac256drbgstate_md_info_pointer.
  simpl.
  unfold mbedtls_HMAC256_DRBG_generate_function in H5. 
  destruct initial_state_abs.  simpl in *. rewrite H5.
  remember (Z.gtb out_len 1024). Focus 2. rewrite if_false.
  rewrite H5. Exists (Vint v). entailer!.
Qed.
*)
Lemma body_hmac_drbg_init: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_init hmac_drbg_init_spec.
Proof.
  start_function.
  abbreviate_semax.
  forward_call (shc,c,size_of_HMACDRBGCTX, Int.zero).
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
   SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat k) (Vint Int.zero) ++
                                       list_repeat (Z.to_nat (n-k)) Vundef) (Vptr b i)))).
  { Exists 0. rewrite Zminus_0_r. entailer!. }
  eapply semax_seq with (Q:=
         PROP ( )
         LOCAL ()
         SEP (data_block sh (list_repeat (Z.to_nat n) Byte.zero) (Vptr b i))).
  2: solve [unfold MORE_COMMANDS, abbreviate; forward]. 
  apply semax_loop with (
  (EX k : Z,
   PROP (0 <= k <= n)
   LOCAL (temp _p (offset_val k (Vptr b i)); temp _n (Vint (Int.repr (n - k)));
   temp _v (Vptr b i))
   SEP (data_at sh (tarray tuchar n)
          (list_repeat (Z.to_nat k) (Vint Int.zero) ++ list_repeat (Z.to_nat (n-k)) Vundef)
          (Vptr b i)))).
  2:{ apply extract_exists_pre. intros k. Intros. forward. entailer.
           Exists k. entailer!.
  }
  apply extract_exists_pre. intros k. Intros. rename H into K.
  forward. forward. 
    forward_if (n-k<>0).
    - forward. entailer!.
    - 
      assert (NK: n = k) by (apply repr_inj_unsigned in H; rep_omega).
      subst k; clear H K. rewrite Zminus_diag.
      forward.
      entailer!. unfold data_block. normalize. simpl.
      autorewrite with sublist. cancel.
    - forward. forward.
      assert (KN: 0 <= k < n) by omega.
      (*forward.  The 2 properties mentioned in the error message are equal*)
      assert_PROP (Vptr b (Ptrofs.add i (Ptrofs.repr k)) = field_address (tarray tuchar n) [ArraySubsc k] (Vptr b i)) as Addrk.
      { rewrite field_address_offset.
        + simpl. rewrite Z.mul_1_l, Z.add_0_l; entailer!.
        + apply (@field_compatible_cons_Tarray hmac_drbg_compspecs.CompSpecs k (tarray tuchar n) tuchar n noattr
                  [] (Vptr b i) (eq_refl _) FC KN). }
      forward.
      Exists (k+1). rewrite ! Z.sub_add_distr. entailer!.
      unfold Ptrofs.of_ints, Ptrofs.of_int; normalize. 
      rewrite upd_Znth_app2 by (rewrite ! Zlength_list_repeat; omega).
      rewrite Zlength_list_repeat, Zminus_diag by omega.
      assert (X: list_repeat (Z.to_nat k) (Vint Int.zero) ++
               upd_Znth 0 (list_repeat (Z.to_nat (n - k)) Vundef)(Vint (Int.zero_ext 8 (Int.repr 0)))
           = list_repeat (Z.to_nat (k + 1)) (Vint Int.zero) ++
             list_repeat (Z.to_nat (n - k - 1)) Vundef).
      2: rewrite X; cancel.
      rewrite Z2Nat.inj_add, <- list_repeat_app, <- app_assoc by omega. f_equal.
      assert (X: (Z.to_nat (n - k) = 1+Z.to_nat (n-k-1))%nat).
      { specialize (Z2Nat.inj_add 1); simpl; intros. rewrite <- H1 by omega. f_equal; omega. }
      rewrite X, <- list_repeat_app, upd_Znth_app1; clear X; trivial.
      simpl; rewrite Zlength_cons, Zlength_nil; omega.
Qed.

Lemma body_hmac_drbg_setPredictionResistance:
      semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
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
      semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
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
      semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
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

