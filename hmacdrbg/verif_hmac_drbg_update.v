Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.general_lemmas.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.verif_hmac_drbg_update_common.

Lemma BDY_update: forall
(Espec : OracleKind)
(contents : list byte)
(additional : val) (sha: share)
(add_len : Z)
(ctx : val) (shc: share)
(initial_state : hmac256drbgstate)
(initial_state_abs : hmac256drbgabs)
(gv : globals)
(info_contents : md_info_state)
(sep: val)( K : val)
(H : 0 <= add_len <= Int.max_unsigned)
(H0 : Zlength (hmac256drbgabs_value initial_state_abs) = 32)
(H1 : add_len = Zlength contents \/ add_len = 0)
(Hsha: readable_share sha)
(Hshc: writable_share shc),
@semax hmac_drbg_compspecs.CompSpecs Espec
 (func_tycontext f_mbedtls_hmac_drbg_update HmacDrbgVarSpecs
        HmacDrbgFunSpecs nil)
  (PROP ( )
   LOCAL (lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
   temp _ctx ctx; temp _additional additional;
   temp _add_len (Vint (Int.repr add_len)); gvars gv)
   SEP (data_at_ Tsh (tarray tuchar 32) K;
   data_at_ Tsh (tarray tuchar 1) sep;
   da_emp sha (tarray tuchar (Zlength contents))
     (map Vubyte contents) additional;
   data_at shc t_struct_hmac256drbg_context_st initial_state ctx;
   hmac256drbg_relate initial_state_abs initial_state;
   data_at shc t_struct_mbedtls_md_info info_contents
     (hmac256drbgstate_md_info_pointer initial_state); K_vector gv))
  (Ssequence (fn_body f_mbedtls_hmac_drbg_update) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP ( )
         LOCAL ()
         SEP (hmac256drbgabs_common_mpreds shc
                (hmac256drbgabs_hmac_drbg_update initial_state_abs
                   (contents_with_add additional add_len contents))
                initial_state ctx info_contents;
         da_emp sha (tarray tuchar (Zlength contents))
           (map Vubyte contents) additional; K_vector gv)))
     (stackframe_of f_mbedtls_hmac_drbg_update)).
Proof. intros. do 2 pose proof I.
  abbreviate_semax.
  destruct initial_state as [IS1 [IS2 [IS3 [IS4 [IS5 IS6]]]]].
  rewrite da_emp_isptrornull.

  (* info = md_ctx.md_info *)
  destruct IS1 as [IS1a [IS1b IS1c]]. simpl.
  rewrite data_at_isptr with (p:=ctx).
  unfold hmac256drbgstate_md_info_pointer. simpl.
  rewrite data_at_isptr with (p:=IS1a).
  Intros.
  freeze [0;1;2;4;6] FR0.
  freeze [0;2] FR1.

  Time forward. (*8.5pl2: 3secs. BUT without doing the 2 lines
     unfold hmac256drbgstate_md_info_pointer. simpl.
     rewrite data_at_isptr with (p:=IS1a),
     this
     entailer takes 1230secs.
     And when we leave the IS1a-data-at unfrozen (eg omit the construction of FR1), it also takes significantly more than 3 secs*)
  thaw FR1.

  (* md_len = mbedtls_md_get_size( info ); *)
  freeze [0;1] FR1.
  forward_call tt.

  (*Intros md_len. LENB: replaced by the following*)
  (*change (Z.of_nat SHA256.DigestLength) with 32.*)
  remember (andb (negb (eq_dec additional nullval)) (negb (eq_dec add_len 0))) as na.
  freeze [0;1] FR2. clear PIS1a.
  forward_if (temp _t'2 (Val.of_bool na)).
  {
    (* show that add_len <> 0 implies the post condition *)
    forward.
    { entailer. destruct additional; try contradiction; simpl in PNadditional.
      subst i; simpl. entailer!. (* simpl. *)
      thaw FR2. thaw FR1. thaw FR0. normalize.
      rewrite da_emp_ptr. normalize.
      auto 50 with valid_pointer. (* TODO regression, this should have solved it *)
    }

    { entailer!.
      destruct additional; simpl in PNadditional; try contradiction.
      subst i; simpl; trivial.
      simpl. destruct (initial_world.EqDec_Z add_len 0); trivial; omega.
    }
  }

  {
    (* show that add_len = 0 implies the post condition *)
    forward.
    entailer!. simpl. rewrite andb_false_r. reflexivity.
  }

  remember (update_rounds na) as rounds. unfold update_rounds in Heqrounds.
  forward_if (temp _t'3 (Vint (Int.repr rounds))).
  {
    (* non_empty_additional = true *)
    forward. rewrite H4 in *; clear H4.
    entailer!.
  }
  {
    (* non_empty_additional = false *)
    forward. rewrite H4 in *; clear H4.
    entailer!.
  }

  forward.
  remember (hmac256drbgabs_key initial_state_abs) as initial_key.
  remember (hmac256drbgabs_value initial_state_abs) as initial_value.
  (* verif_sha_final2.v, @exp (environ -> mpred) *)
  (* for ( sep_value = 0; sep_value < rounds; sep_value++ ) *)
  Time forward_for_simple_bound rounds (EX i: Z,
      PROP  ()
      LOCAL ((*In VST 1.6, we need to add the entry for temp*)
               temp _rounds (Vint (Int.repr rounds));
       temp _md_len (Vint (Int.repr 32));
       temp _ctx ctx;
       lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
       temp _additional additional; temp _add_len (Vint (Int.repr add_len));
       gvars gv
         )
      SEP  (
        (EX key: list byte, EX value: list byte, EX final_state_abs: hmac256drbgabs,
          !!(
              (key, value) = HMAC_DRBG_update_round HMAC256
                (*contents*) (if na then contents else [])
                initial_key initial_value (Z.to_nat i)
              /\ key = hmac256drbgabs_key final_state_abs
              /\ value = hmac256drbgabs_value final_state_abs
              /\ hmac256drbgabs_metadata_same final_state_abs initial_state_abs
              /\ Zlength value = Z.of_nat SHA256.DigestLength
            ) &&
           (hmac256drbgabs_common_mpreds shc final_state_abs
             (*initial_state*) ((IS1a,(IS1b,IS1c)),(IS2,(IS3,(IS4,(IS5,IS6)))))
              ctx info_contents)
         );
        (data_at_ Tsh (tarray tuchar 32) K);
        (da_emp sha (tarray tuchar (Zlength contents)) (map Vubyte contents) additional);
        (data_at_ Tsh (tarray tuchar 1) sep );
        (K_vector gv)
         )
  ). (* 2 *)
  {
    (* Int.min_signed <= 0 <= rounds *)
    rewrite Heqrounds; destruct na; auto.
  }
  {
    (* rounds <= Int.max_signed *)
    rewrite Heqrounds; destruct na; auto.
  }
  {
    (* pre conditions imply loop invariant *)
    entailer!.
    Exists (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs) initial_state_abs.
    destruct initial_state_abs. simpl. Time entailer!.
    thaw FR2. thaw FR1. thaw FR0. cancel.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state. cancel.
    unfold hmac256drbg_relate. entailer!.
  }
  {
    (* loop body *)
    Intros key value state_abs.
    clear FR2 FR1 FR0.
    + simpl.
    unfold hmac256drbgabs_common_mpreds. repeat flatten_sepcon_in_SEP.
    (*unfold hmac256drbgabs_to_state. simpl.*)
    unfold hmac256drbgabs_to_state. simpl. destruct state_abs. simpl in *. subst key0 value.
    abbreviate_semax. Intros.
    freeze [1;2;3;5;6] FR0.
    unfold_data_at 1%nat. thaw FR0.
    freeze [7;8;9;10] OtherFields.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]); simpl.
    rewrite (field_at_data_at _ _ [StructField _V]); simpl.

    freeze [0;1;2;3;4;5;8] FR1.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx) as FC_ctx_MDCTX by entailer!.
    assert (FA_ctx_MDCTX: field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx = ctx).
    { unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. rewrite offset_val_force_ptr. destruct ctx; try contradiction. reflexivity.
    }
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx) as FC_ctx_V by entailer!.
    assert (FA_ctx_V: field_address t_struct_hmac256drbg_context_st [StructField _V] ctx = offset_val 12 ctx).
    { unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      reflexivity.
    }
    thaw FR1.
    unfold hmac256drbg_relate. unfold md_full.

    (* sep[0] = sep_value; *)
    freeze [0;1;2;3;5;6;7;8] FR2.
    forward.
    thaw FR2. freeze [0;1;4;6;8;9] FR3.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    Time forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), shc, key, gv). 
    {unfold md_full; simpl; cancel. }
    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    thaw FR3. rewrite <- H9. freeze [3;4;5;6;8] FR4.
    Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), shc,
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, shc,
                       @nil byte, V, gv). 
    {
      rewrite H9.
      repeat split; auto.
    }
    Intros. 
    simpl.
    assert (Hiuchar: Int.zero_ext 8 (Int.repr i) = Int.repr i).
    {
      clear - H4 Heqrounds. destruct na; subst;
      apply zero_ext_inrange; simpl; rewrite Int.unsigned_repr;  rep_omega.
    }

    (* mbedtls_md_hmac_update( &ctx->md_ctx, sep, 1 ); *)
    thaw FR4. freeze [2;4;5;6;7] FR5.
    unfold upd_Znth, sublist. simpl. rewrite Hiuchar; clear Hiuchar.
    Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), shc, sep, Tsh, V, [Byte.repr i], gv). 
     { simpl map. unfold Vubyte. rewrite Byte.unsigned_repr. cancel.
       clear - Heqrounds H4. destruct na; rep_omega.
     }
(*   rewrite <- (data_at_share_join _ _ _ _ _ _ (join_comp_Tsh shc)); cancel. *)
    {
      (* prove the PROP clauses *)
      rewrite H9.
      change (Zlength [i]) with 1.
      repeat split; auto.
    }
    Intros.
(*    sep_apply (data_at_share_join_W _ _ _ (tarray tuchar 1) [Vint (Int.repr i)] [Vint (Int.repr i)]  sep 
                         (join_comp_Tsh shc)); auto.
*)
    (* if( rounds == 2 ) *)
     thaw FR5.
     freeze [2;4;5;6;7] FR6.
     Time forward_if (PROP  ()
      LOCAL  (temp _sep_value (Vint (Int.repr i));
      temp _rounds (Vint (Int.repr rounds));  temp _md_len (Vint (Int.repr 32));
      temp _ctx ctx; lvar _K (tarray tuchar (Zlength V)) K;
      lvar _sep (tarray tuchar 1) sep; temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvars gv)
      SEP  (md_relate key (V ++ [Byte.repr i] ++ (if na then contents else nil)) (*md_ctx*)(IS1a, (IS1b, IS1c));
      (data_at shc t_struct_md_ctx_st (*md_ctx*)(IS1a, (IS1b, IS1c))
          (field_address t_struct_hmac256drbg_context_st
             [StructField _md_ctx] ctx));
      (K_vector gv);FRZL FR6;      
      (da_emp sha (tarray tuchar (Zlength contents))
          (map Vubyte contents) additional))
    ). (* 4.4 *)
    {
      (* rounds = 2 case *)
      destruct na; rewrite Heqrounds in *; [ clear H6 | solve [inv H6]]. 
      subst rounds. simpl in Heqna.
      assert (isptr additional) as Hisptr_add.
      { 
        destruct additional; simpl in PNadditional; try contradiction.
        subst i0; simpl in *; discriminate. trivial.
      }
      clear PNadditional.
      destruct additional; try contradiction. clear Hisptr_add.
      simpl in Heqna. destruct H1; subst add_len. 2: solve [simpl in Heqna; discriminate].
      rewrite da_emp_ptr. Intros.

      (* mbedtls_md_hmac_update( &ctx->md_ctx, additional, add_len ); *)
      Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, 
                         (*md_ctx*)(IS1a, (IS1b, IS1c)),  shc,Vptr b i0, sha, V ++ [Byte.repr i], contents, gv).
      {
        (* prove the PROP clause matches *)
        repeat split; auto; try rep_omega.
        rewrite Zlength_app; rewrite H9.
        simpl. remember (Zlength contents) as n; clear - H.
        destruct H. rewrite <- Zplus_assoc.
        unfold Int.max_unsigned in H0.
        rewrite hmac_pure_lemmas.IntModulus32 in H0; rewrite two_power_pos_equiv.
        simpl. simpl in H0.
        assert (H1: Z.pow_pos 2 61 = 2305843009213693952) by reflexivity; rewrite H1; clear H1.
        omega.
      }
      (* prove the post condition of the if statement *)
      rewrite <- app_assoc.
      rewrite H9. rewrite da_emp_ptr.
      entailer!. 
    }
    {
      (* rounds <> 2 case *)
      assert (RNDS1: rounds = 1).
      { subst rounds.
        destruct na; trivial; elim H6; trivial. }
      rewrite RNDS1 in *; clear H6 H4.
      assert (NAF: na = false).
      { destruct na; try omega. trivial. }
      rewrite NAF in *. clear Heqrounds.
      forward. rewrite H9, NAF.
      destruct additional; try contradiction; simpl in PNadditional.
      + subst i0. rewrite da_emp_null; trivial. entailer!.
      + rewrite da_emp_ptr. Intros. normalize. entailer!.
    }

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, K ); *)
    thaw FR6. freeze [3;4;5;6;8] FR8.  rewrite H9.
    rewrite data_at__memory_block. change (sizeof (*cenv_cs*) (tarray tuchar 32)) with 32.
    Intros.
    Time forward_call ((V ++ [Byte.repr i] ++ (if na then contents else [])), key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), shc, K, Tsh, gv).
        sep_apply (memory_block_data_at__tarray_tuchar Tsh K 32).
        rep_omega. cancel.
    Intros.
    freeze [0;1;2;4] FR9.
    rewrite data_at_isptr with (p:=K). Intros.
    apply vst_lemmas.isptrD in PK; destruct PK as [sk [ik HK]]; subst K.
    thaw FR9.
    replace_SEP 1 (md_empty (IS1a, (IS1b, IS1c))).
      { unfold md_full, md_empty; entailer!.
        apply UNDER_SPEC.FULL_EMPTY. }

    (* mbedtls_md_hmac_starts( &ctx->md_ctx, K, md_len ); *)
    Time forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, shc,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)),
                       (Zlength (HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key)),
                       HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key, sk, ik, Tsh, gv). 
    {
      (* prove the function parameters match up *)
      apply prop_right. 
      rewrite hmac_common_lemmas.HMAC_Zlength, FA_ctx_MDCTX; simpl.
      rewrite offset_val_force_ptr, isptr_force_ptr; trivial. auto.
    }
    rewrite hmac_common_lemmas.HMAC_Zlength. cancel. 

    {
      split3; auto.
      + (* prove that output of HMAC can serve as its key *)
        unfold spec_hmac.has_lengthK; simpl; auto. split; auto.
        rewrite hmac_common_lemmas.HMAC_Zlength. simpl. split. rep_omega. compute; auto.
    }
    Intros.
(*    match goal with |- context [data_at (Share.comp Ews) ?t ?v ?p] =>
    sep_apply (data_at_share_join_W _ _ _  t v v p (join_comp_Tsh Ews)); auto
    end.
*)

    thaw FR8.
    freeze [2;4;6;7;8] FR9.
    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    Time forward_call (HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), shc,
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, shc, 
                       @nil byte, V, gv). (*9 *)
    {
      (* prove the function parameters match up *)
      rewrite H9, FA_ctx_V. apply prop_right. destruct ctx; try contradiction.
      split; try reflexivity.
      simpl. rewrite FA_ctx_MDCTX. rewrite ptrofs_add_repr_0_r; auto.
    }
    {
      (* prove the PROP clauses *)
      rewrite H9.
      repeat split; auto.
    }
    Intros.
    rewrite H9.
    replace_SEP 2 (memory_block shc (sizeof (*cenv_cs*) (tarray tuchar 32)) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) by (entailer!; apply data_at_memory_block).
    simpl.

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    Time forward_call (V, HMAC256 (V ++ Byte.repr i::(if na then contents else [])) key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), shc,
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, shc, gv).
    change 32 with (sizeof (tarray tuchar 32)) at 1.
    rewrite memory_block_data_at__tarray_tuchar_eq by (simpl; rep_omega).
    simpl sizeof. cancel.

    Time go_lower. (*necessary due to existence of local () && in postcondition of for-rule*)
    idtac "previous timing was for go_lower (goal: 12secs)".
    apply andp_right; [ apply prop_right; repeat split; trivial |].
    Exists (HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key).

    Exists (HMAC256 V (HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key)).
    Exists (HMAC256DRBGabs (HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key)
                           (HMAC256 V (HMAC256 (V ++ [Byte.repr i] ++ (if na then contents else [])) key)) reseed_counter entropy_len prediction_resistance reseed_interval).
    normalize.
    apply andp_right.
    { apply prop_right. repeat split; eauto.
      subst initial_key initial_value.
      apply HMAC_DRBG_update_round_incremental_Z; try eassumption. omega.
      apply hmac_common_lemmas.HMAC_Zlength. }
    thaw FR9; cancel.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    unfold hmac256drbg_relate.
    rewrite hmac_common_lemmas.HMAC_Zlength. rewrite hmac_common_lemmas.HMAC_Zlength.
    
    cancel; unfold md_full; entailer!.
    repeat rewrite sepcon_assoc. rewrite sepcon_comm. apply sepcon_derives; [| apply derives_refl].
    unfold_data_at 3%nat.
    thaw OtherFields. cancel.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]).
    cancel.
  } 
  Intros key value final_state_abs.
  assert (UPD: hmac256drbgabs_hmac_drbg_update initial_state_abs (contents_with_add additional add_len contents) = final_state_abs).
  { destruct initial_state_abs; destruct final_state_abs. destruct H7 as [? [? [? ?]]]; subst.  
    clear - H1 H4. simpl in *.
    apply update_char; trivial. }
  clear H4 Heqna Heqrounds.
  (* return *)
  forward.
 
  (* prove function post condition *)
  entailer!. 
Time Qed. (*Coq8.6: 31secs*)

Lemma body_hmac_drbg_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_hmac_drbg_update hmac_drbg_update_spec.
Proof. start_function. apply BDY_update; trivial. Qed.

Require Import VST.floyd.ASTsize.
Eval compute in (ASTsize (fn_body f_mbedtls_hmac_drbg_update)).