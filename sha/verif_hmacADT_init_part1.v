Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac_NK.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmacADT.

Require Import verif_hmacADT_init_part1_5.

(*now in part 1_5
Definition initPostKeyNullConditional l r (c:val) (k: val) h key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 
                   then (hmacstate_PreInitNull key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else EX ll:_, EX CONT:_,
                      !!(Forall isbyteZ key /\ has_lengthK ll key /\ l = Vint(Int.repr ll)) &&
                    ((data_at Tsh t_struct_hmac_ctx_st CONT c) *
                     (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      ctxkey) *
                     (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                      (Vptr b ofs)))
  | _ => FF
  end. 
*)

Lemma hmac_init_part1: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : val)
(key : list Z)
(kv : val)
(h1 : hmacabs)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(pad : val)
(ckb : block)
(ckoff : int)
(PostKeyNull : environ -> mpred)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb : block,
                 (EX  cofs : int,
                  (EX  r : Z,
                   PROP  (c = Vptr cb cofs /\ (r = 0 \/ r = 1))
                   LOCAL  (temp _reset (Vint (Int.repr r));
                   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                   lvar _pad (tarray tuchar 64) pad; temp _ctx c;
                   temp _key k; temp _len l; gvar sha._K256 kv)
                   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                   `(initPostKeyNullConditional l r c k h1 key
                       (Vptr ckb ckoff)); `(K_vector kv))))),
semax
  (initialized_list [_reset]
     (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 0));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k; temp _len l;
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
   `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv);
   `(initPre l c k h1 key)))
  (Sifthenelse
     (Ebinop One (Etempvar _key (tptr tuchar))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
     (Ssequence (Sset _reset (Econst_int (Int.repr 1) tint))
        (Ssequence (Sset _j (Econst_int (Int.repr 64) tint))
           (Sifthenelse
              (Ebinop Olt (Etempvar _j tint) (Etempvar _len tint) tint)
              (Ssequence
                 (Scall None
                    (Evar _SHA256_Init
                       (Tfunction (Tcons (tptr t_struct_SHA256state_st) Tnil)
                          tvoid cc_default))
                    [Eaddrof
                       (Efield
                          (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                             t_struct_hmac_ctx_st) _md_ctx
                          t_struct_SHA256state_st)
                       (tptr t_struct_SHA256state_st)])
                 (Ssequence
                    (Scall None
                       (Evar _SHA256_Update
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                t_struct_hmac_ctx_st) _md_ctx
                             t_struct_SHA256state_st)
                          (tptr t_struct_SHA256state_st);
                       Etempvar _key (tptr tuchar); Etempvar _len tint])
                    (Ssequence
                       (Scall None
                          (Evar _SHA256_Final
                             (Tfunction
                                (Tcons (tptr tuchar)
                                   (Tcons (tptr t_struct_SHA256state_st) Tnil))
                                tvoid cc_default))
                          [Evar _ctx_key (tarray tuchar 64);
                          Eaddrof
                            (Efield
                               (Ederef
                                  (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                  t_struct_hmac_ctx_st) _md_ctx
                               t_struct_SHA256state_st)
                            (tptr t_struct_SHA256state_st)])
                       (Scall None
                          (Evar _memset
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Eaddrof
                             (Ederef
                                (Ebinop Oadd
                                   (Evar _ctx_key (tarray tuchar 64))
                                   (Econst_int (Int.repr 32) tint)
                                   (tptr tuchar)) tuchar) (tptr tuchar);
                          Econst_int (Int.repr 0) tint;
                          Econst_int (Int.repr 32) tint]))))
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction
                          (Tcons (tptr tvoid)
                             (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Evar _ctx_key (tarray tuchar 64);
                    Etempvar _key (tptr tuchar); Etempvar _len tint])
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Eaddrof
                       (Ederef
                          (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                             (Etempvar _len tint) (tptr tuchar)) tuchar)
                       (tptr tuchar); Econst_int (Int.repr 0) tint;
                    Ebinop Osub (Econst_int (Int.repr 64) tuint)
                      (Etempvar _len tint) tuint]))))) Sskip)
  (normal_ret_assert PostKeyNull).
Proof. intros. abbreviate_semax.
forward_if PostKeyNull.
  { (* THEN*)
    simpl.  
    unfold initPre.
    assert_PROP (isptr k).  {
         entailer!. hnf in TC0. destruct key'; try contradiction.
        subst i; contradiction H; reflexivity. auto. 
    }
    make_Vptr k. clear H H0. rename b into kb; rename i into kofs.
    normalize. intros ll. normalize. intros Ctx. normalize. 
    destruct H as [KL1 [KL2 KL3]]. 
    subst ll.
(*    assert_PROP (isptr c). { entailer!. }
    apply isptrD in H. destruct H as [cb [cofs CC]]; subst c.
    rename b into kb; rename i into kofs.*)
    assert_PROP (Forall isbyteZ key).
      { unfold data_block. entailer!. }
    rename H into isbyte_key. 
    unfold data_block; rewrite prop_true_andp by auto. 
    forward v. subst v. 
    forward. (*j=HMAC_MAX_MD_CBLOCK*)
    simpl.
    forward_if.
    { (* j < len*) 
      rename H into lt_64_l.

      (*call to SHA256_init*)
      unfold data_at_ at 1. simpl default_val. 
      unfold_data_at 1%nat.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
         entailer!. rename H into FC.
      make_Vptr c. rename b into cb; rename i into cofs.
      unfold field_address; rewrite if_true by auto.
      normalize.
      forward_call' (Vptr cb cofs).
      { assert (FR: Frame = [
         field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd Ctx))
           (Vptr cb cofs);
         field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] (snd (snd Ctx))
           (Vptr cb cofs);
         data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
           (Vptr kb kofs); data_at_ Tsh (tarray tuchar 64) pad;
         data_at Tsh (tarray tuchar 64) [] (Vptr ckb ckoff); K_vector kv ]).
          subst Frame; reflexivity.
        rewrite FR; clear FR Frame. simpl; normalize. cancel.
        assert (XX: nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx]
                 = sha.t_struct_SHA256state_st). unfold nested_field_type2; simpl. unfold sha.t_struct_SHA256state_st. 
            admit. (*TODO: TYPES/NAMES*)
        erewrite data_at_type_changable. 2: eassumption. 2: eapply JMeq.JMeq_refl.
        cancel.
      }
      normalize.

      (*call to SHA256_Update*)
      rewrite (split_offset_array_at (Z.to_nat (Zlength key)))
         by (try reflexivity; subst l; rewrite ?Zlength_map, Z2Nat.id; omega). 
      rewrite firstn_same 
         by (subst l; rewrite !map_length, Zlength_correct, Nat2Z.id; omega).

      normalize. simpl in H, H0. rewrite Zplus_0_r in H.
      rename H into OIR_kofs. rename H1 into OIR_kofs_key.
      rename H0 into KL1.
      replace_SEP 0 (`(data_block Tsh key (Vptr kb kofs))).
         unfold data_block. rewrite prop_true_andp by auto. rewrite Zlength_correct. entailer!.
      forward_call' (init_s256abs, key, Vptr cb cofs,
                Vptr kb kofs, Tsh, Zlength key, kv) ctxSha.
      { split. omega. 
        split. specialize Int.max_signed_unsigned. omega.
        apply KL3.
      }

      simpl. rename H into updAbs. 
      assert (L: length key = length (map Vint (map Int.repr key))).
        repeat rewrite map_length; trivial.
      specialize (skipn_exact_length (map Vint (map Int.repr key))).
      rewrite <- L. unfold skipn; intros SEL; rewrite SEL; clear SEL.
      rewrite firstn_same in updAbs.
      Focus 2. rewrite Zlength_correct, Nat2Z.id. omega.

      replace_SEP 3 (`emp). 
      { entailer.
        rewrite <- Zlength_correct. rewrite Z.sub_diag.        
        eapply derives_trans; try eapply data_at_data_at_.
        rewrite data_at__memory_block.
        rewrite memory_block_zero_Vptr. entailer!.
        reflexivity. simpl. specialize Int.modulus_pos; omega.
      }

     (*call SHA256_Final*)
(*     assert_PROP(isptr ctxkey). entailer!.
     apply isptrD in H; destruct H as [ckb [ckoff X]]; subst ctxkey.*)
     rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32). 2: omega.
     simpl.
     specialize (split_offset_array_at 32). unfold tarray; intros SOA.
     rewrite SOA; try reflexivity; simpl; clear SOA.
            2: rewrite Zlength_correct; simpl; omega.
            2: omega. 
     normalize. rename H into BND1; rename H0 into BND2; rename H1 into BND3.
     forward_call' (ctxSha, Vptr ckb ckoff, Vptr cb cofs, Tsh, kv).

     (*call memset*) 
     replace_SEP 3 (`(memory_block Tsh (Int.repr 32) (offset_val (Int.repr 32) (Vptr ckb ckoff)))).
     { entailer!. }
     forward_call' (Tsh, offset_val (Int.repr 32) (Vptr ckb ckoff), 32, Int.zero) vret.
     { (*subst PostIf_j_Len.*)
       subst PostKeyNull.
       apply (exp_right cb).
       apply (exp_right cofs).
       apply (exp_right 1).
       unfold initPostKeyNullConditional.
       rewrite if_false by omega.
       unfold data_block.
       set (z32 := (list_repeat (Z.to_nat 32) (Vint Int.zero))).
       change (Z.of_nat 32) with 32%Z.
       entailer.
       fold (tarray tuchar 64). cancel. 
       apply (exp_right (Zlength key)). cancel.
       apply (exp_right (default_val t_struct_hmac_ctx_st)).
       unfold has_lengthK; entailer. cancel.
       unfold_data_at 3%nat. cancel.
       assert (SFL: Zlength  (sha_finish ctxSha) = 32).
       { destruct ctxSha. simpl. rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity. } 
       rewrite SFL.   
       rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
       simpl. 
       rewrite field_address_clarify by auto.
       unfold nested_field_type2, nested_field_offset2. simpl.
       normalize. cancel.
       unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32) by omega.
       specialize (split_offset_array_at 32). unfold tarray; intros SOA.
       rewrite SOA with (len :=64)(v:=Vptr ckb ckoff); try reflexivity; clear SOA.
       Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add, nat_of_Z_eq.
                assert (HZ: Z.of_nat 32=32) by reflexivity. rewrite HZ; clear HZ. omega.
                omega.
       2: simpl; omega.
       entailer.
       apply andp_right. apply prop_right. split; rewrite Zplus_0_r; trivial.
       rewrite firstn_app1.
       Focus 2. rewrite force_lengthn_length_n. simpl; omega. 
       rewrite firstn_same. 
       Focus 2. rewrite force_lengthn_length_n. simpl; omega. 
       assert (NZ: nat_of_Z 32 = 32%nat) by reflexivity. rewrite NZ; clear NZ.
       rewrite skipn_force_lengthn_app.
       assert (SF:64 - Z.of_nat 32 = 32) by reflexivity. rewrite SF; clear SF.
       rewrite sepcon_comm. 
       apply sepcon_derives. 
       { apply data_at_Tarray_ext_derives. intros. 
              unfold Znth. if_tac. omega.
              assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H3; destruct H3 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
         apply data_at_triv.
         rewrite nth_force_lengthn. 2: simpl; omega.
         rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
         rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
         repeat rewrite map_nth. f_equal. f_equal. unfold sha_finish. destruct ctxSha.
         unfold HMAC_SHA256.mkKey. simpl. 
              assert (Z6: Zlength key > 64) by omega. 
              apply Zgt_is_gt_bool in Z6; rewrite Z6.
              unfold HMAC_SHA256.zeroPad.
              rewrite <- functional_prog.SHA_256'_eq.
              rewrite app_nth1. inversion updAbs. subst. clear updAbs. simpl in *.
                      rewrite <- H21. trivial.
              rewrite length_SHA256'; trivial.
              repeat rewrite map_length. rewrite mkKey_length; unfold SHA256.BlockSize; simpl. omega.
              repeat rewrite map_length. unfold sha_finish. inversion updAbs. rewrite <- functional_prog.SHA_256'_eq, length_SHA256'. trivial.
       }
       { apply data_at_Tarray_ext_derives. intros. 
         unfold Znth. if_tac. omega. if_tac. omega. clear H5 H6. 
         apply data_at_triv.
         assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H3; destruct H3 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
         unfold HMAC_SHA256.mkKey. 
               assert (Kgt: Zlength key > Z.of_nat SHA256.BlockSize).  simpl; omega.
               apply Zgt_is_gt_bool in Kgt.
               rewrite Kgt. unfold HMAC_SHA256.zeroPad. repeat rewrite map_app.
               rewrite app_nth2; repeat rewrite map_length; rewrite length_SHA256'.
                 assert (ZN:(Z.to_nat 32 - SHA256.DigestLength = 0)%nat).
                            unfold SHA256.DigestLength. simpl; omega.
                 rewrite ZN.
                 assert (SHA32: (SHA256.BlockSize - SHA256.DigestLength)%nat = 32%nat) by reflexivity.
                 rewrite SHA32; clear SHA32.
                 rewrite nth_map' with (d':=Int.zero).
                   rewrite nth_map' with (d':=Z0).
                     rewrite nth_list_repeat; trivial.
                 assert (X: (nat_of_Z (32 + 1) = 1 + 32)%nat) by reflexivity.
                 rewrite X; clear X. rewrite <- skipn_drop.
                 rewrite skipn_app2.
                   repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'.
                   assert (NN: (32 - SHA256.DigestLength = 0)%nat) by reflexivity. rewrite NN.
                 rewrite skipn_0.
                 do 2 rewrite skipn_map.
                rewrite skipn_list_repeat. do 2 rewrite map_list_repeat. reflexivity.
                omega.
                repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'. 
                   unfold SHA256.DigestLength. omega. 
                rewrite length_list_repeat. omega. 
                rewrite map_length, length_list_repeat. omega. 
                unfold SHA256.DigestLength. simpl; omega.
       }
     }
   }

   { (* j >= len*)
     rename H into ge_64_l.
     semax_subcommand HmacVarSpecs HmacFunSpecs f_HMAC_Init. 
     eapply hmac_init_part1_5; try eassumption.
   }
 } 
(*
   intros. 
   entailer!. unfold POSTCONDITION, abbreviate; simpl. entailer!.
   unfold overridePost, initPostKeyNullConditional. 
   if_tac; trivial.
   entailer!.
     apply (exp_right cb). apply andp_right. entailer!.
   entailer!.
     apply (exp_right cofs). normalize. clear H. 
     apply (exp_right 1). entailer!.
     if_tac. omega. apply (exp_right ll).
     apply (exp_right x). entailer!. 
  }*)
  { (*key == NULL*)
     forward. normalize. rewrite HeqPostKeyNull. clear  HeqPostKeyNull. normalize.
     entailer!.
     unfold initPre, initPostKeyNullConditional. simpl.
     (*destruct key'; try contradiction; simpl in *; subst; simpl in *.*)
     (*integer*)
        unfold hmacstate_PreInitNull. normalize. rewrite data_at_isptr.
        normalize. apply isptrD in Pctx'. destruct Pctx' as [cb [cofs CTX']].
        subst; simpl in *. 
        apply (exp_right cb).
        apply (exp_right cofs).
        apply (exp_right 0). entailer!.
        if_tac; try omega. cancel.
          apply (exp_right r). cancel. 
          apply (exp_right v). entailer!.
(*     inversion H.*)
  }
  { (*side condition of forward_if key != NULL*)
    intros. entailer!. unfold overridePost, normal_ret_assert; simpl. 
    if_tac. simpl. unfold POSTCONDITION, abbreviate, normal_ret_assert.
       entailer!. trivial.
  }
Qed.













