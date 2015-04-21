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
Require Import sha.spec_hmacNK.

Definition initPostKeyNullConditional r (c:val) (k: val) h key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 
                   then (hmacstate_PreInitNull key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st keyedHMS c) *
                     (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      ctxkey)  *
                     (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                      (Vptr b ofs)))
  | _ => FF
  end.

Lemma hmac_init_part1: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(kv : val)
(h1:hmacabs)
(KL1 : l = Zlength key)
(KL2 : 0 <= l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(pad : val)
(Delta := initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
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
                   temp _key k; temp _len (Vint (Int.repr l));
                   gvar sha._K256 kv)
                   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                   `(initPostKeyNullConditional r c k h1 key (Vptr ckb ckoff));
                   `(K_vector kv))))),
@semax Espec Delta
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 0));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); lvar _pad (tarray tuchar 64) pad;
   temp _ctx c; temp _key k; temp _len (Vint (Int.repr l));
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
   `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv);
   `(initPre c k h1 key)))
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
Proof. intros.
 subst PostKeyNull.
 abbreviate_semax.
 forward_if. 
  { (* THEN*)
    simpl.  
    unfold initPre.
    assert_PROP (isptr k).  {
         entailer!. hnf in TC0. destruct key'; try contradiction.
        subst i; contradiction H; reflexivity. auto. 
    }
    make_Vptr k. clear H H0. rename b into kb; rename i into kofs.
    normalize.
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

      (*call to SHA256_Update*)
      rewrite (split_offset_array_at (Z.to_nat l))
         by (try reflexivity; subst l; rewrite ?Zlength_map, Z2Nat.id; omega). 
      rewrite firstn_same 
         by (subst l; rewrite !map_length, Zlength_correct, Nat2Z.id; omega).

      normalize. simpl in H, H0.  rewrite Zplus_0_r in H.
      rename H into OIR_kofs. rename H0 into OIR_kofs_key.
      replace_SEP 0 (`(data_block Tsh key (Vptr kb kofs))).
         unfold data_block. rewrite prop_true_andp by auto. rewrite Z2Nat.id by omega. entailer!.
      forward_call' (init_s256abs, key, Vptr cb cofs,
                Vptr kb kofs, Tsh, l, kv) ctxSha.
      { subst l. split. omega. 
        split. specialize Int.max_signed_unsigned. omega.
        apply KL3.
      }

      simpl.
      replace_SEP 3 (`emp). 
      { entailer.
        rewrite <- Zlength_correct. rewrite Z.sub_diag.        
        eapply derives_trans; try eapply data_at_data_at_.
        rewrite data_at__memory_block; [ | reflexivity | simpl; omega].
        rewrite memory_block_zero_Vptr. 
        entailer.
      }
      rename H into updAbs.

      (*Call to _SHA256_Final*)
      focus_SEP 7. unfold data_at_. 
      rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32) by omega.
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
      forward_call' (Tsh, offset_val (Int.repr 32) (Vptr ckb ckoff), 32, Int.zero) v.
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
                 clear - H10; destruct H10 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
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
               rewrite firstn_precise in H21.
                     rewrite <- H21; clear H21. trivial.
               rewrite Zlength_correct. rewrite Nat2Z.id; trivial.
             rewrite length_SHA256'; trivial.
             repeat rewrite map_length. rewrite mkKey_length; unfold SHA256.BlockSize; simpl. omega.
             repeat rewrite map_length. unfold sha_finish. inversion updAbs. rewrite <- functional_prog.SHA_256'_eq, length_SHA256'. trivial.
      }
      { apply data_at_Tarray_ext_derives. intros. 
        unfold Znth. if_tac. omega. if_tac. omega. clear H5 H6. 
        apply data_at_triv.
        assert (Z32: (Z.to_nat i < 32)%nat).
                 clear - H10; destruct H10 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                 apply YY. omega. omega.
        unfold HMAC_SHA256.mkKey. 
        assert (Kgt: Zlength key > Z.of_nat SHA256.BlockSize).  simpl; omega.
        apply Zgt_is_gt_bool in Kgt.
        rewrite Kgt. unfold HMAC_SHA256.zeroPad. repeat rewrite map_app.
        rewrite app_nth2; repeat rewrite map_length; rewrite length_SHA256'.
        { assert (ZN:(Z.to_nat 32 - SHA256.DigestLength = 0)%nat).
                    unfold SHA256.DigestLength. simpl; omega.
          rewrite ZN.
          assert (SHA32: (SHA256.BlockSize - SHA256.DigestLength)%nat = 32%nat) by reflexivity.
          rewrite SHA32; clear SHA32.
          rewrite nth_map' with (d':=Int.zero).
          rewrite nth_map' with (d':=Z0).
          { rewrite nth_list_repeat; trivial.
            assert (X: (nat_of_Z (32 + 1) = 1 + 32)%nat) by reflexivity.
            rewrite X; clear X. rewrite <- skipn_drop.
            rewrite skipn_app2.
            repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'.
            assert (NN: (32 - SHA256.DigestLength = 0)%nat) by reflexivity.
            rewrite NN, skipn_0.
            do 2 rewrite skipn_map.
            rewrite skipn_list_repeat. do 2 rewrite map_list_repeat. reflexivity.
            omega.
            repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'. 
            unfold SHA256.DigestLength. omega. }
          { rewrite length_list_repeat. omega. }
          { rewrite map_length, length_list_repeat. omega. } 
        }
        unfold SHA256.DigestLength. simpl; omega.
      }
    }
    { (* j >= len*)
      rename H into ge_64_l. 

      (*call to memcpy*)
      focus_SEP 3 2.
      unfold data_at_. 
      unfold tarray.
      assert (LL: Zlength key = Z.of_nat (Z.to_nat l)). 
       { subst l. rewrite nat_of_Z_eq; trivial. omega. }
      remember (`(data_at Tsh (Tarray tuchar 64 noattr) (default_val (Tarray tuchar 64 noattr)) pad)) as ZZ.
      rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr l). 2: omega.
      simpl.
      specialize (split_offset_array_at (Z.to_nat l)). unfold tarray; intros SOA.
      rewrite SOA; try reflexivity; clear SOA.
      Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n. simpl.
               rewrite Nat2Z.inj_add. unfold nat_of_Z. omega. 
      2: rewrite Z2Nat.id; omega.
      subst ZZ.
      normalize.
      rename H into OIR0_328. rename H0 into OIR64_328.

      rewrite firstn_app1. 2: rewrite force_lengthn_length_n; trivial.
      rewrite firstn_precise. 2: rewrite force_lengthn_length_n; trivial.
      rewrite skipn_app2. 2: rewrite force_lengthn_length_n; unfold  nat_of_Z; omega.
      rewrite force_lengthn_length_n.
      assert (X: (Z.to_nat l - nat_of_Z l = 0)%nat).
                    unfold nat_of_Z.  omega. 
      rewrite X, skipn_0, Z2Nat.id; clear X. 2: omega.
 
      remember (64 - l) as l64.
      assert  (HH: match Z.max 0 (Zlength key) with
               | 0 => 0
               | Z.pos y' => Z.pos y'
               | Z.neg y' => Z.neg y'
               end = Zlength key).
      { rewrite Z.max_r by omega. destruct (Zlength key); auto; omega. }

      forward_call' ((Tsh, Tsh), Vptr ckb ckoff, 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) v.
      { rewrite HH. entailer!. }
      { simpl; split; auto. rewrite HH. repable_signed. }
      subst v; normalize. simpl. clear HH.

      assert (l64 <= Int.max_unsigned) by MyOmega. 

      (*call memset*)
      remember (map Vint (map Int.repr key)) as CONT. 
      forward_call' (Tsh, Vptr ckb (Int.add ckoff (Int.repr l)), l64, Int.zero) vret.
      { split; auto. omega. }

      assert_PROP (isptr c); [entailer! |].
      make_Vptr c. rename b into cb; rename i into cofs; clear H.
      apply exp_right with cb; apply exp_right with cofs; apply exp_right with 1.
      unfold initPostKeyNullConditional. rewrite zeq_false by omega.
      entailer!. cancel. unfold tarray.

      destruct (zlt 64 (Zlength key)). omega. rewrite Zlength_correct in g. apply (Nat2Z.inj_ge 64) in g.
      remember (64 - Zlength key) as ZK64.
      rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr (Zlength key)). 2: omega.
      simpl. unfold nat_of_Z. rewrite Zlength_correct, Nat2Z.id.
      rewrite sepcon_comm.
      specialize (split_offset_array_at (length key) Tsh tuchar 64). unfold tarray; intros SOA.
      rewrite SOA; try reflexivity; clear SOA.
      2: rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add; omega.
      2: rewrite Zlength_correct in ge_64_l; omega.
      assert (STO: sizeof tuchar = 1) by reflexivity. rewrite STO, Z.mul_1_l. rewrite Z.mul_1_l.
      entailer!. 

      remember (64 - Zlength key) as ZK64. 
      specialize (split_offset_array_at (Z.to_nat ZK64) Tsh tuchar ZK64). intros X. unfold tarray in X. 
      rewrite X. clear X. entailer!.
      remember (64 - Zlength key) as ZK64. 
      assert (F64: false = (Zlength key >? 64)). 
      { rewrite Z.gtb_ltb. symmetry. apply Fcore_Zaux.Zlt_bool_false. omega. }
      rewrite firstn_app1. 2: rewrite force_lengthn_length_n; trivial.
      rewrite firstn_precise. 2: rewrite length_list_repeat; trivial.
      rewrite firstn_precise. 2: rewrite force_lengthn_length_n; trivial.
      assert (NULL: ZK64 - Z.of_nat (Z.to_nat ZK64) = 0).
      { rewrite Z2Nat.id. omega. omega. }
      rewrite NULL.
      rewrite skipn_short. 2: rewrite length_list_repeat; omega.
      apply derives_trans
      with (Q:=data_at Tsh (Tarray tuchar (Z.of_nat (length key)) noattr)
                  (map Vint (map Int.repr key)) (Vptr ckb ckoff) *
               data_at Tsh (Tarray tuchar (Z.of_nat (Z.to_nat ZK64)) noattr)
                  (list_repeat (Z.to_nat ZK64) (Vint Int.zero))
                  (Vptr ckb (Int.add ckoff (Int.repr (Z.of_nat (length key)))))).
      { cancel.
        eapply derives_trans; try apply data_at_data_at_.
        rewrite data_at__memory_block. simpl. entailer!.
        reflexivity. simpl. specialize Int.modulus_pos. omega.
      }
      { apply sepcon_derives.
        { apply data_at_Tarray_ext_derives. intros i I.
          apply data_at_triv. unfold Znth. if_tac. trivial. clear H.
          rewrite nth_force_lengthn.
          Focus 2. split. omega. destruct I as [Ipos I]. apply Z2Nat.inj_lt in I; trivial.
                   rewrite Nat2Z.id in I. trivial. omega.
          assert (Z32: (Z.to_nat i < length key)%nat).
                  clear - I; destruct I as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  rewrite Nat2Z.id in YY; trivial. trivial. omega. 
          apply eq_sym.
          assert (L1: (Z.to_nat i < length (HMAC_SHA256.mkKey key))%nat).
            rewrite mkKey_length; unfold SHA256.BlockSize.
            assert (Zlength key <= 64) by omega.  apply Z2Nat.inj_le in H. simpl in H.
            rewrite Zlength_correct, Nat2Z.id in H. omega.
            omega. omega.
          rewrite nth_map' with (d':=Int.zero).
          rewrite nth_map' with (d':=Int.zero).
          rewrite nth_map' with (d':=Z0); trivial.
          rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.         
          eapply mkKey_left; trivial. rewrite Zlength_correct. trivial.
          rewrite map_length; trivial. rewrite map_length; trivial.
        }
        { unfold offset_val. rewrite skipn_force_lengthn_app. rewrite Z2Nat.id.  
          rewrite HeqZK64, Zlength_correct.
          apply data_at_Tarray_ext_derives. rewrite <- Zlength_correct, <- HeqZK64.
          intros i I.
          apply data_at_triv. unfold Znth. if_tac. trivial. clear H.
          rewrite Zlength_correct.
          destruct (zlt (Z.of_nat (length key)) 0).
          rewrite <- Zlength_correct in l. omega.
          rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
          Focus 2.  rewrite length_list_repeat. apply Z2Nat.inj_lt. omega. omega. omega.
          rewrite nth_list_repeat. rewrite HeqZK64, Zlength_correct in I.
          remember (Z.to_nat i) as K; destruct K; simpl.
          rewrite nth_map' with (d':=Int.zero).
          rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.    
          rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
          rewrite mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
          rewrite map_length, mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
          rewrite nth_skipn. 
          assert (K + Z.to_nat (Z.of_nat (length key) + 1) = Z.to_nat (Z.of_nat (length key) + i))%nat.
            rewrite Z2Nat.inj_add. rewrite Z2Nat.inj_add. rewrite <- HeqK.
            remember (Z.to_nat (Z.of_nat (length key))) as u. simpl. rewrite <- plus_n_Sm. rewrite <- (plus_Snm_nSm u). omega.
            rewrite <- Zlength_correct. apply Zlength_nonneg.
            omega.
            rewrite <- Zlength_correct. apply Zlength_nonneg.
            omega.
          rewrite H; clear H.
          rewrite nth_map' with (d':=Int.zero).
          rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal. 
          rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
          rewrite mkKey_length. unfold SHA256.BlockSize. apply (Z2Nat.inj_lt _ 64). omega. omega. omega. 
          rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize. apply (Z2Nat.inj_lt _ 64). omega. omega. omega. 
          omega.
        }
      } 
      { reflexivity. }
      { rewrite Zlength_correct, length_list_repeat. omega. }
      { rewrite Z2Nat.id; omega. }
    }
  }
  { (*key == NULL*)
    revert POSTCONDITION; subst k; intro. normalize.
    forward.

    unfold initPre, initPostKeyNullConditional. simpl SEPx.
    unfold hmacstate_PreInitNull.

    assert_PROP (isptr c). entailer.
    make_Vptr c. rename b into cb; rename i into cofs; clear H.
    apply (exp_right cb). apply (exp_right cofs). apply (exp_right 0).
    rewrite if_true by auto.
    entailer.
    apply (exp_right r). cancel. apply (exp_right v). entailer!. 
  }
Qed.




