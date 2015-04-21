Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac091c.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmac.

Definition initPostKeyNullConditional r (c:val) (k: val) h key : mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) c) *
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
(Delta := (initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)))
(PostKeyNull : environ -> mpred)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb : block,
                 (EX  cofs : int,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (temp _reset (Vint (Int.repr r));
                      lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k;
                      temp _len (Vint (Int.repr l));
                      gvar sha._K256 kv)
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector kv))))),
@semax Espec Delta
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 0)); lvar _pad (tarray tuchar 64) pad;
     temp _ctx c; temp _key k; temp _len (Vint (Int.repr l));
     gvar sha._K256 kv)
   SEP 
   (`(data_at_ Tsh (tarray tuchar 64) pad);
   `(K_vector kv); `(initPre c k h1 key)))
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
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st) Tnil)
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
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
                                      (Tcons (tptr t_struct_SHA256state_st)
                                         Tnil)) tvoid cc_default))
                             [Efield
                                (Ederef
                                   (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                   t_struct_hmac_ctx_st) _key
                                (tarray tuchar 64);
                             Eaddrof
                               (Efield
                                  (Ederef
                                     (Etempvar _ctx
                                        (tptr t_struct_hmac_ctx_st))
                                     t_struct_hmac_ctx_st) _md_ctx
                                  t_struct_SHA256state_st)
                               (tptr t_struct_SHA256state_st)])
                          (Ssequence
                             (Scall None
                                (Evar _memset
                                   (Tfunction
                                      (Tcons (tptr tvoid)
                                         (Tcons tint (Tcons tuint Tnil)))
                                      (tptr tvoid) cc_default))
                                [Eaddrof
                                   (Ederef
                                      (Ebinop Oadd
                                         (Efield
                                            (Ederef
                                               (Etempvar _ctx
                                                  (tptr t_struct_hmac_ctx_st))
                                               t_struct_hmac_ctx_st) _key
                                            (tarray tuchar 64))
                                         (Econst_int (Int.repr 32) tint)
                                         (tptr tuchar)) tuchar) (tptr tuchar);
                                Econst_int (Int.repr 0) tint;
                                Econst_int (Int.repr 32) tint])
                             (Sassign
                                (Efield
                                   (Ederef
                                      (Etempvar _ctx
                                         (tptr t_struct_hmac_ctx_st))
                                      t_struct_hmac_ctx_st) _key_length tuint)
                                (Econst_int (Int.repr 32) tint))))))
                 (Ssequence
                    (Scall None
                       (Evar _memcpy
                          (Tfunction
                             (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             (tptr tvoid) cc_default))
                       [Efield
                          (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                             t_struct_hmac_ctx_st) _key (tarray tuchar 64);
                       Etempvar _key (tptr tuchar); Etempvar _len tint])
                    (Ssequence
                       (Scall None
                          (Evar _memset
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Eaddrof
                             (Ederef
                                (Ebinop Oadd
                                   (Efield
                                      (Ederef
                                         (Etempvar _ctx
                                            (tptr t_struct_hmac_ctx_st))
                                         t_struct_hmac_ctx_st) _key
                                      (tarray tuchar 64))
                                   (Etempvar _len tint) (tptr tuchar)) tuchar)
                             (tptr tuchar); Econst_int (Int.repr 0) tint;
                          Ebinop Osub (Econst_int (Int.repr 64) tuint)
                            (Etempvar _len tint) tuint])
                       (Sassign
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                t_struct_hmac_ctx_st) _key_length tuint)
                          (Etempvar _len tint))))))) Sskip)
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
      { unfold data_block. entailer. }
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

   (*call Final*)
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]) by reflexivity.
   
(*      (*new: extract info from field_address as early as possible*)
      assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _key] (Vptr cb cofs)).
         entailer. 
      rename H into f.
*)
   unfold nested_field_offset2, nested_field_type2; simpl.
   (*now:*) unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32) by omega.
            change (force_lengthn (nat_of_Z 32) [] (default_val tuchar) ++
                              Znth 32 [] (default_val tuchar)  :: skipn (nat_of_Z (32 + 1)) [])
            with (list_repeat 33 Vundef).
            specialize (split_offset_array_at 32). unfold tarray; intros SOA.
            rewrite SOA; try reflexivity. clear SOA.
               2: rewrite Zlength_correct; simpl; omega.
               2: simpl; omega.
   change (firstn 32 (list_repeat 33 Vundef)) with (list_repeat 32 Vundef).
   change (skipn 32 (list_repeat 33 Vundef)) with [Vundef].
   normalize.
   rename H into BND1; rename H0 into BND2.

   (*Call to _SHA256_Final*)
   forward_call' (ctxSha, (field_address t_struct_hmac_ctx_st [StructField _key] (Vptr cb cofs)),
                  Vptr cb cofs, Tsh, kv).
     entailer!. unfold field_address; rewrite if_true by auto. reflexivity.
   normalize.

   (*call memset*)
   forward_call' (Tsh, (offset_val (Int.repr (Z.of_nat 32))
          (field_address t_struct_hmac_ctx_st [StructField _key]
             (Vptr cb cofs))), 32, Int.zero) v.
    entailer!.  unfold field_address; rewrite if_true by auto. 
    normalize; reflexivity.
   normalize. subst v.

   forward. (*ctx->key_length=32*)
   apply exp_right with cb; apply exp_right with cofs; apply exp_right with 1.
   unfold initPostKeyNullConditional.
   rewrite if_false by omega.
   unfold data_block.
   set (z32 := (list_repeat (Z.to_nat 32) (Vint Int.zero))).
   change (Z.of_nat 32) with 32%Z.
   entailer.
   fold (tarray tuchar 64). 
   unfold_data_at 4%nat.
   rewrite if_true by omega.
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
   cancel.
   unfold nested_field_type2; simpl.


   unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32). 2: omega.
   specialize (split_offset_array_at 32). unfold tarray; intros SOA.
   rewrite SOA with (len:=64); auto; clear SOA.
       Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add, nat_of_Z_eq.
                assert (TT: Z.of_nat 32=32) by reflexivity. rewrite TT; clear TT. omega.
                omega.
    entailer.
     rewrite firstn_app1.
     Focus 2. rewrite force_lengthn_length_n. simpl; omega. 
     rewrite firstn_same. 
     Focus 2. rewrite force_lengthn_length_n. simpl; omega. 
     assert (LengthShaFinish: Zlength (sha_finish ctxSha) = 32).
                 unfold sha_finish. destruct ctxSha.
        rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity.
     rewrite LengthShaFinish.
     change (nat_of_Z 32) with 32%nat.
     change (64 - Z.of_nat 32) with 32.
     rewrite skipn_force_lengthn_app.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
     fold (tarray tuchar 32).
     unfold HMAC_SHA256.mkKey.
     assert (Z6: Zlength key > 64) by omega. 
     apply Zgt_is_gt_bool in Z6.
     change (Z.of_nat SHA256.BlockSize) with 64. rewrite Z6.
  match goal with |- _ |-- _ * data_at Tsh (tarray tuchar 32) ?A _ =>
   replace A with z32
  end.
Focus 2. {
unfold HMAC_SHA256.zeroPad.
unfold SHA256.Hash. rewrite length_SHA256'.
change (SHA256.BlockSize - SHA256.DigestLength)%nat with 32%nat.
rewrite !skipn_map.
rewrite skipn_app2
  by (rewrite length_SHA256'; compute; omega).
unfold Znth.
rewrite if_false by omega.
rewrite !map_app.
rewrite app_nth2 by (rewrite !map_length, length_SHA256'; compute; omega).
rewrite !map_length, length_SHA256'.
reflexivity.
} Unfocus.
 change (Z.of_nat 32) with 32.
 fold (tarray tuchar 32).
assert (sha_finish ctxSha ++ list_repeat 32 0 = HMAC_SHA256.zeroPad (SHA256.Hash key)). {
  clear - lt_64_l H2 updAbs.
  inv updAbs. 
  unfold sha_finish. simpl. rewrite <- H8; simpl.
   rewrite firstn_same by (rewrite Zlength_correct, Nat2Z.id; auto).
   unfold HMAC_SHA256.zeroPad.
  unfold SHA256.Hash. rewrite length_SHA256'.
  f_equal. rewrite functional_prog.SHA_256'_eq; auto. 
}
rewrite <- H8.
assert (length (sha_finish ctxSha) = 32)%nat
 by (apply Nat2Z.inj; rewrite  <- Zlength_correct, LengthShaFinish; auto).
rewrite force_lengthn_long
  by (rewrite !map_length, app_length, length_list_repeat; omega).
rewrite !firstn_map.
rewrite firstn_app1 by omega.
rewrite firstn_same by omega.
cancel.
unfold field_address; rewrite if_true by auto.
simpl offset_val; normalize.
}
   { (* j >= len*)
     rename H into ge_64_l. 

     (*call to memcpy*)
     focus_SEP 0 2.
     unfold data_at_. 
     unfold_data_at 1%nat.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
     unfold nested_field_offset2, nested_field_type2; simpl. 
     unfold tarray.
     remember (`(data_at Tsh (Tarray tuchar 64 noattr) [] pad)) as ZZ.
     rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr l). 2: omega.
     simpl.
     specialize (split_offset_array_at (Z.to_nat l)). unfold tarray; intros SOA.
     rewrite SOA; try reflexivity; clear SOA.
     Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n. simpl. 
                       rewrite Nat2Z.inj_add. repeat rewrite nat_of_Z_eq; omega.
     2:rewrite Z2Nat.id; omega.
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
         rewrite Z.max_r by omega. destruct (Zlength key); auto; omega.

     (*Call to memcpy*)
     forward_call' ((Tsh, Tsh), (field_address t_struct_hmac_ctx_st [StructField _key] c), 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) v.
     { rewrite HH. entailer!.
       unfold field_address; rewrite if_true by auto; reflexivity. }
     { simpl; split; auto. rewrite HH. repable_signed. }
     subst v; normalize. simpl. clear HH.

     assert (l64 <= Int.max_unsigned) by MyOmega. 

     (*call memset*)
     remember (map Vint (map Int.repr key)) as CONT. 
     forward_call' (Tsh, offset_val (Int.repr (Zlength key)) (field_address t_struct_hmac_ctx_st [StructField _key] c), l64, Int.zero) v.
     { entailer!. unfold field_address; rewrite if_true by auto. 
       f_equal. unfold nested_field_offset2. simpl. rewrite offset_offset_val.
       f_equal. rewrite add_repr. reflexivity. }
     { rewrite <- KL1. cancel. }
     { split; auto. omega. }

     simpl map.
     assert_PROP (isptr c); [entailer! |].
     forward. (*ctx->key_length=len*)
     make_Vptr c. rename b into cb; rename i into cofs; clear H.
     apply exp_right with cb; apply exp_right with cofs; apply exp_right with 1.
     unfold initPostKeyNullConditional. rewrite zeq_false by omega.
     entailer. cancel.
     unfold_data_at 3%nat. rewrite if_false by omega.
     cancel.
     clear TC0 h1.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
     remember (64 - Zlength key) as ZK64. 
     unfold nested_field_offset2, nested_field_type2; simpl.
     unfold tarray.
     rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr (Zlength key)). 2: omega.
              simpl. unfold nat_of_Z. rewrite Zlength_correct, Nat2Z.id.
              specialize (split_offset_array_at (length key) Tsh tuchar 64). unfold tarray; intros SOA.
              rewrite SOA; try reflexivity; clear SOA.
     2: rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add; omega.
     2: rewrite Zlength_correct in ge_64_l; omega.
     entailer.
     assert (F64: false = (Zlength key >? 64)). 
       rewrite Z.gtb_ltb. symmetry. apply Fcore_Zaux.Zlt_bool_false. omega.
     rewrite sepcon_comm.
     apply sepcon_derives.
     { rewrite firstn_app1. 2: rewrite force_lengthn_length_n; trivial.
       rewrite firstn_precise. 2: rewrite force_lengthn_length_n; trivial.
       apply data_at_Tarray_ext_derives. intros i I.
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
         rewrite map_length; trivial.
       rewrite map_length; trivial.
     }
     { rewrite skipn_force_lengthn_app.
       rewrite  Zlength_correct.
       apply data_at_Tarray_ext_derives. intros i I.
       apply data_at_triv. unfold Znth. if_tac. trivial.
       rewrite if_false by omega.
       rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
       Focus 2.  rewrite length_list_repeat. apply Z2Nat.inj_lt. omega. omega. omega.
       rewrite nth_list_repeat.
       remember (Z.to_nat i) as K; destruct K; simpl.
         rewrite nth_map' with (d':=Int.zero).
           rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.     
             rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
           rewrite mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
         rewrite map_length, mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
       rewrite nth_skipn. 
       assert (KK: (K + Z.to_nat (Z.of_nat (length key) + 1) = Z.to_nat (Z.of_nat (length key) + i))%nat).
       { rewrite Z2Nat.inj_add. rewrite Z2Nat.inj_add. rewrite <- HeqK.
         remember (Z.to_nat (Z.of_nat (length key))) as u. simpl. rewrite <- plus_n_Sm. rewrite <- (plus_Snm_nSm u). omega.
         rewrite <- Zlength_correct. apply Zlength_nonneg.
         omega.
         rewrite <- Zlength_correct. apply Zlength_nonneg.
         omega.
       }
       rewrite KK; clear KK.
       rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal. 
           rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
         rewrite mkKey_length. unfold SHA256.BlockSize.
           apply (Z2Nat.inj_lt _ 64); omega.
       rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize.
         apply (Z2Nat.inj_lt _ 64); omega.
     }
   }
 }
 { (*key == NULL*)
   revert POSTCONDITION; subst k; intro.
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



















