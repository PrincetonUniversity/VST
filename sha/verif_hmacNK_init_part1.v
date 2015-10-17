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

Require Import split_array_lemmas. (*TODO: move this file to floyd?*)

Lemma Zlength_list_repeat {A} n (v:A): Zlength (list_repeat n v) = Z.of_nat n.
Proof. rewrite Zlength_correct, length_list_repeat; trivial. Qed. 
(*from tweetnaclbase*)

Definition initPostKeyNullConditional r (c:val) (k: val) h key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 
                   then (hmacstate_PreInitNull key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st (*keyed*)HMS c) *
                     (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      ctxkey)  *
                     (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                      (Vptr b ofs)))
  | _ => FF
  end.

Definition hmac_init_part1_FRAME1 key kb kofs cb cofs pad : mpred :=  
   (data_at_ Tsh (Tarray tuchar 64 noattr) pad) *
   (field_at Tsh t_struct_hmac_ctx_st [StructField 14%positive]
       (fst (snd (default_val t_struct_hmac_ctx_st))) (Vptr cb cofs)) *
   (field_at Tsh t_struct_hmac_ctx_st [StructField 15%positive]
       (snd (snd (default_val t_struct_hmac_ctx_st))) (Vptr cb cofs)) *
   (data_block Tsh key (Vptr kb kofs)).
Opaque hmac_init_part1_FRAME1.

Definition hmac_init_part1_FRAME2 cb cofs := data_at Tsh
       (nested_field_type2 t_struct_hmac_ctx_st [StructField 13%positive])
       (fst (default_val t_struct_hmac_ctx_st))
       (field_address t_struct_hmac_ctx_st [StructField 13%positive]
          (Vptr cb cofs)). 
Opaque hmac_init_part1_FRAME2.

Lemma Init_part1_keynonnull Espec (kb ckb cb: block) (kofs ckoff cofs:int) l key kv pad: forall h1
(KL1 : l = Zlength key)
(KL2 : 0 <= l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
PostKeyNull
(HeqPostKeyNull : PostKeyNull =
                 EX  cb0 : block,
                 (EX  cofs0 : int,
                  (EX  r : Z,
                   PROP  (Vptr cb cofs = Vptr cb0 cofs0 /\ (r = 0 \/ r = 1))
                   LOCAL  (temp _reset (Vint (Int.repr r));
                   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                   lvar _pad (tarray tuchar 64) pad;
                   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
                   temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
                   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                   `(initPostKeyNullConditional r (Vptr cb cofs)
                       (Vptr kb kofs) h1 key (Vptr ckb ckoff));
                   `(K_vector kv)))))
(isbyte_key : Forall isbyteZ key)
(HMS' : reptype t_struct_hmac_ctx_st)
(KHMS : HMS' = HMS)
(PostIf_j_Len : environ -> mpred)
(HeqPostIf_j_Len : PostIf_j_Len =
                  PROP  ()
                  LOCAL  (temp _reset (Vint (Int.repr 1));
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
                  temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
                  SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                  `(data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs));
                  `(data_at Tsh (tarray tuchar (Zlength key))
                      (map Vint (map Int.repr key)) (Vptr kb kofs));
                  `(data_at Tsh (tarray tuchar 64)
                      (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      (Vptr ckb ckoff)); `(K_vector kv)))
(FC_ctx : field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
(FC_md_ctx : field_compatible t_struct_hmac_ctx_st [StructField _md_ctx]
              (Vptr cb cofs))
(FC_cxtkey : field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff))
(lt_64_l : 64 < l),
@semax CompSpecs Espec (initialized_list [_reset; _j]
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 64)); temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
   temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs)); `(data_at_ Tsh (tarray tuchar 64) pad);
   `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv)))
  (Ssequence
     (Scall None
        (Evar _SHA256_Init
           (Tfunction (Tcons (tptr t_struct_SHA256state_st) Tnil) tvoid
              cc_default))
        [Eaddrof
           (Efield
              (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                 t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
           (tptr t_struct_SHA256state_st)])
     (Ssequence
        (Scall None
           (Evar _SHA256_Update
              (Tfunction
                 (Tcons (tptr t_struct_SHA256state_st)
                    (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default))
           [Eaddrof
              (Efield
                 (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                    t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
              (tptr t_struct_SHA256state_st); Etempvar _key (tptr tuchar);
           Etempvar _len tint])
        (Ssequence
           (Scall None
              (Evar _SHA256_Final
                 (Tfunction
                    (Tcons (tptr tuchar)
                       (Tcons (tptr t_struct_SHA256state_st) Tnil)) tvoid
                    cc_default))
              [Evar _ctx_key (tarray tuchar 64);
              Eaddrof
                (Efield
                   (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                      t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
                (tptr t_struct_SHA256state_st)])
           (Scall None
              (Evar _memset
                 (Tfunction
                    (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                    (tptr tvoid) cc_default))
              [Eaddrof
                 (Ederef
                    (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Econst_int (Int.repr 32) tint) (tptr tuchar)) tuchar)
                 (tptr tuchar); Econst_int (Int.repr 0) tint;
              Econst_int (Int.repr 32) tint]))))
  (overridePost PostIf_j_Len
     (overridePost PostKeyNull (normal_ret_assert PostKeyNull))).
Proof. intros. abbreviate_semax.
      (*call to SHA256_init*)
(*      remember (`(data_at_ Tsh (tarray tuchar 64) pad)) as PAD.*)
      unfold data_at_ at 1. unfold field_at_ at 1.
      Opaque default_val. unfold_field_at 1%nat. normalize. Transparent default_val.
      rename H into VF.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      unfold field_address. rewrite if_true; trivial.

      (*new: extract info from field_address as early as possible*)
      assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _md_ctx]
                          (Vptr cb cofs))).
      { entailer. } 
      rename H into FA_MDCTX. (*
      apply isptrD in H; destruct H as [? [? PT]]; rewrite PT.
      unfold field_address in PT.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
           (Vptr cb cofs)); inversion PT; clear PT. 
      subst x x0.
      rename f into FC.*)
(*      subst PAD. normalize.*)
      forward_call (Vptr cb cofs). (*Issue: takes 5mins...*)
      { repeat rewrite sepcon_assoc. apply sepcon_derives. 2: cancel.
        eapply derives_trans. apply data_at_data_at_. 
          unfold offset_val. simpl. unfold field_offset; simpl. unfold fieldlist.field_offset2; simpl. unfold field_type; simpl.
          rewrite Int.add_zero. apply derives_refl. }
       normalize.
      (*call to SHA256_Update*) 
      assert (MaxSignedMod: Int.max_signed < Int.modulus) by intuition. 
      assert_PROP (field_compatible (Tarray tuchar (Zlength key) noattr) [] (Vptr kb kofs)). entailer.
      rename H into FC_k.
      unfold tarray. rewrite (split2_data_at_Tarray_at_tuchar _ _ l); trivial; try omega.
      Focus 2. repeat rewrite Zlength_map; trivial.
      rewrite sublist_same; repeat rewrite Zlength_map; trivial.
 (*     normalize. simpl in H, H0. rewrite Zplus_0_r in H.
      rename H into OIR_kofs. rename H0 into OIR_kofs_key.
*)
      rewrite KL1, Zminus_diag, sublist_nil. normalize.
      replace_SEP 1 (`emp). 
      { unfold at_offset. entailer. 
        eapply derives_trans. apply data_at_data_at_.
             rewrite data_at__memory_block.
               rewrite memory_block_zero_Vptr. entailer. 
      }
      forward_call (init_s256abs, key, Vptr cb cofs, Vptr kb kofs, Tsh, l, kv) ctxSha.
      { unfold data_block. 
        (*Issue: calling entailer or normalize here yields 
             "Anomaly: undefined_evars_of_term: evar not found. Please report."*)
        assert (FR: Frame = [
         field_at Tsh t_struct_hmac_ctx_st [StructField 14%positive]
            (fst (snd (default_val t_struct_hmac_ctx_st))) (Vptr cb cofs);
         field_at Tsh t_struct_hmac_ctx_st [StructField 15%positive]
            (snd (snd (default_val t_struct_hmac_ctx_st))) (Vptr cb cofs);
         data_at_ Tsh (Tarray tuchar 64 noattr) pad;
         data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff)]).
          subst Frame; reflexivity.
        rewrite FR; clear FR Frame.
        simpl. normalize.
      }
      { clear Frame HeqPostIf_j_Len HeqPostKeyNull.
        specialize Int.max_signed_unsigned.
        subst l. intuition.
      }
      Opaque default_val.
      simpl. rename H into updAbs.
      rewrite sublist_same in updAbs; trivial.

     (*call Final*)
(*     assert_PROP(isptr ctxkey). entailer.
     apply isptrD in H; destruct H as [ckb [ckoff X]]; subst ctxkey.*)
     focus_SEP 6. unfold data_at_ at 1. unfold field_at_.
     rewrite field_at_data_at at 1. (*Issue very slow...*)
     unfold field_address. rewrite if_true. 2: assumption.
     simpl. rewrite Int.add_zero.

    assert_PROP (field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff)). normalize.
    rename H into FC_ctxkey.

     replace_SEP 0 (`(memory_block Tsh 64 (Vptr ckb ckoff))).
     { entailer!. apply data_at_memory_block. }
    
     specialize (memory_block_split Tsh ckb (Int.unsigned ckoff) 32 32).
     rewrite Int.repr_unsigned.
     assert (32 + 32 =64) by reflexivity. rewrite H. Opaque Zplus. clear H.
     intros MBS; rewrite MBS; clear MBS; trivial. 
     Focus 2. destruct (Int.unsigned_range ckoff). split; try omega.
              red in FC_ctxkey. simpl in FC_ctxkey. intuition.
     normalize. 

   gather_SEP 4 5 6 7. (*Issue: why does gather_SEP take 1min???*)  (*How can the order of arguments affect what's unfolded: try gather_SEP 7 5 6 4 instead!!*)
   replace_SEP 0 (`(hmac_init_part1_FRAME1 key kb kofs cb cofs pad)).
   { Transparent hmac_init_part1_FRAME1. unfold hmac_init_part1_FRAME1. Opaque hmac_init_part1_FRAME1.
     Transparent default_val. entailer. cancel. Opaque default_val. (*Issue: without making default_val transparent, entailer/nornmalize/entailer! here don't terminate within 1h*)
   } 
   forward_call (ctxSha, Vptr ckb ckoff, Vptr cb cofs, Tsh, kv). (*with transparent hmac_init_part1_FRAME1 it's a bit faster, but then unfolds hmac_init_part1_FRAME in the precondition of the next goal*) 
(*Issue : WAS: Transparent default_val. unfold default_val. simpl. (*Issue: adding this line is necessary to make the following forward_call terminate in < 5mins*)
     forward_call (ctxSha, Vptr ckb ckoff, Vptr cb cofs, Tsh, kv). 
  and even then the call taks significantly longer than the variant above, using hmac_init_part1_FRAME. 
   I think this means the frezzer will speed things up*)

     replace_SEP 1 (`(hmac_init_part1_FRAME2 cb cofs)).
     { Transparent hmac_init_part1_FRAME2. unfold hmac_init_part1_FRAME2. Opaque hmac_init_part1_FRAME2.
       Transparent default_val. entailer. Opaque default_val. 
       unfold data_at_, field_at_.
       rewrite field_at_data_at.
       unfold field_address. rewrite if_true; trivial. rewrite if_true; trivial. }

   (*call memset*) 
     unfold tarray in *.
     forward_call (Tsh, Vptr ckb (Int.repr (Int.unsigned ckoff + 32)), 32, Int.zero)
        vret.
     { rewrite (lvar_eval_var _ _ _ _ H0). split; trivial. }
     { subst PostIf_j_Len.
      unfold data_block.
      entailer!.
      unfold data_at at 3. 
      Transparent Z.add. unfold_field_at 1%nat. Opaque Z.add. normalize.
      unfold nested_field_type2, HMS; simpl.
      rewrite field_at_data_at at 1.  
     assert (SFL: Zlength  (sha_finish ctxSha) = 32).
        destruct ctxSha. simpl. rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity. 
     rewrite SFL.

     unfold tarray.
     assert (LK64: Zlength (HMAC_SHA256.mkKey key) = 64).
       unfold HMAC_SHA256.mkKey.
       remember (Zlength key >? Z.of_nat SHA256.BlockSize).
       destruct b; rewrite Zlength_correct, zeroPad_BlockSize. reflexivity. 
                   unfold SHA256.Hash. rewrite length_SHA256'. unfold SHA256.DigestLength, SHA256.BlockSize. omega.
       reflexivity. apply Nat2Z.inj_le.
       specialize (Zgt_cases (Zlength key) (Z.of_nat SHA256.BlockSize)). rewrite <- Heqb. rewrite Zlength_correct; trivial.
     rewrite (split2_data_at_Tarray_at_tuchar Tsh 64 32); repeat rewrite Zlength_map; trivial; try omega.
     unfold at_offset. 
     unfold HMAC_SHA256.mkKey. 
     remember (Zlength key >? Z.of_nat SHA256.BlockSize).
      destruct b.
      Focus 2. specialize (Zgt_cases (Zlength key) (Z.of_nat SHA256.BlockSize)).
               rewrite <- Heqb. intros. simpl in H. omega.
      clear Heqb.
      unfold HMAC_SHA256.zeroPad. repeat rewrite map_app. 
      assert (LHash: Zlength (SHA256.Hash key) = 32).
        unfold SHA256.Hash. rewrite Zlength_correct, length_SHA256'; reflexivity.
      rewrite sublist_app1; repeat rewrite Zlength_map; try omega. 
      rewrite sublist_same; repeat rewrite Zlength_map; try omega.
      rewrite Zlength_app, Zlength_list_repeat, LHash.
      rewrite sublist_app2; repeat rewrite Zlength_map. 2: omega.
      rewrite LHash, Zminus_diag, Zminus_plus. 
      rewrite sublist_same; repeat rewrite Zlength_map; try rewrite Zlength_list_repeat; trivial. 
      assert (AR1: length (SHA256.Hash key) = 32%nat). unfold SHA256.Hash. rewrite length_SHA256'; reflexivity.
      rewrite AR1. 
      assert (AR2 :64 - 32 = 32). omega. unfold SHA256.BlockSize. rewrite AR2.
      assert (AR3: (64 - 32 = 32)%nat). omega. rewrite AR3. clear AR1 AR2 AR3.

      simpl. cancel. destruct ctxSha. simpl. inv updAbs. simpl in H18; rewrite <- H18. unfold SHA256.Hash. 
      rewrite functional_prog.SHA_256'_eq. cancel.

      Transparent hmac_init_part1_FRAME1. unfold hmac_init_part1_FRAME1. (* remember (default_val t_struct_hmac_ctx_st) as DDD. *) clear. 
       (*cancel. FAILS to solve - terminated after 2mins*)
      apply sepcon_derives.
          (*cancel. FAILS  to solve - terminated after 2mins*)
          Transparent default_val. 
            (*cancel. still FAILS  to solve - terminated after 2mins*) 
             apply derives_refl. (*Succeeds in 1sec*)
          Opaque default_val.
        unfold data_block. normalize. apply andp_left2. cancel. 
      Opaque hmac_init_part1_FRAME1.
   }
Qed.

Lemma Init_part1_keynull Espec (kb ckb cb: block) (kofs ckoff cofs:int) l key kv pad: forall h1
(KL1 : l = Zlength key)
(KL2 : 0 <= l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(*(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)*)
(PostKeyNull : environ -> mpred)
(*Delta_specs := abbreviate : PTree.t funspec*)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb0 : block,
                 (EX  cofs0 : int,
                  (EX  r : Z,
                   PROP  (Vptr cb cofs = Vptr cb0 cofs0 /\ (r = 0 \/ r = 1))
                   LOCAL  (temp _reset (Vint (Int.repr r));
                   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                   lvar _pad (tarray tuchar 64) pad;
                   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
                   temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
                   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                   `(initPostKeyNullConditional r (Vptr cb cofs)
                       (Vptr kb kofs) h1 key (Vptr ckb ckoff));
                   `(K_vector kv)))))
(isbyte_key : Forall isbyteZ key)
(HMS' : reptype t_struct_hmac_ctx_st)
(KHMS : HMS' = HMS)
(PostIf_j_Len : environ -> mpred)
(HeqPostIf_j_Len : PostIf_j_Len =
                  PROP  ()
                  LOCAL  (temp _reset (Vint (Int.repr 1));
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
                  temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
                  SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                  `(data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs));
                  `(data_at Tsh (tarray tuchar (Zlength key))
                      (map Vint (map Int.repr key)) (Vptr kb kofs));
                  `(data_at Tsh (tarray tuchar 64)
                      (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      (Vptr ckb ckoff)); `(K_vector kv)))
(FC_ctx : field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
(FC_md_ctx : field_compatible t_struct_hmac_ctx_st [StructField _md_ctx]
              (Vptr cb cofs))
(FC_cxtkey : field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff))
(ge_64_l : 64 >= l),
@semax CompSpecs Espec (initialized_list [_reset; _j]
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 64)); temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
   temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs)); `(data_at_ Tsh (tarray tuchar 64) pad);
   `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv)))
  (Ssequence
     (Scall None
        (Evar _memcpy
           (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Evar _ctx_key (tarray tuchar 64); Etempvar _key (tptr tuchar);
        Etempvar _len tint])
     (Scall None
        (Evar _memset
           (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Eaddrof
           (Ederef
              (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                 (Etempvar _len tint) (tptr tuchar)) tuchar) (tptr tuchar);
        Econst_int (Int.repr 0) tint;
        Ebinop Osub (Econst_int (Int.repr 64) tuint) (Etempvar _len tint)
          tuint]))
  (overridePost PostIf_j_Len
     (overridePost PostKeyNull (normal_ret_assert PostKeyNull))).
Proof. intros.
     (*call to memcpy*)
     focus_SEP 1 3.
     unfold data_at_. 
     forward_call ((Tsh, Tsh), Vptr ckb ckoff, 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key)), l) v.
     { unfold tarray. unfold field_at_ at 1. rewrite field_at_data_at.
       unfold field_address. rewrite if_true; trivial. simpl. rewrite Int.add_zero.
       rewrite (split2_data_at_Tarray_at_tuchar _ _ l); trivial. 2: omega.
       repeat rewrite sepcon_assoc.
       apply sepcon_derives. eapply derives_trans. apply data_at_memory_block.
          Opaque Z.mul. simpl. rewrite Z.max_r. rewrite Z.mul_1_l. apply derives_refl. omega.
       cancel. }
     { simpl. rewrite Z.max_r. rewrite Z.mul_1_l.  intuition. specialize Int.max_signed_unsigned; omega. omega. }
     normalize. 
     unfold tarray.
     remember (64 - l) as l64.
     simpl. subst v. remember (map Vint (map Int.repr key)) as KCONT.

     (*call memset*)
     forward_call (Tsh, Vptr ckb (Int.add ckoff (Int.repr (Zlength key))), l64, Int.zero)
       vret.
     { rewrite (lvar_eval_var _ _ _ _ H0). split; trivial. }
     { rewrite <- KL1.
       match goal with |- _ * _ * ?A * _ * _ * _ |-- _ => 
                  pull_left A end.
       repeat rewrite sepcon_assoc. apply sepcon_derives; [ | cancel].
       unfold at_offset. simpl.
       eapply derives_trans; try apply data_at_memory_block.
               rewrite sizeof_Tarray. trivial.
       apply Z.max_r. omega. }
     { split; auto. repable_signed. }

     subst PostIf_j_Len.

   normalize. entailer!. 
   rewrite sepcon_comm.
(*   apply sepcon_derives. 
   + unfold field_at_. rewrite field_at_data_at.
     unfold field_address. rewrite if_true; trivial. simpl. rewrite Int.add_zero.
     apply derives_refl'. f_equal. admit.OP--is in comment
   +*) rewrite (split2_data_at_Tarray_at_tuchar Tsh 64 (Zlength key)); 
     try repeat rewrite Zlength_map; try rewrite Zlength_correct, mkKey_length; 
     trivial. 2: omega. 
     unfold at_offset. rewrite sepcon_comm.
     unfold HMAC_SHA256.mkKey. remember (64 - Zlength key) as SF. simpl. 
       remember (Zlength key >? 64).
       destruct b. symmetry in Heqb; apply Zgt_is_gt_bool in Heqb. omega. 
       unfold HMAC_SHA256.zeroPad. repeat rewrite map_app. 
     rewrite sublist_app1; repeat rewrite Zlength_map; try omega.
     rewrite sublist_same; repeat rewrite Zlength_map; trivial.
     rewrite sublist_app2; repeat rewrite Zlength_map; try omega.
     rewrite Zminus_diag, Zlength_app. rewrite Z.add_comm, Z.add_simpl_r. 
     assert (XX: (SHA256.BlockSize - length key = Z.to_nat SF)%nat).
          subst SF. rewrite Zlength_correct, Z2Nat.inj_sub, Nat2Z.id. reflexivity. omega.
     rewrite XX.
     repeat rewrite map_list_repeat. 
     rewrite sublist_same; trivial. 
     cancel.
     do 2 rewrite Zlength_list_repeat. trivial.
Qed.  
  
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
(*(ctxkey : val)*)
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
@semax CompSpecs Espec Delta
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
Proof. intros. subst Delta. abbreviate_semax.
forward_if PostKeyNull.
  { admit. (*denote_tc_comparable k (Vint (Int.repr 0))*) }
  { (* THEN*)
    simpl.  
    unfold force_val2, force_val1 in H; simpl in H. 
    unfold initPre. 
    destruct k; try solve [eapply semax_pre; try eapply semax_ff; entailer].
    (*key' is integer, ie Null*)
      remember (Int.eq i Int.zero) as d.
      destruct d; try solve [eapply semax_pre; try eapply semax_ff; entailer].
      apply binop_lemmas2.int_eq_true in Heqd. simpl in *. subst i.
      elim H. reflexivity.
    (*key' is ptr*)
    normalize. clear H.
    assert_PROP (isptr c). entailer. apply isptrD in H. destruct H as [cb [cofs CC]]; subst c.
    rename b into kb; rename i into kofs.
    assert_PROP (Forall isbyteZ key).
      { unfold data_block. entailer. }
    rename H into isbyte_key. 
    replace_SEP 1 (`(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))).
       unfold data_block. entailer.

    forward.
    forward. (*j=HMAC_MAX_MD_CBLOCK*)
    simpl.

    (* Issue: Potential Coq (8.4?) bug about type equalities*)
(*    assert (exists keyedHMS': reptype t_struct_hmac_ctx_st, keyedHMS'=keyedHMS). exists keyedHMS; reflexivity.
    destruct H as [keyedHMS' KHMS].
*)
    assert (exists HMS': reptype t_struct_hmac_ctx_st, HMS'=HMS). exists HMS; reflexivity.
    destruct H as [HMS' KHMS].

    remember
     (PROP  ()
      LOCAL  (temp _reset (Vint (Int.repr 1));
        lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); lvar _pad (tarray tuchar 64) pad;
        temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
        temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
      SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
            `(data_at Tsh t_struct_hmac_ctx_st (*keyedHMS'*) HMS' (Vptr cb cofs));
            `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs));
           `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                  (Vptr ckb ckoff));
          `(K_vector kv))) as PostIf_j_Len.

    assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)). entailer.
    rename H into FC_ctx.

    assert (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)).
    { red. red in FC_ctx. intuition. split; trivial. left. reflexivity. }
    rename H into FC_md_ctx.

    assert_PROP (field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff)). entailer.
    rename H into FC_cxtkey.

    forward_if PostIf_j_Len. 
    { (* j < len*) 
      rename H into lt_64_l.
      eapply (Init_part1_keynonnull Espec kb ckb cb kofs ckoff cofs l key kv pad h1); try eassumption.
    }
    { (* j >= len*)
      rename H into ge_64_l.
      eapply (Init_part1_keynull Espec kb ckb cb kofs ckoff cofs l key kv pad h1); try eassumption.
    }
  intros ek vl. apply andp_left2.
   unfold POSTCONDITION, abbreviate.
   unfold overridePost, initPostKeyNullConditional. 
   if_tac; trivial. normalize.
   subst.
   Exists cb. Exists cofs. Exists 1. entailer. cancel. 
  }
  { (*key == NULL*)
     forward. rewrite HeqPostKeyNull; clear HeqPostKeyNull. 
     unfold initPre, initPostKeyNullConditional.
     destruct key'; try contradiction. subst k. entailer.
     (*integer*)
        unfold hmacstate_PreInitNull. normalize.
        rewrite data_at_isptr.
        normalize. apply isptrD in Pctx'. destruct Pctx' as [cb [cofs CTX']].
        Exists cb. Exists cofs. Exists 0. entailer. rewrite if_true; trivial. 
        cancel.
        Exists r. Exists v. normalize. cancel. } 
  { (*side condition of forward_if key != NULL*)
    intros. apply andp_left2. unfold POSTCONDITION, abbreviate, overridePost. 
    if_tac. unfold normal_ret_assert. entailer.
    apply derives_refl. }
Qed.




