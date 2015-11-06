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
       (nested_field_type t_struct_hmac_ctx_st [StructField 13%positive])
       (fst (default_val t_struct_hmac_ctx_st))
       (field_address t_struct_hmac_ctx_st [StructField 13%positive]
          (Vptr cb cofs)). 
Opaque hmac_init_part1_FRAME2.

Lemma Init_part1_keynonnull Espec (kb ckb cb: block) (kofs ckoff cofs:int) l key kv pad: forall h1
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
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
      unfold data_at_ at 1. unfold field_at_ at 1.
      simpl.
      Time unfold_field_at 1%nat. (*7.7*)
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      unfold field_address. rewrite if_true by trivial.
      simpl @nested_field_type. simpl @nested_field_offset.
      Time normalize. (*2.6*) 

      (*new: extract info from field_address as early as possible*)
      assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _md_ctx]
                          (Vptr cb cofs))) as FA_MDCTX by entailer!.
 (*
      apply isptrD in H; destruct H as [? [? PT]]; rewrite PT.
      unfold field_address in PT.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
           (Vptr cb cofs)); inversion PT; clear PT. 
      subst x x0.
      rename f into FC.*)
(*      subst PAD. normalize.*)
Time      forward_call (Vptr cb cofs). (*Issue: takes 5mins... [now takes 18 sec] *)
      forward_call (init_s256abs, key, Vptr cb cofs, Vptr kb kofs, Tsh, l, kv) ctxSha.
      { unfold data_block.
        change_compspecs CompSpecs. (* needed, because spec_sha.compspecs was hidden by data_block *)
        (*Issue: calling entailer or normalize here yields 
             "Anomaly: undefined_evars_of_term: evar not found. Please report."*)
       rewrite prop_true_andp by auto.
       cancel.
      }
      { clear Frame HeqPostIf_j_Len HeqPostKeyNull.
        specialize Int.max_signed_unsigned.
        subst l. intuition.
      }
      unfold map at 1. (* this should not be necessary *)
      rename H into updAbs.
      rewrite sublist_same in updAbs; trivial.

     (*call Final*)
     focus_SEP 6. unfold data_at_ at 1. unfold field_at_.
     Time rewrite field_at_data_at at 1. (* 5.2 sec*)
     unfold field_address. rewrite if_true by assumption.
     simpl. rewrite Int.add_zero.

    assert_PROP (field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff)) as FC_ctxkey.
    { Time normalize. (*1.7*) }

     replace_SEP 0 (`(memory_block Tsh 64 (Vptr ckb ckoff))).
     { Time entailer!. (*2.7*) apply data_at_memory_block. }
    
     Time specialize (memory_block_split Tsh ckb (Int.unsigned ckoff) 32 32).
     rewrite Int.repr_unsigned.
     change (32+32) with 64.
     Opaque Zplus.
     intros MBS; rewrite MBS; clear MBS; trivial. 
     Focus 2. destruct (Int.unsigned_range ckoff). split; try omega.
              red in FC_ctxkey. simpl in FC_ctxkey. intuition.
     Time normalize. (*3.2*)

     Time gather_SEP 4 5 6 7. (*0.1*)
     replace_SEP 0 (`(hmac_init_part1_FRAME1 key kb kofs cb cofs pad)).
     { Transparent hmac_init_part1_FRAME1. unfold hmac_init_part1_FRAME1. Opaque hmac_init_part1_FRAME1.
       Time entailer!. (*10*)
       apply derives_refl.
     } 
     Time forward_call (ctxSha, Vptr ckb ckoff, Vptr cb cofs, Tsh, kv). (*4.7*) (*with transparent hmac_init_part1_FRAME1 it's a bit faster, but then unfolds hmac_init_part1_FRAME in the precondition of the next goal*) 
     replace_SEP 1 (`(hmac_init_part1_FRAME2 cb cofs)).
     { Transparent hmac_init_part1_FRAME2. unfold hmac_init_part1_FRAME2. Opaque hmac_init_part1_FRAME2.
       Time entailer!. (*3.8*)
       unfold data_at_, field_at_.
       rewrite field_at_data_at.
       unfold field_address. rewrite if_true; trivial. rewrite if_true; trivial. }

     (*call memset*) 
     unfold tarray in *.
     Time forward_call (Tsh, Vptr ckb (Int.repr (Int.unsigned ckoff + 32)), 32, Int.zero)
        vret. (*9.1*)
     { rewrite (lvar_eval_var _ _ _ _ H0). split; trivial. }
     { subst PostIf_j_Len.
       Time entailer!. (*11*)
       unfold data_block. simpl. Time normalize. (*1.4*) 
       unfold HMS.
       assert (SFL: Zlength  (sha_finish ctxSha) = 32).
         destruct ctxSha. simpl. rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity. 
       rewrite SFL.
       assert (LK64: Zlength (HMAC_SHA256.mkKey key) = 64).
         unfold HMAC_SHA256.mkKey.
         remember (Zlength key >? Z.of_nat SHA256.BlockSize).
         destruct b; rewrite Zlength_correct, zeroPad_BlockSize. reflexivity. 
                     unfold SHA256.Hash. rewrite length_SHA256'. unfold SHA256.DigestLength, SHA256.BlockSize. omega.
         reflexivity. apply Nat2Z.inj_le.
         specialize (Zgt_cases (Zlength key) (Z.of_nat SHA256.BlockSize)). rewrite <- Heqb. rewrite Zlength_correct; trivial.

      Transparent Z.add. unfold_data_at 3%nat. Opaque Z.add.
      Time normalize. (*1.8*)
      Time rewrite field_at_data_at at 1. (*1.2*)
      simpl @nested_field_type.
 
      unfold tarray.
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
      rewrite Zlength_app, Zlength_list_repeat', LHash.
      rewrite sublist_app2; repeat rewrite Zlength_map. 2: omega.
      rewrite LHash, Zminus_diag, Zminus_plus. 
      rewrite sublist_same; repeat rewrite Zlength_map; try rewrite Zlength_list_repeat; trivial. 
      assert (AR1: length (SHA256.Hash key) = 32%nat). unfold SHA256.Hash. rewrite length_SHA256'; reflexivity.
      rewrite AR1; clear AR1. 
      unfold SHA256.BlockSize.
      change (64 - 32) with 32.
      change ((64 - 32)%nat) with 32%nat.

      simpl. 
      change (@data_at spec_sha.CompSpecs Tsh (Tarray tuchar 32 noattr))
        with (@data_at CompSpecs Tsh (Tarray tuchar 32 noattr)).
      change (Int.repr 0) with Int.zero.
      fold (list_repeat 32 (Vint Int.zero)).
      change 32%nat with (Z.to_nat 32).
      change (Int.repr (Int.unsigned ckoff + 32))
             with (Int.add ckoff (Int.repr 32)).
      Time cancel. (*1.*) 
      destruct ctxSha. simpl. inv updAbs. simpl in H16; rewrite <- H16. unfold SHA256.Hash. 
      rewrite functional_prog.SHA_256'_eq. Time cancel. (*0.6*)

      Transparent hmac_init_part1_FRAME1. unfold hmac_init_part1_FRAME1. Opaque hmac_init_part1_FRAME1.
      clear.
      Time repeat simplify_project_default_val. (*5.2*)
      Time cancel. (* 0.4*)
      unfold data_block. simpl. rewrite sepcon_andp_prop.
      apply andp_left2. Time cancel. (*0.2*)   
      apply derives_refl.
    rewrite Zlength_list_repeat'. trivial.
   }
Time Qed. (*66*)

Lemma Init_part1_keynull Espec (kb ckb cb: block) (kofs ckoff cofs:int) l key kv pad: forall h1
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
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
        Ebinop Osub (Esizeof (tarray tuchar 64) tuint) (Etempvar _len tint)
          tuint]))
  (overridePost PostIf_j_Len
     (overridePost PostKeyNull (normal_ret_assert PostKeyNull))).
Proof. intros.
     (*call to memcpy*)
     focus_SEP 1 3.
     unfold data_at_. 
     Time forward_call ((Tsh, Tsh), Vptr ckb ckoff, 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key)), l) v. (*4.4*)
     { unfold tarray. unfold field_at_ at 1. rewrite field_at_data_at.
       unfold field_address. rewrite if_true; trivial. simpl. rewrite Int.add_zero.
       rewrite (split2_data_at_Tarray_at_tuchar _ _ l); trivial. 2: omega.
       repeat rewrite sepcon_assoc.
       apply sepcon_derives. eapply derives_trans. apply data_at_memory_block.
          Opaque Z.mul. simpl. rewrite Z.max_r. rewrite Z.mul_1_l. apply derives_refl. omega.
       Time cancel. (*2.4*) }
     { simpl. rewrite Z.max_r. rewrite Z.mul_1_l.  intuition. specialize Int.max_signed_unsigned; omega. omega. }
     simpl.
     unfold tarray.
     remember (64 - l) as l64.
     simpl. subst v. remember (map Vint (map Int.repr key)) as KCONT.

     (*call memset*)
     Time forward_call (Tsh, Vptr ckb (Int.add ckoff (Int.repr (Zlength key))), l64, Int.zero)
       vret. (*10.7*)
     { rewrite (lvar_eval_var _ _ _ _ H0). split; trivial. }
     { (*Issue: this side condition is NEW*) 
       apply prop_right. simpl. rewrite Int.mul_commut, Int.mul_one.
       rewrite sub_repr, <- KL1, Heql64. split; trivial. }
     { rewrite <- KL1.
       match goal with |- _ * _ * ?A * _ * _ * _ |-- _ => 
                  pull_left A end.
       repeat rewrite sepcon_assoc. Time apply sepcon_derives; [ | cancel]. (*1.2*)
       unfold at_offset. simpl.
       eapply derives_trans; try apply data_at_memory_block.
               rewrite sizeof_Tarray. trivial.
       apply Z.max_r. omega. }
     { split; auto. repable_signed. }

     subst PostIf_j_Len.

   Time entailer!. (*6.2*)
   rewrite sepcon_comm.
   rewrite (split2_data_at_Tarray_at_tuchar Tsh 64 (Zlength key)); 
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
     change_compspecs CompSpecs.
     change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
     cancel. apply derives_refl.
     do 2 rewrite Zlength_list_repeat'. trivial.
Time Qed. (*18*)

Lemma hmac_init_part1: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(kv : val)
(h1:hmacabs)
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
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
                       (Tfunction
                          (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil)
                          tvoid cc_default))
                    [Eaddrof
                       (Efield
                          (Ederef
                             (Etempvar _ctx
                                (tptr (Tstruct _hmac_ctx_st noattr)))
                             (Tstruct _hmac_ctx_st noattr)) _md_ctx
                          (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))])
                 (Ssequence
                    (Scall None
                       (Evar _SHA256_Update
                          (Tfunction
                             (Tcons (tptr (Tstruct _SHA256state_st noattr))
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx
                                   (tptr (Tstruct _hmac_ctx_st noattr)))
                                (Tstruct _hmac_ctx_st noattr)) _md_ctx
                             (Tstruct _SHA256state_st noattr))
                          (tptr (Tstruct _SHA256state_st noattr));
                       Etempvar _key (tptr tuchar); Etempvar _len tint])
                    (Ssequence
                       (Scall None
                          (Evar _SHA256_Final
                             (Tfunction
                                (Tcons (tptr tuchar)
                                   (Tcons
                                      (tptr (Tstruct _SHA256state_st noattr))
                                      Tnil)) tvoid cc_default))
                          [Evar _ctx_key (tarray tuchar 64);
                          Eaddrof
                            (Efield
                               (Ederef
                                  (Etempvar _ctx
                                     (tptr (Tstruct _hmac_ctx_st noattr)))
                                  (Tstruct _hmac_ctx_st noattr)) _md_ctx
                               (Tstruct _SHA256state_st noattr))
                            (tptr (Tstruct _SHA256state_st noattr))])
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
                    Ebinop Osub (Esizeof (tarray tuchar 64) tuint)
                      (Etempvar _len tint) tuint]))))) Sskip)
  (normal_ret_assert PostKeyNull).
Proof. intros. subst Delta. abbreviate_semax.
forward_if PostKeyNull.
  { apply denote_tc_comparable_split. unfold initPre; normalize. destruct k; try contradiction.
    remember (Int.eq i Int.zero). destruct b. 
     apply binop_lemmas2.int_eq_true in Heqb. rewrite Heqb; apply valid_pointer_zero. entailer. 
     apply sepcon_valid_pointer2. apply sepcon_valid_pointer2.
      apply data_block_valid_pointer. auto. omega. apply valid_pointer_null. }
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
    Time assert_PROP (isptr c) as Pc by entailer!. (*1*)
    apply isptrD in Pc; destruct Pc as [cb [cofs CC]]; subst c.
    rename b into kb; rename i into kofs.
    assert_PROP (Forall isbyteZ key) as isbyte_key.
      { unfold data_block. Time entailer!. (*1.5*) }
    replace_SEP 1 (`(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))).
       Time unfold data_block; entailer!. (*1.5*)

    Time forward. (*2*)
    Time forward. (*j=HMAC_MAX_MD_CBLOCK*) (*1.8*)

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

    Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
      as FC_ctx by entailer!. (*1.7*)

    assert (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)) as  FC_md_ctx.
    { red. clear - FC_ctx. red in FC_ctx; simpl in FC_ctx.
      intuition. split; trivial. left; reflexivity. }

    Time assert_PROP (field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff))
      as FC_cxtkey by entailer!. (*1.9*) 

    Time forward_if PostIf_j_Len. (*5.6*)
    { (* j < len*) 
      rename H into lt_64_l.
      eapply (Init_part1_keynonnull Espec kb ckb cb kofs ckoff cofs l key kv pad h1); try eassumption.
    }
    { (* j >= len*)
      rename H into ge_64_l. unfold MORE_COMMANDS, abbreviate.
      eapply (Init_part1_keynull Espec kb ckb cb kofs ckoff cofs l key kv pad h1); try eassumption.
    }
  intros ek vl. apply andp_left2.
   unfold POSTCONDITION, abbreviate.
   unfold overridePost, initPostKeyNullConditional. 
   if_tac; trivial. Time normalize. (*0.8*)
   subst.
   Exists cb cofs 1. Time entailer!. (*8.1*)
  }
  { (*key == NULL*)
     Time forward. (*0.2*)
     rewrite HeqPostKeyNull; clear HeqPostKeyNull. 
     unfold initPre, initPostKeyNullConditional.
     destruct key'; try contradiction. subst k. Time entailer!. (*4.3*)
     (*integer*)
        unfold hmacstate_PreInitNull. Intros r v.
        rewrite data_at_isptr.
        Time normalize. (*16*) 
        apply isptrD in Pctx'. destruct Pctx' as [cb [cofs CTX']].
        Exists cb cofs 0. rewrite if_true; trivial.
        Exists r v. Time entailer!. (*7*) }
  { (*side condition of forward_if key != NULL*)
    intros. apply andp_left2. unfold POSTCONDITION, abbreviate, overridePost. 
    if_tac. unfold normal_ret_assert. Time entailer!. (*0.2*)
    apply derives_refl. }
Time Qed. (*17*)